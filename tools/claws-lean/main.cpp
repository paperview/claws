// claws-lean: translates a file in the claws C++ subset into Lean 4.
//
// The output is a Lean module of pure definitions. LAWS.lean states facts
// about them and PROOF.lean proves those facts. This tool is trusted: the
// proofs are about its output, so a mistranslation makes a proof say
// nothing about the C++. Keep every rule here small enough to read.
//
// The subset:
// - Types: uint32_t (Lean `BitVec 32`), uint8_t (`BitVec 8`), bool
//   (`Bool`), aggregate structs (`structure`), `enum class` (`inductive`),
//   claws::list<T> (`List`) and claws::vec<T> (`Array`).
// - Bytes: C++ turns a uint8_t into an int in any arithmetic. The subset
//   allows such an int only under `&`, `|`, `^`, `>>` by a literal and
//   comparisons, which keep it nonnegative, so it reads as a BitVec 32.
//   Converting to uint8_t keeps the low 8 bits, as C++ defines.
// - Constants: `inline constexpr` globals of those types, and built-in
//   arrays of them as lookup tables, read as `table[i]`. Each becomes a
//   Lean def of the value Clang computes.
// - claws::vec: `vec<T>{}`, `vec<T>(n, fill)`, `v.size()`, `v[i]`,
//   `v[i] = x` (a functional update, like a struct field) and `v.push(x)`.
//   Each index must be below `v.size()` and each push must leave the size
//   below 2^32, as part of the safety obligation.
// - Functions: parameters by value, `const T&` (read the same as a value)
//   or `T&` (inout), and results by value. A `T&` parameter's final value
//   is returned alongside the result: `bool f(A& a, B& b)` becomes a Lean
//   function returning `Bool × A × B`, and `void` is allowed when there is
//   at least one `T&`. A body holds locals,
//   assignments, `if`, `switch` over an enum class, counting `for` loops
//   and `return`. A function may call itself; Lean must accept that it
//   terminates, so in practice it recurses on the tail of a list.
// - Loops: `for (uint32_t i = start; i < end; ++i)` whose body never
//   returns and assigns neither i nor anything `end` reads. Each loop
//   becomes a recursive Lean function that checks `i < end` on every
//   step, as C++ does, and terminates by `(end - i).toNat`.
// - `while (c) { claws::decreases(m); body }`, whose body may `break`,
//   `continue` and `return`. It becomes a recursive Lean function that
//   starts the next iteration only if m, a uint32_t, has shrunk; the
//   safety obligation proves that it always has.
// - An `if` with one path that leaves and one that falls through moves
//   the code after it into each branch that may fall through.
// - Calls that pass `T&` arguments: each such argument is a variable or
//   field path, which the call rebinds (`let (r, x) := f x`). No other
//   reference argument of the same call may overlap it (exclusivity, as
//   in Hylo): `swap(p.a, p.b)` is fine, `swap(p, p.a)` is not. A by-value
//   argument is copied before the call runs, so it may name the same
//   variable. The call must be a statement, an initializer, the right side
//   of an assignment, or a returned value, since C++ leaves the order of
//   effects inside a larger expression unspecified.
// - Expressions: literals, + - * & | ^ ~ on uint32_t (wrapping, as C++
//   defines for unsigned), comparisons, && || !, ?:, field access,
//   aggregate init, enumerators, `list<T>{}`, `cons(h, t)`,
//   `xs.match(lambda, lambda)`, and calls to functions defined earlier.
// - Partial operations: `/` and `%` need a divisor other than zero,
//   `table[i]` an index below the table's length, and
//   `<<` and `>>` an amount below 32. The value translation is total
//   (Lean's `x / 0 = 0`), and a separate Bool function `f.safe` mirrors f
//   and checks each partial operation on the path f takes. A function's
//   leading `claws::expects(c);` statements are its precondition `f.pre`;
//   a call must establish the callee's `pre`. For each function with
//   something to check, the output ends with an obligation in namespace
//   `<Project>.Laws.Safety`: `∀ args, f.pre args → f.safe args`.
// Everything else is rejected with a reason.
//
// claws library names (claws::list, claws::cons) are recognized only when
// declared under the claws include directory, so a program cannot define
// its own `claws::cons` and have it translated as `::`.

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <fstream>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace clang;

namespace {

llvm::cl::OptionCategory Category("claws-lean options");
llvm::cl::opt<std::string> Namespace("namespace", llvm::cl::Required,
                                     llvm::cl::desc("Lean namespace for the output, such as Clamp.Code"),
                                     llvm::cl::cat(Category));
llvm::cl::opt<std::string> Output("o", llvm::cl::desc("Output file (default: stdout)"),
                                  llvm::cl::value_desc("file"), llvm::cl::cat(Category));
llvm::cl::opt<std::string> DiffCpp("diff-cpp", llvm::cl::desc("Write a C++ differential test harness here"),
                                   llvm::cl::value_desc("file"), llvm::cl::cat(Category));
llvm::cl::opt<std::string> DiffLean("diff-lean", llvm::cl::desc("Write the Lean differential test harness here"),
                                    llvm::cl::value_desc("file"), llvm::cl::cat(Category));
llvm::cl::opt<unsigned> DiffCases("diff-cases", llvm::cl::desc("Inputs per function (default 100)"),
                                  llvm::cl::init(100), llvm::cl::cat(Category));
llvm::cl::opt<unsigned> DiffSeed("diff-seed", llvm::cl::desc("Seed for the inputs (default 1)"), llvm::cl::init(1),
                                 llvm::cl::cat(Category));

// Thrown when a construct is outside the subset. Caught per declaration, so
// one run reports every rejected declaration.
struct Reject {
  SourceLocation Loc;
  std::string Why;
};

[[noreturn]] void reject(SourceLocation Loc, std::string Why) {
  throw Reject{Loc, std::move(Why)};
}

// Lean keywords and names that a C++ identifier must not shadow.
const std::set<std::string> LeanReserved = {
    "abbrev", "at", "attribute", "axiom", "by", "calc", "class", "def", "deriving",
    "do", "else", "end", "example", "exists", "extends", "for", "forall", "from",
    "fun", "have", "if", "import", "in", "inductive", "instance", "let", "local",
    "match", "mut", "namespace", "notation", "open", "private", "Prop", "protected",
    "return", "section", "show", "Sort", "structure", "suffices", "then", "theorem",
    "Type", "universe", "variable", "where", "with",
};

std::string leanName(StringRef Name) {
  std::string S = Name.str();
  if (LeanReserved.count(S) || S.front() == '_') {
    return "«" + S + "»";
  }
  return S;
}

std::string indent(int N) { return std::string(2 * N, ' '); }

// A Lean type as an argument of another type, as in `List (BitVec 32)`.
std::string paren(const std::string &T) { return T.find(' ') == std::string::npos ? T : "(" + T + ")"; }

class Translator {
public:
  explicit Translator(ASTContext &Ctx) : Ctx(Ctx) {
    llvm::SmallString<256> Real;
    if (!llvm::sys::fs::real_path(CLAWS_INCLUDE_ROOT "/claws", Real)) {
      LibraryDir = std::string(Real) + "/";
    }
  }

  void translate(TranslationUnitDecl *TU) {
    const SourceManager &SM = Ctx.getSourceManager();
    for (Decl *D : TU->decls()) {
      if (!SM.isInMainFile(SM.getExpansionLoc(D->getLocation()))) {
        continue;
      }
      try {
        decl(D);
      } catch (const Reject &R) {
        error(R.Loc, R.Why);
      }
    }
  }

  bool failed() const { return Errors > 0; }
  std::string output() const { return Out.str(); }
  const std::vector<std::string> &obligations() const { return Obligations; }

private:
  ASTContext &Ctx;
  std::ostringstream Out;
  int Errors = 0;
  std::set<const RecordDecl *> Structs;
  std::set<const EnumDecl *> Enums;
  std::set<const FunctionDecl *> Functions;
  // `constexpr` globals, and the length of each that is an array.
  std::set<const VarDecl *> Constants;
  std::map<const VarDecl *, uint64_t> ConstArrays;
  const FunctionDecl *Current = nullptr;
  // The function or lambda whose body is being translated. Assignments may
  // target only its own variables.
  const DeclContext *Scope = nullptr;
  // Loop functions of the function being translated, in the order Lean
  // needs them (inner loops first), and how deep the translation is in
  // loop bodies.
  std::vector<std::string> LoopDefs;
  int Loops = 0;
  int LoopDepth = 0;
  // The `while` loop whose body is being translated, if any: where its
  // `continue`, `break` and `return` go. Safe is set while translating
  // its safety function.
  struct LoopCtx {
    std::string Name;
    std::string Args;
    std::vector<const VarDecl *> Mods;
    bool Returns = false;
    const Expr *Cond = nullptr;
    const Expr *Measure = nullptr;
    bool Safe = false;
  };
  const LoopCtx *Loop = nullptr;
  // The `T&` parameters of the function being translated, whether it
  // returns void, and a counter for fresh Lean names. A fresh name has an
  // apostrophe, which no C++ identifier has.
  std::vector<const VarDecl *> Inouts;
  bool VoidFn = false;
  int Fresh = 0;
  // Functions with a `claws::expects` precondition, the name each loop
  // got (so a loop translated twice keeps one name), the safety functions
  // of the current function's loops, and every safety obligation.
  std::set<const FunctionDecl *> HasPre;
  std::map<const Stmt *, std::string> LoopNames;
  std::vector<std::string> SafeLoopDefs;
  std::set<std::string> SafeLoopsDone;
  std::set<std::string> DefinedLoops;
  std::vector<std::string> Obligations;
  // For differential testing: the functions, structs and enums in order,
  // each precondition's C++ source, and which parameters bound a loop or
  // a vec's size (and so get small test values).
  std::vector<const FunctionDecl *> Tested;
  std::vector<const RecordDecl *> StructOrder;
  std::vector<const EnumDecl *> EnumOrder;
  std::map<const FunctionDecl *, std::vector<std::string>> PreSource;
  std::map<const FunctionDecl *, std::set<unsigned>> BoundParams;
  std::set<const VarDecl *> BoundVars;

  // A `T&` parameter, as opposed to one by value or `const T&`.
  static bool isInout(const ParmVarDecl *P) {
    QualType T = P->getType();
    return T->isLValueReferenceType() && !T->getPointeeType().isConstQualified();
  }

  static std::vector<unsigned> inoutParams(const FunctionDecl *F) {
    std::vector<unsigned> Out;
    for (unsigned I = 0; I < F->getNumParams(); ++I) {
      if (isInout(F->getParamDecl(I))) {
        Out.push_back(I);
      }
    }
    return Out;
  }

  // The Lean type of a variable. A parameter's `const T&` or `T&` is T.
  std::string varType(const VarDecl *V) {
    QualType T = V->getType();
    if (isa<ParmVarDecl>(V) && T->isLValueReferenceType()) {
      T = T->getPointeeType().getUnqualifiedType();
    } else if (isa<ParmVarDecl>(V) && T->isRValueReferenceType()) {
      reject(V->getLocation(), "`T&&` parameters are outside the subset");
    }
    return type(T, V->getLocation());
  }
  std::string LibraryDir;
  // The indentation of the statement being translated, for expressions
  // that span lines (a match).
  int ExprDepth = 1;

  // Whether D is declared in the claws library headers.
  bool isLibrary(const Decl *D) {
    const SourceManager &SM = Ctx.getSourceManager();
    auto File = SM.getFileEntryRefForID(SM.getFileID(SM.getSpellingLoc(D->getLocation())));
    llvm::SmallString<256> Real;
    if (LibraryDir.empty() || !File || llvm::sys::fs::real_path(File->getName(), Real)) {
      return false;
    }
    return StringRef(Real).starts_with(LibraryDir);
  }

  bool isLibraryName(const NamedDecl *D, StringRef Qualified) {
    return D->getQualifiedNameAsString() == Qualified && isLibrary(D);
  }

  // The element type of a claws::list<T>.
  std::optional<QualType> listElement(QualType T) {
    auto *R = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T.getCanonicalType()->getAsCXXRecordDecl());
    if (!R || !isLibraryName(R, "claws::list")) {
      return std::nullopt;
    }
    return R->getTemplateArgs()[0].getAsType();
  }

  // The element type of a claws::vec<T>.
  std::optional<QualType> vecElement(QualType T) {
    auto *R = dyn_cast_or_null<ClassTemplateSpecializationDecl>(T.getCanonicalType()->getAsCXXRecordDecl());
    if (!R || !isLibraryName(R, "claws::vec")) {
      return std::nullopt;
    }
    return R->getTemplateArgs()[0].getAsType();
  }

  // The vec a subscript `v[i]` indexes, if E is one.
  const CXXOperatorCallExpr *subscript(const Expr *E) {
    auto *O = dyn_cast<CXXOperatorCallExpr>(E);
    if (O && O->getOperator() == OO_Subscript && O->getNumArgs() == 2 && vecElement(O->getArg(0)->getType())) {
      return O;
    }
    return nullptr;
  }

  // A call to the vec method Name, if E is one.
  const CXXMemberCallExpr *vecMethod(const Expr *E, StringRef Name) {
    auto *C = dyn_cast<CXXMemberCallExpr>(E);
    const CXXMethodDecl *M = C ? C->getMethodDecl() : nullptr;
    if (M && M->getName() == Name && vecElement(Ctx.getCanonicalTagType(M->getParent()))) {
      return C;
    }
    return nullptr;
  }

  const EnumDecl *enumOf(QualType T) {
    auto *E = T.getCanonicalType()->getAsEnumDecl();
    return E && Enums.count(E->getCanonicalDecl()) ? E : nullptr;
  }

  std::string enumerator(const EnumConstantDecl *K) {
    return leanName(cast<EnumDecl>(K->getDeclContext())->getName()) + "." + leanName(K->getName());
  }

  std::string exprAt(const Expr *E, int Depth) {
    int Saved = ExprDepth;
    ExprDepth = Depth;
    std::string S = expr(E);
    ExprDepth = Saved;
    return S;
  }

  void error(SourceLocation Loc, const std::string &Why) {
    ++Errors;
    PresumedLoc P = Ctx.getSourceManager().getPresumedLoc(Loc);
    if (P.isValid()) {
      llvm::errs() << P.getFilename() << ":" << P.getLine() << ":" << P.getColumn() << ": ";
    }
    llvm::errs() << "error: " << Why << "\n";
  }

  std::string where(SourceLocation Loc) {
    PresumedLoc P = Ctx.getSourceManager().getPresumedLoc(Loc);
    return llvm::sys::path::filename(P.getFilename()).str() + ":" + std::to_string(P.getLine());
  }

  // Declarations

  void decl(Decl *D) {
    if (auto *U = dyn_cast<UsingDecl>(D)) {
      // `using claws::list;` only names library declarations.
      for (const UsingShadowDecl *S : U->shadows()) {
        if (!isLibrary(S->getTargetDecl())) {
          reject(U->getLocation(), "`using` may only name claws library declarations");
        }
      }
    } else if (isa<UsingShadowDecl>(D)) {
      // Checked with its UsingDecl.
    } else if (auto *E = dyn_cast<EnumDecl>(D)) {
      enumDecl(E);
    } else if (auto *R = dyn_cast<CXXRecordDecl>(D)) {
      structDecl(R);
    } else if (auto *F = dyn_cast<FunctionDecl>(D)) {
      functionDecl(F);
    } else if (auto *V = dyn_cast<VarDecl>(D)) {
      constantDecl(V);
    } else {
      reject(D->getLocation(), std::string("a ") + D->getDeclKindName() +
                                   " declaration is outside the claws subset");
    }
  }

  void structDecl(CXXRecordDecl *R) {
    if (!R->isStruct()) {
      reject(R->getLocation(), "only `struct` records are in the subset");
    }
    if (!R->isThisDeclarationADefinition()) {
      reject(R->getLocation(), "a struct must be defined where it is declared");
    }
    if (R->getName().empty()) {
      reject(R->getLocation(), "an anonymous struct is outside the subset");
    }
    if (R->getDescribedClassTemplate() || isa<ClassTemplateSpecializationDecl>(R)) {
      reject(R->getLocation(), "templates are outside the subset");
    }
    if (!R->isAggregate() || R->getNumBases() != 0) {
      reject(R->getLocation(), "a struct must be an aggregate with no base classes");
    }
    for (Decl *M : R->decls()) {
      if (isa<FieldDecl>(M) || (isa<CXXRecordDecl>(M) && cast<CXXRecordDecl>(M)->isInjectedClassName())) {
        continue;
      }
      if (M->isImplicit()) {
        continue;
      }
      reject(M->getLocation(), "a struct may hold only data fields");
    }
    std::ostringstream S;
    S << "-- " << where(R->getLocation()) << "\n";
    S << "structure " << leanName(R->getName()) << " where\n";
    for (FieldDecl *F : R->fields()) {
      if (F->isBitField() || F->hasInClassInitializer()) {
        reject(F->getLocation(), "a field may not be a bit-field or have a default initializer");
      }
      if (F->getAccess() != AS_public) {
        reject(F->getLocation(), "every field must be public");
      }
      S << "  " << leanName(F->getName()) << " : " << type(F->getType(), F->getLocation()) << "\n";
    }
    S << "  deriving DecidableEq, Repr, Inhabited\n\n";
    Structs.insert(R);
    StructOrder.push_back(R);
    Out << S.str();
  }

  void enumDecl(EnumDecl *E) {
    if (!E->isScoped()) {
      reject(E->getLocation(), "use `enum class`; a plain enum converts to int");
    }
    if (!E->isThisDeclarationADefinition() || E->enumerators().empty()) {
      reject(E->getLocation(), "an enum must be defined where it is declared, with at least one enumerator");
    }
    std::ostringstream S;
    S << "-- " << where(E->getLocation()) << "\n";
    S << "inductive " << leanName(E->getName()) << " where\n";
    for (const EnumConstantDecl *K : E->enumerators()) {
      S << "  | " << leanName(K->getName()) << "\n";
    }
    S << "  deriving DecidableEq, Repr, Inhabited\n\n";
    Enums.insert(E->getCanonicalDecl());
    EnumOrder.push_back(E);
    Out << S.str();
  }

  // `inline constexpr T name = init;` becomes `def name : T := value`,
  // with the value Clang computes, so the Lean side never redoes C++'s
  // constant arithmetic (which may use int, outside the subset). T is a
  // scalar, a struct, or a built-in array of either: a lookup table, read
  // only as `table[i]`.
  void constantDecl(VarDecl *V) {
    if (!V->isConstexpr() || V->hasLocalStorage() || !V->hasInit()) {
      reject(V->getLocation(), "a global must be a constant: write `inline constexpr`");
    }
    QualType T = V->getType();
    std::string LeanType;
    if (const ConstantArrayType *A = Ctx.getAsConstantArrayType(T)) {
      LeanType = "Array " + paren(type(A->getElementType(), V->getLocation()));
    } else {
      LeanType = type(T, V->getLocation());
    }
    const APValue *Val = V->evaluateValue();
    if (!Val) {
      reject(V->getLocation(), "Clang cannot evaluate this constant");
    }
    std::string Value = constValue(T, *Val, V->getLocation());
    Out << "-- " << where(V->getLocation()) << "\n";
    Out << "def " << leanName(V->getName()) << " : " << LeanType << " :=\n  " << Value << "\n\n";
    Constants.insert(V->getCanonicalDecl());
    if (const ConstantArrayType *A = Ctx.getAsConstantArrayType(T)) {
      ConstArrays[V->getCanonicalDecl()] = A->getSize().getZExtValue();
    }
  }

  // A constant's value as a Lean term of the type its def declares.
  std::string constValue(QualType T, const APValue &V, SourceLocation Loc) {
    if (const ConstantArrayType *A = Ctx.getAsConstantArrayType(T)) {
      std::string S = "#[";
      for (unsigned I = 0; I < V.getArraySize(); ++I) {
        const APValue &E = I < V.getArrayInitializedElts() ? V.getArrayInitializedElt(I) : V.getArrayFiller();
        S += (I ? ", " : "") + constValue(A->getElementType(), E, Loc);
      }
      return S + "]";
    }
    if (isBool(T)) {
      return V.getInt().getBoolValue() ? "true" : "false";
    }
    if (isU8(T) || isU32(T)) {
      uint64_t N = V.getInt().getZExtValue();
      if (N < 10) {
        return std::to_string(N);
      }
      char Hex[16];
      std::snprintf(Hex, sizeof Hex, isU8(T) ? "0x%02llX" : "0x%llX", static_cast<unsigned long long>(N));
      return Hex;
    }
    if (const EnumDecl *E = enumOf(T)) {
      for (const EnumConstantDecl *K : E->enumerators()) {
        if (K->getInitVal() == V.getInt()) {
          return enumerator(K);
        }
      }
    }
    if (const RecordDecl *R = T.getCanonicalType()->getAsRecordDecl(); R && Structs.count(R) && V.isStruct()) {
      std::string S = "{ ";
      unsigned I = 0;
      for (const FieldDecl *F : R->fields()) {
        S += (I ? ", " : "") + leanName(F->getName()) + " := " + constValue(F->getType(), V.getStructField(I), Loc);
        ++I;
      }
      return S + " }";
    }
    reject(Loc, "a constant must be a uint32_t, uint8_t, bool, enum class, struct, or an array of them");
  }

  void functionDecl(FunctionDecl *F) {
    if (isa<CXXMethodDecl>(F)) {
      reject(F->getLocation(), "methods are outside the subset");
    }
    if (F->getDescribedFunctionTemplate() || F->isTemplateInstantiation()) {
      reject(F->getLocation(), "templates are outside the subset");
    }
    if (!F->doesThisDeclarationHaveABody()) {
      reject(F->getLocation(), "a function must be defined where it is declared");
    }
    if (F->isVariadic() || F->isOverloadedOperator() || !F->getIdentifier()) {
      reject(F->getLocation(), "only plain named functions are in the subset");
    }
    for (const FunctionDecl *G : Functions) {
      if (G->getName() == F->getName()) {
        reject(F->getLocation(), "overloads are outside the subset");
      }
    }
    std::ostringstream S;
    S << "-- " << where(F->getLocation()) << "\n";
    S << "def " << leanName(F->getName());
    for (ParmVarDecl *P : F->parameters()) {
      if (P->getName().empty()) {
        reject(P->getLocation(), "every parameter needs a name");
      }
      if (P->hasDefaultArg()) {
        reject(P->getLocation(), "default arguments are outside the subset");
      }
      S << " (" << leanName(P->getName()) << " : " << varType(P) << ")";
    }
    Inouts.clear();
    for (unsigned I : inoutParams(F)) {
      Inouts.push_back(F->getParamDecl(I));
    }
    VoidFn = F->getReturnType()->isVoidType();
    if (VoidFn && Inouts.empty()) {
      reject(F->getLocation(), "a function must return a value or modify a `T&` parameter");
    }
    // The result, then the final value of each `T&` parameter.
    std::string Result = VoidFn ? "" : type(F->getReturnType(), F->getLocation());
    for (const VarDecl *V : Inouts) {
      Result += (Result.empty() ? "" : " × ") + varType(V);
    }
    S << " : " << Result << " :=\n";
    Current = F;
    Scope = F;
    BoundVars.clear();
    LoopDefs.clear();
    Loops = 0;
    LoopDepth = 0;
    Fresh = 0;
    SafeLoopDefs.clear();
    auto *Body = cast<CompoundStmt>(F->getBody());
    std::vector<Stmt *> List(Body->body_begin(), Body->body_end());
    // Leading `claws::expects(c);` statements are the precondition.
    std::vector<std::string> Pre;
    while (!List.empty() && isExpects(List.front())) {
      const Expr *C = expectsArg(List.front());
      if (cond(C) != "true") {
        reject(C->getExprLoc(), "a precondition may not itself divide, or shift by a variable amount");
      }
      ExprDepth = 1;
      Pre.push_back(boolExpr(C));
      PreSource[F].push_back(Lexer::getSourceText(CharSourceRange::getTokenRange(C->getSourceRange()),
                                                  Ctx.getSourceManager(), Ctx.getLangOpts())
                                 .str());
      List.erase(List.begin());
    }
    std::string Params;
    std::string Args;
    for (ParmVarDecl *P : F->parameters()) {
      Params += " (" + leanName(P->getName()) + " : " + varType(P) + ")";
      Args += " " + leanName(P->getName());
    }
    std::string PreDef;
    if (!Pre.empty()) {
      PreDef = "-- " + where(F->getLocation()) + ", the precondition of " + F->getName().str() + "\ndef " +
               leanName(F->getName()) + ".pre" + Params + " : Bool :=\n  " + conj(Pre) + "\n\n";
      HasPre.insert(F->getCanonicalDecl());
    }
    if (VoidFn && flow(List) != Flow::Returns) {
      // A void function may fall off its end, which returns.
      List.push_back(ReturnStmt::Create(Ctx, Body->getRBracLoc(), nullptr, nullptr));
    }
    S << indent(1) << stmts(List, Body->getRBracLoc(), 1) << "\n\n";
    // The safety function, if anything on any path needs checking.
    Fresh = 0;
    ExprDepth = 1;
    std::string Safe = sstmts(List, Body->getRBracLoc(), 1);
    std::string SafeDef;
    if (Safe != "true") {
      SafeDef = "-- " + where(F->getLocation()) + ", the safety of " + F->getName().str() + "\ndef " +
                leanName(F->getName()) + ".safe" + Params + " : Bool :=\n  " + Safe + "\n\n";
      std::string Q = Namespace + "." + leanName(F->getName());
      std::string Binders;
      for (ParmVarDecl *P : F->parameters()) {
        Binders += " (" + leanName(P->getName()) + " : " + varType(P) + ")";
      }
      std::string Claim = Q + ".safe" + Args + " = true";
      if (!Pre.empty()) {
        Claim = Q + ".pre" + Args + " = true → " + Claim;
      }
      // A vec never holds 2^32 elements, since push keeps it below.
      for (ParmVarDecl *P : F->parameters()) {
        if (vecElement(P->getType().getNonReferenceType())) {
          Claim = leanName(P->getName()) + ".size < 4294967296 → " + Claim;
        }
      }
      Obligations.push_back("-- " + where(F->getLocation()) + ": " + F->getName().str() +
                            " never divides by zero, shifts by 32 or more, indexes a vec or a\n-- table out of "
                            "bounds, grows a vec to 2^32 elements, runs a while loop whose\n-- measure fails to "
                            "shrink, or calls a function outside its claws::expects,\n-- whenever its own "
                            "claws::expects hold.\ndef " +
                            leanName(F->getName()) + " : Prop :=\n  " +
                            (Binders.empty() ? Claim : "∀" + Binders + ", " + Claim) + "\n\n");
    }
    boundParams(F, List);
    Current = nullptr;
    Functions.insert(F);
    Tested.push_back(F);
    Out << PreDef;
    for (const std::string &L : LoopDefs) {
      Out << L;
    }
    Out << S.str();
    for (const std::string &L : SafeLoopDefs) {
      Out << L;
    }
    Out << SafeDef;
  }

  bool isExpects(const Stmt *S) {
    auto *E = dyn_cast<Expr>(S);
    if (!E) {
      return false;
    }
    if (auto *W = dyn_cast<ExprWithCleanups>(E)) {
      E = W->getSubExpr();
    }
    auto *C = dyn_cast<CallExpr>(E);
    return C && C->getDirectCallee() && isLibraryName(C->getDirectCallee(), "claws::expects");
  }

  static const Expr *expectsArg(const Stmt *S) {
    auto *E = cast<Expr>(S);
    if (auto *W = dyn_cast<ExprWithCleanups>(E)) {
      E = W->getSubExpr();
    }
    return cast<CallExpr>(E)->getArg(0);
  }

  // Types

  bool isU32(QualType T) {
    auto *B = T.getCanonicalType()->getAs<BuiltinType>();
    return B && B->getKind() == BuiltinType::UInt && Ctx.getTypeSize(T) == 32;
  }

  bool isBool(QualType T) { return T.getCanonicalType()->isBooleanType(); }

  bool isU8(QualType T) {
    auto *B = T.getCanonicalType()->getAs<BuiltinType>();
    return B && B->getKind() == BuiltinType::UChar;
  }

  // An `int`. C++ makes one of an unsuffixed literal, and of a uint8_t in
  // any arithmetic or comparison (integer promotion). The subset lets an
  // int arise only from those and from `&`, `|`, `^` and `>>` by a
  // literal, which keep it between 0 and 2^31 - 1. Such an int is the same
  // BitVec 32 as the uint32_t of the same value, and its comparisons agree.
  bool isInt(QualType T) {
    auto *B = T.getCanonicalType()->getAs<BuiltinType>();
    return B && B->getKind() == BuiltinType::Int && Ctx.getTypeSize(T) == 32;
  }

  std::string type(QualType T, SourceLocation Loc) {
    if (T->isReferenceType() || T->isPointerType()) {
      reject(Loc, "pointers are outside the subset, and references may only be parameters (`T&` or `const T&`)");
    }
    if (isU32(T)) {
      return "BitVec 32";
    }
    if (isU8(T)) {
      return "BitVec 8";
    }
    if (isBool(T)) {
      return "Bool";
    }
    if (const EnumDecl *E = enumOf(T)) {
      return leanName(E->getName());
    }
    if (auto Elem = listElement(T)) {
      return "List " + paren(type(*Elem, Loc));
    }
    if (auto Elem = vecElement(T)) {
      return "Array " + paren(type(*Elem, Loc));
    }
    if (auto *R = T.getCanonicalType()->getAsRecordDecl()) {
      if (auto *C = dyn_cast<CXXRecordDecl>(R); C && C->isLambda()) {
        reject(Loc, "a lambda may appear only as an argument of `match`");
      }
      if (Structs.count(R)) {
        return leanName(R->getName());
      }
    }
    reject(Loc, "type `" + T.getAsString(Ctx.getPrintingPolicy()) +
                    "` is outside the subset (use uint32_t, uint8_t, bool, claws::list, claws::vec, or a claws struct or enum class)");
  }

  // Statements
  //
  // A list of statements becomes one Lean expression. In value mode (Tail
  // is null) the list must end in `return`, and the expression is the
  // returned value. In effect mode (Tail names variables) the list must
  // never return, and the expression is the tuple of those variables'
  // values when the list finishes.
  //
  // An assignment `x = e;` becomes `let x := e`, shadowing x. A branch,
  // block or switch that falls through becomes an effect-mode expression
  // over the outer variables it assigns, bound back with
  // `let (a, b) := ..`. A branch must either always return or never
  // return, so the code after a branch is never duplicated.

  using Vars = std::vector<const VarDecl *>;

  enum class Flow { Falls, Returns, Mixed };

  // Whether a statement list always returns, never returns, or mixes.
  Flow flow(ArrayRef<Stmt *> List) {
    for (size_t I = 0; I < List.size(); ++I) {
      Flow F = flow(List[I]);
      if (F == Flow::Returns) {
        return Flow::Returns;
      }
      if (F == Flow::Mixed) {
        // `if (c) return a; ... return b;` still always returns.
        return flow(List.drop_front(I + 1)) == Flow::Returns ? Flow::Returns : Flow::Mixed;
      }
    }
    return Flow::Falls;
  }

  Flow flow(Stmt *S) {
    // `break` and `continue` end the path through a loop body, as `return`
    // ends the path through a function.
    if (isa<ReturnStmt>(S) || isa<BreakStmt>(S) || isa<ContinueStmt>(S)) {
      return Flow::Returns;
    }
    if (auto *W = dyn_cast<WhileStmt>(S)) {
      return containsReturn(W->getBody()) ? Flow::Mixed : Flow::Falls;
    }
    if (auto *C = dyn_cast<CompoundStmt>(S)) {
      return flow(C->body());
    }
    if (auto *If = dyn_cast<IfStmt>(S)) {
      Flow T = flow(If->getThen());
      Flow E = If->getElse() ? flow(If->getElse()) : Flow::Falls;
      return T == E ? T : Flow::Mixed;
    }
    if (auto *F = dyn_cast<ForStmt>(S)) {
      return flow(body(F->getBody())) == Flow::Falls ? Flow::Falls : Flow::Mixed;
    }
    if (auto *Sw = dyn_cast<SwitchStmt>(S)) {
      std::optional<Flow> All;
      for (const Arm &A : arms(Sw)) {
        Flow F = A.Break ? Flow::Falls : flow(A.Body);
        All = !All || *All == F ? F : Flow::Mixed;
      }
      return All.value_or(Flow::Falls);
    }
    return Flow::Falls;
  }

  // Whether S contains a `return`, outside any lambda.
  static bool containsReturn(const Stmt *S) {
    if (!S || isa<LambdaExpr>(S)) {
      return false;
    }
    if (isa<ReturnStmt>(S)) {
      return true;
    }
    for (const Stmt *C : S->children()) {
      if (containsReturn(C)) {
        return true;
      }
    }
    return false;
  }

  // Code after a branch can be moved into the branch (when one path of
  // the branch returns and another falls through) only if no name the
  // branch declares hides one the code after it uses.
  void noCapture(ArrayRef<Stmt *> Branch, ArrayRef<Stmt *> Rest) {
    std::set<std::string> Declared;
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S || isa<LambdaExpr>(S)) {
        return;
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        for (const Decl *X : D->decls()) {
          if (auto *V = dyn_cast<VarDecl>(X)) {
            Declared.insert(V->getNameAsString());
          }
        }
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    for (const Stmt *S : Branch) {
      walk(S);
    }
    for (const Stmt *S : Rest) {
      for (const VarDecl *V : referenced(S)) {
        if (Declared.count(V->getNameAsString())) {
          reject(S->getBeginLoc(), "`" + V->getNameAsString() +
                                       "` here would be hidden by a variable of the same name declared in the branch "
                                       "before it; rename one of them");
        }
      }
    }
  }

  static std::vector<Stmt *> concat(ArrayRef<Stmt *> A, ArrayRef<Stmt *> B) {
    std::vector<Stmt *> Out(A.begin(), A.end());
    Out.insert(Out.end(), B.begin(), B.end());
    return Out;
  }

  bool isDecreases(const Stmt *S) {
    auto *E = dyn_cast<Expr>(S);
    if (auto *W = E ? dyn_cast<ExprWithCleanups>(E) : nullptr) {
      E = W->getSubExpr();
    }
    auto *C = E ? dyn_cast<CallExpr>(E) : nullptr;
    return C && C->getDirectCallee() && isLibraryName(C->getDirectCallee(), "claws::decreases");
  }

  static std::string items(const std::vector<const VarDecl *> &Vs) {
    std::string S;
    for (const VarDecl *V : Vs) {
      S += (S.empty() ? "" : ", ") + leanName(V->getName());
    }
    return S;
  }

  // What leaving the current loop with `break`, or by its condition,
  // gives: the variables it assigns, after `none` if it may also return.
  std::string loopExit() {
    if (Loop->Safe) {
      return "true";
    }
    return Loop->Returns ? "(none, " + items(Loop->Mods) + ")" : tuple(Loop->Mods);
  }

  // What `continue`, or the end of the body, gives: the next iteration,
  // if the condition holds and the measure has shrunk. A measure that has
  // not shrunk stops the loop here; the safety function reports it, so
  // the obligation proves it never happens.
  std::string loopNext(int Depth) {
    std::string Call = Loop->Name + (Loop->Safe ? ".safe" : "") + Loop->Args;
    std::string Stuck = Loop->Safe ? "false" : loopExit();
    ExprDepth = Depth + 1;
    std::string M = expr(Loop->Measure);
    std::string Step = "if hd' : " + M + " < m' then\n" + indent(Depth + 2) + Call + "\n" + indent(Depth + 1) +
                       "else\n" + indent(Depth + 2) + Stuck;
    ExprDepth = Depth;
    std::string C = boolExpr(Loop->Cond);
    if (Loop->Safe) {
      Step = guard(cond(Loop->Measure), Step, Depth + 1);
    }
    std::string Out = "if " + C + " then\n" + indent(Depth + 1) + Step + "\n" + indent(Depth) + "else\n" +
                      indent(Depth + 1) + loopExit();
    return Loop->Safe ? guard(cond(Loop->Cond), Out, Depth) : Out;
  }

  // A function's result for `return V`: with the final value of each
  // `T&` parameter, or, inside a loop, as the loop's early exit.
  std::string returned(const std::string &V) {
    if (Loop) {
      return "(some " + V + ", " + items(Loop->Mods) + ")";
    }
    if (Inouts.empty()) {
      return V;
    }
    if (VoidFn) {
      return tuple(Inouts);
    }
    return "(" + V + ", " + items(Inouts) + ")";
  }

  // One step of an assignment target: a field, or an index into a vec.
  struct Step {
    const FieldDecl *Field = nullptr;
    const Expr *Index = nullptr;
  };
  using Path = std::vector<Step>;

  // The variable at the root of an assignment target such as `s.max` or
  // `v[i].x`.
  static const VarDecl *rootVar(const Expr *E) {
    while (true) {
      E = E->IgnoreParenImpCasts();
      if (auto *M = dyn_cast<MemberExpr>(E)) {
        E = M->getBase();
      } else if (auto *O = dyn_cast<CXXOperatorCallExpr>(E); O && O->getOperator() == OO_Subscript) {
        E = O->getArg(0);
      } else if (auto *R = dyn_cast<DeclRefExpr>(E)) {
        return dyn_cast<VarDecl>(R->getDecl());
      } else {
        return nullptr;
      }
    }
  }

  // The target of an assignment expression, if E is one.
  static const Expr *assignedTo(const Stmt *S) {
    if (auto *B = dyn_cast<BinaryOperator>(S); B && B->isAssignmentOp()) {
      return B->getLHS();
    }
    if (auto *U = dyn_cast<UnaryOperator>(S); U && U->isIncrementDecrementOp()) {
      return U->getSubExpr();
    }
    if (auto *O = dyn_cast<CXXOperatorCallExpr>(S); O && O->getOperator() == OO_Equal && O->getNumArgs() == 2) {
      return O->getArg(0);
    }
    // `v.push(x)` assigns v.
    if (auto *C = dyn_cast<CXXMemberCallExpr>(S); C && C->getMethodDecl() && C->getMethodDecl()->getName() == "push") {
      return C->getImplicitObjectArgument();
    }
    return nullptr;
  }

  // The variables of the current scope that S assigns, excluding those S
  // declares itself, in declaration order.
  Vars modified(ArrayRef<Stmt *> List) {
    std::set<const VarDecl *> Assigned, Declared;
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S) {
        return;
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        for (const Decl *X : D->decls()) {
          if (auto *V = dyn_cast<VarDecl>(X)) {
            Declared.insert(V);
          }
        }
      }
      if (const Expr *T = assignedTo(S)) {
        if (const VarDecl *V = rootVar(T); V && V->getDeclContext() == Scope) {
          Assigned.insert(V);
        }
      }
      if (auto *C = dyn_cast<CallExpr>(S); C && C->getDirectCallee()) {
        for (unsigned I : inoutParams(C->getDirectCallee())) {
          if (const VarDecl *V = I < C->getNumArgs() ? rootVar(C->getArg(I)) : nullptr;
              V && V->getDeclContext() == Scope) {
            Assigned.insert(V);
          }
        }
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    for (const Stmt *S : List) {
      walk(S);
    }
    Vars Out;
    for (const VarDecl *V : Assigned) {
      if (!Declared.count(V)) {
        Out.push_back(V);
      }
    }
    const SourceManager &SM = Ctx.getSourceManager();
    std::sort(Out.begin(), Out.end(), [&](const VarDecl *A, const VarDecl *B) {
      return SM.isBeforeInTranslationUnit(A->getLocation(), B->getLocation());
    });
    return Out;
  }

  static std::string tuple(const Vars &Vs) {
    if (Vs.size() == 1) {
      return leanName(Vs[0]->getName());
    }
    std::string S = "(";
    for (size_t I = 0; I < Vs.size(); ++I) {
      S += (I ? ", " : "") + leanName(Vs[I]->getName());
    }
    return S + ")";
  }

  // `let (a, b) :=` and an effect-mode expression on the next lines, then
  // the rest of the list. A region that assigns nothing outside itself is
  // checked and dropped, since it cannot change the result.
  std::string bindEffects(const Vars &Mods, const std::string &Region, const std::string &Rest, int Depth) {
    if (Mods.empty()) {
      return Rest;
    }
    return "let " + tuple(Mods) + " :=\n" + indent(Depth + 1) + Region + "\n" + indent(Depth) + Rest;
  }

  std::string stmts(ArrayRef<Stmt *> List, SourceLocation End, int Depth, const Vars *Tail = nullptr) {
    for (size_t I = 0; I < List.size(); ++I) {
      Stmt *S = List[I];
      ArrayRef<Stmt *> Rest = List.drop_front(I + 1);
      auto requireLast = [&](const char *What) {
        if (!Rest.empty()) {
          reject(Rest.front()->getBeginLoc(), std::string("unreachable code after ") + What);
        }
      };
      auto rest = [&](int D) { return stmts(Rest, End, D, Tail); };
      if (isa<NullStmt>(S)) {
        continue;
      }
      if (auto *R = dyn_cast<ReturnStmt>(S); R && Loop && Scope == Current) {
        requireLast("`return`");
        if (Tail) {
          reject(R->getReturnLoc(), "internal: a `return` in a loop region that falls through");
        }
        if (!R->getRetValue()) {
          return returned("()");
        }
        std::string Prefix;
        std::string Value = valueOf(R->getRetValue(), Depth, Prefix);
        return Prefix + returned(Value);
      }
      if ((isa<BreakStmt>(S) || isa<ContinueStmt>(S)) && Loop && Scope == Current) {
        requireLast(isa<BreakStmt>(S) ? "`break`" : "`continue`");
        if (Tail) {
          reject(S->getBeginLoc(), "internal: a `break` or `continue` in a loop region that falls through");
        }
        return isa<BreakStmt>(S) ? loopExit() : loopNext(Depth);
      }
      if (auto *R = dyn_cast<ReturnStmt>(S)) {
        requireLast("`return`");
        // A return from the function itself (not from a match lambda) also
        // hands back the `T&` parameters.
        bool Outer = Scope == Current;
        if (Tail || (!R->getRetValue() && !(Outer && VoidFn))) {
          reject(R->getReturnLoc(), "a `return` must give a value, in code that always returns");
        }
        if (!R->getRetValue()) {
          return tuple(Inouts);
        }
        std::string Prefix;
        std::string Value = valueOf(R->getRetValue(), Depth, Prefix);
        if (Outer && !Inouts.empty()) {
          std::string Outs = tuple(Inouts);
          Value = "(" + Value + ", " + (Inouts.size() == 1 ? Outs : Outs.substr(1, Outs.size() - 2)) + ")";
        }
        return Prefix + Value;
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        if (!D->isSingleDecl() || !isa<VarDecl>(D->getSingleDecl())) {
          reject(D->getBeginLoc(), "declare one local variable per statement");
        }
        auto *V = cast<VarDecl>(D->getSingleDecl());
        if (!V->hasLocalStorage() || !V->hasInit()) {
          reject(V->getLocation(), "a local must be initialized and not `static`");
        }
        type(V->getType(), V->getLocation());
        if (Scope == Current) {
          for (const VarDecl *P : Inouts) {
            if (P->getName() == V->getName()) {
              reject(V->getLocation(), "a local may not shadow the `T&` parameter `" + P->getNameAsString() + "`");
            }
          }
        }
        std::string Prefix;
        std::string Value = valueOf(V->getInit(), Depth, Prefix);
        return Prefix + "let " + leanName(V->getName()) + " := " + Value + "\n" + indent(Depth) + rest(Depth);
      }
      if (auto *E = dyn_cast<Expr>(S)) {
        if (isExpects(E)) {
          reject(E->getExprLoc(), "`claws::expects` must come before any other statement of a function");
        }
        if (isDecreases(E)) {
          reject(E->getExprLoc(), "`claws::decreases` must be the first statement of a `while` body");
        }
        std::string Prefix;
        if (const CallExpr *C = effectCall(E)) {
          effects(C, Depth, Prefix);
          return Prefix + rest(Depth);
        }
        auto [Name, Value] = assignment(E, Depth, Prefix);
        return Prefix + "let " + Name + " := " + Value + "\n" + indent(Depth) + rest(Depth);
      }
      if (auto *C = dyn_cast<CompoundStmt>(S)) {
        Flow F = flow(C->body());
        if (F == Flow::Returns) {
          requireLast("a block that returns");
          return stmts(C->body(), C->getRBracLoc(), Depth);
        }
        if (F == Flow::Mixed) {
          // Some paths through the block leave, others fall through to
          // the rest: the rest moves into the block.
          if (Tail) {
            reject(C->getBeginLoc(), "a block here must either always return or never return");
          }
          noCapture(C->body(), Rest);
          return stmts(concat(C->body(), Rest), End, Depth);
        }
        Vars Mods = modified(C->body());
        std::string Region = stmts(C->body(), C->getRBracLoc(), Depth + 1, &Mods);
        return bindEffects(Mods, Region, rest(Depth), Depth);
      }
      if (auto *If = dyn_cast<IfStmt>(S)) {
        return ifStmt(If, Rest, End, Depth, Tail);
      }
      if (auto *Sw = dyn_cast<SwitchStmt>(S)) {
        return switchStmt(Sw, Rest, End, Depth, Tail);
      }
      if (auto *F = dyn_cast<ForStmt>(S)) {
        return forStmt(F, Rest, End, Depth, Tail);
      }
      if (auto *W = dyn_cast<WhileStmt>(S)) {
        return whileStmt(W, Rest, End, Depth, Tail);
      }
      if (isa<BreakStmt>(S) || isa<ContinueStmt>(S)) {
        reject(S->getBeginLoc(), "`break` and `continue` work only in a `while` body and at the end of a `switch` case");
      }
      if (isa<CXXForRangeStmt>(S)) {
        reject(S->getBeginLoc(), "range `for` is not yet in the subset; write `for (uint32_t i = 0; i < v.size(); ++i)`");
      }
      if (isa<DoStmt>(S)) {
        reject(S->getBeginLoc(), "`do` loops are outside the subset; write a `while` loop");
      }
      reject(S->getBeginLoc(), std::string("a ") + S->getStmtClassName() + " statement is outside the subset");
    }
    if (Tail) {
      return tuple(*Tail);
    }
    if (Loop && Scope == Current) {
      // The end of a loop body starts the next iteration.
      return loopNext(Depth);
    }
    reject(End, "control reaches the end without `return`");
  }

  static std::vector<Stmt *> body(Stmt *S) {
    if (auto *C = dyn_cast<CompoundStmt>(S)) {
      return {C->body_begin(), C->body_end()};
    }
    return {S};
  }

  // The variable of `if (T x = e; c)`, which must be a local with an
  // initializer. It is bound before the `if`, so the code after the `if`
  // must not use another variable of the same name.
  const VarDecl *ifInit(IfStmt *If, ArrayRef<Stmt *> Rest) {
    if (If->getConditionVariable() || If->isConsteval() || If->isConstexpr()) {
      reject(If->getIfLoc(), "only `if (condition)` and `if (T x = e; condition)` are in the subset");
    }
    Stmt *Init = If->getInit();
    if (!Init) {
      return nullptr;
    }
    auto *D = dyn_cast<DeclStmt>(Init);
    auto *V = D && D->isSingleDecl() ? dyn_cast<VarDecl>(D->getSingleDecl()) : nullptr;
    if (!V || !V->hasInit()) {
      reject(Init->getBeginLoc(), "the statement before an `if` condition must declare one initialized local");
    }
    type(V->getType(), V->getLocation());
    noCapture({Init}, Rest);
    return V;
  }

  std::string ifStmt(IfStmt *If, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    if (const VarDecl *V = ifInit(If, Rest)) {
      std::string Prefix;
      std::string Value = valueOf(V->getInit(), Depth, Prefix);
      return Prefix + "let " + leanName(V->getName()) + " := " + Value + "\n" + indent(Depth) +
             ifBody(If, Rest, End, Depth, Tail);
    }
    return ifBody(If, Rest, End, Depth, Tail);
  }

  std::string ifBody(IfStmt *If, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    std::vector<Stmt *> Then = body(If->getThen());
    std::vector<Stmt *> Else = If->getElse() ? body(If->getElse()) : std::vector<Stmt *>();
    SourceLocation ElseEnd = If->getElse() ? If->getElse()->getEndLoc() : If->getEndLoc();
    Flow T = flow(Then);
    Flow E = flow(Else);
    if (T == Flow::Mixed || E == Flow::Mixed) {
      // A branch that sometimes leaves and sometimes falls through: the
      // rest moves into each branch that may fall through, so it appears
      // once per such branch.
      if (Tail) {
        reject(If->getIfLoc(), "each branch of this `if` must either always return or never return");
      }
      ExprDepth = Depth;
      std::string Cond = boolExpr(If->getCond());
      auto branch = [&](ArrayRef<Stmt *> B, Flow F, SourceLocation BEnd) {
        if (F == Flow::Returns) {
          return stmts(B, BEnd, Depth + 1);
        }
        noCapture(B, Rest);
        return stmts(concat(B, Rest), End, Depth + 1);
      };
      std::string A = branch(Then, T, If->getThen()->getEndLoc());
      std::string B = branch(Else, E, ElseEnd);
      return "if " + Cond + " then\n" + indent(Depth + 1) + A + "\n" + indent(Depth) + "else\n" + indent(Depth + 1) + B;
    }
    auto restAt = [&](int D) { return stmts(Rest, End, D, Tail); };
    if (T == Flow::Returns && E == Flow::Returns) {
      if (!Rest.empty()) {
        reject(Rest.front()->getBeginLoc(), "unreachable code after an `if` whose branches all return");
      }
      int Saved = ExprDepth;
      ExprDepth = Depth;
      std::string Cond = boolExpr(If->getCond());
      ExprDepth = Saved;
      std::string A = stmts(Then, If->getThen()->getEndLoc(), Depth + 1);
      std::string B = stmts(Else, ElseEnd, Depth + 1);
      return "if " + Cond + " then\n" + indent(Depth + 1) + A + "\n" + indent(Depth) + "else\n" + indent(Depth + 1) + B;
    }
    if (T == Flow::Falls && E == Flow::Falls) {
      // Both branches fall through: join on the variables either assigns.
      std::vector<Stmt *> Both(Then.begin(), Then.end());
      Both.insert(Both.end(), Else.begin(), Else.end());
      Vars Mods = modified(Both);
      int Saved = ExprDepth;
      ExprDepth = Depth + 1;
      std::string Cond = boolExpr(If->getCond());
      ExprDepth = Saved;
      std::string A = stmts(Then, If->getThen()->getEndLoc(), Depth + 2, &Mods);
      std::string B = stmts(Else, ElseEnd, Depth + 2, &Mods);
      std::string Region = "if " + Cond + " then\n" + indent(Depth + 2) + A + "\n" + indent(Depth + 1) + "else\n" +
                           indent(Depth + 2) + B;
      return bindEffects(Mods, Region, restAt(Depth), Depth);
    }
    // One branch returns and the other falls through to the rest, so the
    // rest appears once, inside the falling branch.
    int Saved = ExprDepth;
    ExprDepth = Depth;
    std::string Cond = boolExpr(If->getCond());
    ExprDepth = Saved;
    auto falling = [&](ArrayRef<Stmt *> Branch, SourceLocation BranchEnd) {
      Vars Mods = modified(Branch);
      std::string Region = stmts(Branch, BranchEnd, Depth + 2, &Mods);
      return bindEffects(Mods, Region, restAt(Depth + 1), Depth + 1);
    };
    std::string A = T == Flow::Returns ? stmts(Then, If->getThen()->getEndLoc(), Depth + 1)
                                       : falling(Then, If->getThen()->getEndLoc());
    std::string B = E == Flow::Returns ? stmts(Else, ElseEnd, Depth + 1) : falling(Else, ElseEnd);
    return "if " + Cond + " then\n" + indent(Depth + 1) + A + "\n" + indent(Depth) + "else\n" + indent(Depth + 1) + B;
  }

  // An assignment statement as the variable it rebinds and its new value.
  std::pair<std::string, std::string> assignment(const Expr *E, int Depth, std::string &Prefix) {
    if (auto *C = dyn_cast<ExprWithCleanups>(E)) {
      E = C->getSubExpr();
    }
    const Expr *Target = assignedTo(E);
    if (!Target) {
      reject(E->getExprLoc(), "an expression statement must be an assignment");
    }
    Path Steps;
    const VarDecl *Root = target(Target, Steps);
    std::string Current = pathText(Root, Steps, Steps.size());
    std::string Value;
    if (const CXXMemberCallExpr *P = vecMethod(E, "push")) {
      Value = "(Array.push " + Current + " " + exprAt(P->getArg(0), Depth) + ")";
    } else if (auto *U = dyn_cast<UnaryOperator>(E)) {
      requireU32(U->getSubExpr());
      Value = "(" + Current + (U->isIncrementOp() ? " + " : " - ") + "1)";
    } else if (auto *O = dyn_cast<CXXOperatorCallExpr>(E)) {
      auto *M = dyn_cast_or_null<CXXMethodDecl>(O->getDirectCallee());
      bool Plain = M && (M->isCopyAssignmentOperator() || M->isMoveAssignmentOperator()) &&
                   (M->isTrivial() || listElement(O->getArg(0)->getType()));
      if (!Plain) {
        reject(O->getOperatorLoc(), "only plain assignment of a struct or list is in the subset");
      }
      Value = valueOf(O->getArg(1), Depth, Prefix);
    } else if (auto *C = dyn_cast<CompoundAssignOperator>(E)) {
      requireU32(C->getLHS());
      const char *Op = nullptr;
      bool Shift = false;
      switch (C->getOpcode()) {
      case BO_AddAssign: Op = "+"; break;
      case BO_SubAssign: Op = "-"; break;
      case BO_MulAssign: Op = "*"; break;
      case BO_AndAssign: Op = "&&&"; break;
      case BO_OrAssign: Op = "|||"; break;
      case BO_XorAssign: Op = "^^^"; break;
      case BO_DivAssign: Op = "/"; break;
      case BO_RemAssign: Op = "%"; break;
      case BO_ShlAssign: Op = "<<<"; Shift = true; break;
      case BO_ShrAssign: Op = ">>>"; Shift = true; break;
      default:
        reject(C->getOperatorLoc(), "operator `" + C->getOpcodeStr().str() + "` is outside the subset");
      }
      std::string Right;
      if (Shift) {
        Right = amount(C->getRHS());
      } else {
        requireU32(C->getRHS());
        if (C->getOpcode() == BO_DivAssign || C->getOpcode() == BO_RemAssign) {
          divisor(C->getRHS());
        }
        // C++17 runs the right side, with any effects, before the update.
        Right = valueOf(C->getRHS(), Depth, Prefix);
      }
      Value = "(" + Current + " " + Op + " " + Right + ")";
    } else {
      auto *B = cast<BinaryOperator>(E);
      type(B->getLHS()->getType(), B->getOperatorLoc());
      Value = valueOf(B->getRHS(), Depth, Prefix);
    }
    return {leanName(Root->getName()), update(Root, Steps, Value)};
  }

  // The value at the first N steps of a path: `s.items`, `(v[i.toNat]!)`.
  std::string pathText(const VarDecl *Root, const Path &Steps, size_t N) {
    std::string Base = leanName(Root->getName());
    for (size_t I = 0; I < N; ++I) {
      if (Steps[I].Field) {
        Base += "." + leanName(Steps[I].Field->getName());
      } else {
        Base = "(" + Base + "[" + expr(Steps[I].Index) + ".toNat]!)";
      }
    }
    return Base;
  }

  // Root with the place at Steps set to Value, from the inside out:
  // `s.a.b = v` is `{ s with a := { s.a with b := v } }`, and `v[i] = x`
  // is `(Array.setIfInBounds v i.toNat x)`.
  std::string update(const VarDecl *Root, const Path &Steps, std::string Value) {
    for (size_t I = Steps.size(); I-- > 0;) {
      std::string Base = pathText(Root, Steps, I);
      if (Steps[I].Field) {
        Value = "{ " + Base + " with " + leanName(Steps[I].Field->getName()) + " := " + Value + " }";
      } else {
        Value = "(Array.setIfInBounds " + Base + " " + expr(Steps[I].Index) + ".toNat " + Value + ")";
      }
    }
    return Value;
  }

  // The variable and path E names, if E is an lvalue such as `s.a` or
  // `v[i]`.
  static const VarDecl *lvalue(const Expr *E, Path &Steps) {
    E = E->IgnoreParens();
    if (auto *C = dyn_cast<ImplicitCastExpr>(E); C && C->getCastKind() == CK_NoOp) {
      return lvalue(C->getSubExpr(), Steps);
    }
    if (auto *M = dyn_cast<MemberExpr>(E); M && !M->isArrow() && isa<FieldDecl>(M->getMemberDecl())) {
      const VarDecl *V = lvalue(M->getBase(), Steps);
      Steps.push_back({cast<FieldDecl>(M->getMemberDecl()), nullptr});
      return V;
    }
    if (auto *O = dyn_cast<CXXOperatorCallExpr>(E); O && O->getOperator() == OO_Subscript && O->getNumArgs() == 2) {
      const VarDecl *V = lvalue(O->getArg(0), Steps);
      Steps.push_back({nullptr, O->getArg(1)});
      return V;
    }
    auto *R = dyn_cast<DeclRefExpr>(E);
    auto *V = R ? dyn_cast<VarDecl>(R->getDecl()) : nullptr;
    return V && V->hasLocalStorage() ? V : nullptr;
  }

  // Whether two paths of one variable may share storage. Different
  // fields are disjoint, and so are two different literal indexes; any
  // other two indexes might be equal, so they may overlap.
  static bool overlap(const Path &A, const Path &B) {
    for (size_t I = 0; I < std::min(A.size(), B.size()); ++I) {
      if (A[I].Field || B[I].Field) {
        if (A[I].Field != B[I].Field) {
          return false;
        }
        continue;
      }
      auto *X = literal(A[I].Index);
      auto *Y = literal(B[I].Index);
      if (X && Y && X->getValue() != Y->getValue()) {
        return false;
      }
    }
    return true;
  }

  // A call to a claws function with `T&` parameters, under the wrappers
  // Clang puts around a value.
  const CallExpr *effectCall(const Expr *E) {
    while (true) {
      if (auto *W = dyn_cast<ExprWithCleanups>(E)) {
        E = W->getSubExpr();
      } else if (auto *B = dyn_cast<CXXBindTemporaryExpr>(E)) {
        E = B->getSubExpr();
      } else if (auto *M = dyn_cast<MaterializeTemporaryExpr>(E)) {
        E = M->getSubExpr();
      } else if (auto *C = dyn_cast<ImplicitCastExpr>(E); C && C->getCastKind() == CK_NoOp) {
        E = C->getSubExpr();
      } else {
        break;
      }
    }
    auto *C = dyn_cast<CallExpr>(E->IgnoreParens());
    if (!C || isa<CXXMemberCallExpr>(C) || isa<CXXOperatorCallExpr>(C) || !C->getDirectCallee()) {
      return nullptr;
    }
    return inoutParams(C->getDirectCallee()).empty() ? nullptr : C;
  }

  // The value of E, after the bindings it needs, which go into Prefix.
  std::string valueOf(const Expr *E, int Depth, std::string &Prefix) {
    if (const CallExpr *C = effectCall(E)) {
      return effects(C, Depth, Prefix);
    }
    return exprAt(E, Depth);
  }

  // A call with `T&` arguments: bind its result and the new values of
  // those arguments, `let (r'1, a, b) := f a b`, then write back any that
  // are field paths. Returns the result's name, or "" for a void call.
  std::string effects(const CallExpr *C, int Depth, std::string &Prefix) {
    const FunctionDecl *F = C->getDirectCallee();
    std::vector<unsigned> Outs = inoutParams(F);
    for (unsigned I : Outs) {
      Path Steps;
      const VarDecl *Root = target(C->getArg(I), Steps);
      for (unsigned J = 0; J < C->getNumArgs(); ++J) {
        if (J == I || !F->getParamDecl(J)->getType()->isReferenceType()) {
          continue;
        }
        Path Other;
        if (lvalue(C->getArg(J), Other) == Root && overlap(Steps, Other)) {
          reject(C->getArg(J)->getExprLoc(), "this argument overlaps another passed to a `T&` parameter of the "
                                             "same call, so the two would alias");
        }
      }
    }
    std::string Call = call(C, true);
    std::vector<std::string> Pattern;
    std::string Updates;
    std::string Result;
    if (!F->getReturnType()->isVoidType()) {
      Result = "r'" + std::to_string(++Fresh);
      Pattern.push_back(Result);
    }
    for (unsigned I : Outs) {
      Path Steps;
      const VarDecl *Root = target(C->getArg(I), Steps);
      if (Steps.empty()) {
        Pattern.push_back(leanName(Root->getName()));
      } else {
        std::string Out = "o'" + std::to_string(++Fresh);
        Pattern.push_back(Out);
        Updates += "let " + leanName(Root->getName()) + " := " + update(Root, Steps, Out) + "\n" + indent(Depth);
      }
    }
    std::string Bind = Pattern[0];
    if (Pattern.size() > 1) {
      Bind = "(";
      for (size_t I = 0; I < Pattern.size(); ++I) {
        Bind += (I ? ", " : "") + Pattern[I];
      }
      Bind += ")";
    }
    Prefix += "let " + Bind + " := " + Call + "\n" + indent(Depth) + Updates;
    return Result;
  }

  // The variable and path an assignment writes, such as s and [.max], or
  // v and [[i], .x].
  const VarDecl *target(const Expr *E, Path &Steps) {
    E = E->IgnoreParens();
    if (auto *C = dyn_cast<ImplicitCastExpr>(E); C && C->getCastKind() == CK_NoOp) {
      return target(C->getSubExpr(), Steps);
    }
    if (auto *M = dyn_cast<MemberExpr>(E)) {
      auto *F = dyn_cast<FieldDecl>(M->getMemberDecl());
      if (M->isArrow() || !F) {
        reject(M->getExprLoc(), "only `variable.field` may be assigned");
      }
      const VarDecl *V = target(M->getBase(), Steps);
      Steps.push_back({F, nullptr});
      return V;
    }
    if (const CXXOperatorCallExpr *O = subscript(E)) {
      const VarDecl *V = target(O->getArg(0), Steps);
      Steps.push_back({nullptr, O->getArg(1)});
      return V;
    }
    auto *R = dyn_cast<DeclRefExpr>(E);
    auto *V = R ? dyn_cast<VarDecl>(R->getDecl()) : nullptr;
    if (!V || !V->hasLocalStorage()) {
      reject(E->getExprLoc(), "only a local variable or parameter may be assigned");
    }
    if (V->getDeclContext() != Scope) {
      reject(E->getExprLoc(), "a lambda may not assign a variable it captures");
    }
    return V;
  }

  // The local variables S reads or writes that it does not declare, in
  // declaration order. A lambda's parameters count as declared inside.
  Vars referenced(const Stmt *Root) {
    std::set<const VarDecl *> Used, Declared;
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S) {
        return;
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        for (const Decl *X : D->decls()) {
          if (auto *V = dyn_cast<VarDecl>(X)) {
            Declared.insert(V);
          }
        }
      }
      if (auto *L = dyn_cast<LambdaExpr>(S)) {
        for (const ParmVarDecl *P : L->getCallOperator()->parameters()) {
          Declared.insert(P);
        }
      }
      if (auto *R = dyn_cast<DeclRefExpr>(S)) {
        if (auto *V = dyn_cast<VarDecl>(R->getDecl()); V && V->hasLocalStorage()) {
          Used.insert(V);
        }
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    walk(Root);
    Vars Out;
    for (const VarDecl *V : Used) {
      if (!Declared.count(V)) {
        Out.push_back(V);
      }
    }
    const SourceManager &SM = Ctx.getSourceManager();
    std::sort(Out.begin(), Out.end(), [&](const VarDecl *A, const VarDecl *B) {
      return SM.isBeforeInTranslationUnit(A->getLocation(), B->getLocation());
    });
    return Out;
  }

  // How a loop's termination is proved. A bound of `v.size()` with element
  // writes to v needs the fact that writing an element keeps the size.
  static std::string decreasing(bool SizeBound) {
    if (SizeBound) {
      return "decreasing_by all_goals (simp only [Array.size_setIfInBounds] at *; bv_omega)";
    }
    return "decreasing_by all_goals bv_omega";
  }

  // Whether E mentions V only as `V.size()`.
  bool onlySize(const Expr *E, const VarDecl *V) {
    bool Ok = true;
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S) {
        return;
      }
      if (auto *C = dyn_cast<CXXMemberCallExpr>(S); C && vecMethod(cast<Expr>(S), "size")) {
        if (auto *R = dyn_cast<DeclRefExpr>(C->getImplicitObjectArgument()->IgnoreParenImpCasts()); R && R->getDecl() == V) {
          return;
        }
      }
      if (auto *R = dyn_cast<DeclRefExpr>(S); R && R->getDecl() == V) {
        Ok = false;
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    walk(E);
    return Ok;
  }

  // Whether every write to V in Body writes an element `V[i]...`, which
  // keeps V's size, and never V itself, a push, or V as a `T&` argument.
  bool onlyElementWrites(ArrayRef<Stmt *> Body, const VarDecl *V) {
    bool Ok = true;
    auto check = [&](const Expr *T) {
      Path Steps;
      if (lvalue(T, Steps) == V && (Steps.empty() || Steps[0].Field)) {
        Ok = false;
      }
    };
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S) {
        return;
      }
      if (const Expr *T = assignedTo(S)) {
        if (isa<CXXMemberCallExpr>(S)) {
          // A push changes the size.
          if (rootVar(T) == V) {
            Ok = false;
          }
        } else {
          check(T);
        }
      }
      if (auto *C = dyn_cast<CallExpr>(S); C && C->getDirectCallee()) {
        for (unsigned I : inoutParams(C->getDirectCallee())) {
          if (I < C->getNumArgs()) {
            check(C->getArg(I));
          }
        }
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    for (const Stmt *S : Body) {
      walk(S);
    }
    return Ok;
  }

  static bool refersTo(const Expr *E, const VarDecl *V) {
    auto *R = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts());
    return R && R->getDecl() == V;
  }

  std::string tupleType(const Vars &Vs) {
    std::string S;
    for (const VarDecl *V : Vs) {
      S += (S.empty() ? "" : " × ") + varType(V);
    }
    return S;
  }

  // `for (uint32_t i = a; i < b; ++i) body` becomes a recursive function
  // over the variables the loop uses, returning those it assigns:
  //
  //   def f.loop1 (b .. s : ..) (i : BitVec 32) : .. :=
  //     if lt' : i < b then
  //       let s := <body>
  //       let i := (i + 1)
  //       f.loop1 b .. s i
  //     else
  //       s
  //   termination_by (b - i).toNat
  //
  // and the loop statement becomes `let s := f.loop1 b .. s a`.
  std::string forStmt(ForStmt *F, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    const char *Shape = "a loop must have the form `for (uint32_t i = start; i < end; ++i)`";
    auto *Init = dyn_cast_or_null<DeclStmt>(F->getInit());
    auto *I = Init && Init->isSingleDecl() ? dyn_cast<VarDecl>(Init->getSingleDecl()) : nullptr;
    if (!I || !I->hasInit() || !isU32(I->getType()) || F->getConditionVariable()) {
      reject(F->getForLoc(), Shape);
    }
    auto *Cond = F->getCond() ? dyn_cast<BinaryOperator>(F->getCond()->IgnoreParens()) : nullptr;
    if (!Cond || Cond->getOpcode() != BO_LT || !refersTo(Cond->getLHS(), I)) {
      reject(F->getForLoc(), Shape);
    }
    const Expr *Inc = F->getInc();
    bool Step = false;
    if (auto *U = Inc ? dyn_cast<UnaryOperator>(Inc) : nullptr) {
      Step = U->isIncrementOp() && refersTo(U->getSubExpr(), I);
    } else if (auto *C = Inc ? dyn_cast<CompoundAssignOperator>(Inc) : nullptr) {
      auto *One = dyn_cast<IntegerLiteral>(C->getRHS()->IgnoreParenImpCasts());
      Step = C->getOpcode() == BO_AddAssign && refersTo(C->getLHS(), I) && One && One->getValue() == 1;
    }
    if (!Step) {
      reject(F->getForLoc(), Shape);
    }
    std::vector<Stmt *> Body = body(F->getBody());
    if (flow(Body) != Flow::Falls) {
      reject(F->getBody()->getBeginLoc(),
             "a `for` body may not `return`, `break` or `continue`; write a `while` loop for that");
    }
    Vars Mods = modified(Body);
    if (std::find(Mods.begin(), Mods.end(), I) != Mods.end()) {
      reject(F->getForLoc(), "the loop counter may not be assigned in the body");
    }
    bool SizeBound = false;
    for (const VarDecl *V : referenced(Cond->getRHS())) {
      bool Changed = V == I || std::find(Mods.begin(), Mods.end(), V) != Mods.end();
      // `i < v.size()` may write elements of v: that keeps its size.
      if (Changed && V != I && onlySize(Cond->getRHS(), V) && onlyElementWrites(Body, V)) {
        SizeBound = true;
        continue;
      }
      if (Changed) {
        reject(Cond->getRHS()->getExprLoc(), "the loop bound may not change inside the loop");
      }
    }
    for (const VarDecl *V : referenced(Cond->getRHS())) {
      BoundVars.insert(V);
    }
    Vars Params = referenced(F);
    // A loop translated twice (once more for f.safe) keeps its name, and
    // its function is emitted once.
    bool Seen = LoopNames.count(F);
    if (!Seen) {
      LoopNames[F] = leanName(Current->getName()) + ".loop" + std::to_string(++Loops);
    }
    std::string Name = LoopNames[F];
    std::string IName = leanName(I->getName());
    std::string Args;
    for (const VarDecl *V : Params) {
      Args += " " + leanName(V->getName());
    }

    ++LoopDepth;
    std::string Bound = exprAt(Cond->getRHS(), 2);
    std::string Region = stmts(Body, F->getBody()->getEndLoc(), 3, &Mods);
    --LoopDepth;
    std::string Next = "let " + IName + " := (" + IName + " + 1)\n" + indent(2) + Name + Args + " " + IName;
    if (!Mods.empty() && !Seen) {
      std::ostringstream D;
      D << "-- " << where(F->getForLoc()) << ", a loop of " << Current->getName().str() << "\n";
      D << "def " << Name;
      for (const VarDecl *V : Params) {
        D << " (" << leanName(V->getName()) << " : " << varType(V) << ")";
      }
      D << " (" << IName << " : BitVec 32) : " << tupleType(Mods) << " :=\n";
      // `lt'` cannot clash with a C++ name, which has no apostrophe.
      D << indent(1) << "if lt' : " << IName << " < " << Bound << " then\n";
      D << indent(2) << bindEffects(Mods, Region, Next, 2) << "\n";
      D << indent(1) << "else\n" << indent(2) << tuple(Mods) << "\n";
      D << "termination_by (" << Bound << " - " << IName << ").toNat\n";
      D << decreasing(SizeBound) << "\n\n";
      // For the validation proofs: the C++ variables the loop's function
      // returns, in order. Not trusted; a wrong list fails the proof.
      D << "def " << Name << ".mods : List String := [";
      for (size_t K = 0; K < Mods.size(); ++K) {
        D << (K ? ", " : "") << "\"" << Mods[K]->getName().str() << "\"";
      }
      D << "]\n\n";
      LoopDefs.push_back(D.str());
    }
    // A loop that assigns nothing outside itself cannot change the result.
    std::string Start = exprAt(I->getInit(), Depth + 1);
    return bindEffects(Mods, "(" + Name + Args + " " + Start + ")", stmts(Rest, End, Depth, Tail), Depth);
  }

  // The parts of `while (c) { claws::decreases(m); body }`, checked.
  struct WhileParts {
    const Expr *Measure;
    std::vector<Stmt *> Body;
    Vars Mods;
    Vars Params;
    bool Returns;
    std::string Name;
    std::string Args;
    std::string Result;
  };

  WhileParts whileParts(WhileStmt *W) {
    if (W->getConditionVariable()) {
      reject(W->getWhileLoc(), "a `while` condition may not declare a variable");
    }
    WhileParts P;
    P.Body = body(W->getBody());
    if (P.Body.empty() || !isDecreases(P.Body.front())) {
      reject(W->getBody()->getBeginLoc(), "a `while` body must begin with `claws::decreases(measure);`, a uint32_t "
                                          "that every iteration makes smaller");
    }
    P.Measure = expectsArg(P.Body.front());
    requireU32(P.Measure);
    P.Body.erase(P.Body.begin());
    P.Mods = modified(P.Body);
    if (P.Mods.empty()) {
      reject(W->getWhileLoc(), "a `while` loop must assign a variable, or its measure cannot shrink");
    }
    P.Returns = containsReturn(W->getBody());
    P.Params = referenced(W);
    if (!LoopNames.count(W)) {
      LoopNames[W] = leanName(Current->getName()) + ".loop" + std::to_string(++Loops);
    }
    P.Name = LoopNames[W];
    for (const VarDecl *V : P.Params) {
      P.Args += " " + leanName(V->getName());
    }
    P.Result = tupleType(P.Mods);
    if (P.Returns) {
      std::string R = VoidFn ? "Unit" : type(Current->getReturnType(), W->getWhileLoc());
      P.Result = "Option " + paren(R) + " × " + P.Result;
    }
    return P;
  }

  // The loop function's header and termination, around its body.
  std::string whileDef(WhileStmt *W, const WhileParts &P, bool Safe, const std::string &Body) {
    std::ostringstream D;
    D << "-- " << where(W->getWhileLoc()) << ", " << (Safe ? "the safety of " : "") << "a loop of "
      << Current->getName().str() << "\n";
    D << "def " << P.Name << (Safe ? ".safe" : "");
    for (const VarDecl *V : P.Params) {
      D << " (" << leanName(V->getName()) << " : " << varType(V) << ")";
    }
    D << " : " << (Safe ? "Bool" : P.Result) << " :=\n";
    D << indent(1) << Body << "\n";
    ExprDepth = 1;
    D << "termination_by (" << expr(P.Measure) << ").toNat\n";
    // hd' compares the measure with m', the let-bound measure at the start
    // of the iteration, which zetaDelta unfolds.
    D << "decreasing_by all_goals ((try simp +zetaDelta only at *); bv_omega)\n\n";
    if (!Safe) {
      // For the validation proofs: the C++ variables the loop's function
      // returns, after the returned value if it has one, and the measure
      // that bounds its passes. Not trusted; a wrong one fails the proof.
      D << "def " << P.Name << ".mods : List String := [";
      for (size_t K = 0; K < P.Mods.size(); ++K) {
        D << (K ? ", " : "") << "\"" << P.Mods[K]->getName().str() << "\"";
      }
      D << "]\n\n";
      D << "def " << P.Name << ".measure";
      for (const VarDecl *V : P.Params) {
        D << " (" << leanName(V->getName()) << " : " << varType(V) << ")";
      }
      ExprDepth = 1;
      D << " : Nat :=\n" << indent(1) << "(" << expr(P.Measure) << ").toNat\n\n";
    }
    return D.str();
  }

  // `while (c) { claws::decreases(m); body }` becomes a recursive function
  // over the variables the loop uses, returning those it assigns, and,
  // first, `some v` if the body ran `return v` (otherwise `none`):
  //
  //   def f.loop1 (n i : ..) : Option Bool × BitVec 32 :=
  //     if c then
  //       let m' := m
  //       <body, where `break` is (none, i), `return v` is (some v, i),
  //        and `continue` or the end of the body is
  //          if c then (if hd' : m < m' then f.loop1 n i else (none, i))
  //          else (none, i)>
  //     else
  //       (none, i)
  //   termination_by m.toNat
  //
  // The statement becomes `let (r'1, i) := f.loop1 n i` and a match on
  // r'1 that returns or runs the rest.
  std::string whileStmt(WhileStmt *W, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    WhileParts P = whileParts(W);
    if (P.Returns && Tail) {
      reject(W->getWhileLoc(), "internal: a loop that returns, in a region that falls through");
    }
    LoopCtx Ctx{P.Name, P.Args, P.Mods, P.Returns, W->getCond(), P.Measure, false};
    const LoopCtx *Outer = Loop;
    Loop = &Ctx;
    ++LoopDepth;
    ExprDepth = 2;
    std::string Cond = boolExpr(W->getCond());
    std::string M = exprAt(P.Measure, 2);
    std::string Body = stmts(P.Body, W->getBody()->getEndLoc(), 2);
    std::string Exit = loopExit();
    --LoopDepth;
    Loop = Outer;
    if (!DefinedLoops.count(P.Name)) {
      DefinedLoops.insert(P.Name);
      LoopDefs.push_back(whileDef(W, P, false,
                                  "if " + Cond + " then\n" + indent(2) + "let m' := " + M + "\n" + indent(2) + Body +
                                      "\n" + indent(1) + "else\n" + indent(2) + Exit));
    }
    std::string Call = "(" + P.Name + P.Args + ")";
    if (!P.Returns) {
      return bindEffects(P.Mods, Call, stmts(Rest, End, Depth, Tail), Depth);
    }
    std::string R = "r'" + std::to_string(++Fresh);
    return "let (" + R + ", " + items(P.Mods) + ") :=\n" + indent(Depth + 1) + Call + "\n" + indent(Depth) +
           "match " + R + " with\n" + indent(Depth) + "| some " + R + " =>\n" + indent(Depth + 1) + returned(R) +
           "\n" + indent(Depth) + "| none =>\n" + indent(Depth + 1) + stmts(Rest, End, Depth + 1, Tail);
  }

  // A while loop is safe when every iteration is and its measure shrinks:
  // a Bool function f.loopN.safe of the same shape.
  std::string swhile(WhileStmt *W, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    WhileParts P = whileParts(W);
    LoopCtx Ctx{P.Name, P.Args, P.Mods, P.Returns, W->getCond(), P.Measure, true};
    const LoopCtx *Outer = Loop;
    Loop = &Ctx;
    ++LoopDepth;
    if (!SafeLoopsDone.count(P.Name)) {
      SafeLoopsDone.insert(P.Name);
      ExprDepth = 2;
      std::string Cond = boolExpr(W->getCond());
      std::string M = exprAt(P.Measure, 2);
      std::string BS = sstmts(P.Body, W->getBody()->getEndLoc(), 2);
      std::string Head = "if " + Cond + " then\n" + indent(2) +
                         guard(cond(P.Measure), "let m' := " + M + "\n" + indent(2) + BS, 2) + "\n" + indent(1) +
                         "else\n" + indent(2) + "true";
      SafeLoopDefs.push_back(whileDef(W, P, true, guard(cond(W->getCond()), Head, 1)));
    }
    --LoopDepth;
    Loop = Outer;
    std::string Check = "(" + P.Name + ".safe" + P.Args + ")";
    std::string K = sstmts(Rest, End, P.Returns ? Depth + 1 : Depth, Tail);
    if (K == "true") {
      return Check;
    }
    std::string Call = "(" + P.Name + P.Args + ")";
    if (!P.Returns) {
      return guard(Check, bindEffects(P.Mods, Call, K, Depth), Depth);
    }
    std::string R = "r'" + std::to_string(++Fresh);
    return guard(Check,
                 "let (" + R + ", " + items(P.Mods) + ") :=\n" + indent(Depth + 1) + Call + "\n" + indent(Depth) +
                     "match " + R + " with\n" + indent(Depth) + "| some _ =>\n" + indent(Depth + 1) +
                     "true\n" + indent(Depth) + "| none =>\n" + indent(Depth + 1) + K,
                 Depth);
  }

  // A switch arm: its patterns, its statements, and whether it ends in
  // `break` (falls out of the switch) or not.
  struct Arm {
    std::vector<std::string> Patterns;
    std::vector<Stmt *> Body;
    bool Default = false;
    bool Break = false;
    SourceLocation Loc;
  };

  std::vector<Arm> arms(SwitchStmt *Sw) {
    auto *Body = dyn_cast<CompoundStmt>(Sw->getBody());
    if (!Body) {
      reject(Sw->getSwitchLoc(), "a `switch` needs a braced body");
    }
    std::vector<Arm> Arms;
    for (Stmt *S : Body->body()) {
      if (!isa<SwitchCase>(S)) {
        if (Arms.empty()) {
          reject(S->getBeginLoc(), "unreachable code before the first `case`");
        }
        Arms.back().Body.push_back(S);
        continue;
      }
      Arms.emplace_back();
      Arms.back().Loc = S->getBeginLoc();
      while (auto *SC = dyn_cast<SwitchCase>(S)) {
        if (auto *C = dyn_cast<CaseStmt>(SC)) {
          auto *Ref = dyn_cast<DeclRefExpr>(C->getLHS()->IgnoreImplicit());
          auto *K = Ref ? dyn_cast<EnumConstantDecl>(Ref->getDecl()) : nullptr;
          if (C->caseStmtIsGNURange() || !K) {
            reject(C->getCaseLoc(), "a `case` must name one enumerator");
          }
          Arms.back().Patterns.push_back(enumerator(K));
        } else {
          Arms.back().Default = true;
        }
        S = SC->getSubStmt();
      }
      Arms.back().Body.push_back(S);
    }
    for (Arm &A : Arms) {
      if (!A.Body.empty() && isa<BreakStmt>(A.Body.back())) {
        A.Body.pop_back();
        A.Break = true;
      }
    }
    return Arms;
  }

  // `switch` over an enum class becomes a match. Either every arm returns,
  // or every arm ends in `break` and the switch joins like an `if`. A
  // `default` no enumerator can reach is dead code, so it is dropped,
  // since Lean rejects a redundant alternative.
  std::string switchStmt(SwitchStmt *Sw, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    if (Loop && flow(Sw) != Flow::Falls) {
      reject(Sw->getSwitchLoc(), "a `switch` inside a `while` body must end every case in `break`");
    }
    if (Sw->getInit() || Sw->getConditionVariable()) {
      reject(Sw->getSwitchLoc(), "only a plain `switch (value)` is in the subset");
    }
    const EnumDecl *E = enumOf(Sw->getCond()->getType());
    if (!E) {
      reject(Sw->getSwitchLoc(), "`switch` works only on a claws enum class");
    }
    std::vector<Arm> Arms = arms(Sw);
    Flow F = flow(Sw);
    if (F == Flow::Mixed) {
      reject(Sw->getSwitchLoc(), "either every case returns or every case ends in `break`");
    }
    for (size_t I = 0; I + 1 < Arms.size(); ++I) {
      if (F == Flow::Falls && !Arms[I].Break) {
        reject(Arms[I].Loc, "a case may not fall through into the next; end it with `break`");
      }
    }
    std::set<std::string> Seen;
    bool HasDefault = false;
    for (const Arm &A : Arms) {
      Seen.insert(A.Patterns.begin(), A.Patterns.end());
      HasDefault |= A.Default;
    }
    size_t Count = std::distance(E->enumerator_begin(), E->enumerator_end());
    bool Covered = Seen.size() == Count;
    if (F == Flow::Returns && !HasDefault && !Covered) {
      reject(Sw->getSwitchLoc(), "a `switch` that returns must cover every enumerator or have a `default`");
    }
    Vars Mods;
    if (F == Flow::Falls) {
      std::vector<Stmt *> All;
      for (const Arm &A : Arms) {
        All.insert(All.end(), A.Body.begin(), A.Body.end());
      }
      Mods = modified(All);
    } else if (!Rest.empty()) {
      reject(Rest.front()->getBeginLoc(), "unreachable code after a `switch` whose cases all return");
    }
    // A joining switch sits one level deeper, under its `let`.
    int D = F == Flow::Falls ? Depth + 1 : Depth;
    const Vars *ArmTail = F == Flow::Falls ? &Mods : nullptr;
    std::string S = switchMatch(
        Sw, D, [&](const Arm &A) { return stmts(A.Body, Sw->getEndLoc(), D + 1, ArmTail); },
        // Enumerators no case names leave every variable as it was.
        F == Flow::Falls && !Mods.empty() ? tuple(Mods) : "");
    if (F == Flow::Returns) {
      return S;
    }
    return bindEffects(Mods, S, stmts(Rest, End, Depth, Tail), Depth);
  }

  // The match a switch becomes, at depth D, with each arm's body from
  // Body. Fallback, if not empty, is the body for enumerators that no case
  // names, when there is no default.
  std::string switchMatch(SwitchStmt *Sw, int D, const std::function<std::string(const Arm &)> &Body,
                          const std::string &Fallback) {
    const EnumDecl *E = enumOf(Sw->getCond()->getType());
    std::vector<Arm> Arms = arms(Sw);
    std::set<std::string> Seen;
    bool HasDefault = false;
    for (const Arm &A : Arms) {
      Seen.insert(A.Patterns.begin(), A.Patterns.end());
      HasDefault |= A.Default;
    }
    bool Covered = Seen.size() == (size_t)std::distance(E->enumerator_begin(), E->enumerator_end());
    // Lean tries alternatives in order, so the wildcard goes last.
    std::stable_partition(Arms.begin(), Arms.end(), [](const Arm &A) { return !A.Default; });
    std::string S = "(match " + exprAt(Sw->getCond(), D) + " with";
    for (Arm &A : Arms) {
      if (A.Default && !Covered) {
        A.Patterns.push_back("_");
      }
      if (A.Patterns.empty()) {
        continue;
      }
      std::string Pats;
      for (const std::string &P : A.Patterns) {
        Pats += (Pats.empty() ? "" : " | ") + P;
      }
      S += "\n" + indent(D) + "| " + Pats + " =>\n" + indent(D + 1) + Body(A);
    }
    if (!HasDefault && !Covered && !Fallback.empty()) {
      S += "\n" + indent(D) + "| _ =>\n" + indent(D + 1) + Fallback;
    }
    return S + ")";
  }

  // Differential testing
  //
  // diffCpp and diffLean write two harnesses that run every function on
  // the same generated inputs and print the results in one format: the
  // result, then after `|` the final value of each `T&` argument. One is
  // C++, compiled with code.hpp, and one is Lean, appended to the
  // translation. A line that differs is a translation bug.

  // Spreads the loop-bound marks from locals to the parameters they come
  // from, through initializers, assignments and calls, until nothing
  // changes. Those parameters get small test values.
  void boundParams(const FunctionDecl *F, ArrayRef<Stmt *> Body) {
    bool Changed = true;
    auto add = [&](const Stmt *S) {
      for (const VarDecl *V : referenced(S)) {
        Changed |= BoundVars.insert(V).second;
      }
    };
    std::function<void(const Stmt *)> walk = [&](const Stmt *S) {
      if (!S) {
        return;
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        for (const Decl *X : D->decls()) {
          if (auto *V = dyn_cast<VarDecl>(X); V && V->hasInit() && BoundVars.count(V)) {
            add(V->getInit());
          }
        }
      }
      if (const Expr *T = assignedTo(S)) {
        if (const VarDecl *V = rootVar(T); V && BoundVars.count(V)) {
          add(S);
        }
      }
      if (auto *C = dyn_cast<CallExpr>(S); C && C->getDirectCallee()) {
        auto It = BoundParams.find(C->getDirectCallee()->getDefinition());
        if (It != BoundParams.end()) {
          for (unsigned I : It->second) {
            if (I < C->getNumArgs()) {
              add(C->getArg(I));
            }
          }
        }
      }
      for (const Stmt *C : S->children()) {
        walk(C);
      }
    };
    while (Changed) {
      Changed = false;
      for (const Stmt *S : Body) {
        walk(S);
      }
    }
    for (unsigned I = 0; I < F->getNumParams(); ++I) {
      if (BoundVars.count(F->getParamDecl(I))) {
        BoundParams[F].insert(I);
      }
    }
  }

  struct Rng {
    uint64_t S;
    uint32_t next() {
      S ^= S << 13;
      S ^= S >> 7;
      S ^= S << 17;
      return static_cast<uint32_t>(S >> 11);
    }
    uint32_t below(uint32_t N) { return next() % N; }
  };

  // A generated value: a number (a uint32_t, a bool, or an enumerator's
  // position), or the fields of a struct, or the elements of a list or vec.
  struct Val {
    uint32_t N = 0;
    std::vector<Val> Items;
  };

  static size_t count(const EnumDecl *E) { return std::distance(E->enumerator_begin(), E->enumerator_end()); }

  std::optional<QualType> seqElement(QualType T) {
    if (auto E = listElement(T)) {
      return E;
    }
    return vecElement(T);
  }

  // Values that find wrapping and shift bugs, then small and arbitrary ones.
  // A Small value feeds a loop bound or a vec size.
  Val gen(QualType T, bool Small, Rng &R) {
    static const uint32_t Edges[] = {0,     1,     2,           3,           16,          31,         32,
                                     255,   65535, 65536,       0x7FFFFFFFu, 0x80000000u, 0xFFFFFFFEu, 0xFFFFFFFFu};
    Val V;
    if (isU32(T)) {
      if (Small) {
        V.N = R.below(11);
      } else if (uint32_t Pick = R.below(3); Pick == 0) {
        V.N = Edges[R.below(std::size(Edges))];
      } else {
        V.N = Pick == 1 ? R.below(101) : R.next();
      }
    } else if (isU8(T)) {
      // Bit boundaries, where UTF-8 and similar byte formats change meaning.
      static const uint32_t Bytes[] = {0, 1, 0x3F, 0x40, 0x7F, 0x80, 0xBF, 0xC0, 0xDF, 0xE0, 0xEF, 0xF0, 0xF7, 0xFF};
      V.N = R.below(2) ? Bytes[R.below(std::size(Bytes))] : R.below(256);
    } else if (isBool(T)) {
      V.N = R.below(2);
    } else if (const EnumDecl *E = enumOf(T)) {
      V.N = R.below(count(E));
    } else if (auto Elem = seqElement(T)) {
      for (uint32_t I = 0, Len = R.below(7); I < Len; ++I) {
        V.Items.push_back(gen(*Elem, Small, R));
      }
    } else if (auto *Rd = T.getCanonicalType()->getAsRecordDecl()) {
      for (const FieldDecl *F : Rd->fields()) {
        V.Items.push_back(gen(F->getType(), Small, R));
      }
    }
    return V;
  }

  std::string cppType(QualType T) { return T.getCanonicalType().getUnqualifiedType().getAsString(Ctx.getPrintingPolicy()); }

  static const EnumConstantDecl *nth(const EnumDecl *E, uint32_t N) { return *std::next(E->enumerator_begin(), N); }

  std::string cppVal(QualType T, const Val &V) {
    if (isU32(T)) {
      return std::to_string(V.N) + "u";
    }
    if (isU8(T)) {
      return "static_cast<unsigned char>(" + std::to_string(V.N) + ")";
    }
    if (isBool(T)) {
      return V.N ? "true" : "false";
    }
    if (const EnumDecl *E = enumOf(T)) {
      return E->getNameAsString() + "::" + nth(E, V.N)->getNameAsString();
    }
    std::string Items;
    if (auto Elem = seqElement(T)) {
      for (const Val &X : V.Items) {
        Items += (Items.empty() ? "" : ", ") + cppVal(*Elem, X);
      }
      return std::string(listElement(T) ? "claws::list<" : "claws::vec<") + cppType(*Elem) + ">::from({" + Items + "})";
    }
    const RecordDecl *Rd = T.getCanonicalType()->getAsRecordDecl();
    size_t I = 0;
    for (const FieldDecl *F : Rd->fields()) {
      Items += (I ? ", " : "") + cppVal(F->getType(), V.Items[I]);
      ++I;
    }
    return Rd->getNameAsString() + "{" + Items + "}";
  }

  std::string leanVal(QualType T, const Val &V) {
    if (isU32(T)) {
      return "(" + std::to_string(V.N) + " : BitVec 32)";
    }
    if (isU8(T)) {
      return "(" + std::to_string(V.N) + " : BitVec 8)";
    }
    if (isBool(T)) {
      return V.N ? "true" : "false";
    }
    if (const EnumDecl *E = enumOf(T)) {
      return enumerator(nth(E, V.N));
    }
    if (auto Elem = seqElement(T)) {
      std::string Items;
      for (const Val &X : V.Items) {
        Items += (Items.empty() ? "" : ", ") + leanVal(*Elem, X);
      }
      return std::string(listElement(T) ? "([" : "(#[") + Items + "] : " + type(T, SourceLocation()) + ")";
    }
    const RecordDecl *Rd = T.getCanonicalType()->getAsRecordDecl();
    std::string S = "(" + leanName(Rd->getName()) + ".mk";
    size_t I = 0;
    for (const FieldDecl *F : Rd->fields()) {
      S += " " + leanVal(F->getType(), V.Items[I++]);
    }
    return S + ")";
  }

  // The Lean function that prints a value of type T.
  std::string leanFmt(QualType T) {
    if (isU32(T)) {
      return "fmt'u32";
    }
    if (isU8(T)) {
      return "fmt'u8";
    }
    if (isBool(T)) {
      return "fmt'bool";
    }
    if (const EnumDecl *E = enumOf(T)) {
      return "fmt'" + E->getNameAsString();
    }
    if (auto Elem = listElement(T)) {
      return "(fmt'list " + leanFmt(*Elem) + ")";
    }
    if (auto Elem = vecElement(T)) {
      return "(fmt'array " + leanFmt(*Elem) + ")";
    }
    return "fmt'" + T.getCanonicalType()->getAsRecordDecl()->getNameAsString();
  }

  // The inputs of every case of F, the same in both harnesses.
  std::vector<std::vector<Val>> cases(const FunctionDecl *F, unsigned N, Rng &R) {
    std::vector<std::vector<Val>> Out;
    for (unsigned K = 0; K < (F->getNumParams() ? N : 1); ++K) {
      std::vector<Val> Args;
      for (unsigned I = 0; I < F->getNumParams(); ++I) {
        Args.push_back(gen(F->getParamDecl(I)->getType().getNonReferenceType(), BoundParams[F].count(I), R));
      }
      Out.push_back(Args);
    }
    return Out;
  }

public:
  std::string diffCpp(const std::string &Source, unsigned N, unsigned Seed) {
    std::ostringstream S;
    S << "// Generated by claws-lean --diff-cpp from " << llvm::sys::path::filename(Source).str() << ". Do not edit.\n";
    S << "#include <cstdio>\n#include <string>\n\n#include <claws/list.hpp>\n#include <claws/vec.hpp>\n\n";
    S << "#include \"" << Source << "\"\n\n";
    S << "static std::string claws_show(uint32_t x);\nstatic std::string claws_show(unsigned char x);\n"
      << "static std::string claws_show(bool x);\n";
    for (const EnumDecl *E : EnumOrder) {
      S << "static std::string claws_show(" << E->getNameAsString() << " x);\n";
    }
    for (const RecordDecl *R : StructOrder) {
      S << "static std::string claws_show(const " << R->getNameAsString() << " &x);\n";
    }
    S << "template <class T> static std::string claws_show(const claws::list<T> &xs);\n";
    S << "template <class T> static std::string claws_show(const claws::vec<T> &xs);\n\n";
    S << "static std::string claws_show(uint32_t x) { return std::to_string(x); }\n";
    S << "static std::string claws_show(unsigned char x) { return std::to_string(x); }\n";
    S << "static std::string claws_show(bool x) { return x ? \"true\" : \"false\"; }\n";
    for (const EnumDecl *E : EnumOrder) {
      S << "static std::string claws_show(" << E->getNameAsString() << " x) {\n  switch (x) {\n";
      for (const EnumConstantDecl *K : E->enumerators()) {
        S << "  case " << E->getNameAsString() << "::" << K->getNameAsString() << ": return \"" << K->getNameAsString()
          << "\";\n";
      }
      S << "  }\n  return \"?\";\n}\n";
    }
    for (const RecordDecl *R : StructOrder) {
      S << "static std::string claws_show(const " << R->getNameAsString() << " &x) {\n  return std::string(\"{\")";
      bool First = true;
      for (const FieldDecl *F : R->fields()) {
        S << (First ? "" : " + \" \"") << " + claws_show(x." << F->getNameAsString() << ")";
        First = false;
      }
      S << " + \"}\";\n}\n";
    }
    for (const char *Seq : {"list", "vec"}) {
      S << "template <class T> static std::string claws_show(const claws::" << Seq << "<T> &xs) {\n"
        << "  std::string s = \"[\";\n  bool first = true;\n"
        << "  for (const T &x : xs.to_vector()) {\n    s += (first ? \"\" : \" \") + claws_show(x);\n    first = false;\n  }\n"
        << "  return s + \"]\";\n}\n";
    }
    S << "\n";
    // A copy of each precondition, so the harness skips the same inputs.
    for (const FunctionDecl *F : Tested) {
      if (!PreSource.count(F)) {
        continue;
      }
      S << "static bool claws_pre_" << F->getNameAsString() << "(";
      for (unsigned I = 0; I < F->getNumParams(); ++I) {
        const ParmVarDecl *P = F->getParamDecl(I);
        S << (I ? ", " : "") << "const " << cppType(P->getType().getNonReferenceType()) << " &" << P->getNameAsString();
      }
      S << ") {\n  return true";
      for (const std::string &C : PreSource[F]) {
        S << " && (" << C << ")";
      }
      S << ";\n}\n";
    }
    S << "\nint main() {\n";
    Rng R{0x9E3779B97F4A7C15ull ^ Seed};
    for (const FunctionDecl *F : Tested) {
      std::string Name = F->getNameAsString();
      unsigned K = 0;
      for (const std::vector<Val> &Args : cases(F, N, R)) {
        S << "  {\n";
        std::string Call = Name + "(";
        std::string Pre = "claws_pre_" + Name + "(";
        for (unsigned I = 0; I < F->getNumParams(); ++I) {
          QualType T = F->getParamDecl(I)->getType().getNonReferenceType().getUnqualifiedType();
          S << "    " << cppType(T) << " a" << I << " = " << cppVal(T, Args[I]) << ";\n";
          Call += (I ? ", " : "") + std::string("a") + std::to_string(I);
          Pre += (I ? ", " : "") + std::string("a") + std::to_string(I);
        }
        Call += ")";
        Pre += ")";
        std::string Line = "std::string(\"" + Name + " " + std::to_string(K) + " =\")";
        std::string Body;
        if (F->getReturnType()->isVoidType()) {
          Body = Call + ";\n";
        } else {
          Body = "auto r = " + Call + ";\n";
          Line += " + \" \" + claws_show(r)";
        }
        std::vector<unsigned> Outs = inoutParams(F);
        if (!Outs.empty()) {
          Line += " + \" |\"";
          for (unsigned I : Outs) {
            Line += " + \" \" + claws_show(a" + std::to_string(I) + ")";
          }
        }
        Body += "      std::printf(\"%s\\n\", (" + Line + ").c_str());\n";
        if (PreSource.count(F)) {
          S << "    if (!" << Pre << ") {\n      std::printf(\"" << Name << " " << K << " skip\\n\");\n    } else {\n      "
            << Body << "    }\n";
        } else {
          S << "    {\n      " << Body << "    }\n";
        }
        S << "  }\n";
        ++K;
      }
    }
    S << "  return 0;\n}\n";
    return S.str();
  }

  std::string diffLean(unsigned N, unsigned Seed) {
    std::ostringstream S;
    std::string NS = Namespace;
    S << "\n-- Differential test harness, generated by claws-lean --diff-lean.\n";
    S << "namespace " << NS << ".Diff\n\nopen " << NS << "\n\nset_option linter.all false\n\n";
    S << "def fmt'u32 (x : BitVec 32) : String := toString x.toNat\n";
    S << "def fmt'u8 (x : BitVec 8) : String := toString x.toNat\n";
    S << "def fmt'bool (x : Bool) : String := toString x\n";
    S << "def fmt'list {α : Type} (f : α → String) (xs : List α) : String := \"[\" ++ \" \".intercalate (xs.map f) ++ \"]\"\n";
    S << "def fmt'array {α : Type} (f : α → String) (xs : Array α) : String := fmt'list f xs.toList\n";
    for (const EnumDecl *E : EnumOrder) {
      S << "def fmt'" << E->getNameAsString() << " : " << leanName(E->getName()) << " → String\n";
      for (const EnumConstantDecl *K : E->enumerators()) {
        S << "  | " << enumerator(K) << " => \"" << K->getNameAsString() << "\"\n";
      }
    }
    for (const RecordDecl *R : StructOrder) {
      S << "def fmt'" << R->getNameAsString() << " (x : " << leanName(R->getName()) << ") : String :=\n  \"{\"";
      bool First = true;
      for (const FieldDecl *F : R->fields()) {
        S << (First ? "" : " ++ \" \"") << " ++ " << leanFmt(F->getType()) << " x." << leanName(F->getName());
        First = false;
      }
      S << " ++ \"}\"\n";
    }
    Rng R{0x9E3779B97F4A7C15ull ^ Seed};
    std::vector<std::string> Runs;
    for (const FunctionDecl *F : Tested) {
      std::string Name = F->getNameAsString();
      std::string Q = NS + "." + leanName(F->getName());
      std::vector<std::vector<Val>> All = cases(F, N, R);
      unsigned P = F->getNumParams();
      std::string Binder;
      std::string Args;
      std::string Types;
      for (unsigned I = 0; I < P; ++I) {
        Binder += (I ? ", " : "") + std::string("a'") + std::to_string(I);
        Args += " a'" + std::to_string(I);
        Types += (I ? " × " : "") + varType(F->getParamDecl(I));
      }
      // The output pattern: the result, then each T& argument.
      std::vector<unsigned> Outs = inoutParams(F);
      bool Void = F->getReturnType()->isVoidType();
      std::vector<std::string> Pat;
      std::string Line = "\"" + Name + " \" ++ toString k ++ \" =\"";
      if (!Void) {
        Pat.push_back("r'");
        Line += " ++ \" \" ++ " + leanFmt(F->getReturnType()) + " r'";
      }
      if (!Outs.empty()) {
        Line += " ++ \" |\"";
      }
      for (unsigned I : Outs) {
        Pat.push_back("o'" + std::to_string(I));
        Line += " ++ \" \" ++ " + leanFmt(F->getParamDecl(I)->getType().getNonReferenceType()) + " o'" +
                std::to_string(I);
      }
      std::string Bind = Pat.size() == 1 ? Pat[0] : "(";
      if (Pat.size() > 1) {
        for (size_t I = 0; I < Pat.size(); ++I) {
          Bind += (I ? ", " : "") + Pat[I];
        }
        Bind += ")";
      }
      std::string Run = "run'" + Name;
      Runs.push_back(Run);
      S << "\ndef " << Run << " : IO Unit := do\n";
      if (P == 0) {
        S << "  let k := 0\n  let " << Bind << " := " << Q << "\n  IO.println (" << Line << ")\n";
        continue;
      }
      S << "  let cases : List (" << Types << ") := [";
      for (size_t K = 0; K < All.size(); ++K) {
        std::string Tuple;
        for (unsigned I = 0; I < P; ++I) {
          Tuple += (I ? ", " : "") + leanVal(F->getParamDecl(I)->getType().getNonReferenceType(), All[K][I]);
        }
        S << (K ? ",\n    " : "\n    ") << (P > 1 ? "(" + Tuple + ")" : Tuple);
      }
      S << "]\n  let mut k := 0\n";
      S << "  for " << (P > 1 ? "(" + Binder + ")" : Binder) << " in cases do\n";
      if (PreSource.count(F)) {
        S << "    if " << Q << ".pre" << Args << " then\n";
        S << "      let " << Bind << " := " << Q << Args << "\n      IO.println (" << Line << ")\n";
        S << "    else\n      IO.println (\"" << Name << " \" ++ toString k ++ \" skip\")\n";
      } else {
        S << "    let " << Bind << " := " << Q << Args << "\n    IO.println (" << Line << ")\n";
      }
      S << "    k := k + 1\n";
    }
    S << "\nend " << NS << ".Diff\n\ndef main : IO Unit := do\n";
    for (const std::string &Run : Runs) {
      S << "  " << NS << ".Diff." << Run << "\n";
    }
    if (Runs.empty()) {
      S << "  pure ()\n";
    }
    return S.str();
  }

private:
  // Safety
  //
  // sstmts mirrors stmts. It returns a Bool that is true when nothing on
  // the path the statements take goes wrong, binding the same variables
  // stmts binds, so each check sees the values C++ would. A list whose
  // remaining checks are all trivial is "true", so code with nothing to
  // check produces no safety function at all.

  static std::string conj(const std::vector<std::string> &Cs) {
    std::vector<std::string> Keep;
    for (const std::string &C : Cs) {
      if (C != "true") {
        Keep.push_back(C);
      }
    }
    if (Keep.empty()) {
      return "true";
    }
    if (Keep.size() == 1) {
      return Keep[0];
    }
    std::string S = "(";
    for (size_t I = 0; I < Keep.size(); ++I) {
      S += (I ? " && " : "") + Keep[I];
    }
    return S + ")";
  }

  // `if !(c) then false else` and K on the next line.
  static std::string guard(const std::string &C, const std::string &K, int Depth) {
    if (C == "true") {
      return K;
    }
    if (K == "true") {
      return C;
    }
    return "if !(" + C + ") then false else\n" + indent(Depth) + K;
  }

  // `I < B.size`, as a Bool.
  std::string inBounds(const std::string &B, const Expr *I) {
    return "(decide (" + expr(I) + ".toNat < " + B + ".size))";
  }

  // The checks a write to Target needs: its indexes are safe and in
  // bounds, given the values before the write.
  std::string targetCond(const Expr *Target) {
    Path Steps;
    const VarDecl *Root = lvalue(Target, Steps);
    if (!Root) {
      return "true";
    }
    std::vector<std::string> Cs;
    for (size_t I = 0; I < Steps.size(); ++I) {
      if (Steps[I].Index) {
        Cs.push_back(cond(Steps[I].Index));
        Cs.push_back(inBounds(pathText(Root, Steps, I), Steps[I].Index));
      }
    }
    return conj(Cs);
  }

  std::string divisorOk(const Expr *R) {
    if (literal(R)) {
      return "true";
    }
    return "(" + expr(R) + " != (0 : BitVec 32))";
  }

  std::string shiftOk(const Expr *R) {
    if (literal(R)) {
      return "true";
    }
    return "(BitVec.ult " + expr(R) + " (32 : BitVec 32))";
  }

  // Whether E evaluates without undefined behavior, given the bindings in
  // scope. `&&`, `||` and `?:` check their later operands only where C++
  // evaluates them, so `n != 0 && t / n > 1` needs nothing.
  std::string cond(const Expr *E) {
    if (auto *P = dyn_cast<ParenExpr>(E)) {
      return cond(P->getSubExpr());
    }
    if (auto *C = dyn_cast<ConstantExpr>(E)) {
      return cond(C->getSubExpr());
    }
    if (auto *C = dyn_cast<ExprWithCleanups>(E)) {
      return cond(C->getSubExpr());
    }
    if (auto *M = dyn_cast<MaterializeTemporaryExpr>(E)) {
      return cond(M->getSubExpr());
    }
    if (auto *B = dyn_cast<CXXBindTemporaryExpr>(E)) {
      return cond(B->getSubExpr());
    }
    if (auto *C = dyn_cast<CastExpr>(E)) {
      return cond(C->getSubExpr());
    }
    if (auto *C = dyn_cast<CXXConstructExpr>(E)) {
      std::vector<std::string> Cs;
      for (const Expr *A : C->arguments()) {
        Cs.push_back(cond(A));
      }
      return conj(Cs);
    }
    if (const CXXOperatorCallExpr *O = subscript(E)) {
      return conj({cond(O->getArg(0)), cond(O->getArg(1)), inBounds(expr(O->getArg(0)), O->getArg(1))});
    }
    if (auto *A = dyn_cast<ArraySubscriptExpr>(E)) {
      // A uint8_t index is always in bounds of a table of 256 or more.
      uint64_t N = ConstArrays.at(constArray(A)->getCanonicalDecl());
      const Expr *I = A->getIdx();
      bool Byte = isU8(I->IgnoreImpCasts()->getType()) && N >= 256;
      return conj({cond(I), Byte ? "true" : "(decide (" + expr(I) + ".toNat < " + std::to_string(N) + "))"});
    }
    if (isa<IntegerLiteral>(E) || isa<CXXBoolLiteralExpr>(E) || isa<DeclRefExpr>(E)) {
      return "true";
    }
    if (auto *U = dyn_cast<UnaryOperator>(E)) {
      return cond(U->getSubExpr());
    }
    if (auto *B = dyn_cast<BinaryOperator>(E)) {
      const Expr *L = B->getLHS();
      const Expr *R = B->getRHS();
      std::string CL = cond(L);
      std::string CR = cond(R);
      switch (B->getOpcode()) {
      case BO_LAnd:
        return conj({CL, CR == "true" ? "true" : "(!" + expr(L) + " || " + CR + ")"});
      case BO_LOr:
        return conj({CL, CR == "true" ? "true" : "(" + expr(L) + " || " + CR + ")"});
      case BO_Div:
      case BO_Rem:
        return conj({CL, CR, divisorOk(R)});
      case BO_Shl:
      case BO_Shr:
        return conj({CL, CR, shiftOk(R)});
      default:
        return conj({CL, CR});
      }
    }
    if (auto *C = dyn_cast<ConditionalOperator>(E)) {
      std::string T = cond(C->getTrueExpr());
      std::string F = cond(C->getFalseExpr());
      std::string Branches = T == "true" && F == "true"
                                 ? "true"
                                 : "(if " + boolExpr(C->getCond()) + " then " + T + " else " + F + ")";
      return conj({cond(C->getCond()), Branches});
    }
    if (auto *C = dyn_cast<CXXMemberCallExpr>(E)) {
      if (vecMethod(C, "size")) {
        return cond(C->getImplicitObjectArgument());
      }
      return matchCond(C);
    }
    if (auto *C = dyn_cast<CallExpr>(E)) {
      return callCond(C);
    }
    if (auto *M = dyn_cast<MemberExpr>(E)) {
      return cond(M->getBase());
    }
    if (auto *I = dyn_cast<InitListExpr>(E)) {
      std::vector<std::string> Cs;
      for (const Expr *X : I->inits()) {
        Cs.push_back(cond(X));
      }
      return conj(Cs);
    }
    reject(E->getExprLoc(), std::string("internal: no safety rule for a ") + E->getStmtClassName());
  }

  // A call is safe when its arguments are and the callee's precondition
  // holds. The callee's own body is the callee's obligation.
  std::string callCond(const CallExpr *C) {
    std::vector<std::string> Cs;
    for (const Expr *A : C->arguments()) {
      Cs.push_back(cond(A));
    }
    const FunctionDecl *F = C->getDirectCallee();
    if (F && HasPre.count(F->getCanonicalDecl())) {
      std::string Pre = "(" + leanName(F->getName()) + ".pre";
      for (const Expr *A : C->arguments()) {
        Pre += " " + expr(A);
      }
      Cs.push_back(Pre + ")");
    }
    return conj(Cs);
  }

  std::string valueCond(const Expr *E) {
    if (const CallExpr *C = effectCall(E)) {
      return callCond(C);
    }
    return cond(E);
  }

  std::string matchCond(const CXXMemberCallExpr *C) {
    const LambdaExpr *Arms[2] = {lambdaArg(C->getArg(0)), lambdaArg(C->getArg(1))};
    const CXXMethodDecl *Cons = Arms[1]->getCallOperator();
    auto name = [](const ParmVarDecl *P) { return P->getName().empty() ? std::string("_") : leanName(P->getName()); };
    int D = ExprDepth;
    std::string Scrut = cond(C->getImplicitObjectArgument());
    auto *NilBody = cast<CompoundStmt>(Arms[0]->getBody());
    auto *ConsBody = cast<CompoundStmt>(Arms[1]->getBody());
    const DeclContext *Outer = Scope;
    Scope = Arms[0]->getCallOperator();
    std::string Nil = sstmts(NilBody->body(), NilBody->getRBracLoc(), D + 1);
    Scope = Cons;
    std::string ConsArm = sstmts(ConsBody->body(), ConsBody->getRBracLoc(), D + 1);
    Scope = Outer;
    ExprDepth = D;
    if (Nil == "true" && ConsArm == "true") {
      return Scrut;
    }
    std::string M = "(match " + expr(C->getImplicitObjectArgument()) + " with\n" + indent(D) + "| [] =>\n" +
                    indent(D + 1) + Nil + "\n" + indent(D) + "| " + name(Cons->getParamDecl(0)) + " :: " +
                    name(Cons->getParamDecl(1)) + " =>\n" + indent(D + 1) + ConsArm + ")";
    return conj({Scrut, M});
  }

  std::string assignCond(const Expr *E) {
    if (auto *W = dyn_cast<ExprWithCleanups>(E)) {
      E = W->getSubExpr();
    }
    std::string TC = targetCond(assignedTo(E));
    if (const CXXMemberCallExpr *P = vecMethod(E, "push")) {
      // The size must stay below 2^32 so that size() fits a uint32_t.
      Path Steps;
      const VarDecl *Root = lvalue(P->getImplicitObjectArgument(), Steps);
      std::string Room = "(decide (" + pathText(Root, Steps, Steps.size()) + ".size < 4294967295))";
      return conj({TC, cond(P->getArg(0)), Room});
    }
    if (isa<UnaryOperator>(E)) {
      return TC;
    }
    if (auto *O = dyn_cast<CXXOperatorCallExpr>(E)) {
      return conj({valueCond(O->getArg(1)), TC});
    }
    if (auto *C = dyn_cast<CompoundAssignOperator>(E)) {
      std::string RC = conj({valueCond(C->getRHS()), TC});
      switch (C->getOpcode()) {
      case BO_DivAssign:
      case BO_RemAssign:
        return conj({RC, divisorOk(C->getRHS())});
      case BO_ShlAssign:
      case BO_ShrAssign:
        return conj({RC, shiftOk(C->getRHS())});
      default:
        return RC;
      }
    }
    return conj({valueCond(cast<BinaryOperator>(E)->getRHS()), TC});
  }

  std::string sstmts(ArrayRef<Stmt *> List, SourceLocation End, int Depth, const Vars *Tail = nullptr) {
    for (size_t I = 0; I < List.size(); ++I) {
      Stmt *S = List[I];
      ArrayRef<Stmt *> Rest = List.drop_front(I + 1);
      auto rest = [&](int D) { return sstmts(Rest, End, D, Tail); };
      ExprDepth = Depth;
      if (isa<NullStmt>(S)) {
        continue;
      }
      if (auto *R = dyn_cast<ReturnStmt>(S)) {
        return R->getRetValue() ? valueCond(R->getRetValue()) : "true";
      }
      if (isa<BreakStmt>(S) && Loop && Scope == Current) {
        return "true";
      }
      if (isa<ContinueStmt>(S) && Loop && Scope == Current) {
        return loopNext(Depth);
      }
      if (auto *D = dyn_cast<DeclStmt>(S)) {
        auto *V = cast<VarDecl>(D->getSingleDecl());
        std::string C = valueCond(V->getInit());
        std::string K = rest(Depth);
        if (K == "true") {
          return C;
        }
        std::string Prefix;
        ExprDepth = Depth;
        std::string Value = valueOf(V->getInit(), Depth, Prefix);
        return guard(C, Prefix + "let " + leanName(V->getName()) + " := " + Value + "\n" + indent(Depth) + K, Depth);
      }
      if (auto *E = dyn_cast<Expr>(S)) {
        std::string C;
        std::string Prefix;
        std::string Bind;
        std::string K = rest(Depth);
        ExprDepth = Depth;
        if (const CallExpr *Call = effectCall(E)) {
          C = callCond(Call);
          if (K != "true") {
            effects(Call, Depth, Prefix);
          }
        } else {
          C = assignCond(E);
          if (K != "true") {
            auto [Name, Value] = assignment(E, Depth, Prefix);
            Bind = "let " + Name + " := " + Value + "\n" + indent(Depth);
          }
        }
        return K == "true" ? C : guard(C, Prefix + Bind + K, Depth);
      }
      if (auto *C = dyn_cast<CompoundStmt>(S)) {
        if (flow(C->body()) == Flow::Returns) {
          return sstmts(C->body(), C->getRBracLoc(), Depth);
        }
        if (flow(C->body()) == Flow::Mixed) {
          return sstmts(concat(C->body(), Rest), End, Depth);
        }
        Vars Mods = modified(C->body());
        std::string RS = sstmts(C->body(), C->getRBracLoc(), Depth + 1, &Mods);
        std::string K = rest(Depth);
        if (K == "true") {
          return RS;
        }
        std::string Region = stmts(C->body(), C->getRBracLoc(), Depth + 1, &Mods);
        return guard(RS, bindEffects(Mods, Region, K, Depth), Depth);
      }
      if (auto *If = dyn_cast<IfStmt>(S)) {
        return sif(If, Rest, End, Depth, Tail);
      }
      if (auto *Sw = dyn_cast<SwitchStmt>(S)) {
        return sswitch(Sw, Rest, End, Depth, Tail);
      }
      if (auto *F = dyn_cast<ForStmt>(S)) {
        return sfor(F, Rest, End, Depth, Tail);
      }
      if (auto *W = dyn_cast<WhileStmt>(S)) {
        return swhile(W, Rest, End, Depth, Tail);
      }
    }
    if (!Tail && Loop && Scope == Current) {
      return loopNext(Depth);
    }
    return "true";
  }

  std::string sif(IfStmt *If, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    if (const VarDecl *V = ifInit(If, Rest)) {
      ExprDepth = Depth;
      std::string C = valueCond(V->getInit());
      std::string Prefix;
      ExprDepth = Depth;
      std::string Value = valueOf(V->getInit(), Depth, Prefix);
      return guard(C, Prefix + "let " + leanName(V->getName()) + " := " + Value + "\n" + indent(Depth) +
                          sifBody(If, Rest, End, Depth, Tail),
                   Depth);
    }
    return sifBody(If, Rest, End, Depth, Tail);
  }

  std::string sifBody(IfStmt *If, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    std::vector<Stmt *> Then = body(If->getThen());
    std::vector<Stmt *> Else = If->getElse() ? body(If->getElse()) : std::vector<Stmt *>();
    SourceLocation ThenEnd = If->getThen()->getEndLoc();
    SourceLocation ElseEnd = If->getElse() ? If->getElse()->getEndLoc() : If->getEndLoc();
    Flow T = flow(Then);
    Flow E = flow(Else);
    std::string CC = cond(If->getCond());
    auto choose = [&](const std::string &A, const std::string &B, int D) {
      if (A == "true" && B == "true") {
        return std::string("true");
      }
      ExprDepth = D;
      std::string Cond = boolExpr(If->getCond());
      return "if " + Cond + " then\n" + indent(D + 1) + A + "\n" + indent(D) + "else\n" + indent(D + 1) + B;
    };
    if (T == Flow::Returns && E == Flow::Returns) {
      std::string A = sstmts(Then, ThenEnd, Depth + 1);
      std::string B = sstmts(Else, ElseEnd, Depth + 1);
      return guard(CC, choose(A, B, Depth), Depth);
    }
    if (T == Flow::Mixed || E == Flow::Mixed) {
      auto branch = [&](ArrayRef<Stmt *> B, Flow F, SourceLocation BEnd) {
        return F == Flow::Returns ? sstmts(B, BEnd, Depth + 1) : sstmts(concat(B, Rest), End, Depth + 1);
      };
      std::string A = branch(Then, T, ThenEnd);
      std::string B = branch(Else, E, ElseEnd);
      return guard(CC, choose(A, B, Depth), Depth);
    }
    if (T == Flow::Falls && E == Flow::Falls) {
      std::vector<Stmt *> Both(Then.begin(), Then.end());
      Both.insert(Both.end(), Else.begin(), Else.end());
      Vars Mods = modified(Both);
      std::string A = sstmts(Then, ThenEnd, Depth + 2, &Mods);
      std::string B = sstmts(Else, ElseEnd, Depth + 2, &Mods);
      std::string RS = choose(A, B, Depth + 1);
      if (RS != "true") {
        RS = "(" + RS + ")";
      }
      std::string K = sstmts(Rest, End, Depth, Tail);
      if (K == "true") {
        return guard(CC, RS, Depth);
      }
      ExprDepth = Depth + 1;
      std::string Cond = boolExpr(If->getCond());
      std::string VA = stmts(Then, ThenEnd, Depth + 2, &Mods);
      std::string VB = stmts(Else, ElseEnd, Depth + 2, &Mods);
      std::string Region =
          "if " + Cond + " then\n" + indent(Depth + 2) + VA + "\n" + indent(Depth + 1) + "else\n" + indent(Depth + 2) + VB;
      return guard(CC, guard(RS, bindEffects(Mods, Region, K, Depth), Depth), Depth);
    }
    // One branch returns, the other falls through to the rest.
    auto falling = [&](ArrayRef<Stmt *> Branch, SourceLocation BranchEnd) {
      Vars Mods = modified(Branch);
      std::string RS = sstmts(Branch, BranchEnd, Depth + 2, &Mods);
      std::string K = sstmts(Rest, End, Depth + 1, Tail);
      if (K == "true") {
        return RS;
      }
      std::string Region = stmts(Branch, BranchEnd, Depth + 2, &Mods);
      return guard(RS == "true" ? RS : "(" + RS + ")", bindEffects(Mods, Region, K, Depth + 1), Depth + 1);
    };
    std::string A = T == Flow::Returns ? sstmts(Then, ThenEnd, Depth + 1) : falling(Then, ThenEnd);
    std::string B = E == Flow::Returns ? sstmts(Else, ElseEnd, Depth + 1) : falling(Else, ElseEnd);
    return guard(CC, choose(A, B, Depth), Depth);
  }

  std::string sswitch(SwitchStmt *Sw, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    Flow F = flow(Sw);
    std::string CC = cond(Sw->getCond());
    Vars Mods;
    if (F == Flow::Falls) {
      std::vector<Stmt *> All;
      for (const Arm &A : arms(Sw)) {
        All.insert(All.end(), A.Body.begin(), A.Body.end());
      }
      Mods = modified(All);
    }
    int D = F == Flow::Falls ? Depth + 1 : Depth;
    const Vars *ArmTail = F == Flow::Falls ? &Mods : nullptr;
    bool Trivial = true;
    for (const Arm &A : arms(Sw)) {
      Trivial &= sstmts(A.Body, Sw->getEndLoc(), D + 1, ArmTail) == "true";
    }
    std::string RS = Trivial ? "true"
                             : switchMatch(
                                   Sw, D, [&](const Arm &A) { return sstmts(A.Body, Sw->getEndLoc(), D + 1, ArmTail); },
                                   "true");
    if (F == Flow::Returns) {
      return guard(CC, RS, Depth);
    }
    std::string K = sstmts(Rest, End, Depth, Tail);
    if (K == "true") {
      return guard(CC, RS, Depth);
    }
    std::string Region = switchMatch(
        Sw, D, [&](const Arm &A) { return stmts(A.Body, Sw->getEndLoc(), D + 1, &Mods); },
        Mods.empty() ? "" : tuple(Mods));
    return guard(CC, guard(RS, bindEffects(Mods, Region, K, Depth), Depth), Depth);
  }

  // A loop is safe when its start and bound are, and every step is: a
  // recursive Bool function over the loop's variables, f.loopN.safe,
  // which checks the bound and the body at each step.
  std::string sfor(ForStmt *F, ArrayRef<Stmt *> Rest, SourceLocation End, int Depth, const Vars *Tail) {
    auto *I = cast<VarDecl>(cast<DeclStmt>(F->getInit())->getSingleDecl());
    auto *Cond = cast<BinaryOperator>(F->getCond()->IgnoreParens());
    std::vector<Stmt *> Body = body(F->getBody());
    Vars Mods = modified(Body);
    Vars Params = referenced(F);
    std::string Name = LoopNames.at(F);
    std::string IName = leanName(I->getName());
    std::string Args;
    for (const VarDecl *V : Params) {
      Args += " " + leanName(V->getName());
    }
    bool SizeBound = false;
    for (const VarDecl *V : referenced(Cond->getRHS())) {
      if (std::find(Mods.begin(), Mods.end(), V) != Mods.end()) {
        SizeBound = true;
      }
    }
    ++LoopDepth;
    std::string CB = cond(Cond->getRHS());
    std::string BS = sstmts(Body, F->getBody()->getEndLoc(), 3, &Mods);
    bool Checks = CB != "true" || BS != "true";
    if (Checks && !SafeLoopsDone.count(Name)) {
      SafeLoopsDone.insert(Name);
      ExprDepth = 2;
      std::string Bound = expr(Cond->getRHS());
      std::string Region = stmts(Body, F->getBody()->getEndLoc(), 3, &Mods);
      std::string Next =
          "let " + IName + " := (" + IName + " + 1)\n" + indent(2) + Name + ".safe" + Args + " " + IName;
      std::ostringstream D;
      D << "-- " << where(F->getForLoc()) << ", the safety of a loop of " << Current->getName().str() << "\n";
      D << "def " << Name << ".safe";
      for (const VarDecl *V : Params) {
        D << " (" << leanName(V->getName()) << " : " << varType(V) << ")";
      }
      D << " (" << IName << " : BitVec 32) : Bool :=\n";
      D << indent(1) << guard(CB, "if lt' : " + IName + " < " + Bound + " then\n" + indent(2) +
                                      guard(BS, bindEffects(Mods, Region, Next, 2), 2) + "\n" + indent(1) +
                                      "else\n" + indent(2) + "true",
                              1)
        << "\n";
      D << "termination_by (" << Bound << " - " << IName << ").toNat\n";
      D << decreasing(SizeBound) << "\n\n";
      SafeLoopDefs.push_back(D.str());
    }
    --LoopDepth;
    ExprDepth = Depth;
    std::string Start = expr(I->getInit());
    std::string Check = conj({cond(I->getInit()), Checks ? "(" + Name + ".safe" + Args + " " + Start + ")" : "true"});
    std::string K = sstmts(Rest, End, Depth, Tail);
    if (K == "true") {
      return Check;
    }
    return guard(Check, bindEffects(Mods, "(" + Name + Args + " " + Start + ")", K, Depth), Depth);
  }

  // Expressions. Compound results are parenthesized, so the output never
  // depends on Lean's precedence rules.

  // A literal operand, which C++ may type as int, such as the 3 in x << 3.
  static const IntegerLiteral *literal(const Expr *E) { return dyn_cast<IntegerLiteral>(E->IgnoreParenImpCasts()); }

  // A literal divisor is checked here; any other is f.safe's job.
  void divisor(const Expr *R) {
    if (auto *L = literal(R); L && L->getValue() == 0) {
      reject(R->getExprLoc(), "division by zero is undefined");
    }
  }

  // A shift amount as a BitVec 32. C++ does not convert the amount to the
  // shifted type, so a literal amount may be an int.
  std::string amount(const Expr *R) {
    if (auto *L = literal(R)) {
      if (L->getValue().uge(32)) {
        reject(R->getExprLoc(), "a shift of 32 or more is undefined for a 32-bit value");
      }
      return u32Literal(L);
    }
    requireU32(R);
    return expr(R);
  }

  std::string boolExpr(const Expr *E) {
    if (!isBool(E->getType())) {
      reject(E->getExprLoc(), "a condition must be a bool, not `" + E->getType().getAsString(Ctx.getPrintingPolicy()) + "`");
    }
    return expr(E);
  }

  std::string u32Literal(const IntegerLiteral *L) {
    llvm::APInt V = L->getValue();
    if (V.getActiveBits() > 32) {
      reject(L->getLocation(), "the literal does not fit in uint32_t");
    }
    return "(" + std::to_string(V.getZExtValue()) + " : BitVec 32)";
  }

  std::string expr(const Expr *E) {
    if (auto *P = dyn_cast<ParenExpr>(E)) {
      return expr(P->getSubExpr());
    }
    if (auto *C = dyn_cast<ConstantExpr>(E)) {
      return expr(C->getSubExpr());
    }
    if (auto *C = dyn_cast<ExprWithCleanups>(E)) {
      return expr(C->getSubExpr());
    }
    if (auto *M = dyn_cast<MaterializeTemporaryExpr>(E)) {
      return expr(M->getSubExpr());
    }
    if (auto *B = dyn_cast<CXXBindTemporaryExpr>(E)) {
      return expr(B->getSubExpr());
    }
    if (auto *C = dyn_cast<ImplicitCastExpr>(E)) {
      return implicitCast(C);
    }
    if (auto *C = dyn_cast<CXXFunctionalCastExpr>(E)) {
      // `Range{lo, hi}` is a functional cast around an init list.
      if (C->getCastKind() == CK_NoOp && isa<InitListExpr>(C->getSubExpr())) {
        return expr(C->getSubExpr());
      }
    }
    if (auto *C = dyn_cast<ExplicitCastExpr>(E)) {
      // `static_cast<uint32_t>(b)`, `uint8_t(x)` or a C-style cast.
      if (C->getCastKind() == CK_IntegralCast) {
        return integralCast(C->getSubExpr(), C->getType(), C->getExprLoc());
      }
      if (C->getCastKind() == CK_NoOp && Ctx.hasSameUnqualifiedType(C->getType(), C->getSubExpr()->getType())) {
        return expr(C->getSubExpr());
      }
      reject(E->getExprLoc(), "the only explicit conversions in the subset are between uint32_t and uint8_t");
    }
    if (auto *L = dyn_cast<IntegerLiteral>(E)) {
      if (!isU32(L->getType()) && !isInt(L->getType())) {
        reject(L->getLocation(), "an integer literal must be used as uint32_t");
      }
      return u32Literal(L);
    }
    if (auto *B = dyn_cast<CXXBoolLiteralExpr>(E)) {
      return B->getValue() ? "true" : "false";
    }
    if (auto *R = dyn_cast<DeclRefExpr>(E)) {
      if (auto *K = dyn_cast<EnumConstantDecl>(R->getDecl()); K && enumOf(K->getType())) {
        return enumerator(K);
      }
      auto *V = dyn_cast<VarDecl>(R->getDecl());
      if (V && Constants.count(V->getCanonicalDecl())) {
        if (ConstArrays.count(V->getCanonicalDecl())) {
          reject(R->getLocation(), "a constant array may only be indexed, as in `table[i]`");
        }
        return leanName(V->getName());
      }
      if (!V || !V->hasLocalStorage()) {
        reject(R->getLocation(), "only parameters, locals and constants may be named here");
      }
      return leanName(V->getName());
    }
    if (auto *U = dyn_cast<UnaryOperator>(E)) {
      return unary(U);
    }
    if (auto *B = dyn_cast<BinaryOperator>(E)) {
      return binary(B);
    }
    if (auto *C = dyn_cast<ConditionalOperator>(E)) {
      return "(if " + boolExpr(C->getCond()) + " then " + expr(C->getTrueExpr()) + " else " +
             expr(C->getFalseExpr()) + ")";
    }
    if (auto *C = dyn_cast<CXXMemberCallExpr>(E)) {
      if (vecMethod(C, "size")) {
        return "(BitVec.ofNat 32 " + expr(C->getImplicitObjectArgument()) + ".size)";
      }
      if (vecMethod(C, "push")) {
        reject(C->getExprLoc(), "`push` must be a statement of its own");
      }
      return listMatch(C);
    }
    if (const CXXOperatorCallExpr *O = subscript(E)) {
      return "(" + expr(O->getArg(0)) + "[" + expr(O->getArg(1)) + ".toNat]!)";
    }
    if (auto *A = dyn_cast<ArraySubscriptExpr>(E)) {
      return "(" + leanName(constArray(A)->getName()) + "[" + expr(A->getIdx()) + ".toNat]!)";
    }
    if (auto *C = dyn_cast<CallExpr>(E)) {
      return call(C);
    }
    if (auto *M = dyn_cast<MemberExpr>(E)) {
      if (M->isArrow() || !isa<FieldDecl>(M->getMemberDecl())) {
        reject(M->getExprLoc(), "only `value.field` access is in the subset");
      }
      std::string Base = expr(M->getBase());
      return Base + "." + leanName(M->getMemberDecl()->getName());
    }
    if (auto *I = dyn_cast<InitListExpr>(E)) {
      return initList(I);
    }
    if (auto *C = dyn_cast<CXXConstructExpr>(E)) {
      // Copying a value is the value itself in Lean. A claws::list copies
      // by sharing nodes that never change, so it counts too.
      CXXConstructorDecl *Ctor = C->getConstructor();
      bool Copy = C->getNumArgs() == 1 && (Ctor->isCopyConstructor() || Ctor->isMoveConstructor());
      auto Elem = listElement(C->getType());
      auto VElem = vecElement(C->getType());
      if (Copy && (Ctor->isTrivial() || Elem || VElem)) {
        return expr(C->getArg(0));
      }
      if (Elem && C->getNumArgs() == 0 && Ctor->isDefaultConstructor()) {
        return "([] : List " + paren(type(*Elem, C->getExprLoc())) + ")";
      }
      if (VElem && C->getNumArgs() == 0 && Ctor->isDefaultConstructor()) {
        return "(#[] : Array " + paren(type(*VElem, C->getExprLoc())) + ")";
      }
      if (VElem && C->getNumArgs() == 2) {
        requireU32(C->getArg(0));
        for (const VarDecl *V : referenced(C->getArg(0))) {
          BoundVars.insert(V);
        }
        return "(Array.replicate " + expr(C->getArg(0)) + ".toNat " + expr(C->getArg(1)) + ")";
      }
      reject(C->getExprLoc(), "only copying a struct and `list<T>{}` construct values in the subset");
    }
    if (isa<LambdaExpr>(E)) {
      reject(E->getExprLoc(), "a lambda may appear only as an argument of `match`");
    }
    reject(E->getExprLoc(), std::string("a ") + E->getStmtClassName() + " expression is outside the subset");
  }

  std::string implicitCast(const ImplicitCastExpr *C) {
    const Expr *Sub = C->getSubExpr();
    switch (C->getCastKind()) {
    case CK_LValueToRValue:
    case CK_NoOp:
      return expr(Sub);
    case CK_IntegralCast:
      return integralCast(Sub, C->getType(), C->getExprLoc());
    default:
      reject(C->getExprLoc(), std::string("an implicit ") + C->getCastKindName() +
                                  " conversion is outside the subset");
    }
  }

  // The table a subscript `table[i]` reads, which must be a constant
  // array.
  const VarDecl *constArray(const ArraySubscriptExpr *A) {
    auto *R = dyn_cast<DeclRefExpr>(A->getBase()->IgnoreParenImpCasts());
    auto *V = R ? dyn_cast<VarDecl>(R->getDecl()) : nullptr;
    if (!V || !ConstArrays.count(V->getCanonicalDecl())) {
      reject(A->getExprLoc(), "only a constant array may be indexed with a built-in `[]`; use claws::vec");
    }
    return V;
  }

  // An integer conversion, implicit or explicit. Widening a uint8_t (to
  // uint32_t, or to int by promotion) zero-extends it; narrowing to
  // uint8_t keeps the low 8 bits, as C++ defines; and an int of the subset
  // is already the BitVec 32 of its value.
  std::string integralCast(const Expr *Sub, QualType To, SourceLocation Loc) {
    QualType From = Sub->getType();
    if (auto *L = dyn_cast<IntegerLiteral>(Sub->IgnoreParens())) {
      if (isU32(To) || isInt(To)) {
        return u32Literal(L);
      }
      if (isU8(To)) {
        if (L->getValue().getActiveBits() > 8) {
          reject(L->getLocation(), "the literal does not fit in uint8_t");
        }
        return "(" + std::to_string(L->getValue().getZExtValue()) + " : BitVec 8)";
      }
    }
    if (isU8(From) && (isU32(To) || isInt(To))) {
      return "(" + expr(Sub) + ".setWidth 32)";
    }
    if ((isU32(From) || isInt(From)) && isU8(To)) {
      return "(" + expr(Sub) + ".setWidth 8)";
    }
    if (isInt(From) && isU32(To)) {
      return expr(Sub);
    }
    if (isInt(To) || isInt(From)) {
      reject(Loc, "signed integers are outside the subset; a conversion between `" +
                      From.getAsString(Ctx.getPrintingPolicy()) + "` and `" + To.getAsString(Ctx.getPrintingPolicy()) +
                      "` is not allowed");
    }
    reject(Loc, "a conversion from `" + From.getAsString(Ctx.getPrintingPolicy()) + "` to `" +
                    To.getAsString(Ctx.getPrintingPolicy()) + "` is outside the subset");
  }

  std::string unary(const UnaryOperator *U) {
    const Expr *Sub = U->getSubExpr();
    switch (U->getOpcode()) {
    case UO_LNot:
      return "(!" + boolExpr(Sub) + ")";
    case UO_Not:
      requireU32(Sub);
      return "(~~~" + expr(Sub) + ")";
    case UO_Minus:
      requireU32(Sub);
      return "(-" + expr(Sub) + ")";
    case UO_Plus:
      requireU32(Sub);
      return expr(Sub);
    default:
      if (U->isIncrementDecrementOp()) {
        reject(U->getOperatorLoc(), "`++` and `--` must be statements of their own");
      }
      reject(U->getOperatorLoc(), "operator `" + UnaryOperator::getOpcodeStr(U->getOpcode()).str() +
                                      "` is outside the subset");
    }
  }

  void requireU32(const Expr *E) {
    if (isInt(E->getType())) {
      reject(E->getExprLoc(), "expected a uint32_t, found `int`. A uint8_t becomes an int in arithmetic, where "
                              "only & | ^, >> by a literal and comparisons are allowed; convert it first, as in "
                              "static_cast<uint32_t>(b)");
    }
    if (!isU32(E->getType())) {
      reject(E->getExprLoc(), "expected a uint32_t, found `" + E->getType().getAsString(Ctx.getPrintingPolicy()) + "`");
    }
  }

  std::string binary(const BinaryOperator *B) {
    const Expr *L = B->getLHS();
    const Expr *R = B->getRHS();
    std::string Op = B->getOpcodeStr().str();
    auto infix = [&](const char *LeanOp) { return "(" + expr(L) + " " + LeanOp + " " + expr(R) + ")"; };
    auto u32Args = [&] {
      requireU32(L);
      requireU32(R);
    };
    // Bitwise operators and comparisons also take two ints of the subset.
    auto wordArgs = [&] {
      if (!(isInt(L->getType()) && isInt(R->getType()))) {
        u32Args();
      }
    };
    switch (B->getOpcode()) {
    case BO_Add:
      u32Args();
      return infix("+");
    case BO_Sub:
      u32Args();
      return infix("-");
    case BO_Mul:
      u32Args();
      return infix("*");
    case BO_And:
      wordArgs();
      return infix("&&&");
    case BO_Or:
      wordArgs();
      return infix("|||");
    case BO_Xor:
      wordArgs();
      return infix("^^^");
    case BO_LT:
      wordArgs();
      return "(BitVec.ult " + expr(L) + " " + expr(R) + ")";
    case BO_LE:
      wordArgs();
      return "(BitVec.ule " + expr(L) + " " + expr(R) + ")";
    case BO_GT:
      wordArgs();
      return "(BitVec.ult " + expr(R) + " " + expr(L) + ")";
    case BO_GE:
      wordArgs();
      return "(BitVec.ule " + expr(R) + " " + expr(L) + ")";
    case BO_EQ:
    case BO_NE:
      if (!((isU32(L->getType()) && isU32(R->getType())) || (isInt(L->getType()) && isInt(R->getType())) ||
            (isBool(L->getType()) && isBool(R->getType())) ||
            (enumOf(L->getType()) && enumOf(L->getType()) == enumOf(R->getType())))) {
        reject(B->getOperatorLoc(), "`" + Op + "` compares two uint32_t, bool or same-enum values only");
      }
      return infix(B->getOpcode() == BO_EQ ? "==" : "!=");
    case BO_LAnd:
      return "(" + boolExpr(L) + " && " + boolExpr(R) + ")";
    case BO_LOr:
      return "(" + boolExpr(L) + " || " + boolExpr(R) + ")";
    case BO_Div:
    case BO_Rem:
      // Total in Lean (x / 0 = 0, x % 0 = x); f.safe rules out zero.
      u32Args();
      divisor(R);
      return infix(B->getOpcode() == BO_Div ? "/" : "%");
    case BO_Shl:
    case BO_Shr:
      if (B->getOpcode() == BO_Shr && isInt(L->getType()) && literal(R)) {
        // A nonnegative int shifted right stays nonnegative.
        return "(" + expr(L) + " >>> " + amount(R) + ")";
      }
      requireU32(L);
      return "(" + expr(L) + (B->getOpcode() == BO_Shl ? " <<< " : " >>> ") + amount(R) + ")";
    default:
      if (B->isAssignmentOp()) {
        reject(B->getOperatorLoc(), "an assignment must be a statement of its own");
      }
      reject(B->getOperatorLoc(), "operator `" + Op + "` is outside the subset");
    }
  }

  static const LambdaExpr *lambdaArg(const Expr *E) {
    while (true) {
      if (auto *M = dyn_cast<MaterializeTemporaryExpr>(E)) {
        E = M->getSubExpr();
      } else if (auto *B = dyn_cast<CXXBindTemporaryExpr>(E)) {
        E = B->getSubExpr();
      } else if (auto *C = dyn_cast<ImplicitCastExpr>(E); C && C->getCastKind() == CK_NoOp) {
        E = C->getSubExpr();
      } else if (auto *C = dyn_cast<CXXConstructExpr>(E); C && C->getNumArgs() == 1) {
        E = C->getArg(0);
      } else {
        return dyn_cast<LambdaExpr>(E->IgnoreParens());
      }
    }
  }

  // `xs.match([&] { .. }, [&](T h, list<T> t) { .. })` becomes
  // `(match xs with | [] => .. | h :: t => ..)`. The lambdas run at once,
  // in a world where nothing changes, so their captures are the outer
  // variables themselves.
  std::string listMatch(const CXXMemberCallExpr *C) {
    const CXXMethodDecl *M = C->getMethodDecl();
    std::optional<QualType> Elem;
    if (M && M->getName() == "match") {
      Elem = listElement(Ctx.getCanonicalTagType(M->getParent()));
    }
    if (!Elem || C->getNumArgs() != 2) {
      reject(C->getExprLoc(), "the only method call in the subset is `list<T>::match(on_nil, on_cons)`");
    }
    const LambdaExpr *Arms[2] = {lambdaArg(C->getArg(0)), lambdaArg(C->getArg(1))};
    std::string ElemType = type(*Elem, C->getExprLoc());
    for (int I = 0; I < 2; ++I) {
      const LambdaExpr *L = Arms[I];
      if (!L) {
        reject(C->getArg(I)->getExprLoc(), "each argument of `match` must be a lambda written in place");
      }
      if (L->isGenericLambda() || L->isMutable()) {
        reject(L->getBeginLoc(), "a `match` lambda may not be generic or `mutable`");
      }
      for (const LambdaCapture &Cap : L->captures()) {
        if (!Cap.capturesVariable() || cast<VarDecl>(Cap.getCapturedVar())->isInitCapture()) {
          reject(Cap.getLocation(), "a `match` lambda may capture only local variables");
        }
      }
      if (!Ctx.hasSameType(L->getCallOperator()->getReturnType(), C->getType())) {
        reject(L->getBeginLoc(), "both `match` lambdas must return the same type");
      }
      unsigned Want = I == 0 ? 0 : 2;
      if (L->getCallOperator()->getNumParams() != Want) {
        reject(L->getBeginLoc(), I == 0 ? "the empty case takes no parameters"
                                        : "the cons case takes (T head, list<T> tail), by value or const&");
      }
    }
    const CXXMethodDecl *Cons = Arms[1]->getCallOperator();
    const ParmVarDecl *Head = Cons->getParamDecl(0);
    const ParmVarDecl *Tail = Cons->getParamDecl(1);
    if (isInout(Head) || isInout(Tail) || varType(Head) != ElemType || varType(Tail) != "List " + paren(ElemType)) {
      reject(Cons->getBeginLoc(), "the cons case takes (T head, list<T> tail), by value or const&");
    }
    auto name = [](const ParmVarDecl *P) { return P->getName().empty() ? std::string("_") : leanName(P->getName()); };
    int D = ExprDepth;
    std::string Scrutinee = expr(C->getImplicitObjectArgument());
    auto *NilBody = cast<CompoundStmt>(Arms[0]->getBody());
    auto *ConsBody = cast<CompoundStmt>(Arms[1]->getBody());
    const DeclContext *Outer = Scope;
    Scope = Arms[0]->getCallOperator();
    std::string Nil = stmts(NilBody->body(), NilBody->getRBracLoc(), D + 1);
    Scope = Arms[1]->getCallOperator();
    std::string ConsArm = stmts(ConsBody->body(), ConsBody->getRBracLoc(), D + 1);
    Scope = Outer;
    ExprDepth = D;
    return "(match " + Scrutinee + " with\n" + indent(D) + "| [] =>\n" + indent(D + 1) + Nil + "\n" + indent(D) +
           "| " + name(Head) + " :: " + name(Tail) + " =>\n" + indent(D + 1) + ConsArm + ")";
  }

  std::string call(const CallExpr *C, bool Effects = false) {
    const FunctionDecl *F = C->getDirectCallee();
    if (F && !Effects && !inoutParams(F).empty()) {
      reject(C->getExprLoc(), "a call that modifies a `T&` argument must be a statement, an initializer, "
                              "the right side of an assignment, or a returned value");
    }
    if (!F || isa<CXXOperatorCallExpr>(C) || isa<CXXMemberCallExpr>(C)) {
      reject(C->getExprLoc(), "only calls to plain functions are in the subset");
    }
    if (isLibraryName(F, "claws::cons")) {
      std::string Head = expr(C->getArg(0));
      std::string Tail = expr(C->getArg(1));
      return "(" + Head + " :: " + Tail + ")";
    }
    if (F->isInStdNamespace() && F->getName() == "move" && C->getNumArgs() == 1) {
      // Every value is immutable, so a move is a copy.
      return expr(C->getArg(0));
    }
    // A call to the function being defined is recursion. Lean decides
    // whether it terminates when it checks the output.
    bool Self = F->getCanonicalDecl() == Current->getCanonicalDecl();
    if (Self && LoopDepth > 0) {
      reject(C->getExprLoc(), "a function may not call itself from inside a loop");
    }
    const FunctionDecl *Def = F->getDefinition();
    if (!Self && (!Def || !Functions.count(Def))) {
      reject(C->getExprLoc(), "`" + F->getNameAsString() + "` is not a claws function defined earlier in this file");
    }
    if (C->getNumArgs() == 0) {
      return leanName(F->getName());
    }
    std::string S = "(" + leanName(F->getName());
    for (const Expr *A : C->arguments()) {
      S += " " + expr(A);
    }
    return S + ")";
  }

  std::string initList(const InitListExpr *I) {
    QualType T = I->getType();
    if (isU32(T) || isBool(T)) {
      // `uint32_t x{5};`
      if (I->getNumInits() != 1) {
        reject(I->getBeginLoc(), "a scalar takes exactly one initializer");
      }
      return expr(I->getInit(0));
    }
    const RecordDecl *R = T.getCanonicalType()->getAsRecordDecl();
    if (!R || !Structs.count(R)) {
      reject(I->getBeginLoc(), "this initializer list is outside the subset");
    }
    std::string S = "{ ";
    unsigned N = 0;
    for (const FieldDecl *F : R->fields()) {
      if (N >= I->getNumInits() || isa<ImplicitValueInitExpr>(I->getInit(N))) {
        reject(I->getBeginLoc(), "initialize every field of `" + R->getNameAsString() + "` explicitly");
      }
      S += (N ? ", " : "") + leanName(F->getName()) + " := " + expr(I->getInit(N));
      ++N;
    }
    return S + " : " + leanName(R->getName()) + " }";
  }
};

class Consumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
    if (Ctx.getDiagnostics().hasErrorOccurred()) {
      Failed = true;
      return;
    }
    Translator T(Ctx);
    T.translate(Ctx.getTranslationUnitDecl());
    if (T.failed()) {
      Failed = true;
      return;
    }
    Result = T.output();
    Obligations = T.obligations();
    if (!DiffCpp.empty()) {
      llvm::SmallString<256> Real;
      llvm::sys::fs::real_path(Ctx.getSourceManager()
                                   .getFileEntryRefForID(Ctx.getSourceManager().getMainFileID())
                                   ->getName(),
                               Real);
      HarnessCpp = T.diffCpp(std::string(Real), DiffCases, DiffSeed);
    }
    if (!DiffLean.empty()) {
      HarnessLean = T.diffLean(DiffCases, DiffSeed);
    }
  }

  static inline std::string HarnessCpp;
  static inline std::string HarnessLean;
  static inline bool Failed = false;
  static inline std::string Result;
  static inline std::vector<std::string> Obligations;
};

class Action : public ASTFrontendAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &, StringRef) override {
    return std::make_unique<Consumer>();
  }
};

// The tool runs the clang driver of the LLVM it was built with, so it
// needs that driver's header paths: its resource directory and, on macOS,
// the SDK. CMake bakes them in.
tooling::CommandLineArguments adjust(const tooling::CommandLineArguments &Args, StringRef) {
  tooling::CommandLineArguments Out(Args);
  if (!Out.empty()) {
    Out[0] = CLAWS_CLANG;
  }
  Out.insert(Out.begin() + 1, {"-resource-dir", CLAWS_RESOURCE_DIR, "-I", CLAWS_INCLUDE_ROOT, "-std=c++20",
                               "-xc++", "-fsyntax-only", "-Wno-pragma-once-outside-header"});
  // Only macOS has an SDK; elsewhere the driver finds the system headers.
  if (std::string(CLAWS_SDK) != "") {
    Out.insert(Out.begin() + 1, {"-isysroot", CLAWS_SDK});
  }
  return Out;
}

} // namespace

int main(int argc, const char **argv) {
  auto Parser = tooling::CommonOptionsParser::create(argc, argv, Category, llvm::cl::OneOrMore);
  if (!Parser) {
    llvm::errs() << Parser.takeError();
    return 2;
  }
  if (Parser->getSourcePathList().size() != 1) {
    llvm::errs() << "claws-lean: give exactly one source file\n";
    return 2;
  }
  std::string Source = Parser->getSourcePathList().front();
  tooling::ClangTool Tool(Parser->getCompilations(), {Source});
  Tool.appendArgumentsAdjuster(adjust);
  int Status = Tool.run(tooling::newFrontendActionFactory<Action>().get());
  if (Status != 0 || Consumer::Failed) {
    llvm::errs() << "claws-lean: " << Source << " is not in the claws subset\n";
    return 1;
  }
  std::string Name = llvm::sys::path::filename(Source).str();
  std::string Text = "-- Generated by claws-lean from " + Name + ". Do not edit.\n\nnamespace " + Namespace +
                     "\n\n" +
                     // C++ allows a store that is overwritten before it is read.
                     "set_option linter.unusedVariables false\n\n" + Consumer::Result + "end " + Namespace + "\n";
  if (!Consumer::Obligations.empty()) {
    // `Foo.Code` keeps its laws in `Foo.Laws`; obligations go beside them.
    StringRef Base(Namespace);
    Base.consume_back(".Code");
    std::string Safety = Base.str() + ".Laws.Safety";
    // Obligations name the project's own types, such as a struct parameter.
    Text += "\n-- Safety obligations: PROOF.lean must prove each, as it proves a law.\nnamespace " + Safety +
            "\n\nopen " + Namespace + "\n\n";
    for (const std::string &O : Consumer::Obligations) {
      Text += O;
    }
    Text += "end " + Safety + "\n";
  }
  if (!DiffCpp.empty()) {
    std::ofstream File(DiffCpp);
    File << Consumer::HarnessCpp;
  }
  if (!DiffLean.empty()) {
    std::ofstream File(DiffLean);
    File << Text << Consumer::HarnessLean;
  }
  if (Output.empty()) {
    if (DiffCpp.empty() && DiffLean.empty()) {
      llvm::outs() << Text;
    }
    return 0;
  }
  std::ofstream File(Output);
  File << Text;
  return File ? 0 : 1;
}
