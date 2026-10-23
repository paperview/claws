// claws-ast: write the Clang AST of a claws source file as a Lean term.
//
//   claws-ast code.hpp --project Clamp -o Ast.lean --
//
// The output is the program as Claws.Sem (lean/Claws/Sem.lean) sees it,
// plus one validation law per function, `<Project>.Laws.Valid.f`: for all
// arguments, the C++ function returns the value of `<Project>.Code.f`.
//
// This tool is part of the trusted base, so it makes no decisions. It
// prints each node Clang built, in Clang's own terms, and prints any node
// it does not know as `other "<kind>"`, which the semantics gives no
// meaning to; a function containing one cannot be validated. It shares no
// code with claws-lean, so a bug in one cannot hide the same bug in the
// other. It does not check that the program is in the subset: claws-lean
// does that, and the semantics does not need it.
//
// Each variable is named by its declaration's position, `x@16:32`, so
// shadowing needs no reasoning here.

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <functional>
#include <optional>
#include <set>
#include <string>
#include <vector>

using namespace clang;

namespace {

llvm::cl::OptionCategory Category("claws-ast options");
llvm::cl::opt<std::string> Project("project", llvm::cl::Required, llvm::cl::desc("The project's Lean namespace"),
                                   llvm::cl::cat(Category));
llvm::cl::opt<std::string> Output("o", llvm::cl::desc("Output file (default: stdout)"), llvm::cl::cat(Category));

std::string quote(StringRef S) {
  std::string R = "\"";
  for (char C : S) {
    if (C == '"' || C == '\\') {
      R += '\\';
    }
    R += C;
  }
  return R + "\"";
}

class Printer {
public:
  explicit Printer(ASTContext &Ctx) : Ctx(Ctx), SM(Ctx.getSourceManager()) {
    llvm::SmallString<256> Real;
    if (!llvm::sys::fs::real_path(CLAWS_INCLUDE_ROOT "/claws", Real)) {
      Library = std::string(Real) + "/";
    }
  }

  // A node the semantics does not cover. The function containing it gets
  // no validation law.
  std::string other(StringRef What) {
    Covered = false;
    return "(.other " + quote(What) + ")";
  }

  // A variable's name: its spelling and where it is declared.
  std::string var(const ValueDecl *D) {
    PresumedLoc P = SM.getPresumedLoc(SM.getSpellingLoc(D->getLocation()));
    return quote(D->getNameAsString() + "@" + std::to_string(P.getLine()) + ":" + std::to_string(P.getColumn()));
  }

  // The element type of claws::vec, if R is one of its instances.
  std::optional<QualType> vecOf(const CXXRecordDecl *R) {
    const auto *S = dyn_cast_or_null<ClassTemplateSpecializationDecl>(R);
    if (!S || S->getQualifiedNameAsString() != "claws::vec" || !inLibrary(S->getSpecializedTemplate()) ||
        S->getTemplateArgs().size() != 1) {
      return std::nullopt;
    }
    return S->getTemplateArgs()[0].getAsType();
  }

  // The element type of a claws::vec, if T is one.
  std::optional<QualType> vecElem(QualType T) {
    return vecOf(T.getCanonicalType().getUnqualifiedType()->getAsCXXRecordDecl());
  }

  // Whether M is a member function of claws::vec.
  bool vecMethod(const CXXMethodDecl *M) {
    return M && vecOf(M->getParent()).has_value();
  }

  // The element type of claws::list, if R is one of its instances.
  std::optional<QualType> listOf(const CXXRecordDecl *R) {
    const auto *S = dyn_cast_or_null<ClassTemplateSpecializationDecl>(R);
    if (!S || S->getQualifiedNameAsString() != "claws::list" || !inLibrary(S->getSpecializedTemplate()) ||
        S->getTemplateArgs().size() != 1) {
      return std::nullopt;
    }
    return S->getTemplateArgs()[0].getAsType();
  }

  std::optional<QualType> listElem(QualType T) {
    return listOf(T.getCanonicalType().getUnqualifiedType()->getAsCXXRecordDecl());
  }

  bool listMethod(const CXXMethodDecl *M) {
    return M && listOf(M->getParent()).has_value();
  }

  // A lambda passed to a list's match, as a function of the program named
  // by its position, which no C++ call can name. Its body sees the names
  // of the scope it is written in. A lambda whose call operator is not
  // const could change what it captures by copy, and one with an init
  // capture declares a name the semantics does not see: both are left to
  // other.
  std::string lambda(const Expr *E, size_t Arity) {
    const auto *L = dyn_cast<LambdaExpr>(E->IgnoreImplicit());
    if (!L) {
      return other("a match argument that is not a lambda");
    }
    const CXXMethodDecl *Op = L->getCallOperator();
    if (L->isMutable() || Op->getNumParams() != Arity) {
      return other("LambdaExpr");
    }
    for (const LambdaCapture &C : L->captures()) {
      if (C.capturesVariable() && C.getCapturedVar()->isInitCapture()) {
        return other("LambdaExpr with an init capture");
      }
    }
    std::vector<std::string> Params;
    for (const ParmVarDecl *P : Op->parameters()) {
      Params.push_back("(" + var(P) + ", " + ty(P->getType()) + ")");
    }
    PresumedLoc P = SM.getPresumedLoc(SM.getSpellingLoc(L->getBeginLoc()));
    std::string Name = "lambda@" + std::to_string(P.getLine()) + ":" + std::to_string(P.getColumn());
    std::string Body = stmt(L->getBody());
    Funcs.push_back(Name);
    FuncDefs += "def Fn.«" + Name + "» : Func := {\n  params := " + list(Params) + ",\n  ret := " +
                ty(Op->getReturnType()) + ",\n  body := " + Body + " }\n\n";
    return quote(Name);
  }

  std::string ty(QualType T) {
    if (const auto *R = T->getAs<LValueReferenceType>()) {
      return "(.ref " + ty(R->getPointeeType()) + ")";
    }
    if (auto V = vecElem(T)) {
      return "(.vec " + ty(*V) + ")";
    }
    if (auto V = listElem(T)) {
      return "(.list " + ty(*V) + ")";
    }
    T = T.getCanonicalType().getUnqualifiedType();
    if (const auto *B = T->getAs<BuiltinType>()) {
      switch (B->getKind()) {
      case BuiltinType::Void:
        return ".void";
      case BuiltinType::Bool:
        return ".bool";
      case BuiltinType::UInt:
        return ".uint";
      case BuiltinType::UChar:
        return ".uchar";
      case BuiltinType::Int:
        return ".int";
      default:
        break;
      }
    }
    if (const auto *E = T->getAs<EnumType>()) {
      return "(.enum " + quote(E->getDecl()->getNameAsString()) + ")";
    }
    if (const auto *R = T->getAsCXXRecordDecl()) {
      return "(.record " + quote(R->getNameAsString()) + ")";
    }
    return other(T.getAsString());
  }

  // A value of type T, as Clang computed it, such as a case label.
  std::optional<std::string> val(QualType T, const llvm::APSInt &V) {
    T = T.getCanonicalType().getUnqualifiedType();
    std::string N = V.isSigned() ? std::to_string(V.getSExtValue()) : std::to_string(V.getZExtValue());
    std::string Paren = N[0] == '-' ? "(" + N + ")" : N;
    if (const auto *E = T->getAs<EnumType>()) {
      return "(.enum " + quote(E->getDecl()->getNameAsString()) + " " + Paren + ")";
    }
    if (const auto *B = T->getAs<BuiltinType>()) {
      switch (B->getKind()) {
      case BuiltinType::UInt:
        return "(.uint " + Paren + ")";
      case BuiltinType::UChar:
        return "(.uchar " + Paren + ")";
      case BuiltinType::Int:
        return "(.int " + Paren + ")";
      case BuiltinType::Bool:
        return std::string("(.bool ") + (V.getBoolValue() ? "true" : "false") + ")";
      default:
        break;
      }
    }
    return std::nullopt;
  }

  // The value Clang computed for a constant of type T: an array as a vec
  // of its elements, the ones its initializer leaves out as the filler.
  std::optional<std::string> apval(QualType T, const APValue &A) {
    T = T.getCanonicalType().getUnqualifiedType();
    if (const auto *AT = Ctx.getAsConstantArrayType(T)) {
      if (!A.isArray()) {
        return std::nullopt;
      }
      std::vector<std::string> Es;
      for (unsigned I = 0; I < A.getArraySize(); ++I) {
        const APValue &E = I < A.getArrayInitializedElts() ? A.getArrayInitializedElt(I) : A.getArrayFiller();
        auto S = apval(AT->getElementType(), E);
        if (!S) {
          return std::nullopt;
        }
        Es.push_back(*S);
      }
      return "(.vec " + list(Es) + ")";
    }
    if (A.isInt()) {
      return val(T, A.getInt());
    }
    if (A.isStruct()) {
      const auto *R = T->getAsCXXRecordDecl();
      if (!R || A.getStructNumBases() != 0) {
        return std::nullopt;
      }
      std::vector<std::string> Fs;
      unsigned I = 0;
      for (const FieldDecl *F : R->fields()) {
        auto S = apval(F->getType(), A.getStructField(I++));
        if (!S) {
          return std::nullopt;
        }
        Fs.push_back("(" + quote(F->getNameAsString()) + ", " + *S + ")");
      }
      return "(.record " + list(Fs) + ")";
    }
    return std::nullopt;
  }

  std::string castKind(CastKind K) {
    switch (K) {
    case CK_LValueToRValue:
      return ".lvalueToRValue";
    case CK_IntegralCast:
      return ".integralCast";
    case CK_IntegralToBoolean:
      return ".integralToBoolean";
    case CK_NoOp:
      return ".noOp";
    default:
      return other(CastExpr::getCastKindName(K));
    }
  }

  std::string binOp(BinaryOperatorKind K) {
    switch (K) {
    case BO_Add:
    case BO_AddAssign:
      return ".add";
    case BO_Sub:
    case BO_SubAssign:
      return ".sub";
    case BO_Mul:
    case BO_MulAssign:
      return ".mul";
    case BO_Div:
    case BO_DivAssign:
      return ".div";
    case BO_Rem:
    case BO_RemAssign:
      return ".rem";
    case BO_Shl:
    case BO_ShlAssign:
      return ".shl";
    case BO_Shr:
    case BO_ShrAssign:
      return ".shr";
    case BO_And:
    case BO_AndAssign:
      return ".and";
    case BO_Or:
    case BO_OrAssign:
      return ".or";
    case BO_Xor:
    case BO_XorAssign:
      return ".xor";
    case BO_LT:
      return ".lt";
    case BO_GT:
      return ".gt";
    case BO_LE:
      return ".le";
    case BO_GE:
      return ".ge";
    case BO_EQ:
      return ".eq";
    case BO_NE:
      return ".ne";
    default:
      return other(std::string("BinaryOperator ") + BinaryOperator::getOpcodeStr(K).str());
    }
  }

  std::string list(const std::vector<std::string> &Xs) {
    std::string S = "[";
    for (size_t I = 0; I < Xs.size(); ++I) {
      S += (I ? ", " : "") + Xs[I];
    }
    return S + "]";
  }

  // Whether D is declared in the claws library, `include/claws`.
  bool inLibrary(const Decl *D) {
    StringRef File = SM.getFilename(SM.getExpansionLoc(D->getLocation()));
    llvm::SmallString<256> Real;
    if (Library.empty() || llvm::sys::fs::real_path(File, Real)) {
      return false;
    }
    return StringRef(Real).starts_with(Library);
  }

  std::string expr(const Expr *E) {
    if (const auto *L = dyn_cast<IntegerLiteral>(E)) {
      return "(.intLit " + ty(L->getType()) + " " + std::to_string(L->getValue().getZExtValue()) + ")";
    }
    if (const auto *B = dyn_cast<CXXBoolLiteralExpr>(E)) {
      return std::string("(.boolLit ") + (B->getValue() ? "true" : "false") + ")";
    }
    if (const auto *R = dyn_cast<DeclRefExpr>(E)) {
      if (const auto *V = dyn_cast<VarDecl>(R->getDecl())) {
        if (!V->isLocalVarDeclOrParm()) {
          if (GlobalNames.count(V->getNameAsString())) {
            return "(.global " + quote(V->getNameAsString()) + ")";
          }
          return other("DeclRefExpr to a global variable");
        }
        return "(.var " + var(V) + ")";
      }
      if (const auto *C = dyn_cast<EnumConstantDecl>(R->getDecl())) {
        const llvm::APSInt &V = C->getInitVal();
        std::string N = std::to_string(V.isSigned() ? V.getSExtValue() : (int64_t)V.getZExtValue());
        return "(.enumLit " + quote(cast<EnumDecl>(C->getDeclContext())->getNameAsString()) + " " +
               (N[0] == '-' ? "(" + N + ")" : N) + ")";
      }
      return other(std::string("DeclRefExpr to ") + R->getDecl()->getDeclKindName());
    }
    if (const auto *A = dyn_cast<ArraySubscriptExpr>(E)) {
      // `a[i]` on an array: the array decays to a pointer to its first
      // element, and a[i] is *(a + i) ([expr.sub]), element i.
      const auto *D = dyn_cast<ImplicitCastExpr>(A->getLHS());
      if (!D || D->getCastKind() != CK_ArrayToPointerDecay) {
        return other("ArraySubscriptExpr on a pointer");
      }
      return "(.subscript " + expr(D->getSubExpr()) + " " + expr(A->getRHS()) + ")";
    }
    if (const auto *M = dyn_cast<MemberExpr>(E)) {
      if (M->isArrow()) {
        return other("MemberExpr ->");
      }
      return "(.member " + expr(M->getBase()) + " " + quote(M->getMemberDecl()->getNameAsString()) + ")";
    }
    if (const auto *C = dyn_cast<CastExpr>(E)) {
      if (isa<ImplicitCastExpr>(C) || isa<CStyleCastExpr>(C) || isa<CXXFunctionalCastExpr>(C) ||
          isa<CXXStaticCastExpr>(C)) {
        return "(.cast " + castKind(C->getCastKind()) + " " + ty(C->getType()) + " " + expr(C->getSubExpr()) + ")";
      }
      return other(C->getStmtClassName());
    }
    if (const auto *C = dyn_cast<ConstantExpr>(E)) {
      // A constant expression has the value of the expression it wraps.
      return expr(C->getSubExpr());
    }
    if (const auto *U = dyn_cast<UnaryOperator>(E)) {
      switch (U->getOpcode()) {
      case UO_PreInc:
      case UO_PostInc:
      case UO_PreDec:
      case UO_PostDec:
        return std::string("(.incdec ") + (U->isIncrementOp() ? "true" : "false") + " " +
               (U->isPostfix() ? "true" : "false") + " " + expr(U->getSubExpr()) + ")";
      default:
        break;
      }
      std::string Op;
      switch (U->getOpcode()) {
      case UO_LNot:
        Op = ".lnot";
        break;
      case UO_Not:
        Op = ".not";
        break;
      case UO_Minus:
        Op = ".minus";
        break;
      case UO_Plus:
        Op = ".plus";
        break;
      default:
        Op = other(UnaryOperator::getOpcodeStr(U->getOpcode()));
      }
      return "(.unary " + Op + " " + expr(U->getSubExpr()) + ")";
    }
    if (const auto *C = dyn_cast<CompoundAssignOperator>(E)) {
      return "(.compound " + binOp(C->getOpcode()) + " " + ty(C->getLHS()->getType()) + " " +
             ty(C->getComputationLHSType()) + " " + expr(C->getLHS()) + " " + expr(C->getRHS()) + ")";
    }
    if (const auto *B = dyn_cast<BinaryOperator>(E)) {
      if (B->getOpcode() == BO_LAnd || B->getOpcode() == BO_LOr) {
        return std::string("(") + (B->getOpcode() == BO_LAnd ? ".land " : ".lor ") + expr(B->getLHS()) + " " +
               expr(B->getRHS()) + ")";
      }
      if (B->getOpcode() == BO_Assign) {
        return "(.assign " + expr(B->getLHS()) + " " + expr(B->getRHS()) + ")";
      }
      return "(.binary " + binOp(B->getOpcode()) + " " + expr(B->getLHS()) + " " + expr(B->getRHS()) + ")";
    }
    if (const auto *C = dyn_cast<ConditionalOperator>(E)) {
      return "(.cond " + expr(C->getCond()) + " " + expr(C->getTrueExpr()) + " " + expr(C->getFalseExpr()) + ")";
    }
    if (const auto *C = dyn_cast<CXXMemberCallExpr>(E)) {
      const CXXMethodDecl *M = C->getMethodDecl();
      if (vecMethod(M) && M->getName() == "size" && C->getNumArgs() == 0) {
        return "(.builtin .size [" + expr(C->getImplicitObjectArgument()) + "])";
      }
      if (vecMethod(M) && M->getName() == "push" && C->getNumArgs() == 1) {
        return "(.builtin .push [" + expr(C->getImplicitObjectArgument()) + ", " + expr(C->getArg(0)) + "])";
      }
      if (listMethod(M) && M->getName() == "match" && C->getNumArgs() == 2) {
        // The two lambdas must return one type: match returns the
        // first's, and the semantics converts neither.
        const auto *N = dyn_cast<LambdaExpr>(C->getArg(0)->IgnoreImplicit());
        const auto *K = dyn_cast<LambdaExpr>(C->getArg(1)->IgnoreImplicit());
        if (!N || !K ||
            N->getCallOperator()->getReturnType().getCanonicalType() !=
                K->getCallOperator()->getReturnType().getCanonicalType()) {
          return other("match whose lambdas return different types");
        }
        std::string Xs = expr(C->getImplicitObjectArgument());
        std::string OnNil = lambda(C->getArg(0), 0);
        std::string OnCons = lambda(C->getArg(1), 2);
        return "(.listMatch " + Xs + " " + OnNil + " " + OnCons + ")";
      }
      return other(C->getStmtClassName());
    }
    if (const auto *C = dyn_cast<CXXOperatorCallExpr>(E)) {
      if (C->getOperator() == OO_Subscript && C->getNumArgs() == 2 &&
          vecMethod(dyn_cast_or_null<CXXMethodDecl>(C->getDirectCallee()))) {
        return "(.builtin .index [" + expr(C->getArg(0)) + ", " + expr(C->getArg(1)) + "])";
      }
      // A list's copy or move assignment stores the value, as assignment
      // of a scalar does: the nodes are shared and never change.
      if (C->getOperator() == OO_Equal && C->getNumArgs() == 2) {
        const auto *M = dyn_cast_or_null<CXXMethodDecl>(C->getDirectCallee());
        if (listMethod(M) && (M->isCopyAssignmentOperator() || M->isMoveAssignmentOperator())) {
          return "(.assign " + expr(C->getArg(0)) + " " + expr(C->getArg(1)) + ")";
        }
      }
      return other(C->getStmtClassName());
    }
    if (const auto *M = dyn_cast<MaterializeTemporaryExpr>(E)) {
      // Only an argument of the claws library binds a temporary that the
      // semantics covers: it reads the value (Mem.value).
      return expr(M->getSubExpr());
    }
    if (const auto *B = dyn_cast<CXXBindTemporaryExpr>(E)) {
      // A temporary that needs a destructor, a list in the subset: the
      // destructor frees nodes no list still shares, which the semantics
      // does not see.
      return expr(B->getSubExpr());
    }
    if (const auto *W = dyn_cast<ExprWithCleanups>(E)) {
      // The cleanups end temporaries, which in the subset hold scalars.
      return expr(W->getSubExpr());
    }
    if (const auto *C = dyn_cast<CallExpr>(E)) {
      const auto *Decay = dyn_cast<ImplicitCastExpr>(C->getCallee());
      const auto *F = C->getDirectCallee();
      if (!Decay || Decay->getCastKind() != CK_FunctionToPointerDecay || !F) {
        return other("CallExpr of an expression");
      }
      std::vector<std::string> Args;
      for (const Expr *A : C->arguments()) {
        Args.push_back(expr(A));
      }
      std::string Name = F->getQualifiedNameAsString();
      if (inLibrary(F)) {
        std::string B = Name == "claws::expects"     ? ".expects"
                        : Name == "claws::decreases" ? ".decreases"
                        : Name == "claws::cons"      ? ".cons"
                                                     : "(.other " + quote(Name) + ")";
        return "(.builtin " + B + " " + list(Args) + ")";
      }
      if (!SM.isInMainFile(SM.getExpansionLoc(F->getLocation()))) {
        return other("a call to " + Name + ", declared outside the program and the claws library");
      }
      Callees.insert(Name);
      return "(.call " + quote(Name) + " " + list(Args) + ")";
    }
    if (const auto *C = dyn_cast<CXXConstructExpr>(E)) {
      const CXXConstructorDecl *K = C->getConstructor();
      if (C->getNumArgs() == 1 && K->isCopyOrMoveConstructor() && K->isTrivial()) {
        return "(.copy " + expr(C->getArg(0)) + ")";
      }
      if (vecMethod(K)) {
        // Copying a vec copies its elements, and so does moving one: the
        // subset moves only a local it returns, which then ends
        // (include/claws/vec.hpp).
        if (C->getNumArgs() == 1 && K->isCopyOrMoveConstructor()) {
          return "(.copy " + expr(C->getArg(0)) + ")";
        }
        if (C->getNumArgs() == 0 && K->isDefaultConstructor()) {
          return "(.builtin .vecEmpty [])";
        }
        if (C->getNumArgs() == 2) {
          return "(.builtin .vecFill [" + expr(C->getArg(0)) + ", " + expr(C->getArg(1)) + "])";
        }
      }
      if (listMethod(K)) {
        // Copying or moving a list copies its elements' values.
        if (C->getNumArgs() == 1 && K->isCopyOrMoveConstructor()) {
          return "(.copy " + expr(C->getArg(0)) + ")";
        }
        if (C->getNumArgs() == 0 && K->isDefaultConstructor()) {
          return "(.builtin .listNil [])";
        }
      }
      return other("CXXConstructExpr");
    }
    if (const auto *I = dyn_cast<InitListExpr>(E)) {
      std::vector<std::string> Es;
      for (const Expr *X : I->inits()) {
        Es.push_back(expr(X));
      }
      return "(.initList " + ty(I->getType()) + " " + list(Es) + ")";
    }
    if (const auto *P = dyn_cast<ParenExpr>(E)) {
      return "(.paren " + expr(P->getSubExpr()) + ")";
    }
    return other(E->getStmtClassName());
  }

  // A substatement of an if is a block scope even without braces
  // ([stmt.pre]/5).
  std::string scoped(const Stmt *S) {
    if (isa<CompoundStmt>(S)) {
      return stmt(S);
    }
    return "(.block [" + stmt(S) + "])";
  }

  // The statements of a switch body, each label a statement of its own
  // where it stands. A label nested deeper than the body's own statements
  // is left to `other`.
  void labels(const Stmt *S, QualType Cond, std::vector<std::string> &Out) {
    if (const auto *C = dyn_cast<CaseStmt>(S)) {
      Expr::EvalResult R;
      std::optional<std::string> V;
      if (!C->caseStmtIsGNURange() && C->getLHS()->EvaluateAsInt(R, Ctx)) {
        V = val(Cond, R.Val.getInt());
      }
      Out.push_back(V ? "(.caseLabel " + *V + ")" : other("a case label of type " + Cond.getAsString()));
      labels(C->getSubStmt(), Cond, Out);
      return;
    }
    if (const auto *D = dyn_cast<DefaultStmt>(S)) {
      Out.push_back(".defaultLabel");
      labels(D->getSubStmt(), Cond, Out);
      return;
    }
    Out.push_back(stmt(S));
  }

  // A loop, its parts named as definitions (`f.loopN.cond`, `.body`,
  // `.step`) so that a proof can recognize it; numbered in the order the
  // loops start, as claws-lean numbers them. Also a proof aid: the
  // variables the loop mentions, and a for loop's counter.
  std::string loop(const Stmt *L, const Expr *Cond, const Stmt *Body, const std::string &Step,
                   const std::string &Counter) {
    std::string N = Project + ".Ast.«" + FnName + "».loop" + std::to_string(++LoopCount);
    std::string Short = "«" + FnName + "».loop" + std::to_string(LoopCount);
    std::string C = expr(Cond);
    std::string B = scoped(Body);
    std::set<std::string> Seen;
    std::vector<std::string> Vs;
    std::function<void(const Stmt *)> walk = [&](const Stmt *X) {
      if (!X) {
        return;
      }
      if (const auto *R = dyn_cast<DeclRefExpr>(X)) {
        if (const auto *V = dyn_cast<VarDecl>(R->getDecl())) {
          if (Seen.insert(var(V)).second) {
            Vs.push_back(var(V));
          }
        }
      }
      for (const Stmt *Ch : X->children()) {
        walk(Ch);
      }
    };
    walk(L);
    LoopDefs += "def " + Short + ".cond : Expr := " + C + "\n" + "def " + Short + ".body : Stmt := " + B + "\n" +
                "def " + Short + ".step : Stmt := " + Step + "\n" + "def " + Short + ".vars : List String := " +
                list(Vs) + "\n" + "def " + Short + ".counter : String := " + (Counter.empty() ? "\"\"" : Counter) +
                "\n\n";
    return "(.loop " + N + ".cond " + N + ".body " + N + ".step)";
  }

  std::string stmt(const Stmt *S) {
    if (const auto *C = dyn_cast<CompoundStmt>(S)) {
      std::vector<std::string> Ss;
      for (const Stmt *X : C->body()) {
        Ss.push_back(stmt(X));
      }
      return "(.block " + list(Ss) + ")";
    }
    if (const auto *D = dyn_cast<DeclStmt>(S)) {
      if (!D->isSingleDecl()) {
        return other("DeclStmt of several declarations");
      }
      const auto *V = dyn_cast<VarDecl>(D->getSingleDecl());
      if (!V || !V->hasInit()) {
        return other("DeclStmt");
      }
      return "(.decl " + var(V) + " " + ty(V->getType()) + " " + expr(V->getInit()) + ")";
    }
    if (const auto *R = dyn_cast<ReturnStmt>(S)) {
      if (!R->getRetValue()) {
        return ".retVoid";
      }
      return "(.ret " + expr(R->getRetValue()) + ")";
    }
    if (const auto *I = dyn_cast<IfStmt>(S)) {
      if (I->getConditionVariable() || I->isConsteval() || I->isConstexpr()) {
        return other("IfStmt with a variable or constexpr");
      }
      std::string Ite = "(.ite " + expr(I->getCond()) + " " + scoped(I->getThen()) + " " +
                        (I->getElse() ? scoped(I->getElse()) : "(.block [])") + ")";
      // `if (init; c) s` is `{ init; if (c) s }` ([stmt.if]/3).
      if (I->getInit()) {
        return "(.block [" + stmt(I->getInit()) + ", " + Ite + "])";
      }
      return Ite;
    }
    if (const auto *W = dyn_cast<SwitchStmt>(S)) {
      const auto *Body = dyn_cast<CompoundStmt>(W->getBody());
      if (W->getInit() || W->getConditionVariable() || !Body) {
        return other("SwitchStmt with an initializer, a variable or no braces");
      }
      std::vector<std::string> Items;
      for (const Stmt *X : Body->body()) {
        labels(X, W->getCond()->getType(), Items);
      }
      return "(.switch " + expr(W->getCond()) + " " + list(Items) + ")";
    }
    if (isa<BreakStmt>(S)) {
      return ".brk";
    }
    if (isa<ContinueStmt>(S)) {
      return ".cont";
    }
    // for (init; c; inc) body is { init; while (c) { body; inc; } }, with
    // inc also run after a continue ([stmt.for]/1).
    if (const auto *F = dyn_cast<ForStmt>(S)) {
      if (!F->getInit() || !F->getCond() || !F->getInc() || F->getConditionVariable()) {
        return other("ForStmt without an initializer, a condition or an increment");
      }
      std::string Counter;
      if (const auto *D = dyn_cast<DeclStmt>(F->getInit())) {
        if (D->isSingleDecl()) {
          if (const auto *V = dyn_cast<VarDecl>(D->getSingleDecl())) {
            Counter = var(V);
          }
        }
      }
      std::string Init = stmt(F->getInit());
      std::string L = loop(F, F->getCond(), F->getBody(), "(.expr " + expr(F->getInc()) + ")", Counter);
      return "(.block [" + Init + ", " + L + "])";
    }
    if (const auto *W = dyn_cast<WhileStmt>(S)) {
      if (W->getConditionVariable()) {
        return other("WhileStmt with a variable");
      }
      return loop(W, W->getCond(), W->getBody(), "(.block [])", "");
    }
    if (isa<NullStmt>(S)) {
      return "(.block [])";
    }
    if (const auto *E = dyn_cast<Expr>(S)) {
      return "(.expr " + expr(E) + ")";
    }
    return other(S->getStmtClassName());
  }

  // The Lean type of a parameter or result in Code.lean, how to encode a
  // Lean value of it as a Claws.Sem.Val, and how to decode one back. Empty
  // when this stage of the semantics has no encoding for the type. A
  // scalar's encoding is a constructor, so a call matches it directly; a
  // struct's or an enum's is not, so the lemmas claws_valid proves about a
  // function read such an argument through its decoding.
  struct Enc {
    std::string LeanTy;
    std::string Fn;
    std::string Dec;
    bool Scalar;
    // A claws::vec, which never holds 2^32 elements.
    bool Vec = false;
  };

  std::optional<Enc> enc(QualType T) {
    if (auto V = vecElem(T)) {
      auto E = enc(*V);
      if (!E) {
        return std::nullopt;
      }
      return Enc{"Array (" + E->LeanTy + ")", "(Claws.Sem.Val.ofArray " + E->Fn + ")",
                 "(Claws.Sem.Val.asArray " + E->Dec + ")", false, true};
    }
    if (auto V = listElem(T)) {
      auto E = enc(*V);
      if (!E) {
        return std::nullopt;
      }
      return Enc{"List (" + E->LeanTy + ")", "(Claws.Sem.Val.ofList " + E->Fn + ")",
                 "(Claws.Sem.Val.asList " + E->Dec + ")", false};
    }
    T = T.getCanonicalType().getUnqualifiedType();
    if (const auto *B = T->getAs<BuiltinType>()) {
      if (B->getKind() == BuiltinType::UInt) {
        return Enc{"BitVec 32", "Claws.Sem.Val.uint", "Claws.Sem.Val.asUint", true};
      }
      if (B->getKind() == BuiltinType::UChar) {
        return Enc{"BitVec 8", "Claws.Sem.Val.uchar", "Claws.Sem.Val.asUchar", true};
      }
      if (B->getKind() == BuiltinType::Bool) {
        return Enc{"Bool", "Claws.Sem.Val.bool", "Claws.Sem.Val.asBool", true};
      }
      return std::nullopt;
    }
    std::string Name;
    if (const auto *E = T->getAs<EnumType>()) {
      Name = E->getDecl()->getNameAsString();
    } else if (const auto *R = T->getAsCXXRecordDecl()) {
      Name = R->getNameAsString();
    }
    if (!Name.empty() && Encoded.count(Name)) {
      return Enc{Project + ".Code.«" + Name + "»", Project + ".Ast.«" + Name + "».toVal",
                 Project + ".Ast.«" + Name + "».ofVal", false};
    }
    return std::nullopt;
  }

  void record(const CXXRecordDecl *R) {
    std::string Name = R->getNameAsString();
    std::vector<std::string> Fields;
    std::vector<std::string> Parts;
    std::vector<std::string> Pats;
    std::vector<std::string> Decs;
    bool Ok = true;
    for (const FieldDecl *F : R->fields()) {
      std::string N = F->getNameAsString();
      Fields.push_back("(" + quote(N) + ", " + ty(F->getType()) + ")");
      auto E = enc(F->getType());
      if (!E) {
        Ok = false;
        continue;
      }
      std::string X = "x" + std::to_string(Pats.size());
      Parts.push_back("(" + quote(N) + ", " + E->Fn + " v.«" + N + "»)");
      Pats.push_back("(" + quote(N) + ", " + X + ")");
      Decs.push_back("«" + N + "» := " + E->Dec + " " + X);
    }
    Structs.push_back(Name);
    StructDefs += "def Struct.«" + Name + "» : List (String × Ty) := " + list(Fields) + "\n\n";
    if (Ok) {
      Encoded.insert(Name);
      std::string Code = Project + ".Code.«" + Name + "»";
      Encoders += "@[claws_interp] def «" + Name + "».toVal (v : " + Code + ") : Claws.Sem.Val :=\n  .record " +
                  list(Parts) + "\n\n";
      std::string D = "{ ";
      for (size_t I = 0; I < Decs.size(); ++I) {
        D += (I ? ", " : "") + Decs[I];
      }
      Encoders += "@[claws_interp] def «" + Name + "».ofVal : Claws.Sem.Val → " + Code + "\n  | .record " +
                  list(Pats) + " => " + D + " }\n  | _ => default\n\n";
      Encoders += "@[claws_interp, claws_codec] theorem «" + Name + "».ofVal_toVal (v : " + Code + ") : «" + Name +
                  "».ofVal («" + Name + "».toVal v) = v := rfl\n\n";
    }
  }

  // A constexpr variable at namespace scope, with the value Clang
  // computes for it. Any other global stays uncovered.
  void global(const VarDecl *V) {
    if (!V->isConstexpr() || V->isLocalVarDeclOrParm()) {
      return;
    }
    const APValue *A = V->evaluateValue();
    if (!A) {
      return;
    }
    auto S = apval(V->getType(), *A);
    if (!S) {
      return;
    }
    std::string Name = V->getNameAsString();
    GlobalNames.insert(Name);
    Globals.push_back("(" + quote(Name) + ", " + *S + ")");
    // A proof aid, checked by rfl: the value is the encoding of the
    // constant Code.lean defines.
    QualType T = V->getType().getCanonicalType().getUnqualifiedType();
    std::optional<Enc> E;
    if (const auto *AT = Ctx.getAsConstantArrayType(T)) {
      if (auto I = enc(AT->getElementType())) {
        E = Enc{"", "(Claws.Sem.Val.ofArray " + I->Fn + ")", "", false};
      }
    } else {
      E = enc(T);
    }
    if (const auto *AT = Ctx.getAsConstantArrayType(T)) {
      GlobalFound += "set_option maxRecDepth 100000 in\n@[claws_interp] theorem Global.«" + Name + "».size : " + Project + ".Code.«" + Name +
                     "».size = " + std::to_string(AT->getSize().getZExtValue()) + " := rfl\n";
    }
    if (E) {
      // A table of 256 entries is deeper than rfl's default recursion.
      GlobalFound += "set_option maxRecDepth 100000 in\n@[claws_interp] theorem Global.«" + Name + "».found : List.lookup " + quote(Name) +
                     " prog.globals = some (" + E->Fn + " " + Project + ".Code.«" + Name + "») := rfl\n";
    }
  }

  void enumeration(const EnumDecl *E) {
    std::string Name = E->getNameAsString();
    if (!E->isScoped()) {
      return;
    }
    std::string Code = Project + ".Code.«" + Name + "»";
    std::string S = "@[claws_interp] def «" + Name + "».toVal : " + Code + " → Claws.Sem.Val\n";
    std::string D = "@[claws_interp] def «" + Name + "».ofVal : Claws.Sem.Val → " + Code + "\n  | .enum _ k =>\n";
    std::string Cases;
    for (const EnumConstantDecl *C : E->enumerators()) {
      const llvm::APSInt &V = C->getInitVal();
      std::string N = std::to_string(V.isSigned() ? V.getSExtValue() : (int64_t)V.getZExtValue());
      std::string Lit = N[0] == '-' ? "(" + N + ")" : N;
      S += "  | .«" + C->getNameAsString() + "» => .enum " + quote(Name) + " " + Lit + "\n";
      D += "    if k = " + Lit + " then .«" + C->getNameAsString() + "» else\n";
      Cases += " <;> rfl";
    }
    D += "    default\n  | _ => default\n";
    Encoded.insert(Name);
    Encoders += S + "\n" + D + "\n";
    Encoders += "@[claws_interp, claws_codec] theorem «" + Name + "».ofVal_toVal (v : " + Code + ") : «" + Name + "».ofVal («" +
                Name + "».toVal v) = v := by\n  cases v <;> rfl\n\n";
  }

  struct Fn {
    std::string Name;
    std::string Law;
    std::string Run;
    std::set<std::string> Callees;
    bool Covered;
  };

  void function(const FunctionDecl *F) {
    std::string Name = F->getQualifiedNameAsString();
    if (!Names.insert(Name).second) {
      // The semantics names functions by name, so a second function with
      // the same name is left out.
      Uncovered.push_back(Name + " (overloaded)");
      return;
    }
    Covered = true;
    Callees.clear();
    FnName = Name;
    LoopCount = 0;
    std::vector<std::string> Params;
    bool Encodable = true;
    // The law states its claim about Lean values a0, a1, ...; the lemma
    // claws_valid proves reads them from the call instead.
    std::string LawBinders, RunBinders, LawHyps, RunHyps;
    std::vector<std::string> Args, LawCode, RunCode, Refs;
    // The objects a call changes: each T& parameter that is not const.
    struct Out {
      std::string Ref;
      Enc E;
    };
    std::vector<Out> Outs;
    for (const ParmVarDecl *P : F->parameters()) {
      Params.push_back("(" + var(P) + ", " + ty(P->getType()) + ")");
      std::string I = std::to_string(Args.size());
      QualType T = P->getType();
      bool Ref = false, Const = false;
      if (const auto *R = T->getAs<LValueReferenceType>()) {
        Ref = true;
        Const = R->getPointeeType().isConstQualified();
        T = R->getPointeeType();
      }
      auto E = enc(T);
      if (!E) {
        Encodable = false;
        Args.push_back("default");
        continue;
      }
      std::string A = "a" + I;
      if (Ref) {
        std::string Pn = "p" + I;
        std::string Rd = "((m[" + Pn + "]?).getD default)";
        LawBinders += " (" + A + " : " + E->LeanTy + ")";
        LawHyps += "    m[" + Pn + "]? = some (" + E->Fn + " " + A + ") →\n";
        RunHyps += "    m[" + Pn + "]? = some (" + E->Fn + " (" + E->Dec + " " + Rd + ")) →\n";
        if (E->Vec) {
          LawHyps += "    " + A + ".size < 2 ^ 32 →\n";
          RunHyps += "    (" + E->Dec + " " + Rd + ").size < 2 ^ 32 →\n";
        }
        Args.push_back("Claws.Sem.Res.loc ⟨" + Pn + ", []⟩");
        LawCode.push_back(A);
        RunCode.push_back("(" + E->Dec + " " + Rd + ")");
        Refs.push_back(Pn);
        if (!Const) {
          Outs.push_back({Pn, *E});
        }
      } else if (E->Scalar) {
        LawBinders += " (" + A + " : " + E->LeanTy + ")";
        RunBinders += " (" + A + " : " + E->LeanTy + ")";
        Args.push_back("Claws.Sem.Res.val (" + E->Fn + " " + A + ")");
        LawCode.push_back(A);
        RunCode.push_back(A);
      } else {
        std::string V = "v" + I;
        LawBinders += " (" + A + " : " + E->LeanTy + ")";
        RunBinders += " (" + V + " : Claws.Sem.Val)";
        RunHyps += "    " + V + " = " + E->Fn + " (" + E->Dec + " " + V + ") →\n";
        if (E->Vec) {
          LawHyps += "    " + A + ".size < 2 ^ 32 →\n";
          RunHyps += "    (" + E->Dec + " " + V + ").size < 2 ^ 32 →\n";
        }
        Args.push_back("Claws.Sem.Res.val (" + E->Fn + " " + A + ")");
        LawCode.push_back(A);
        RunCode.push_back("(" + E->Dec + " " + V + ")");
      }
    }
    std::string Body = stmt(F->getBody());
    Funcs.push_back(Name);
    FuncDefs += "def Fn.«" + Name + "» : Func := {\n  params := " + list(Params) + ",\n  ret := " +
                ty(F->getReturnType()) + ",\n  body := " + Body + " }\n\n";
    bool Void = F->getReturnType()->isVoidType();
    auto R = enc(F->getReturnType());
    Fn Info{Name, "", "", Callees, Covered && Encodable && (Void || R.has_value())};
    if (Info.Covered) {
      std::string RefBinders;
      for (const std::string &Pn : Refs) {
        RefBinders += " (" + Pn + " : Nat)";
      }
      std::string Distinct;
      for (size_t I = 0; I < Refs.size(); ++I) {
        for (size_t J = I + 1; J < Refs.size(); ++J) {
          Distinct += "    " + Refs[I] + " ≠ " + Refs[J] + " →\n";
        }
      }
      // The translation returns its value, if any, then each changed object.
      size_t Total = (Void ? 0 : 1) + Outs.size();
      auto part = [&](const std::string &Res, size_t C) {
        if (Total == 1) {
          return Res;
        }
        std::string S = Res;
        for (size_t K = 0; K < C; ++K) {
          S += ".2";
        }
        return C + 1 < Total ? S + ".1" : S;
      };
      auto claim = [&](const std::vector<std::string> &Code, std::string &ResOut, std::string &MemOut) {
        std::string Call = "(" + Project + ".Code.«" + Name + "»";
        for (const std::string &A : Code) {
          Call += " " + A;
        }
        Call += ")";
        ResOut = Void ? "none" : "(some (" + R->Fn + " " + part(Call, 0) + "))";
        MemOut = "m";
        for (size_t K = 0; K < Outs.size(); ++K) {
          MemOut = "(" + MemOut + ".set " + Outs[K].Ref + " (" + Outs[K].E.Fn + " " +
                   part(Call, (Void ? 0 : 1) + K) + "))";
        }
      };
      std::string LawRes, LawMem, RunRes, RunMem;
      claim(LawCode, LawRes, LawMem);
      claim(RunCode, RunRes, RunMem);
      std::string Prog = Project + ".Ast.prog";
      PresumedLoc P = SM.getPresumedLoc(F->getLocation());
      Info.Law = "-- " + std::string(llvm::sys::path::filename(P.getFilename())) + ":" + std::to_string(P.getLine()) +
                 ": the C++ " + Name + ", called with any objects whenever its claws::expects hold, returns what Code." +
                 Name + " computes and leaves its T& arguments as Code." + Name + " does.\n";
      Info.Law += "def «" + Name + "» : Prop :=\n  ∀" + LawBinders + " (m : Claws.Sem.Mem)" + RefBinders + ",\n" +
                  LawHyps + Distinct + "    Claws.Sem.Pre " + Prog + " m " + quote(Name) + " " + list(Args) +
                  " →\n    Claws.Sem.Call " + Prog + " m " + quote(Name) + " " + list(Args) + "\n      " + LawRes +
                  "\n      " + LawMem + "\n\n";
      // In the lemma, a struct or enum argument is the value the call passes.
      std::string RunArgsS = "[";
      {
        size_t K = 0;
        for (const ParmVarDecl *Pa : F->parameters()) {
          QualType T = Pa->getType();
          bool Ref = T->getAs<LValueReferenceType>() != nullptr;
          auto E = enc(Ref ? T->getAs<LValueReferenceType>()->getPointeeType() : T);
          std::string I = std::to_string(K);
          std::string S = Ref ? "Claws.Sem.Res.loc ⟨p" + I + ", []⟩"
                              : (E->Scalar ? "Claws.Sem.Res.val (" + E->Fn + " a" + I + ")" : "Claws.Sem.Res.val v" + I);
          RunArgsS += (K ? ", " : "") + S;
          ++K;
        }
      }
      RunArgsS += "]";
      Info.Run = "def RunStmt.«" + Name + "» (base : Nat) : Prop :=\n  ∀" + RunBinders + " (m : Claws.Sem.Mem)" +
                 RefBinders + ",\n" + RunHyps + Distinct + "    Claws.Sem.Pre " + Prog + " m " + quote(Name) + " " +
                 RunArgsS + " →\n    ∀ n, base ≤ n → Claws.Sem.callFn n " + Prog + " m " + quote(Name) + " " +
                 RunArgsS + " =\n      some (" + RunRes + ", " + RunMem + ")\n\n";
    }
    Infos.push_back(Info);
  }

  void run(const TranslationUnitDecl *TU) {
    for (const Decl *D : TU->decls()) {
      if (!SM.isInMainFile(SM.getExpansionLoc(D->getLocation()))) {
        continue;
      }
      if (const auto *R = dyn_cast<CXXRecordDecl>(D)) {
        if (R->isThisDeclarationADefinition()) {
          record(R);
        }
      } else if (const auto *E = dyn_cast<EnumDecl>(D)) {
        if (E->isThisDeclarationADefinition()) {
          enumeration(E);
        }
      } else if (const auto *F = dyn_cast<FunctionDecl>(D)) {
        if (F->doesThisDeclarationHaveABody()) {
          function(F);
        }
      } else if (const auto *V = dyn_cast<VarDecl>(D)) {
        global(V);
      }
    }
    // A function that calls one the semantics cannot cover cannot be
    // covered either.
    for (bool Changed = true; Changed;) {
      Changed = false;
      std::set<std::string> Bad;
      for (const Fn &I : Infos) {
        if (!I.Covered) {
          Bad.insert(I.Name);
        }
      }
      for (Fn &I : Infos) {
        for (const std::string &C : I.Callees) {
          if (I.Covered && (Bad.count(C) || !Names.count(C))) {
            I.Covered = false;
            Changed = true;
          }
        }
      }
    }
    for (const Fn &I : Infos) {
      if (I.Covered) {
        Laws += I.Law;
        Runs += I.Run;
      } else {
        Uncovered.push_back(I.Name);
      }
    }
  }

  std::string output(StringRef File) {
    std::string S = "-- Generated by claws-ast from " + File.str() + ". Do not edit.\n";
    S += "-- The program as Claws.Sem sees it, and one validation law per function.\n";
    S += "import Claws.Codec\nimport Claws.SimpAttr\nimport " + Project + ".Code\n\nnamespace " + Project +
         ".Ast\n\nopen Claws.Sem\n\n";
    S += StructDefs + LoopDefs + FuncDefs;
    S += "def prog : Prog := {\n  structs := [";
    for (size_t I = 0; I < Structs.size(); ++I) {
      S += std::string(I ? ", " : "") + "(" + quote(Structs[I]) + ", Struct.«" + Structs[I] + "»)";
    }
    S += "],\n  funcs := [";
    for (size_t I = 0; I < Funcs.size(); ++I) {
      S += std::string(I ? ",\n    " : "") + "(" + quote(Funcs[I]) + ", Fn.«" + Funcs[I] + "»)";
    }
    S += "],\n  globals := [";
    for (size_t I = 0; I < Globals.size(); ++I) {
      S += std::string(I ? ",\n    " : "") + Globals[I];
    }
    S += "] }\n\n";
    // Proof aids for claws_validate, proven here by rfl: they let it find
    // a function or a struct without unfolding the whole program.
    for (const std::string &N : Structs) {
      S += "@[claws_interp] theorem Struct.«" + N + "».found : List.lookup " + quote(N) +
           " prog.structs = some Struct.«" + N + "» := rfl\n";
    }
    for (const std::string &N : Funcs) {
      S += "@[claws_interp] theorem Fn.«" + N + "».found : List.lookup " + quote(N) + " prog.funcs = some Fn.«" + N +
           "» := rfl\n";
    }
    S += "\nattribute [claws_interp]";
    for (const std::string &N : Structs) {
      S += " Struct.«" + N + "»";
    }
    for (const std::string &N : Funcs) {
      S += " Fn.«" + N + "»";
    }
    S += "\n\n" + Encoders + GlobalFound + "\n";
    S += "-- Proof aids: what claws_valid proves of each function, for every fuel\n"
         "-- from `base` up, reading struct and enum arguments from the call.\n" +
         Runs;
    S += "-- The functions this stage of the semantics cannot yet state a law for.\n";
    S += "def uncovered : List String := [";
    for (size_t I = 0; I < Uncovered.size(); ++I) {
      S += (I ? ", " : "") + quote(Uncovered[I]);
    }
    S += "]\n\nend " + Project + ".Ast\n\nnamespace " + Project + ".Laws.Valid\n\n" + Laws + "end " + Project +
         ".Laws.Valid\n";
    return S;
  }

private:
  ASTContext &Ctx;
  SourceManager &SM;
  std::vector<std::string> Structs;
  std::vector<std::string> Funcs;
  std::set<std::string> Names;
  std::vector<std::string> Globals;
  std::set<std::string> GlobalNames;
  std::string GlobalFound;
  std::set<std::string> Encoded;
  std::vector<std::string> Uncovered;
  std::vector<Fn> Infos;
  std::set<std::string> Callees;
  bool Covered = true;
  std::string Library;
  std::string StructDefs;
  std::string LoopDefs;
  std::string FnName;
  int LoopCount = 0;
  std::string FuncDefs;
  std::string Encoders;
  std::string Laws;
  std::string Runs;
};

std::string Result;
bool Failed = false;

class Consumer : public ASTConsumer {
public:
  void HandleTranslationUnit(ASTContext &Ctx) override {
    if (Ctx.getDiagnostics().hasErrorOccurred()) {
      Failed = true;
      return;
    }
    Printer P(Ctx);
    P.run(Ctx.getTranslationUnitDecl());
    const SourceManager &SM = Ctx.getSourceManager();
    Result = P.output(llvm::sys::path::filename(SM.getFileEntryRefForID(SM.getMainFileID())->getName()));
  }
};

class Action : public ASTFrontendAction {
public:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &, StringRef) override {
    return std::make_unique<Consumer>();
  }
};

// The same compiler flags claws-lean and the gate use.
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
    llvm::errs() << "claws-ast: give exactly one source file\n";
    return 2;
  }
  tooling::ClangTool Tool(Parser->getCompilations(), Parser->getSourcePathList());
  Tool.appendArgumentsAdjuster(adjust);
  if (Tool.run(tooling::newFrontendActionFactory<Action>().get()) != 0 || Failed) {
    llvm::errs() << "claws-ast: clang rejected the file\n";
    return 1;
  }
  if (Output.empty()) {
    llvm::outs() << Result;
    return 0;
  }
  std::ofstream File(Output);
  File << Result;
  return File ? 0 : 1;
}
