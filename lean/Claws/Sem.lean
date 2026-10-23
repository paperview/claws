/-!
# The semantics of the claws subset

This file says what a program in the subset means, independently of
claws-lean. It is part of the trusted base, in place of the translator:
review it against the C++ standard (C++20, the version the gate
compiles with), not against claws-lean.

A program is the AST that Clang builds, written as a Lean term by
claws-ast (`Ast.lean` in each project). Clang has already resolved every
implicit conversion, promotion and value category, and the AST shows
each as a node, so the rules below only say what each node does.

`Exec` is a big-step relation. A derivation exists only for a run that
is defined and ends. Undefined behavior has no rule, so the run gets
stuck: reading a variable that holds no value, an `int` result outside
32 bits, dividing by zero, shifting by 32 or more, or falling off the end
of a function that returns a value. So does every node this file does
not cover (`other`), and so does a failed `claws::expects`, which traps:
nothing is claimed about a run that traps. The rules are syntax
directed, so a derivation that ends in `ret v` says the C++ returns v
(`Claws.Det` proves it).

Each variable is named by its declaration's position (`x@16:32`), so
lookups follow C++ scoping, shadowing included.

The objects of a run are a list, by address (`Mem`); a name in scope
names an object (`Env`). A local or a value parameter is a new object at
the end of the list. A `T&` parameter names its argument's object, which
belongs to the caller, so a call can change its caller's objects only
through its references. When a call returns, and when a block ends, the
objects it created end: memory is cut back to its length before. Two
references to one object are one object, as in C++: no rule assumes
references differ.

Expressions have no side effects, except a call through its references,
so evaluating operands in any order gives the only result C++ allows
([intro.execution]/10 leaves most orders unsequenced). A call inside a
larger expression must leave the objects as they were. Assignment,
compound assignment, `++`, `--`, and a call that changes objects have
rules only where nothing else is evaluated with them: as a statement,
an initializer, the right side of an assignment, or a returned value.

This version covers stages A to D of DESIGN.md, "A trusted
translation": `uint32_t`, `uint8_t`, `bool`, `int`, enums and structs;
locals, assignment and compound assignment; `if`, `switch` with `break`,
`?:`, `&&`, `||`; division, remainder and shifts; calls, `T&` and
`const T&` parameters, `return`, `void` functions and `claws::expects`;
`for` and `while` loops with `break` and `continue`; `claws::vec`; and
`claws::list` with recursion.

A `claws::vec` is a value holding its elements (`include/claws/vec.hpp`,
which is trusted to behave as the rules for it here say). Its element
is an object: `v[i]` names it, and indexing out of bounds traps, so it
has no rule.

A `claws::list` is a value holding its elements (`include/claws/list.hpp`,
trusted to behave as these rules say: its nodes are shared and never
change, so no list can observe another). It is built with `list<T>{}` and
`claws::cons`, and taken apart with `xs.match(on_nil, on_cons)`, whose
two arguments are lambdas. The program lists each lambda as a function,
named by its position (`lambda@27:7`), which no C++ call can name. Its
body runs in the scope it is written in, so it sees the names the
enclosing function sees: a variable captured by reference is the same
object ([expr.prim.lambda.capture]/12), and one captured by copy holds
the same value, since a lambda must leave the objects as they were, as a
call inside an expression must.

A `constexpr` variable at namespace scope is a constant: the program
lists the value Clang computes for it, an array as a `vec` of its
elements. An lvalue naming one, or a part of one, is `Res.glob`; it can
be read, never written. Indexing an array out of bounds is undefined
([expr.add]/4.3), so it has no rule.
-/

namespace Claws.Sem

/-! ## Values and types -/

/-- A type, after Clang has removed typedefs and qualifiers. -/
inductive Ty where
  | bool
  /-- `unsigned int`, which is `uint32_t` on every target claws supports. -/
  | uint
  /-- `unsigned char`, which is `uint8_t`. -/
  | uchar
  /-- `int`, 32 bits. -/
  | int
  /-- An enumeration, by name; claws has only `enum class` with the
  underlying type `int`. -/
  | enum (name : String)
  | record (name : String)
  /-- `T&` or `const T&`, as the type of a parameter. -/
  | ref (t : Ty)
  /-- `claws::vec<T>` -/
  | vec (t : Ty)
  /-- `claws::list<T>` -/
  | list (t : Ty)
  | void
  | other (what : String)
  deriving Repr, Inhabited

inductive Val where
  | bool (b : Bool)
  | uint (v : BitVec 32)
  | uchar (v : BitVec 8)
  /-- An `int`, as the mathematical integer it stands for. -/
  | int (v : Int)
  /-- A value of an enumeration: its type and its underlying value. -/
  | enum (name : String) (v : Int)
  | record (fields : List (String × Val))
  /-- A `claws::vec`, by its elements. -/
  | vec (elems : List Val)
  /-- A `claws::list`, by its elements. -/
  | list (elems : List Val)
  deriving Repr, Inhabited

/-! ## Syntax -/

/-- An implicit or explicit conversion, named as Clang names its cast kinds. -/
inductive CastKind where
  /-- Read the object an lvalue names ([conv.lval]). -/
  | lvalueToRValue
  /-- Between integer types and from bool ([conv.integral], [conv.prom]). -/
  | integralCast
  /-- An integer to bool ([conv.bool]). -/
  | integralToBoolean
  /-- A change of type that leaves the value alone, such as adding `const`. -/
  | noOp
  | other (what : String)
  deriving Repr, Inhabited

inductive UnOp where
  /-- `!` -/
  | lnot
  /-- `~` -/
  | not
  /-- unary `-` -/
  | minus
  /-- unary `+` -/
  | plus
  | other (what : String)
  deriving Repr, Inhabited

/-- A binary operator other than `&&` and `||`, which are `Expr.land` and
`Expr.lor` because they do not always evaluate their right operand. -/
inductive BinOp where
  | add | sub | mul | div | rem | shl | shr | and | or | xor
  | lt | gt | le | ge | eq | ne
  | other (what : String)
  deriving Repr, Inhabited

/-- A function of the claws library (`include/claws`). -/
inductive Builtin where
  /-- `claws::expects` -/
  | expects
  /-- `claws::decreases` -/
  | decreases
  /-- `v.size()` of a `claws::vec`, with `v` as the argument. -/
  | size
  /-- `v[i]` of a `claws::vec`, with arguments `v` and `i`. -/
  | index
  /-- `v.push(x)` of a `claws::vec`, with arguments `v` and `x`. -/
  | push
  /-- `vec<T>{}`, the empty vec. -/
  | vecEmpty
  /-- `vec<T>(n, x)`, n copies of x, with arguments `n` and `x`. -/
  | vecFill
  /-- `list<T>{}`, the empty list. -/
  | listNil
  /-- `claws::cons(h, t)`, with arguments `h` and `t`. -/
  | cons
  | other (name : String)
  deriving Repr, Inhabited

inductive Expr where
  /-- `IntegerLiteral`, of type `unsigned int` or `int`. -/
  | intLit (ty : Ty) (n : Nat)
  /-- `CXXBoolLiteralExpr` -/
  | boolLit (b : Bool)
  /-- `DeclRefExpr` naming an enumerator, with its type and value. -/
  | enumLit (name : String) (v : Int)
  /-- `DeclRefExpr` naming a variable or parameter: an lvalue. -/
  | var (x : String)
  /-- `MemberExpr`, `e.f` -/
  | member (e : Expr) (f : String)
  /-- `ImplicitCastExpr` and the explicit casts, to type `ty`. -/
  | cast (k : CastKind) (ty : Ty) (e : Expr)
  | unary (op : UnOp) (e : Expr)
  | binary (op : BinOp) (a b : Expr)
  | land (a b : Expr)
  | lor (a b : Expr)
  /-- `ConditionalOperator`, `c ? a : b` -/
  | cond (c a b : Expr)
  /-- `CallExpr` of a function of the program, named directly. -/
  | call (f : String) (args : List Expr)
  /-- `CallExpr` of a function of the claws library (`include/claws`),
  which has a rule of its own here instead of a body. -/
  | builtin (f : Builtin) (args : List Expr)
  /-- `DeclRefExpr` naming a constant of the program: an lvalue. -/
  | global (x : String)
  /-- `ArraySubscriptExpr` on an array, `a[i]` ([expr.sub]): the element
  of the array a names, not of a pointer to it. -/
  | subscript (a i : Expr)
  /-- `CXXConstructExpr` that runs a trivial copy or move constructor. -/
  | copy (e : Expr)
  /-- `InitListExpr` of a struct, one expression per field in order. -/
  | initList (ty : Ty) (es : List Expr)
  | paren (e : Expr)
  /-- `xs.match(on_nil, on_cons)` on a `claws::list`, with each lambda
  named as the program lists it. -/
  | listMatch (xs : Expr) (onNil onCons : String)
  /-- `a = b` -/
  | assign (a b : Expr)
  /-- `a op= b` (`CompoundAssignOperator`): `a` has type `ty`, and the
  operation runs at type `comp`, Clang's `ComputeLHSTy`. -/
  | compound (op : BinOp) (ty comp : Ty) (a b : Expr)
  /-- `++a`, `a++`, `--a`, `a--` -/
  | incdec (inc post : Bool) (a : Expr)
  | other (what : String)
  deriving Repr, Inhabited

inductive Stmt where
  /-- A `DeclStmt` declaring one variable with an initializer. -/
  | decl (x : String) (ty : Ty) (init : Expr)
  /-- An expression statement. -/
  | expr (e : Expr)
  | ret (e : Expr)
  /-- `return;` -/
  | retVoid
  /-- `IfStmt`; a missing `else` is `block []`. -/
  | ite (c : Expr) (t f : Stmt)
  /-- `CompoundStmt` -/
  | block (ss : List Stmt)
  /-- `SwitchStmt`. Its body is the statements of the braces in order,
  with each `case` and `default` label as a statement of its own where
  it stands. -/
  | switch (c : Expr) (body : List Stmt)
  /-- `case v:`, with the value Clang computed for the label, converted
  to the type of the condition ([stmt.switch]/2). -/
  | caseLabel (v : Val)
  | defaultLabel
  | brk
  /-- `while (c) body` is `loop c body (block [])`; `for (init; c; inc)
  body` is `block [init, loop c body (expr inc)]` ([stmt.for]/1): after
  the body, and after a `continue`, `step` runs before c is tested
  again. -/
  | loop (c : Expr) (body : Stmt) (step : Stmt)
  | cont
  | other (what : String)
  deriving Repr, Inhabited

structure Func where
  params : List (String × Ty)
  ret : Ty
  body : Stmt
  deriving Repr, Inhabited

structure Prog where
  /-- Each struct's fields, in declaration order. -/
  structs : List (String × List (String × Ty))
  funcs : List (String × Func)
  /-- Each constant's value, as Clang computes its initializer. -/
  globals : List (String × Val) := []
  deriving Repr, Inhabited

/-- The objects of a run, by address. A variable is an object; a
reference parameter names an object of its caller ([dcl.ref]). -/
abbrev Mem := List Val

/-- One step into an object: a field of a struct, or an element of a
vec. -/
inductive Step where
  | field (f : String)
  | index (i : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- An object an lvalue names: an object by address, then a path of
steps into it. -/
structure Loc where
  addr : Nat
  path : List Step
  deriving Repr, Inhabited, DecidableEq

/-- The names in scope, innermost first, and the objects they name. -/
abbrev Env := List (String × Loc)

/-- What an expression evaluates to: a value (a prvalue) or the object
an lvalue names. -/
inductive Res where
  | val (v : Val)
  | loc (l : Loc)
  /-- A constant of the program, or a part of one: its name, then a path
  of steps into it. -/
  | glob (x : String) (path : List Step)
  deriving Repr, Inhabited

/-- How a statement finishes: normally or at a `break`, with the names
in scope and the objects, or by returning, with a value unless the
function returns `void`. -/
inductive Outcome where
  | normal (e : Env) (m : Mem)
  | brk (e : Env) (m : Mem)
  | cont (e : Env) (m : Mem)
  | ret (v : Option Val) (m : Mem)
  deriving Repr, Inhabited

/-! ## Objects -/

def Val.field : Val → String → Option Val
  | .record fs, f => List.lookup f fs
  | _, _ => none

def Val.elem : Val → Nat → Option Val
  | .vec xs, i => xs[i]?
  | _, _ => none

def Val.at (v : Val) : List Step → Option Val
  | [] => some v
  | .field f :: fs => (v.field f).bind (·.at fs)
  | .index i :: fs => (v.elem i).bind (·.at fs)

def Mem.read (m : Mem) (l : Loc) : Option Val :=
  m[l.addr]?.bind (·.at l.path)

/-- Replace the first entry for key `k`. -/
def setFirst (k : String) (w : Val) : List (String × Val) → Option (List (String × Val))
  | [] => none
  | (k', v) :: rest => if (k == k') = true then some ((k', w) :: rest) else (setFirst k w rest).map ((k', v) :: ·)

/-- `v` with the object at `path` replaced by `w`. -/
def Val.set (v : Val) : List Step → Val → Option Val
  | [], w => some w
  | .field f :: fs, w =>
    match v with
    | .record flds =>
      match List.lookup f flds with
      | some x => (x.set fs w).bind fun x' => (setFirst f x' flds).map .record
      | none => none
    | _ => none
  | .index i :: fs, w =>
    match v with
    | .vec xs =>
      match xs[i]? with
      | some x => (x.set fs w).map fun x' => .vec (xs.set i x')
      | none => none
    | _ => none

/-- The value of the part `p` of the constant `x`. -/
def globRead (P : Prog) (x : String) (p : List Step) : Option Val :=
  (List.lookup x P.globals).bind (·.at p)

/-- The value of an argument bound to a `const T&` parameter of the
claws library: the value itself, or the value of the object it names. -/
def Mem.value (P : Prog) (m : Mem) : Res → Option Val
  | .val v => some v
  | .loc l => m.read l
  | .glob x p => globRead P x p

/-- An array index ([expr.sub]): a value of any integer type, which is
not promoted, that is not negative. -/
def Val.index : Val → Option Nat
  | .uint k => some k.toNat
  | .uchar k => some k.toNat
  | .int k => if 0 ≤ k then some k.toNat else none
  | _ => none

/-- The objects after writing `w` to the object `l` names ([expr.ass]). -/
def Mem.write (m : Mem) (l : Loc) (w : Val) : Option Mem :=
  match m[l.addr]? with
  | some v => (v.set l.path w).map (m.set l.addr ·)
  | none => none

/-! ## Operations

Each says what the standard says the operation computes, or `none`
where it is undefined. -/

/-- An `int` result: undefined outside 32 bits ([expr.pre]/4). -/
def inInt (n : Int) : Option Val :=
  if -2 ^ 31 ≤ n ∧ n < 2 ^ 31 then some (.int n) else none

/-- A conversion to type `t` ([conv.integral]). Since C++20 a value
converts to an integer type as the unique value congruent to it modulo
2^N, N the width of the type. -/
def convert : Ty → Val → Option Val
  | .uint, .uint v => some (.uint v)
  | .uint, .uchar v => some (.uint (v.setWidth 32))
  | .uint, .int n => some (.uint (BitVec.ofInt 32 n))
  | .uint, .bool b => some (.uint (if b then 1 else 0))
  | .uchar, .uchar v => some (.uchar v)
  | .uchar, .uint v => some (.uchar (v.setWidth 8))
  | .uchar, .int n => some (.uchar (BitVec.ofInt 8 n))
  | .uchar, .bool b => some (.uchar (if b then 1 else 0))
  | .int, .int n => some (.int n)
  | .int, .uint v => some (.int v.toInt)
  | .int, .uchar v => some (.int v.toNat)
  | .int, .bool b => some (.int (if b then 1 else 0))
  | _, _ => none

/-- A conversion to bool ([conv.bool]). -/
def truth : Val → Option Bool
  | .uint v => some (v != 0)
  | .uchar v => some (v != 0)
  | .int n => some (n != 0)
  | _ => none

/-- Unsigned arithmetic is modulo 2^32 ([basic.fundamental]/2), which is
what Lean's `BitVec 32` operations compute. -/
def unop : UnOp → Val → Option Val
  | .lnot, .bool b => some (.bool !b)
  | .not, .uint a => some (.uint (~~~a))
  | .not, .int n => some (.int (~~~(BitVec.ofInt 32 n)).toInt)
  | .minus, .uint a => some (.uint (-a))
  | .minus, .int n => inInt (-n)
  | .plus, .uint a => some (.uint a)
  | .plus, .int n => some (.int n)
  | _, _ => none

/-- A shift amount: undefined unless it is below 32, the width of the
promoted left operand ([expr.shift]/1). -/
def amount : Val → Option Nat
  | .uint k => if k.toNat < 32 then some k.toNat else none
  | .int k => if 0 ≤ k ∧ k < 32 then some k.toNat else none
  | _ => none

/-- An `int` operation on the two's complement bits, which C++20 fixes
as the representation ([basic.fundamental]/3). -/
def bitsInt (f : BitVec 32 → BitVec 32 → BitVec 32) (a b : Int) : Val :=
  .int (f (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)).toInt

/-- Except for shifts, both operands have the same type: Clang has
already applied the usual arithmetic conversions ([expr.arith.conv]).
A shift's operands are promoted separately and the result has the left
operand's type ([expr.shift]/1).

Unsigned arithmetic is modulo 2^32 ([basic.fundamental]/2), which is
what `BitVec 32` computes: `+`, `-` and `*` modulo 2^32, `/` and `%` on
the numbers, `<<<` as a * 2^k modulo 2^32 and `>>>` as a / 2^k rounded
down ([expr.shift]/2, /3), and `<` comparing the numbers. Division by
zero is undefined ([expr.mul]/4). `int` arithmetic is on the
mathematical integers, undefined outside 32 bits. -/
def binop : BinOp → Val → Val → Option Val
  | .add, .uint a, .uint b => some (.uint (a + b))
  | .sub, .uint a, .uint b => some (.uint (a - b))
  | .mul, .uint a, .uint b => some (.uint (a * b))
  | .div, .uint a, .uint b => if b = 0 then none else some (.uint (a / b))
  | .rem, .uint a, .uint b => if b = 0 then none else some (.uint (a % b))
  | .shl, .uint a, k => (amount k).map fun k => .uint (a <<< k)
  | .shr, .uint a, k => (amount k).map fun k => .uint (a >>> k)
  | .and, .uint a, .uint b => some (.uint (a &&& b))
  | .or, .uint a, .uint b => some (.uint (a ||| b))
  | .xor, .uint a, .uint b => some (.uint (a ^^^ b))
  | .lt, .uint a, .uint b => some (.bool (decide (a < b)))
  | .gt, .uint a, .uint b => some (.bool (decide (b < a)))
  | .le, .uint a, .uint b => some (.bool (decide (a ≤ b)))
  | .ge, .uint a, .uint b => some (.bool (decide (b ≤ a)))
  | .eq, .uint a, .uint b => some (.bool (decide (a = b)))
  | .ne, .uint a, .uint b => some (.bool (decide (a ≠ b)))
  | .add, .int a, .int b => inInt (a + b)
  | .sub, .int a, .int b => inInt (a - b)
  | .mul, .int a, .int b => inInt (a * b)
  /- `int` division truncates toward zero, and is undefined when the
  quotient does not fit ([expr.mul]/4). -/
  | .div, .int a, .int b => if b = 0 then none else inInt (a.tdiv b)
  | .rem, .int a, .int b => if b = 0 then none else (inInt (a.tdiv b)).bind fun _ => some (.int (a.tmod b))
  /- Since C++20, `a << k` on `int` is a * 2^k modulo 2^32, and `a >> k`
  is a / 2^k rounded down ([expr.shift]/2, /3). -/
  | .shl, .int a, k => (amount k).map fun k => .int (BitVec.ofInt 32 (a * 2 ^ k)).toInt
  | .shr, .int a, k => (amount k).map fun k => .int (a.fdiv (2 ^ k))
  | .and, .int a, .int b => some (bitsInt (· &&& ·) a b)
  | .or, .int a, .int b => some (bitsInt (· ||| ·) a b)
  | .xor, .int a, .int b => some (bitsInt (· ^^^ ·) a b)
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .gt, .int a, .int b => some (.bool (decide (b < a)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .ge, .int a, .int b => some (.bool (decide (b ≤ a)))
  | .eq, .int a, .int b => some (.bool (decide (a = b)))
  | .ne, .int a, .int b => some (.bool (decide (a ≠ b)))
  /- Two values of one enumeration compare by their underlying values
  ([expr.rel]/6, [expr.eq]/6). -/
  | .eq, .enum t a, .enum u b => if t = u then some (.bool (decide (a = b))) else none
  | .ne, .enum t a, .enum u b => if t = u then some (.bool (decide (a ≠ b))) else none
  | _, _, _ => none

/-- The type of a scalar value. -/
def Val.ty : Val → Ty
  | .bool _ => .bool
  | .uint _ => .uint
  | .uchar _ => .uchar
  | .int _ => .int
  | .enum n _ => .enum n
  | .record _ => .other "struct"
  | .vec _ => .other "vec"
  | .list _ => .other "list"

/-- The integral promotion of a value ([conv.prom]): `unsigned char` and
`bool` become `int`. -/
def promote : Val → Val
  | .uchar v => .int v.toNat
  | .bool b => .int (if b then 1 else 0)
  | v => v

/-- `++a` is `a += 1` ([expr.pre.incr]), and `1` takes the type of the
promoted `a` by the usual arithmetic conversions. -/
def one : Val → Val
  | .uint _ => .uint 1
  | _ => .int 1

/-- Two case values are the same value. -/
def Val.same : Val → Val → Bool
  | .bool a, .bool b => a == b
  | .uint a, .uint b => a == b
  | .uchar a, .uchar b => a == b
  | .int a, .int b => a == b
  | .enum t a, .enum u b => t == u && a == b
  | _, _ => false

/-- The position of the label a `switch` on `v` jumps to: the case with
value `v`, else `default` ([stmt.switch]/5). -/
def caseAt (v : Val) : List Stmt → Nat → Option Nat
  | [], _ => none
  | .caseLabel w :: rest, i => if Val.same w v then some i else caseAt v rest (i + 1)
  | _ :: rest, i => caseAt v rest (i + 1)

def defaultAt : List Stmt → Nat → Option Nat
  | [], _ => none
  | .defaultLabel :: _, i => some i
  | _ :: rest, i => defaultAt rest (i + 1)

def pick (v : Val) (body : List Stmt) : Option Nat :=
  match caseAt v body 0 with
  | some i => some i
  | none => defaultAt body 0

/-- The names a call starts with, and the objects. A reference parameter
names the object its argument names; any other parameter is a new
object holding its argument's value ([expr.call]/7). -/
def bindParams : List (String × Ty) → List Res → Env → Mem → Option (Env × Mem)
  | [], [], e, m => some (e, m)
  | (x, .ref _) :: ps, .loc l :: rs, e, m => bindParams ps rs ((x, l) :: e) m
  | (_, .ref _) :: _, .val _ :: _, _, _ => none
  | (x, _) :: ps, .val v :: rs, e, m => bindParams ps rs ((x, ⟨m.length, []⟩) :: e) (m ++ [v])
  | _, _, _, _ => none

/-- What a call returns, and the caller's objects after it: the callee's
own objects end with it, so only the first `n`, the caller's, remain. A
function returning a value must return one ([stmt.return]/4); a `void`
function may also reach the end of its body. -/
def finish (rt : Ty) (n : Nat) : Outcome → Option (Option Val × Mem)
  | .ret (some v) m => match rt with
    | .void => none
    | _ => some (some v, m.take n)
  | .ret none m => match rt with
    | .void => some (none, m.take n)
    | _ => none
  | .normal _ m => match rt with
    | .void => some (none, m.take n)
    | _ => none
  | .brk _ _ => none
  | .cont _ _ => none

/-- A literal's value must fit its type ([lex.icon]; Clang picks a type
it fits). -/
def literal : Ty → Nat → Option Val
  | .uint, n => if n < 2 ^ 32 then some (.uint (BitVec.ofNat 32 n)) else none
  | .int, n => if n < 2 ^ 31 then some (.int n) else none
  | _, _ => none

/-- A struct value from its fields' values ([dcl.init.aggr]). -/
def aggregate (P : Prog) : Ty → List Val → Option Val
  | .record n, vs =>
    match List.lookup n P.structs with
    | some fs => if fs.length = vs.length then some (.record ((fs.map Prod.fst).zip vs)) else none
    | none => none
  | _, _ => none

/-- The names and objects at the end of a block: names declared in it
go out of scope, and objects created in it end ([basic.stc.auto]). -/
def close (e' e : Env) : Env := e'.drop (e'.length - e.length)

/-! ## The semantics

`Eval` has no effect on the objects. A call can change its caller's
objects through reference parameters, so a call with an effect has
rules only where nothing else is evaluated with it: as a statement, an
initializer, the right side of an assignment, or a returned value
(`EvalTop`). -/

mutual

inductive Eval (P : Prog) : Env → Mem → Expr → Res → Prop where
  | lit : literal t n = some v → Eval P e m (.intLit t n) (.val v)
  | boolLit : Eval P e m (.boolLit b) (.val (.bool b))
  | enumLit : Eval P e m (.enumLit n v) (.val (.enum n v))
  | var : List.lookup x e = some l → Eval P e m (.var x) (.loc l)
  /-- A member of an lvalue is an lvalue ([expr.ref]/6.2). -/
  | memberLoc : Eval P e m a (.loc l) → Eval P e m (.member a f) (.loc ⟨l.addr, l.path ++ [.field f]⟩)
  | memberVal : Eval P e m a (.val v) → v.field f = some w → Eval P e m (.member a f) (.val w)
  | memberGlob : Eval P e m a (.glob x p) → Eval P e m (.member a f) (.glob x (p ++ [.field f]))
  | global : List.lookup x P.globals = some v → Eval P e m (.global x) (.glob x [])
  /-- Element i of a constant array; out of bounds it is undefined. -/
  | subscript : Eval P e m a (.glob x p) → Eval P e m i (.val k) → k.index = some n →
      globRead P x p = some (.vec xs) → n < xs.length →
      Eval P e m (.subscript a i) (.glob x (p ++ [.index n]))
  /-- Reading an object that holds no value is undefined: no rule. -/
  | load : Eval P e m a (.loc l) → m.read l = some v →
      Eval P e m (.cast .lvalueToRValue t a) (.val v)
  | loadGlob : Eval P e m a (.glob x p) → globRead P x p = some v →
      Eval P e m (.cast .lvalueToRValue t a) (.val v)
  | integral : Eval P e m a (.val v) → convert t v = some w →
      Eval P e m (.cast .integralCast t a) (.val w)
  | toBool : Eval P e m a (.val v) → truth v = some b →
      Eval P e m (.cast .integralToBoolean t a) (.val (.bool b))
  | noOp : Eval P e m a r → Eval P e m (.cast .noOp t a) r
  | unary : Eval P e m a (.val v) → unop op v = some w → Eval P e m (.unary op a) (.val w)
  | binary : Eval P e m a (.val va) → Eval P e m b (.val vb) → binop op va vb = some v →
      Eval P e m (.binary op a b) (.val v)
  /-- `&&` evaluates its right operand only when the left is true ([expr.log.and]). -/
  | landF : Eval P e m a (.val (.bool false)) → Eval P e m (.land a b) (.val (.bool false))
  | landT : Eval P e m a (.val (.bool true)) → Eval P e m b (.val (.bool v)) →
      Eval P e m (.land a b) (.val (.bool v))
  | lorT : Eval P e m a (.val (.bool true)) → Eval P e m (.lor a b) (.val (.bool true))
  | lorF : Eval P e m a (.val (.bool false)) → Eval P e m b (.val (.bool v)) →
      Eval P e m (.lor a b) (.val (.bool v))
  /-- `?:` evaluates one arm, and is an lvalue when both arms are ([expr.cond]). -/
  | condT : Eval P e m c (.val (.bool true)) → Eval P e m a r → Eval P e m (.cond c a b) r
  | condF : Eval P e m c (.val (.bool false)) → Eval P e m b r → Eval P e m (.cond c a b) r
  /-- A call inside a larger expression must leave the objects as they
  were. -/
  | call : EvalArgs P e m args rs → Call P m f rs (some v) m → Eval P e m (.call f args) (.val v)
  | copy : Eval P e m a (.loc l) → m.read l = some v → Eval P e m (.copy a) (.val v)
  | copyVal : Eval P e m a (.val v) → Eval P e m (.copy a) (.val v)
  | copyGlob : Eval P e m a (.glob x p) → globRead P x p = some v → Eval P e m (.copy a) (.val v)
  | initList : EvalList P e m es vs → aggregate P t vs = some v → Eval P e m (.initList t es) (.val v)
  | paren : Eval P e m a r → Eval P e m (.paren a) r
  /-- A vec's size fits a `uint32_t`, since `push` traps before it
  would not. -/
  | size : Eval P e m a (.loc l) → m.read l = some (.vec xs) →
      Eval P e m (.builtin .size [a]) (.val (.uint (BitVec.ofNat 32 xs.length)))
  /-- `v[i]` names element i; out of bounds it traps, so it has no rule. -/
  | index : Eval P e m a (.loc l) → Eval P e m i (.val (.uint k)) → m.read l = some (.vec xs) →
      k.toNat < xs.length → Eval P e m (.builtin .index [a, i]) (.loc ⟨l.addr, l.path ++ [.index k.toNat]⟩)
  | vecEmpty : Eval P e m (.builtin .vecEmpty []) (.val (.vec []))
  | vecFill : Eval P e m a (.val (.uint k)) → Eval P e m x r → m.value P r = some w →
      Eval P e m (.builtin .vecFill [a, x]) (.val (.vec (List.replicate k.toNat w)))
  | listNil : Eval P e m (.builtin .listNil []) (.val (.list []))
  /-- `cons(h, t)` is a list of h's value, then t's elements. -/
  | cons : Eval P e m a ra → m.value P ra = some w → Eval P e m b rb → m.value P rb = some (.list ws) →
      Eval P e m (.builtin .cons [a, b]) (.val (.list (w :: ws)))
  /-- `xs.match(on_nil, on_cons)` returns what `on_nil()` returns when xs
  is empty, and otherwise what `on_cons(head, tail)` does, each
  parameter a new object ([expr.call]/7), as a call's are; the lambda's
  own objects end when it returns. -/
  | matchNil : Eval P e m xs r → m.value P r = some (.list []) →
      List.lookup onNil P.funcs = some fn → bindParams fn.params [] e m = some (e₀, m₀) →
      Exec P e₀ m₀ fn.body o → finish fn.ret m.length o = some (some v, m) →
      Eval P e m (.listMatch xs onNil onCons) (.val v)
  | matchCons : Eval P e m xs r → m.value P r = some (.list (w :: ws)) →
      List.lookup onCons P.funcs = some fn →
      bindParams fn.params [.val w, .val (.list ws)] e m = some (e₀, m₀) →
      Exec P e₀ m₀ fn.body o → finish fn.ret m.length o = some (some v, m) →
      Eval P e m (.listMatch xs onNil onCons) (.val v)

inductive EvalList (P : Prog) : Env → Mem → List Expr → List Val → Prop where
  | nil : EvalList P e m [] []
  | cons : Eval P e m a (.val v) → EvalList P e m as vs → EvalList P e m (a :: as) (v :: vs)

/-- Arguments: values, or the objects a reference parameter will name. -/
inductive EvalArgs (P : Prog) : Env → Mem → List Expr → List Res → Prop where
  | nil : EvalArgs P e m [] []
  | cons : Eval P e m a r → EvalArgs P e m as rs → EvalArgs P e m (a :: as) (r :: rs)

/-- An expression in a place where a call may change the objects. -/
inductive EvalTop (P : Prog) : Env → Mem → Expr → Res → Mem → Prop where
  | pure : Eval P e m a r → EvalTop P e m a r m
  | call : EvalArgs P e m args rs → Call P m f rs (some v) m' →
      EvalTop P e m (.call f args) (.val v) m'

/-- Calling `f` on arguments `rs`, with the caller's objects `m`, returns
`res` (none for `void`) and leaves the objects `m'`. -/
inductive Call (P : Prog) : Mem → String → List Res → Option Val → Mem → Prop where
  | mk : List.lookup f P.funcs = some fn → bindParams fn.params rs [] m = some (e₀, m₀) →
      Exec P e₀ m₀ fn.body o → finish fn.ret m.length o = some (res, m') → Call P m f rs res m'

inductive Exec (P : Prog) : Env → Mem → Stmt → Outcome → Prop where
  | decl : EvalTop P e m a (.val v) m' →
      Exec P e m (.decl x t a) (.normal ((x, ⟨m'.length, []⟩) :: e) (m' ++ [v]))
  | expr : Eval P e m a r → Exec P e m (.expr a) (.normal e m)
  /-- A call as a statement, which may change the objects; its value, if
  any, is discarded. -/
  | exprCall : EvalArgs P e m args rs → Call P m f rs res m' →
      Exec P e m (.expr (.call f args)) (.normal e m')
  /-- `a = b` stores the value of b in the object a names ([expr.ass]/2);
  b is evaluated first ([expr.ass]/1). -/
  | assign : EvalTop P e m b (.val v) m₁ → Eval P e m₁ a (.loc l) → m₁.write l v = some m' →
      Exec P e m (.expr (.assign a b)) (.normal e m')
  /-- `a op= b` is `a = a op b`, with a evaluated once ([expr.ass]/6): a's
  value is converted to the computation type, combined with b, and
  converted back to a's type. -/
  | compound : Eval P e m b (.val vb) → Eval P e m a (.loc l) → m.read l = some va →
      convert comp va = some va' → binop op va' vb = some r → convert t r = some w →
      m.write l w = some m' → Exec P e m (.expr (.compound op t comp a b)) (.normal e m')
  /-- `++a` is `a += 1` and `--a` is `a -= 1` ([expr.pre.incr]); as a
  statement, `a++` does the same. -/
  | incdec : Eval P e m a (.loc l) → m.read l = some v →
      binop (if inc then .add else .sub) (promote v) (one (promote v)) = some r →
      convert v.ty r = some w → m.write l w = some m' →
      Exec P e m (.expr (.incdec inc post a)) (.normal e m')
  /-- `claws::expects(c)` does nothing when c holds; otherwise it traps
  (`include/claws/expects.hpp`), and a run that traps has no rule. -/
  | expects : Eval P e m c (.val (.bool true)) →
      Exec P e m (.expr (.builtin .expects [c])) (.normal e m)
  /-- `claws::decreases(a)` names a loop's measure for the proofs and does
  nothing (`include/claws/decreases.hpp`). -/
  | decreases : Eval P e m a (.val v) →
      Exec P e m (.expr (.builtin .decreases [a])) (.normal e m)
  /-- `v.push(x)` appends the value of x, read before v changes; it traps
  rather than let the size reach 2^32 - 1 (`include/claws/vec.hpp`). -/
  | push : Eval P e m a (.loc l) → Eval P e m x r → m.value P r = some w →
      m.read l = some (.vec xs) → xs.length < 2 ^ 32 - 1 → m.write l (.vec (xs ++ [w])) = some m' →
      Exec P e m (.expr (.builtin .push [a, x])) (.normal e m')
  | ret : EvalTop P e m a (.val v) m' → Exec P e m (.ret a) (.ret (some v) m')
  | retVoid : Exec P e m .retVoid (.ret none m)
  | iteT : Eval P e m c (.val (.bool true)) → Exec P e m t o → Exec P e m (.ite c t f) o
  | iteF : Eval P e m c (.val (.bool false)) → Exec P e m f o → Exec P e m (.ite c t f) o
  /-- Names declared in a block go out of scope at its end, and the
  objects they name end, however the block is left ([stmt.jump]/2). -/
  | blockNormal : ExecList P e m ss (.normal e' m') →
      Exec P e m (.block ss) (.normal (close e' e) (m'.take m.length))
  | blockBrk : ExecList P e m ss (.brk e' m') →
      Exec P e m (.block ss) (.brk (close e' e) (m'.take m.length))
  | blockCont : ExecList P e m ss (.cont e' m') →
      Exec P e m (.block ss) (.cont (close e' e) (m'.take m.length))
  | blockRet : ExecList P e m ss (.ret v m') → Exec P e m (.block ss) (.ret v (m'.take m.length))
  /-- A `switch` jumps to the label for its value and runs from there,
  through later labels, until the end or a `break` ([stmt.switch]/5,
  [stmt.break]). -/
  | switchNormal : Eval P e m c (.val v) → pick v body = some i →
      ExecList P e m (body.drop i) (.normal e' m') →
      Exec P e m (.switch c body) (.normal (close e' e) (m'.take m.length))
  | switchBrk : Eval P e m c (.val v) → pick v body = some i →
      ExecList P e m (body.drop i) (.brk e' m') →
      Exec P e m (.switch c body) (.normal (close e' e) (m'.take m.length))
  | switchRet : Eval P e m c (.val v) → pick v body = some i →
      ExecList P e m (body.drop i) (.ret w m') → Exec P e m (.switch c body) (.ret w (m'.take m.length))
  /-- A `continue` inside a `switch` belongs to the loop around it. -/
  | switchCont : Eval P e m c (.val v) → pick v body = some i →
      ExecList P e m (body.drop i) (.cont e' m') →
      Exec P e m (.switch c body) (.cont (close e' e) (m'.take m.length))
  /-- With no matching label and no `default`, nothing runs. -/
  | switchNone : Eval P e m c (.val v) → pick v body = none → Exec P e m (.switch c body) (.normal e m)
  | caseLabel : Exec P e m (.caseLabel v) (.normal e m)
  | defaultLabel : Exec P e m .defaultLabel (.normal e m)
  | brk : Exec P e m .brk (.brk e m)
  | cont : Exec P e m .cont (.cont e m)
  /-- A loop runs its body while its condition holds ([stmt.while]): a
  `break` ends it, a `continue` ends one pass of the body. -/
  | loopF : Eval P e m c (.val (.bool false)) → Exec P e m (.loop c body step) (.normal e m)
  | loopNext : Eval P e m c (.val (.bool true)) → Exec P e m body (.normal e₁ m₁) →
      Exec P e₁ m₁ step (.normal e₂ m₂) → Exec P e₂ m₂ (.loop c body step) o →
      Exec P e m (.loop c body step) o
  | loopCont : Eval P e m c (.val (.bool true)) → Exec P e m body (.cont e₁ m₁) →
      Exec P e₁ m₁ step (.normal e₂ m₂) → Exec P e₂ m₂ (.loop c body step) o →
      Exec P e m (.loop c body step) o
  | loopBrk : Eval P e m c (.val (.bool true)) → Exec P e m body (.brk e₁ m₁) →
      Exec P e m (.loop c body step) (.normal e₁ m₁)
  | loopRet : Eval P e m c (.val (.bool true)) → Exec P e m body (.ret v m₁) →
      Exec P e m (.loop c body step) (.ret v m₁)

inductive ExecList (P : Prog) : Env → Mem → List Stmt → Outcome → Prop where
  | nil : ExecList P e m [] (.normal e m)
  | next : Exec P e m st (.normal e' m') → ExecList P e' m' ss o → ExecList P e m (st :: ss) o
  | brk : Exec P e m st (.brk e' m') → ExecList P e m (st :: ss) (.brk e' m')
  | cont : Exec P e m st (.cont e' m') → ExecList P e m (st :: ss) (.cont e' m')
  | ret : Exec P e m st (.ret v m') → ExecList P e m (st :: ss) (.ret v m')

end

/-- The `claws::expects` statements a body starts with. -/
def leading : List Stmt → List Expr
  | .expr (.builtin .expects [c]) :: rest => c :: leading rest
  | _ => []

/-- `f`'s precondition: the conditions of the `claws::expects` statements
its body starts with all hold, for the arguments `rs` and the caller's
objects `m`. -/
def Pre (P : Prog) (m : Mem) (f : String) (rs : List Res) : Prop :=
  match List.lookup f P.funcs with
  | some fn =>
    match bindParams fn.params rs [] m, fn.body with
    | some (e₀, m₀), .block ss => ∀ c ∈ leading ss, Eval P e₀ m₀ c (.val (.bool true))
    | _, _ => True
  | none => True

end Claws.Sem
