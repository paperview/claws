import Claws.Interp
import Claws.Det
import Claws.Codec
import Claws.SimpAttr
import Std.Tactic.BVDecide

/-!
# `claws_valid`

Proves a validation law, `Laws.Valid.f`: for all arguments and objects,
the C++ function returns what `Code.f` computes and leaves its `T&`
arguments as `Code.f` does. The tactic runs the interpreter symbolically
on the function's AST with `simp`, unfolds `Code.f` the same way, and
whenever both sides are stuck on a condition, splits on it and
continues in each case. It closes each case with `simp`, then
`bv_omega` or `bv_decide`, which reports a counterexample if the
translation is wrong.

Nothing here is trusted: the result is a proof, checked by the kernel,
that `Exec` derives the run.
-/

namespace Claws.Sem

open Lean Meta Elab Tactic

/-- The facts the interpreter's unfolding needs. -/
theorem lookup_cons {α β} [BEq α] (a k : α) (b : β) (es : List (α × β)) :
    List.lookup a ((k, b) :: es) = if (a == k) = true then some b else List.lookup a es := by
  simp only [List.lookup]; split <;> simp_all

/-- A call the semantics derives is what the run reads at the call: the
semantics is deterministic (`Claws.Det`). -/
theorem semCall_of_call {P : Prog} {m : Mem} {f : String} {rs : List Res} {res : Option Val} {m' : Mem}
    (h : Call P m f rs res m') : semCall P m f rs = some (res, m') := by
  have hc : ∃ p : Option Val × Mem, Call P m f rs p.1 p.2 := ⟨(res, m'), h⟩
  unfold semCall
  split
  · rename_i hc'
    obtain ⟨h1, h2⟩ := Call.det (Classical.choose_spec hc') h
    exact congrArg some (Prod.ext h1 h2)
  · contradiction

theorem semCall_of_callFn {P : Prog} {m : Mem} {f : String} {rs : List Res} {res : Option Val}
    {m' : Mem} {n : Nat} (h : callFn n P m f rs = some (res, m')) : semCall P m f rs = some (res, m') :=
  semCall_of_call (call_of_callFn h)

theorem ult_decide (a b : BitVec 32) : a.ult b = decide (a < b) := by
  simp [BitVec.lt_def, BitVec.ult]

theorem ule_decide (a b : BitVec 32) : a.ule b = decide (a ≤ b) := by
  simp [BitVec.le_def, BitVec.ule]

theorem lt_of_getElem? {l : List Val} {i : Nat} {x : Val} (h : l[i]? = some x) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- Writing back what an object already holds changes nothing. -/
theorem set_self_of {l : List Val} {i : Nat} {x : Val} (h : l[i]? = some x) : l.set i x = l := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set]
  split
  · subst_vars; rw [if_pos (lt_of_getElem? h)]; exact h.symm
  · rfl

/-- An element of a vec of a Lean array, in bounds, is the array's
element as Code.lean reads it. -/
theorem getElem?_map_toList {α : Type} [Inhabited α] (f : α → Val) (a : Array α) (i : Nat) :
    (a.toList.map f)[i]? = if i < a.size then some (f a[i]!) else none := by
  split
  · rename_i h; simp [h, getElem!_pos]
  · rename_i h; simp; omega

/-! The semantics computes `int` on the integers, the translation on
`BitVec 32`: these state an `int` as the `toInt` of a bit vector, so
comparisons end up on bit vectors, where bv_decide reads them. -/

theorem ofNat_toInt_small (k : Nat) (h : k < 2 ^ 31) : (BitVec.ofNat 32 k).toInt = k := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]
  split <;> omega

theorem toInt_eq_lit (x : BitVec 32) (k : Nat) (h : k < 2 ^ 31) :
    (x.toInt = (no_index (OfNat.ofNat k : Int))) = (x = BitVec.ofNat 32 k) := by
  have : (OfNat.ofNat k : Int) = (k : Int) := rfl
  rw [this, ← ofNat_toInt_small k h]; exact propext BitVec.toInt_inj

theorem toInt_eq_toInt (x y : BitVec 32) : (x.toInt = y.toInt) = (x = y) := propext BitVec.toInt_inj

theorem toInt_lt_toInt (x y : BitVec 32) : (x.toInt < y.toInt) = (x.slt y = true) :=
  propext BitVec.slt_iff_toInt_lt.symm

theorem toInt_le_toInt (x y : BitVec 32) : (x.toInt ≤ y.toInt) = (x.sle y = true) :=
  propext BitVec.sle_iff_toInt_le.symm

/-- A promoted `uint8_t`, as the `toInt` of its 32-bit extension. -/
theorem natCast_toNat_eq_toInt (x : BitVec 8) : ((x.toNat : Nat) : Int) = (x.setWidth 32).toInt := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_setWidth]
  have := x.isLt
  split <;> omega

/-- An `int` converted to `uint8_t` keeps its low 8 bits
([conv.integral]/3). -/
theorem ofInt_toInt_setWidth (x : BitVec 32) : BitVec.ofInt 8 x.toInt = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

/-- Bytes promoted to `int` compare as the translation compares them,
unsigned, so a split on one settles the other. -/
theorem slt_setWidth (x y : BitVec 8) :
    (x.setWidth 32).slt (y.setWidth 32) = (x.setWidth 32).ult (y.setWidth 32) := by
  bv_decide

theorem sle_setWidth (x y : BitVec 8) :
    (x.setWidth 32).sle (y.setWidth 32) = (x.setWidth 32).ule (y.setWidth 32) := by
  bv_decide

/-- `int` `>>` rounds down ([expr.shift]/3), as an arithmetic shift does. -/
theorem toInt_fdiv_pow (y : BitVec 32) (k : Nat) : y.toInt.fdiv (2 ^ k) = (y.sshiftRight k).toInt := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg]
  · simp [Int.natCast_pow]
  · exact Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2))

/-- A `uint8_t` extended to 32 bits is not negative, so shifting it
right is the same either way. -/
theorem sshiftRight_setWidth (x : BitVec 8) (k : Nat) :
    (x.setWidth 32).sshiftRight k = x.setWidth 32 >>> k := by
  apply BitVec.sshiftRight_eq_of_msb_false
  simp [BitVec.msb_setWidth]

/-- An `int` index, as the `toNat` of a bit vector. -/
theorem index_toInt (z : BitVec 32) :
    Val.index (.int z.toInt) = if z.toNat < 2 ^ 31 then some z.toNat else none := by
  simp only [Val.index]
  rw [BitVec.toInt_eq_toNat_cond]
  have := z.isLt
  split <;> split <;> simp_all <;> omega

/-- A byte, extended and shifted right, is a non-negative `int`. -/
theorem toNat_shift_setWidth_lt (x : BitVec 8) (k : Nat) :
    ((x.setWidth 32 >>> k).toNat < 2147483648) = True := by
  simp only [eq_iff_iff, iff_true, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  have := x.isLt
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega)

theorem index_uint (k : BitVec 32) : Val.index (.uint k) = some k.toNat := rfl
theorem index_uchar (k : BitVec 8) : Val.index (.uchar k) = some k.toNat := rfl

/-- A byte indexes a table of 256 entries. (A version for any width and
any bound sends every `x.toNat < n` to the discharger, which is slow.) -/
theorem toNat_lt_256 (x : BitVec 8) : (x.toNat < 256) = True := by
  simp only [eq_iff_iff, iff_true]; exact x.isLt

/-- `&&` and `||` whose operands both evaluate are Boolean expressions,
as the translation writes them, not branches. -/
theorem land_collapse (p : Prop) [Decidable p] (y : Bool) :
    (if p then some (Res.val (Val.bool y)) else some (Res.val (Val.bool false))) =
      some (Res.val (Val.bool (decide p && y))) := by
  by_cases h : p <;> simp [h]

theorem lor_collapse (p : Prop) [Decidable p] (y : Bool) :
    (if p then some (Res.val (Val.bool true)) else some (Res.val (Val.bool y))) =
      some (Res.val (Val.bool (decide p || y))) := by
  by_cases h : p <;> simp [h]

/-- A safety check holds when each branch holds where it is taken. -/
theorem ite_eq_true_iff {c : Prop} [Decidable c] {x y : Bool} :
    ((if c then x else y) = true) = ((c → x = true) ∧ (¬c → y = true)) := by
  by_cases h : c <;> simp [h]

theorem ofArray_eq {α : Type} (f : α → Val) (a : Array α) : Val.ofArray f a = .vec (a.toList.map f) := rfl

/-- Two writes to one object leave the same memory exactly when they
write the same value. -/
theorem set_set_inj {l : List Val} {i : Nat} {a b : Val} (h : i < l.length) :
    (l.set i a = l.set i b) = (a = b) := by
  apply propext; constructor
  · intro e; have := congrArg (·[i]?) e; simpa [h] using this
  · intro e; rw [e]

/-- Literal offsets add up, so a block that declares several names
closes: `n + 1 + 1 - n` is `2`. -/
theorem add_lit_add_lit (n a b : Nat) :
    n + no_index (OfNat.ofNat a) + no_index (OfNat.ofNat b) = n + (OfNat.ofNat a + OfNat.ofNat b) :=
  Nat.add_assoc _ _ _

theorem add_lt_self_false (a k : Nat) : (a + k < a) = False := by simp

theorem lt_add_self_iff (a k : Nat) : (a < a + k) = (0 < k) := by simp

/-- What a precondition tells the interpreter: each leading
`claws::expects` condition, run with any fuel, gives true or runs out. -/
theorem Pre.facts {P : Prog} {m : Mem} {f : String} {rs : List Res} {fn : Func} {e₀ : Env}
    {m₀ : Mem} {ss : List Stmt} (h : Pre P m f rs) (hf : List.lookup f P.funcs = some fn)
    (hp : bindParams fn.params rs [] m = some (e₀, m₀)) (hb : fn.body = .block ss) (n : Nat) :
    ∀ c ∈ leading ss, eval n P e₀ m₀ c = none ∨ eval n P e₀ m₀ c = some (.val (.bool true)) := by
  intro c hc
  simp only [Pre, hf, hp, hb] at h
  cases he : eval n P e₀ m₀ c with
  | none => exact .inl rfl
  | some r => exact .inr (by rw [Eval.det ((sound n).1 _ _ _ _ _ he) (h c hc)])

/-- The converse: a precondition holds when the interpreter finds every
leading condition true. -/
theorem Pre.of_eval {P : Prog} {m : Mem} {f : String} {rs : List Res} {fn : Func} {e₀ : Env}
    {m₀ : Mem} {ss : List Stmt} (n : Nat) (hf : List.lookup f P.funcs = some fn)
    (hp : bindParams fn.params rs [] m = some (e₀, m₀)) (hb : fn.body = .block ss)
    (h : ∀ c ∈ leading ss, eval n P e₀ m₀ c = some (.val (.bool true))) : Pre P m f rs := by
  simp only [Pre, hf, hp, hb]
  intro c hc
  exact (sound n).1 _ _ _ _ _ (h c hc)

/-- Close the goal if a hypothesis is `False`, or two say `p` and `¬p`
for the same term `p`. `contradiction` also unfolds hypotheses to
compare them, which on a run's large terms exceeds Lean's recursion
limit; this compares terms as they are written. Fails otherwise. -/
elab "claws_absurd" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ds := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
    let mut tys : Std.HashMap Lean.Expr Lean.Expr := {}
    for d in ds do
      tys := tys.insert (← instantiateMVars d.type) d.toExpr
    for d in ds do
      let t ← instantiateMVars d.type
      if t.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) d.toExpr); return
      if let some p := t.not? then
        if let some hp := tys.get? p then
          g.assign (← mkAbsurd (← g.getType) hp d.toExpr); return
    throwError "claws_absurd: no contradiction"

/-- Whether `n` is an enumeration: an inductive type whose constructors
take no arguments, other than `Bool`. -/
def isEnum (env : Environment) (n : Name) : Bool :=
  n != ``Bool &&
  match env.find? n with
  | some (.inductInfo info) =>
    info.numParams == 0 && info.numIndices == 0 && !info.isRec &&
      info.ctors.all fun c => match env.find? c with
        | some (.ctorInfo ci) => ci.numFields == 0
        | _ => false
  | _ => false

/-- The atoms of a condition, left to right: what `&&`, `||` and `!`, or
`∧`, `∨` and `¬`, combine. The interpreter tests the left operand of
`&&` and `||` first, so splitting on atoms in this order meets each of
its branches settled. -/
partial def atoms (c : Lean.Expr) : List Lean.Expr :=
  if let some (p, q) := c.and? then atoms p ++ atoms q
  else if let some (p, q) := c.app2? ``Or then atoms p ++ atoms q
  else if let some p := c.not? then atoms p
  else if let some (_, x, y) := c.eq? then
    if y.isConstOf ``Bool.true then
      if let some (a, b) := x.app2? ``and then atoms (mkEq' a) ++ atoms (mkEq' b)
      else if let some (a, b) := x.app2? ``or then atoms (mkEq' a) ++ atoms (mkEq' b)
      else if let some a := x.app1? ``not then atoms (mkEq' a)
      else if x.isAppOfArity ``Decidable.decide 2 then atoms (x.getArg! 0)
      else [c]
    else [c]
  else [c]
where
  mkEq' (b : Lean.Expr) : Lean.Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- Split on the first `if` condition in the goal that mentions no bound
variable and is not already settled by a hypothesis, or on its first
unsettled atom. Failing that, split
a `match` on a value of an enumeration that is not a variable, such as an
element of a vec, into its cases. Fails when there is neither. -/
def clawsCase (results : Bool) : TacticM Unit := do
  let g ← getMainGoal
  let env ← getEnv
  let enumDiscr ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let lctx ← getLCtx
    let settled (c : Lean.Expr) : Bool :=
      lctx.any fun d => d.type == c || d.type == mkNot c
    if let some e := t.find? fun e =>
        e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars && !settled (e.getArg! 1) then
      let c := e.getArg! 1
      -- An atom a rewrite has already settled to `true` or `false` is no
      -- condition: splitting on it would never end.
      let trivial (a : Lean.Expr) : Bool :=
        a.isConstOf ``True || a.isConstOf ``False ||
          ((a.eq?.map fun (_, x, _) => x.isConstOf ``Bool.true || x.isConstOf ``Bool.false).getD false)
      let c := ((atoms c).find? fun a => !trivial a && !settled a).getD c
      let gs ← g.byCases c `hc
      replaceMainGoal [gs.1.mvarId, gs.2.mvarId]
      return none
    let discrs := fun (e : Lean.Expr) => Id.run do
      let some n := e.getAppFn.constName? | return #[]
      let some info := Meta.getMatcherInfoCore? env n | return #[]
      let args := e.getAppArgs
      if args.size < info.numParams + 1 + info.numDiscrs then return #[]
      return args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
    let found ← IO.mkRef (none : Option Lean.Expr)
    Meta.forEachExpr t fun e => do
      if (← found.get).isSome then return
      for d in discrs e do
        if d.isFVar || d.hasLooseBVars || (← found.get).isSome then continue
        let ty ← whnfR (← inferType d)
        if let some n := ty.constName? then
          if isEnum env n && !(d.getAppFn.constName?.map (isEnum env ·.getPrefix) |>.getD false) then
            found.set (some d)
        -- What a loop that may return gives back, `(r, i)` or `r`: a
        -- translated function's result, or a part of one.
        if results && (ty.isAppOfArity ``Option 1 || ty.isAppOfArity ``Prod 2) then
          let mut h := d
          for _ in [0:8] do
            if h.isAppOfArity ``Prod.fst 3 || h.isAppOfArity ``Prod.snd 3 then h := h.appArg!
          if let some c := h.getAppFn.constName? then
            if c.components.contains `Code then found.set (some d)
    match ← found.get with
    | some d => return some (← Term.exprToSyntax d)
    | none => throwError "claws_case: no condition to split on"
  if let some stx := enumDiscr then
    evalTactic (← `(tactic| (generalize $stx = hv at *; cases hv)))
    evalTactic (← `(tactic| all_goals (try simp only [] at *)))

elab "claws_case" : tactic => clawsCase true

/-- `claws_case`, except on what a loop returns: before the run, the
translation's loop has no counterpart yet, and splitting on its result
would lose the link to the loop's lemma. -/
elab "claws_case_cond" : tactic => clawsCase false

/-- Split every variable of an enumeration type (an inductive type whose
constructors take no arguments, other than `Bool`) into its cases, so
that a `match` in the translation and a `switch` in the C++ both meet a
known value. -/
elab "claws_enum_cases" : tactic => do
  let g ← getMainGoal
  let gs ← g.withContext do
    let mut goals := [g]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      let some n := ty.constName? | continue
      if n == ``Bool then continue
      let env ← getEnv
      let some (.inductInfo info) := env.find? n | continue
      if info.numParams != 0 || info.numIndices != 0 || info.isRec then continue
      let nullary ← info.ctors.allM fun c => do
        let some (.ctorInfo ci) := env.find? c | return false
        return ci.numFields == 0
      if !nullary then continue
      let mut next := []
      for h in goals do
        let subs ← h.cases d.fvarId
        next := next ++ (subs.map (·.mvarId)).toList
      goals := next
    return goals
  replaceMainGoal gs

/-- Whether `e` decodes a value: `S.ofVal x` or `Val.asUint x`. -/
def isDecoding (e : Lean.Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n => (e.getAppNumArgs == 1 && (n.getString! == "ofVal" ||
      n == ``Val.asUint || n == ``Val.asUchar || n == ``Val.asBool)) ||
      (e.getAppNumArgs == 3 && (n == ``Val.asArray || n == ``Val.asList))
  | none => false

/-- The first decoding in the goal or a hypothesis that `pick` accepts. -/
def findDecoding (pick : Lean.Expr → Bool) : TacticM (Option Lean.Expr) := do
  let g ← getMainGoal
  g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if let some e := t.find? fun e => isDecoding e && !e.hasLooseBVars && pick e.appArg! then
        return some e
    let t ← instantiateMVars (← g.getType)
    return t.find? fun e => isDecoding e && !e.hasLooseBVars && pick e.appArg!

/-- In a lemma `claws_valid` proves, each struct or enum argument is
read from the call, as `S.ofVal x`. Name each such reading by a
variable, so the lemma takes the shape of the law; a value argument
`v = S.toVal (S.ofVal v)` then becomes `v = S.toVal a`, and v is
replaced by `S.toVal a`. -/
elab "claws_decode" : tactic => do
  -- Readings of an object, `S.ofVal (m[p]?.getD default)`, first.
  for _ in [0:64] do
    let some e ← findDecoding (fun x => !x.isFVar) | break
    let stx ← Term.exprToSyntax e
    evalTactic (← `(tactic| generalize $stx = a at *))
  -- Then readings of a value argument, `S.ofVal v`.
  for _ in [0:64] do
    let some e ← findDecoding (fun x => x.isFVar) | break
    let stx ← Term.exprToSyntax e
    evalTactic (← `(tactic| generalize $stx = a at *))
  evalTactic (← `(tactic| try subst_vars))

/-- For each hypothesis `l[i]? = some x`, add `i < l.length`. -/
elab "claws_bounds" : tactic => do
  let g ← getMainGoal
  let facts ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      let some (_, lhs, _) := t.eq? | continue
      if !(lhs.isAppOf ``GetElem?.getElem?) then continue
      try
        let pf ← mkAppM ``lt_of_getElem? #[d.toExpr]
        out := out.push pf
      catch _ => pure ()
    return out
  let mut g := g
  for pf in facts do
    let ty ← g.withContext (inferType pf)
    let (_, g') ← (← g.assert `hb ty pf).intro1P
    g := g'
  replaceMainGoal [g]

/-- Unfold the law the goal states, `Laws.Valid.f`, to its statement. -/
elab "claws_unfold_law" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some c := t.getAppFn.constName? | throwError "claws_unfold_law: the goal is not a law"
  let g ← g.deltaTarget (· == c)
  replaceMainGoal [g]

attribute [claws_interp] exec execList eval evalList evalArgs evalTop bindParams
  Mem.read Mem.write close Val.at
  lookup_cons List.lookup_nil inInt
  BitVec.ult_iff_lt BitVec.ule_iff_le List.map List.zip List.zipWith List.length List.drop Option.map
  Option.bind Function.comp decide_eq_true_eq beq_iff_eq Option.some.injEq Val.uint.injEq
  Val.bool.injEq Val.record.injEq ite_true ite_false Bool.false_eq_true Option.isSome_some
  Option.isSome_none not_true_eq_false not_false_eq_true List.nil_append List.cons_append
  Bool.true_and Bool.false_and Bool.and_true
  Bool.and_false Bool.true_or Bool.false_or Bool.or_true Bool.or_false Bool.not_true Bool.not_false
  decide_true decide_false decide_not Val.set setFirst pick caseAt
  defaultAt bitsInt leading List.forall_mem_cons
  List.not_mem_nil BitVec.shiftLeft_eq'
  BitVec.ushiftRight_eq' Val.uchar.injEq Val.enum.injEq Val.int.injEq reduceCtorEq
  Option.map_some Option.map_none Option.bind_some Option.bind_none false_or or_false
  true_and and_true implies_true forall_const Int.cast_ofNat_Int BitVec.ofInt_ofNat bne_iff_ne
  ult_decide ule_decide Val.asUint Val.asUchar Val.asBool Option.getD_some
  List.length_append List.length_cons List.length_nil List.length_set List.length_take
  List.append_assoc List.getElem?_cons_zero List.getElem?_cons_succ List.append_nil
  List.getElem?_append_left List.getElem?_append_right List.getElem?_set_self
  List.getElem?_set_ne List.set_append List.take_append_of_le_length List.take_of_length_le
  List.take_left' List.take_length List.take_take List.take_length_add_append List.take_succ_cons List.take_zero Nat.min_eq_left Nat.min_self Nat.add_sub_cancel_left Nat.sub_self Nat.add_zero Nat.zero_add
  Nat.add_lt_add_iff_left Nat.add_sub_add_left add_lt_self_false lt_add_self_iff Nat.lt_irrefl List.set_cons_zero
  List.set_cons_succ set_self_of List.take_set_of_le
  Prod.mk.injEq Res.val.injEq Res.loc.injEq Outcome.normal.injEq Outcome.ret.injEq
  Option.some_ne_none eq_self_iff_true BitVec.ofNat_eq_ofNat Bool.not_eq_true' decide_eq_false_iff_not
  BitVec.ofInt_natCast BitVec.ofNat_toNat BitVec.ofInt_toInt toInt_eq_lit toInt_eq_toInt
  toInt_lt_toInt toInt_le_toInt Int.toNat_natCast Int.natCast_nonneg toNat_lt_256
  natCast_toNat_eq_toInt ofInt_toInt_setWidth slt_setWidth sle_setWidth toInt_fdiv_pow sshiftRight_setWidth index_toInt
  add_lit_add_lit List.set_set set_set_inj List.append_cancel_left_eq List.cons.injEq land_collapse lor_collapse Mem.value globRead index_uint index_uchar toNat_shift_setWidth_lt ofArray_eq getElem?_map_toList List.length_map Array.length_toList
  List.length_replicate Array.toList_setIfInBounds Array.toList_push Array.toList_replicate
  Array.toList_empty List.map_set List.map_append List.map_cons List.map_nil List.map_replicate
  Array.size_setIfInBounds Array.size_push Array.size_replicate Val.vec.injEq

end Claws.Sem

/-- `claws_interp_eqns f g ..` adds the equations of each definition by
cases to `claws_interp`, and not the definition: on an argument that is
not yet a constructor, simp would otherwise unfold it into a `match` and
simplify every branch, which multiplies through the rest of a run. -/
syntax "claws_interp_eqns " ident+ : command

open Lean Elab Command Meta in
elab_rules : command
  | `(claws_interp_eqns $fs*) => do
    for f in fs do
      let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
      let some eqns ← liftTermElabM <| getEqnsFor? n | throwError "claws_interp_eqns: no equations for {n}"
      let ids := eqns.map mkIdent
      elabCommand (← `(attribute [claws_interp] $ids*))

claws_interp_eqns Claws.Sem.binop Claws.Sem.unop Claws.Sem.convert Claws.Sem.truth Claws.Sem.literal
  Claws.Sem.aggregate Claws.Sem.finish Claws.Sem.Val.field Claws.Sem.Val.elem Claws.Sem.Val.same
  Claws.Sem.promote Claws.Sem.one Claws.Sem.Val.ty Claws.Sem.amount

/-- One pass of the interpreter, with the definitions `ls` unfolded. A
call to a validated function is rewritten with its lemma from
`claws_calls`, whose side conditions `claws_disch` establishes. -/
syntax "claws_run" " [" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

/-- Establish a side condition: an address bound or inequality, a callee's
precondition, or that an object holds an encoded value. -/
syntax "claws_disch" : tactic

namespace Claws.Sem

open Lean Meta Simp

theorem ite_cond_rw {α : Sort u} {c c' : Prop} [inst : Decidable c] (h : c = c') (t f : α) :
    @ite α c inst t f = @ite α c' (h ▸ inst) t f := by subst h; rfl

/-- The interpreter's functions. -/
def interpFns : List Name :=
  [``eval, ``evalList, ``evalArgs, ``evalTop, ``callFn, ``exec, ``execList, ``execLoop]

/-- Whether `e` still has some of the interpreter to run. -/
def mentionsRun (e : Lean.Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => interpFns.contains n
    | _ => false).isSome

/-- Run the interpreter the way it runs, on the path it takes: a `match`
of the interpreter simplifies only what it tests, and an `if` whose
branches run more of the program only its condition, until they settle
which branch is taken. simp otherwise also simplifies every branch not
yet taken, with nothing known about the names and memory there, and on a
loop body that is most of the work. -/
def lazyPre : Simproc := fun e => do
  if e.isAppOfArity ``ite 5 then
    let t := e.getArg! 3
    let f := e.getArg! 4
    unless mentionsRun t || mentionsRun f do return .continue
    let α := e.getArg! 0
    let c := e.getArg! 1
    let inst := e.getArg! 2
    let u := e.getAppFn.constLevels!
    let rc ← simp c
    if rc.expr.isTrue then
      return .visit { expr := t, proof? := some (mkApp6 (mkConst ``ite_cond_eq_true u) α c inst t f (← rc.getProof)) }
    if rc.expr.isFalse then
      return .visit { expr := f, proof? := some (mkApp6 (mkConst ``ite_cond_eq_false u) α c inst t f (← rc.getProof)) }
    if rc.expr == c then return .done { expr := e }
    let pf ← rc.getProof
    let inst' ← mkEqNDRec (← withLocalDeclD `p (mkSort .zero) fun p => mkLambdaFVars #[p] (mkApp (mkConst ``Decidable) p)) inst pf
    return .done {
      expr := mkApp5 (mkConst ``ite u) α rc.expr inst' t f
      proof? := some (mkApp7 (mkConst ``ite_cond_rw u) α c rc.expr inst pf t f) }
  let .const n _ := e.getAppFn | return .continue
  unless (`Claws.Sem).isPrefixOf n do return .continue
  let some info ← getMatcherInfo? n | return .continue
  let r := (← simpMatchDiscrs? info e).getD { expr := e }
  match ← withSimpMetaConfig (reduceMatcher? r.expr) with
  | .reduced e' => return .visit { expr := e'.headBeta, proof? := r.proof? }
  | _ => return .done r

/-- simp's methods, with `lazyPre` first. -/
def lazyMethods (simprocs : SimprocsArray) (disch? : Option Simp.Discharge) : Simp.Methods :=
  let base := match disch? with
    | some d => Simp.mkMethods simprocs d (wellBehavedDischarge := false)
    | none => Simp.mkDefaultMethodsCore simprocs
  { base with pre := fun e => do
      match ← lazyPre e with
      | .continue none => base.pre e
      | s => return s }

/-- `simpGoal`, with `lazyMethods`. -/
def lazySimpGoal (mvarId : MVarId) (ctx : Simp.Context) (methods : Simp.Methods)
    (simplifyTarget : Bool) (fvarIdsToSimp : Array FVarId) : MetaM (Option MVarId) := do
  mvarId.withContext do
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
      let (r, _) ← Simp.main type ctx (methods := methods)
      match r.proof? with
      | some _ => match (← applySimpResult mvarIdNew (mkFVar fvarId) type r) with
        | none => return none
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return none
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let target ← instantiateMVars (← mvarIdNew.getType)
      let (r, _) ← Simp.main target ctx (methods := methods)
      if r.expr.isTrue then
        match r.proof? with
        | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
        | none => mvarIdNew.assign (mkConst ``True.intro)
        return none
      mvarIdNew ← applySimpResultToTarget mvarIdNew target r
    let (_, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`claws_run` made no progress"
    return some mvarIdNew

end Claws.Sem

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| claws_run [$ls,*] $[$loc]?) => withMainContext do
    let stx ← `(tactic|
      simp (disch := claws_disch) only [$ls,*, claws_interp, claws_calls, String.reduceBEq,
        String.reduceEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceMod,
        Nat.reduceDiv, Nat.reduceLT, Int.reduceLT, Int.reduceLE, Int.reduceNeg, Int.reduceToNat,
        Int.reduceBEq, Int.reduceEq, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceOfInt,
        BitVec.reduceLT, BitVec.reduceLE, BitVec.reduceEq, BitVec.reduceNe, BitVec.reduceAdd,
        BitVec.reduceSub, BitVec.reduceMul, List.drop_zero, ↓reduceIte, ↓reduceDIte, dite_true,
        dite_false, *] $[$loc]?)
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    let loc := expandOptLocation stx.raw[5]
    dischargeWrapper.with fun disch? => do
      let methods := Claws.Sem.lazyMethods simprocs disch?
      let go (fvarIds : Array FVarId) (target : Bool) : TacticM Unit := do
        match ← Claws.Sem.lazySimpGoal (← getMainGoal) ctx methods target fvarIds with
        | none => replaceMainGoal []
        | some g => replaceMainGoal [g]
      match loc with
      | .targets hyps target => withMainContext do go (← getFVarIds hyps) target
      | .wildcard => withMainContext do go (← (← getMainGoal).getNondepPropHyps) true

open Lean Meta Elab Tactic in
/-- A side condition of a `match` equation for a catch-all pattern says
that no earlier pattern matches: `∀ .., x = C .. → False`, with a
constructor on one side. Prove it by `contradiction`, or leave it open
at once: the other ways to discharge are slow, and simp tries the
catch-all before the equation that applies. Fails on any other goal. -/
elab "claws_ctor_side" : tactic => do
  let g ← getMainGoal
  let isSide ← g.withContext do
    forallTelescopeReducing (← whnfR (← instantiateMVars (← g.getType))) fun xs body => do
      unless body.isConstOf ``False && !xs.isEmpty do return false
      xs.anyM fun x => do
        let some (_, a, b) := (← whnfR (← inferType x)).eq? | return false
        return (← isConstructorApp a) || (← isConstructorApp b)
  unless isSide do throwError "claws_ctor_side: not a match side condition"
  evalTactic (← `(tactic| try (intros; contradiction)))

/-- Side conditions inside `claws_disch`, without calls: a discharger
that runs the interpreter with itself as discharger can admit a goal it
leaves open. -/
syntax "claws_disch_simple" : tactic

macro_rules
  | `(tactic| claws_disch_simple) => `(tactic| first
      | claws_ctor_side
      | omega
      | (simp only [List.length_append, List.length_cons, List.length_nil, List.length_set,
          List.length_take, Nat.min_def] at *; omega)
      -- Syntactically: unfolding to compare a side condition with every
      -- hypothesis is slow, and a match is what is wanted.
      | with_reducible assumption
      | (simp only [*, Option.getD_some, claws_codec] <;> fail "open")
      | (simp only [claws_interp, String.reduceBEq,
          String.reduceEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceMod,
          Nat.reduceDiv, Nat.reduceLT, Int.reduceLT, Int.reduceLE, Int.reduceNeg, Int.reduceToNat,
          Int.reduceBEq, Int.reduceEq, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceOfInt,
          Option.getD_some, claws_codec, ↓reduceIte, *] <;> fail "open")
      | skip)

macro_rules
  | `(tactic| claws_disch) => `(tactic| first
      | claws_ctor_side
      | (claws_disch_simple <;> fail "open")
      | (refine Claws.Sem.Pre.of_eval 1000 rfl rfl rfl ?_
         simp only [Claws.Sem.leading, List.forall_mem_cons, List.not_mem_nil, false_implies,
           implies_true, and_true]
         all_goals (simp (disch := claws_disch_simple) only [Claws.Sem.eval, claws_interp,
           String.reduceBEq, String.reduceEq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
           Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Int.reduceLT, Int.reduceLE,
           Int.reduceNeg, Int.reduceToNat, Int.reduceBEq, Int.reduceEq, BitVec.reduceToNat,
           BitVec.reduceOfNat, BitVec.reduceOfInt, ↓reduceIte, *])
         all_goals (first | (simp_all <;> fail "open") | bv_omega | bv_decide))
      | skip)

/-- Rewrite a loop in the goal with its lemma (`Claws.Loop`). -/
syntax "claws_loop_use" : tactic

/-- The body of every validation proof. The goal states what `callFn`
returns; the hypotheses are the arguments, the objects and the
precondition. -/
syntax "claws_prove" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- The first half of `claws_prove`: name the arguments, and state the
precondition as facts. -/
syntax "claws_prove_start" : tactic

/-- The second half of `claws_prove`: run the body. -/
syntax "claws_prove_finish" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- The last step of `claws_prove`. With `Claws.validTrace` defined, show
the goal instead. -/
syntax "claws_prove_end" : tactic

macro_rules
  | `(tactic| claws_prove [$ls,*]) => `(tactic| (claws_prove_start; claws_prove_finish [$ls,*]))

macro_rules
  | `(tactic| claws_prove_start) => `(tactic| (
      claws_decode
      claws_bounds
      -- Run the function's own body. Calls inside it are not unfolded:
      -- each callee is used through its lemma in claws_calls, so
      -- validate callees first.
      simp only [Claws.Sem.callFn]
      claws_enum_cases
      -- The precondition, as facts: each leading claws::expects holds.
      -- One fact per condition first: unfolding eval on a condition not
      -- yet known would run through all the fuel.
      all_goals (try (
        have hpre := Claws.Sem.Pre.facts ‹Claws.Sem.Pre _ _ _ _› rfl rfl rfl 1000
        clear ‹Claws.Sem.Pre _ _ _ _›
        simp only [Claws.Sem.leading, List.forall_mem_cons, List.not_mem_nil, false_implies,
          implies_true, and_true] at hpre
        (try claws_run [Claws.Sem.eval] at hpre)))))

macro_rules
  | `(tactic| claws_prove_finish [$ls,*]) => `(tactic| (
      -- Split on the translation's conditions first, so the interpreter
      -- meets each condition already settled.
      all_goals (try simp only [$ls,*, BitVec.ult_iff_lt, BitVec.ule_iff_le, beq_iff_eq, bne_iff_ne,
        Claws.Sem.ult_decide, Claws.Sem.ule_decide, BitVec.ofNat_eq_ofNat])
      -- A split settles an atom of a condition; the constant lemmas then
      -- settle the condition, or leave what is left to split.
      all_goals repeat' (claws_case_cond <;>
        (try simp only [$ls,*, BitVec.ult_iff_lt, BitVec.ule_iff_le, beq_iff_eq, bne_iff_ne,
          Bool.false_eq_true, BitVec.ofNat_eq_ofNat, ↓reduceIte, Bool.true_and, Bool.false_and,
          Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
          Bool.not_true, Bool.not_false, decide_true, decide_false, decide_eq_true_eq, true_and,
          false_and, and_true, and_false, true_or, false_or, or_true, or_false, not_true_eq_false,
          not_false_eq_true, *] at *))
      -- One pass of the interpreter, then a loop's lemma or a split where
      -- it stopped; a pass that closes the goal leaves nothing to do.
      all_goals repeat' ((try claws_run [$ls,*] at *) <;> first
        | claws_loop_use
        | claws_case)
      -- What is left compares values, some stated on numbers (the
      -- semantics) and some on bit vectors (the translation). bv_omega
      -- reads both. Failing that, state comparisons on bit vectors, so
      -- bv_decide uses them and reports a counterexample if the
      -- translation is wrong.
      -- bv_omega and bv_decide first: simp_all rewrites terms such as
      -- `a[(i + 1).toNat]!` into forms that no longer match each other,
      -- which bv_decide then reads as unrelated (CLAUDE.md, rule 9).
      all_goals (try claws_run [$ls,*] at *)
      all_goals (first
        | (claws_prove_end; done)
        | (simp_all; done)
        | ((try simp_all); all_goals (try claws_run [$ls,*]); all_goals claws_prove_end))))

open Lean Meta Elab Tactic in
/-- Unfold each constant of the translation, a bit vector defined as a
literal, in the goal and the hypotheses: bv_decide reads a constant it
cannot see into as an unknown, and reports a spurious counterexample. -/
elab "claws_unfold_consts" : tactic => do
  let g ← getMainGoal
  let env ← getEnv
  let consts ← g.withContext do
    let mut ts := #[← instantiateMVars (← g.getType)]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do ts := ts.push (← instantiateMVars d.type)
    let mut out : Array Name := #[]
    for t in ts do
      for n in t.getUsedConstants do
        if out.contains n then continue
        let some (.defnInfo info) := env.find? n | continue
        unless info.type.isAppOfArity ``BitVec 1 && info.levelParams.isEmpty do continue
        unless info.value.isAppOf ``OfNat.ofNat || info.value.isAppOf ``BitVec.ofNat do continue
        out := out.push n
    return out
  if consts.isEmpty then return
  let ids := consts.map mkIdent
  evalTactic (← `(tactic| try unfold $ids* at *))

open Lean Elab Tactic in
elab_rules : tactic | `(tactic| claws_prove_end) => do
  if (← getEnv).contains `Claws.validTrace then
    evalTactic (← `(tactic| (trace_state; sorry)))
  else
    evalTactic (← `(tactic| claws_unfold_consts))
    evalTactic (← `(tactic| first
      | bv_omega
      -- bv_decide only on a goal the rewrite leaves: with no goal it
      -- logs an error rather than failing.
      | ((try simp only [← BitVec.lt_def, ← BitVec.le_def] at *) <;> bv_decide)))

namespace Claws

open Lean Meta Elab Command Term Tactic

/-- After `intros`, the last two hypotheses are the fuel `n` and
`hn : r + s ≤ n`; replace n by `k + s`, keeping `r ≤ k`. The interpreter
unfolds the small s; r, reserved for callees and loops, never enters the
fuel, since the kernel unfolds `k + r` one step at a time and simp would
fold `(k + r) + s` into `k + (r + s)`. -/
elab "intro_fuel_core" r:num s:num : tactic => do
  evalTactic (← `(tactic| intros))
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let some hn := lctx.lastDecl | throwError "intro_fuel_core: no fuel hypothesis"
    let t ← instantiateMVars hn.type
    let some (_, _, _, n) := t.app4? ``LE.le | throwError "intro_fuel_core: no bound"
    let nStx ← Term.exprToSyntax n
    evalTactic (← `(tactic| (
      obtain ⟨k, hk, hr⟩ : ∃ k, $nStx = k + $s ∧ $r ≤ k := ⟨$nStx - $s, by omega, by omega⟩
      subst hk)))

attribute [claws_safe] dite_true dite_false dite_eq_ite not_true_eq_false false_implies Claws.Sem.ite_eq_true_iff Bool.false_eq_true Bool.true_eq_false
  imp_false implies_true true_implies true_and and_true Bool.not_eq_true' Bool.not_eq_false'
  Bool.not_eq_false decide_eq_false_iff_not decide_eq_true_eq Decidable.not_not Bool.and_eq_true
  Bool.or_eq_true Bool.not_not Bool.not_true Bool.not_false not_or not_false_eq_true
  Claws.Sem.ult_decide Claws.Sem.ule_decide bne_iff_ne beq_iff_eq ne_eq and_assoc


/-- `claws_safe Proof.Safety.f Code.f` adds `hsafe`: `Code.f.safe` holds
of the arguments the goal applies `Code.f` to, by the safety obligation
proven for f. Its conditions, such as an index in bounds, are what the
semantics needs where the C++ would trap. -/
elab "claws_safe " thm:ident fn:ident : tactic => do
  let g ← getMainGoal
  let fnName ← realizeGlobalConstNoOverloadWithInfo fn
  let stx ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some app := t.find? (fun e => e.isAppOf fnName) | throwError "claws_safe: the goal does not mention {fnName}"
    Term.exprToSyntax (mkAppN (mkConst (fnName ++ `safe)) app.getAppArgs)
  let safeId := mkIdent (fnName ++ `safe)
  let side ← if (← getEnv).contains (fnName ++ `pre) then
      let pre := mkIdent (fnName ++ `pre)
      `(tactic| first
        | assumption
        | omega
        | (simp only [$pre:ident]; simp_all; done)
        | (simp only [$pre:ident] at *; bv_decide))
    else `(tactic| first | assumption | omega)
  evalTactic (← `(tactic| (
    have hsafe : $stx = true := by
      apply $thm
      all_goals ($side:tactic)
    try simp only [$safeId:ident] at hsafe
    -- What the check tests unconditionally becomes a hypothesis of its
    -- own, and what it tests on a branch an implication from the
    -- branch's condition.
    try simp only [↓reduceDIte, claws_safe] at hsafe
    -- A second pass removes premises the first leaves as `¬False`, and
    -- uses each conjunct to simplify the next, which settles
    -- `A ∧ (A → B)`.
    try simp (config := { contextual := true }) only [↓reduceDIte, claws_safe] at hsafe
    repeat (obtain ⟨_, hsafe⟩ := hsafe)
    -- A few more rounds: the parts split off settle the premises of
    -- what is left.
    iterate 3 (try (
      simp only [*, ↓reduceDIte, claws_safe] at hsafe
      repeat (obtain ⟨_, hsafe⟩ := hsafe)))
    -- A path the check rules out ends here, before any run.
    try claws_absurd)))

/-- In the proof of a recursive function, turn each induction hypothesis,
which states what `callFn` returns for the arguments of a recursive
call, into what the run reads at that call, `semCall`. Each encoding of
an enumeration is unfolded, as the run unfolds it once the cases are
split, and each list's encoding states the list by its elements, as the
run does. -/
elab "claws_ih" : tactic => do
  let g ← getMainGoal
  let (news, olds) ← g.withContext do
    let mut news : Array (Lean.Expr × Lean.Expr) := #[]
    let mut olds : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      let some r ← forallTelescope t fun xs body => do
          let k := xs.size
          let some (_, lhs, rhs) := body.eq? | return none
          unless lhs.isAppOfArity ``Claws.Sem.callFn 5 && k ≥ 2 do return none
          let some (_, _, b, _) := (← inferType xs[k - 1]!).app4? ``LE.le | return none
          let hs := xs[0:k - 2].toArray
          let ty ← mkForallFVars hs (← mkEq (mkAppN (mkConst ``Claws.Sem.semCall) lhs.getAppArgs[1:]) rhs)
          let run := mkAppN d.toExpr (hs ++ #[b, mkApp (mkConst ``Nat.le_refl) b])
          let pf ← mkLambdaFVars hs (← mkAppM ``Claws.Sem.semCall_of_callFn #[run])
          return some (ty, pf)
        | continue
      news := news.push r
      olds := olds.push d.fvarId
    return (news, olds)
  let mut g := g
  for (ty, pf) in news do
    let (_, g') ← (← g.assert `ih ty pf).intro1P
    g := g'
  g ← g.tryClearMany olds
  replaceMainGoal [g]
  -- The enumerations' encodings, unfolded.
  let names ← g.withContext do
    let mut out : Array Name := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      for n in (← instantiateMVars d.type).getUsedConstants do
        if n.getString! == "toVal" && !out.contains n then
          if let some (.defnInfo _) := (← getEnv).find? n then out := out.push n
    return out
  -- And each list's, by its elements, as the run states lists.
  let names := names.push ``Claws.Sem.Val.ofList_def
  do
    let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← names.mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    let ls : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems ids
    evalTactic (← `(tactic| try simp only [$ls,*] at $(mkIdent `ih):ident))

/-- The start of the proof of a recursive function f: name the arguments
as `Code.f` reads them, and go by induction over `Code.f`, for any
objects, so the hypothesis covers the call the body makes with the
objects it has by then. -/
elab "claws_rec_start " c:ident : tactic => do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let g ← getMainGoal
  -- The binders before the precondition: the arguments, the objects and
  -- the decodings of the arguments.
  let k ← g.withContext do
    forallTelescope (← instantiateMVars (← g.getType)) fun xs _ => do
      let mut k := 0
      for x in xs do
        if (← inferType x).isAppOf ``Claws.Sem.Pre then break
        k := k + 1
      return k
  let (_, g) ← g.introNP k
  replaceMainGoal [g]
  evalTactic (← `(tactic| claws_decode))
  let g ← getMainGoal
  let (mem, args) ← g.withContext do
    let some d := (← getLCtx).findDecl? fun d =>
        if !d.isImplementationDetail && d.type.isConstOf ``Claws.Sem.Mem then some d else none
      | throwError "claws_rec_start: no objects"
    let some app := (← instantiateMVars (← g.getType)).find? (·.isAppOf cn)
      | throwError "claws_rec_start: the goal does not mention {cn}"
    let args ← app.getAppArgs.mapM fun a => do
      unless a.isFVar do throwError "claws_rec_start: {cn} applied to {a}, not a variable"
      Term.exprToSyntax a
    return (d.fvarId, args)
  let (_, g) ← g.revert #[mem]
  replaceMainGoal [g]
  evalTactic (← `(tactic| fun_induction $(mkIdent cn):ident $args*))

/-- Whether `Code.f` calls itself: one of its equations mentions it on
the right. -/
def isRecursive (cn : Name) : MetaM Bool := do
  let some eqns ← getEqnsFor? cn | return false
  eqns.anyM fun e => do
    let some info := (← getEnv).find? e | return false
    forallTelescope info.type fun _ body => do
      let some (_, _, rhs) := body.eq? | return false
      return rhs.getUsedConstants.contains cn

/-- `claws_valid f [Code.f]` proves the validation law `Laws.Valid.f` of
the current project, as `Proof.Valid.f`, by way of a lemma `Proof.Run.f`
(the statement `Ast.RunStmt.f` claws-ast writes): for any fuel from some
base up, the interpreter returns what `Code.f` computes. From it,
`Proof.Call.f` states what a call of f reads (`semCall`) and joins
`claws_calls`, so a later function that calls f uses it instead of
running f's body again. Validate callees first. A recursive f goes by
induction over `Code.f`. -/
syntax (name := clawsValid) "claws_valid " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : command

@[command_elab clawsValid] def elabClawsValid : CommandElab := fun stx => do
  match stx with
  | `(claws_valid $f [$ls,*]) =>
    let ns ← getCurrNamespace
    let proj := ns.getPrefix
    let fname := f.getId
    let law := proj ++ `Laws ++ `Valid ++ fname
    let runStmt := proj ++ `Ast ++ `RunStmt ++ fname
    let runName := ns ++ `Run ++ fname
    let validName := ns ++ `Valid ++ fname
    let env ← getEnv
    -- Each lemma's base fuel is above every earlier one's, so a caller
    -- always has fuel to spare at a call.
    let earlier := env.constants.fold (init := 0) fun n c _ =>
      if ((ns ++ `Run).isPrefixOf c || (ns ++ `Loop).isPrefixOf c) && !c.isInternal then n + 1 else n
    -- In reserve for callees and loops, above everything proven earlier.
    let reserve := 2 ^ 40 * (earlier + 1)
    let slack := 1000
    let base := reserve + slack
    unless env.contains law do
      throwError "claws_valid: no validation law {law}; does PROOF.lean import the project's Ast?"
    let stmt ← liftTermElabM do
      let some e ← unfoldDefinition? (mkApp (mkConst runStmt) (mkNatLit base))
        | throwError "claws_valid: no statement {runStmt}"
      instantiateMVars (← whnfCore e)
    -- Where the C++ would trap, as at an index out of bounds, the run
    -- needs the function's safety obligation, proven earlier.
    let codeF := proj ++ `Code ++ fname
    let safety := ns ++ `Safety ++ fname
    let safeTac ← if env.contains (codeF ++ `safe) then
        unless env.contains safety do
          throwError "claws_valid: prove {safety} before validating {fname}"
        `(tactic| all_goals claws_safe $(mkIdent safety) $(mkIdent codeF))
      else `(tactic| skip)
    -- A recursive function goes by induction over its translation; the
    -- body's call to itself reads the induction hypothesis.
    let recursive ← liftTermElabM (isRecursive codeF)
    let pf ← liftTermElabM do
      let tac ← if recursive then `(by
          claws_rec_start $(mkIdent codeF)
          all_goals (
            intro_fuel_core $(Syntax.mkNumLit (toString reserve)) $(Syntax.mkNumLit (toString slack))
            claws_prove_start
            all_goals claws_ih
            $safeTac
            claws_prove_finish [$ls,*]))
        else `(by
          intro_fuel_core $(Syntax.mkNumLit (toString reserve)) $(Syntax.mkNumLit (toString slack))
          claws_prove_start
          $safeTac
          claws_prove_finish [$ls,*])
      -- A function's proof splits on each condition it tests; allow it
      -- twenty times a command's time, which `set_option maxHeartbeats`
      -- raises for a function that needs more.
      withTheReader Core.Context (fun c => { c with maxHeartbeats := c.maxHeartbeats * 20 }) do
        let pf ← elabTermEnsuringType tac stmt
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
    liftCoreM <| addDecl <| .thmDecl { name := runName, levelParams := [], type := stmt, value := pf }
    -- At a call, a run reads what the semantics derives (`semCall`); the
    -- lemma `Proof.Call.f` states that, without fuel, for claws_calls.
    let callName := ns ++ `Call ++ fname
    let (cty, cval) ← liftTermElabM do
      forallTelescope stmt fun xs body => do
        let k := xs.size
        let some (_, lhs, rhs) := body.eq? | throwError "claws_valid: {runStmt} is not an equation"
        let args := lhs.getAppArgs
        let lhs' := mkAppN (mkConst ``Claws.Sem.semCall) args[1:]
        let hs := xs[0:k - 2].toArray
        let ty ← mkForallFVars hs (← mkEq lhs' rhs)
        let run := mkAppN (mkConst runName) (hs ++ #[mkNatLit base, mkApp (mkConst ``Nat.le_refl) (mkNatLit base)])
        let val ← mkLambdaFVars hs (← mkAppM ``Claws.Sem.semCall_of_callFn #[run])
        return (ty, val)
    liftCoreM <| addDecl <| .thmDecl { name := callName, levelParams := [], type := cty, value := cval }
    elabCommand (← `(attribute [claws_calls] $(mkIdent callName)))
    let vpf ← liftTermElabM do
      let tac ← `(by
        claws_unfold_law
        intros
        apply Claws.Sem.call_of_callFn (n := $(Syntax.mkNumLit (toString base)))
        rw [$(mkIdent runName):ident]
        all_goals (first | omega | assumption | (simp only [*, Option.getD_some, implies_true, claws_codec]; done)))
      let pf ← elabTermEnsuringType tac (mkConst law)
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars pf
    liftCoreM <| addDecl <| .thmDecl
      { name := validName, levelParams := [], type := mkConst law, value := vpf }
  | _ => throwUnsupportedSyntax

end Claws
