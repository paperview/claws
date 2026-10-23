import Claws.Sem

/-!
# An interpreter for the semantics

`eval`, `exec` and the rest run a program, with `fuel` bounding the
depth of the run. `sound` proves, once, that any result they give is one
the semantics in `Claws.Sem` derives. Nothing here is trusted: a
validation proof runs the interpreter symbolically on a function's AST
and uses `sound` to turn the result into a derivation.

The interpreter is never executed, only unfolded inside proofs, so it
compares memories with classical decidability.
-/

namespace Claws.Sem

set_option linter.unusedVariables false

/-- What a call returns, by the semantics: the result of the derivation
`Call` has, if any. A run reads a call's result here rather than running
the callee, so its fuel bounds only its own body: a proof about a caller
uses a lemma about the callee, and a recursive function's proof its
induction hypothesis, however deep the callee's own run. -/
noncomputable def semCall (P : Prog) (m : Mem) (f : String) (rs : List Res) : Option (Option Val × Mem) :=
  open Classical in
  if h : ∃ p : Option Val × Mem, Call P m f rs p.1 p.2 then some (Classical.choose h) else none

theorem semCall_sound {P : Prog} {m : Mem} {f : String} {rs : List Res} {res : Option Val} {m' : Mem}
    (h : semCall P m f rs = some (res, m')) : Call P m f rs res m' := by
  unfold semCall at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    have := Classical.choose_spec hc
    rw [h] at this
    exact this
  · simp at h

open Classical in
mutual

noncomputable def eval : Nat → Prog → Env → Mem → Expr → Option Res
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, .intLit t k => (literal t k).map .val
  | n + 1, P, e, m, .boolLit b => some (.val (.bool b))
  | n + 1, P, e, m, .enumLit t v => some (.val (.enum t v))
  | n + 1, P, e, m, .var x => (List.lookup x e).map .loc
  | n + 1, P, e, m, .member a f =>
    match eval n P e m a with
    | some (.loc l) => some (.loc ⟨l.addr, l.path ++ [.field f]⟩)
    | some (.val v) => (v.field f).map .val
    | some (.glob x p) => some (.glob x (p ++ [.field f]))
    | none => none
  | n + 1, P, e, m, .cast k t a =>
    match k with
    | .lvalueToRValue =>
      match eval n P e m a with
      | some (.loc l) => (m.read l).map .val
      | some (.glob x p) => (globRead P x p).map .val
      | _ => none
    | .integralCast =>
      match eval n P e m a with
      | some (.val v) => (convert t v).map .val
      | _ => none
    | .integralToBoolean =>
      match eval n P e m a with
      | some (.val v) => (truth v).map (fun b => .val (.bool b))
      | _ => none
    | .noOp => eval n P e m a
    | .other _ => none
  | n + 1, P, e, m, .unary op a =>
    match eval n P e m a with
    | some (.val v) => (unop op v).map .val
    | _ => none
  | n + 1, P, e, m, .binary op a b =>
    match eval n P e m a, eval n P e m b with
    | some (.val va), some (.val vb) => (binop op va vb).map .val
    | _, _ => none
  -- A branch on the left operand, as C++ evaluates the right one only
  -- when it matters. When both evaluate, a proof rewrites the branch back
  -- into a Boolean expression (`Claws.Sem.land_collapse`); when the right
  -- one is defined only where the left holds, the branch is what lets
  -- the proof go on.
  | n + 1, P, e, m, .land a b =>
    match eval n P e m a with
    | some (.val (.bool x)) =>
      if x then
        match eval n P e m b with
        | some (.val (.bool y)) => some (.val (.bool y))
        | _ => none
      else some (.val (.bool false))
    | _ => none
  | n + 1, P, e, m, .lor a b =>
    match eval n P e m a with
    | some (.val (.bool x)) =>
      if x then some (.val (.bool true))
      else
        match eval n P e m b with
        | some (.val (.bool y)) => some (.val (.bool y))
        | _ => none
    | _ => none
  | n + 1, P, e, m, .cond c a b =>
    match eval n P e m c with
    | some (.val (.bool x)) =>
      match eval n P e m a, eval n P e m b with
      | some ra, some rb => some (if x then ra else rb)
      | _, _ => if x then eval n P e m a else eval n P e m b
    | _ => none
  | n + 1, P, e, m, .call f args =>
    match evalArgs n P e m args with
    | some rs =>
      match semCall P m f rs with
      | some (some v, m') => if m' = m then some (.val v) else none
      | _ => none
    | none => none
  | n + 1, P, e, m, .copy a =>
    match eval n P e m a with
    | some (.loc l) => (m.read l).map .val
    | some (.val v) => some (.val v)
    | some (.glob x p) => (globRead P x p).map .val
    | none => none
  | n + 1, P, e, m, .global x => (List.lookup x P.globals).map fun _ => .glob x []
  | n + 1, P, e, m, .subscript a i =>
    match eval n P e m a, eval n P e m i with
    | some (.glob x p), some (.val k) =>
      match k.index, globRead P x p with
      | some j, some (.vec xs) => if j < xs.length then some (.glob x (p ++ [.index j])) else none
      | _, _ => none
    | _, _ => none
  | n + 1, P, e, m, .initList t es =>
    match evalList n P e m es with
    | some vs => (aggregate P t vs).map .val
    | none => none
  | n + 1, P, e, m, .paren a => eval n P e m a
  | n + 1, P, e, m, .listMatch xs onNil onCons =>
    match eval n P e m xs with
    | some r =>
      match m.value P r with
      | some (.list []) =>
        match List.lookup onNil P.funcs with
        | some fn =>
          match bindParams fn.params [] e m with
          | some (e₀, m₀) =>
            match exec n P e₀ m₀ fn.body with
            | some o =>
              match finish fn.ret m.length o with
              | some (some v, m') => if m' = m then some (.val v) else none
              | _ => none
            | none => none
          | none => none
        | none => none
      | some (.list (w :: ws)) =>
        match List.lookup onCons P.funcs with
        | some fn =>
          match bindParams fn.params [.val w, .val (.list ws)] e m with
          | some (e₀, m₀) =>
            match exec n P e₀ m₀ fn.body with
            | some o =>
              match finish fn.ret m.length o with
              | some (some v, m') => if m' = m then some (.val v) else none
              | _ => none
            | none => none
          | none => none
        | none => none
      | _ => none
    | none => none
  | n + 1, P, e, m, .builtin f as =>
    match f, as with
    | .size, [a] =>
      match eval n P e m a with
      | some (.loc l) =>
        match m.read l with
        | some (.vec xs) => some (.val (.uint (BitVec.ofNat 32 xs.length)))
        | _ => none
      | _ => none
    | .index, [a, i] =>
      match eval n P e m a, eval n P e m i with
      | some (.loc l), some (.val (.uint k)) =>
        match m.read l with
        | some (.vec xs) =>
          if k.toNat < xs.length then some (.loc ⟨l.addr, l.path ++ [.index k.toNat]⟩) else none
        | _ => none
      | _, _ => none
    | .vecEmpty, [] => some (.val (.vec []))
    | .listNil, [] => some (.val (.list []))
    | .cons, [a, b] =>
      match eval n P e m a, eval n P e m b with
      | some ra, some rb =>
        match m.value P ra, m.value P rb with
        | some w, some (.list ws) => some (.val (.list (w :: ws)))
        | _, _ => none
      | _, _ => none
    | .vecFill, [a, x] =>
      match eval n P e m a, eval n P e m x with
      | some (.val (.uint k)), some r => (m.value P r).map fun w => .val (.vec (List.replicate k.toNat w))
      | _, _ => none
    | _, _ => none
  | n + 1, P, e, m, .assign _ _ => none
  | n + 1, P, e, m, .compound _ _ _ _ _ => none
  | n + 1, P, e, m, .incdec _ _ _ => none
  | n + 1, P, e, m, .other _ => none

noncomputable def evalList : Nat → Prog → Env → Mem → List Expr → Option (List Val)
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, [] => some []
  | n + 1, P, e, m, a :: rest =>
    match eval n P e m a, evalList n P e m rest with
    | some (.val v), some vs => some (v :: vs)
    | _, _ => none

noncomputable def evalArgs : Nat → Prog → Env → Mem → List Expr → Option (List Res)
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, [] => some []
  | n + 1, P, e, m, a :: rest =>
    match eval n P e m a, evalArgs n P e m rest with
    | some r, some rs => some (r :: rs)
    | _, _ => none

noncomputable def evalTop : Nat → Prog → Env → Mem → Expr → Option (Res × Mem)
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, a =>
    match a with
    | .call f args =>
      match evalArgs n P e m args with
      | some rs =>
        match semCall P m f rs with
        | some (some v, m') => some (.val v, m')
        | _ => none
      | none => none
    | a => (eval n P e m a).map (·, m)

/-- Call a function of the program on arguments. -/
noncomputable def callFn : Nat → Prog → Mem → String → List Res → Option (Option Val × Mem)
  | 0, _, _, _, _ => none
  | n + 1, P, m, f, rs =>
    match List.lookup f P.funcs with
    | some fn =>
      match bindParams fn.params rs [] m with
      | some (e₀, m₀) =>
        match exec n P e₀ m₀ fn.body with
        | some o => finish fn.ret m.length o
        | none => none
      | none => none
    | none => none

noncomputable def exec : Nat → Prog → Env → Mem → Stmt → Option Outcome
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, .decl x _ a =>
    match evalTop n P e m a with
    | some (.val v, m') => some (.normal ((x, ⟨m'.length, []⟩) :: e) (m' ++ [v]))
    | _ => none
  | n + 1, P, e, m, .expr a =>
    match a with
    | .call f args =>
      match evalArgs n P e m args with
      | some rs =>
        match semCall P m f rs with
        | some (_, m') => some (.normal e m')
        | none => none
      | none => none
    | .assign a b =>
      match evalTop n P e m b with
      | some (.val v, m₁) =>
        match eval n P e m₁ a with
        | some (.loc l) => (m₁.write l v).map (.normal e ·)
        | _ => none
      | _ => none
    | .compound op t comp a b =>
      match eval n P e m b, eval n P e m a with
      | some (.val vb), some (.loc l) =>
        match m.read l with
        | some va =>
          match convert comp va with
          | some va' =>
            match binop op va' vb with
            | some r =>
              match convert t r with
              | some w => (m.write l w).map (.normal e ·)
              | none => none
            | none => none
          | none => none
        | none => none
      | _, _ => none
    | .incdec inc _ a =>
      match eval n P e m a with
      | some (.loc l) =>
        match m.read l with
        | some v =>
          match binop (if inc then .add else .sub) (promote v) (one (promote v)) with
          | some r =>
            match convert v.ty r with
            | some w => (m.write l w).map (.normal e ·)
            | none => none
          | none => none
        | none => none
      | _ => none
    | .builtin .expects [c] =>
      match eval n P e m c with
      | some (.val (.bool x)) => if x then some (.normal e m) else none
      | _ => none
    | .builtin .decreases [a] =>
      match eval n P e m a with
      | some (.val _) => some (.normal e m)
      | _ => none
    | .builtin .push [a, x] =>
      match eval n P e m a, eval n P e m x with
      | some (.loc l), some r =>
        match m.value P r, m.read l with
        | some w, some (.vec xs) =>
          if xs.length < 2 ^ 32 - 1 then (m.write l (.vec (xs ++ [w]))).map (.normal e ·) else none
        | _, _ => none
      | _, _ => none
    | a =>
      match eval n P e m a with
      | some _ => some (.normal e m)
      | none => none
  | n + 1, P, e, m, .ret a =>
    match evalTop n P e m a with
    | some (.val v, m') => some (.ret (some v) m')
    | _ => none
  | n + 1, P, e, m, .retVoid => some (.ret none m)
  | n + 1, P, e, m, .ite c t f =>
    match eval n P e m c with
    | some (.val (.bool x)) => if x then exec n P e m t else exec n P e m f
    | _ => none
  | n + 1, P, e, m, .block ss =>
    match execList n P e m ss with
    | some (.normal e' m') => some (.normal (close e' e) (m'.take m.length))
    | some (.brk e' m') => some (.brk (close e' e) (m'.take m.length))
    | some (.cont e' m') => some (.cont (close e' e) (m'.take m.length))
    | some (.ret v m') => some (.ret v (m'.take m.length))
    | none => none
  | n + 1, P, e, m, .switch c body =>
    match eval n P e m c with
    | some (.val v) =>
      match pick v body with
      | some i =>
        match execList n P e m (body.drop i) with
        | some (.normal e' m') => some (.normal (close e' e) (m'.take m.length))
        | some (.brk e' m') => some (.normal (close e' e) (m'.take m.length))
        | some (.cont e' m') => some (.cont (close e' e) (m'.take m.length))
        | some (.ret w m') => some (.ret w (m'.take m.length))
        | none => none
      | none => some (.normal e m)
    | _ => none
  | n + 1, P, e, m, .caseLabel _ => some (.normal e m)
  | n + 1, P, e, m, .defaultLabel => some (.normal e m)
  | n + 1, P, e, m, .brk => some (.brk e m)
  | n + 1, P, e, m, .cont => some (.cont e m)
  | n + 1, P, e, m, .loop c body step => execLoop n P e m c body step
  | n + 1, P, e, m, .other _ => none

/-- A loop, run apart from `exec` so that a proof can leave it folded: a
lemma about the loop, proven by induction, takes its place. -/
noncomputable def execLoop : Nat → Prog → Env → Mem → Expr → Stmt → Stmt → Option Outcome
  | 0, _, _, _, _, _, _ => none
  | n + 1, P, e, m, c, body, step =>
    match eval n P e m c with
    | some (.val (.bool x)) =>
      if x then
        match exec n P e m body with
        | some (.normal e₁ m₁) =>
          match exec n P e₁ m₁ step with
          | some (.normal e₂ m₂) => execLoop n P e₂ m₂ c body step
          | _ => none
        | some (.cont e₁ m₁) =>
          match exec n P e₁ m₁ step with
          | some (.normal e₂ m₂) => execLoop n P e₂ m₂ c body step
          | _ => none
        | some (.brk e₁ m₁) => some (.normal e₁ m₁)
        | some (.ret v m₁) => some (.ret v m₁)
        | none => none
      else some (.normal e m)
    | _ => none

noncomputable def execList : Nat → Prog → Env → Mem → List Stmt → Option Outcome
  | 0, _, _, _, _ => none
  | n + 1, P, e, m, [] => some (.normal e m)
  | n + 1, P, e, m, st :: rest =>
    match exec n P e m st with
    | some (.normal e' m') => execList n P e' m' rest
    | some (.brk e' m') => some (.brk e' m')
    | some (.cont e' m') => some (.cont e' m')
    | some (.ret v m') => some (.ret v m')
    | none => none

end

theorem eval_expects (n : Nat) (P : Prog) (e : Env) (m : Mem) (as : List Expr) :
    eval n P e m (.builtin .expects as) = none := by
  cases n <;> rfl

theorem eval_decreases (n : Nat) (P : Prog) (e : Env) (m : Mem) (as : List Expr) :
    eval n P e m (.builtin .decreases as) = none := by
  cases n <;> rfl

theorem eval_push (n : Nat) (P : Prog) (e : Env) (m : Mem) (as : List Expr) :
    eval n P e m (.builtin .push as) = none := by
  cases n <;> rfl

theorem sound (n : Nat) :
    (∀ P e m a r, eval n P e m a = some r → Eval P e m a r) ∧
    (∀ P e m as vs, evalList n P e m as = some vs → EvalList P e m as vs) ∧
    (∀ P e m as rs, evalArgs n P e m as = some rs → EvalArgs P e m as rs) ∧
    (∀ P e m a r m', evalTop n P e m a = some (r, m') → EvalTop P e m a r m') ∧
    (∀ P m f rs res m', callFn n P m f rs = some (res, m') → Call P m f rs res m') ∧
    (∀ P e m st o, exec n P e m st = some o → Exec P e m st o) ∧
    (∀ P e m ss o, execList n P e m ss = some o → ExecList P e m ss o) ∧
    (∀ P e m c body step o, execLoop n P e m c body step = some o → Exec P e m (.loop c body step) o) := by
  induction n with
  | zero => exact ⟨by simp [eval], by simp [evalList], by simp [evalArgs], by simp [evalTop],
      by simp [callFn], by simp [exec], by simp [execList], by simp [execLoop]⟩
  | succ n ih =>
    obtain ⟨ihE, ihL, ihA, ihT, ihC, ihX, ihXL, ihLp⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P e m a r h
      cases a with
      | intLit t k =>
        simp only [eval, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        exact .lit hv
      | boolLit b =>
        simp only [eval, Option.some.injEq] at h
        subst h; exact .boolLit
      | enumLit t v =>
        simp only [eval, Option.some.injEq] at h
        subst h; exact .enumLit
      | var x =>
        simp only [eval, Option.map_eq_some_iff] at h
        obtain ⟨l, hl, rfl⟩ := h
        exact .var hl
      | member a f =>
        simp only [eval] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact .memberLoc (ihE _ _ _ _ _ (by assumption))
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .memberVal (ihE _ _ _ _ _ (by assumption)) hw
        · simp only [Option.some.injEq] at h; subst h; exact .memberGlob (ihE _ _ _ _ _ (by assumption))
        · simp at h
      | cast k t a =>
        cases k with
        | lvalueToRValue =>
          simp only [eval] at h
          split at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨w, hw, rfl⟩ := h
            exact .load (ihE _ _ _ _ _ (by assumption)) hw
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨w, hw, rfl⟩ := h
            exact .loadGlob (ihE _ _ _ _ _ (by assumption)) hw
          · simp at h
        | integralCast =>
          simp only [eval] at h
          split at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨w, hw, rfl⟩ := h
            exact .integral (ihE _ _ _ _ _ (by assumption)) hw
          · simp at h
        | integralToBoolean =>
          simp only [eval] at h
          split at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨w, hw, rfl⟩ := h
            exact .toBool (ihE _ _ _ _ _ (by assumption)) hw
          · simp at h
        | noOp =>
          simp only [eval] at h
          exact .noOp (ihE _ _ _ _ _ h)
        | other _ => simp [eval] at h
      | unary op a =>
        simp only [eval] at h
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .unary (ihE _ _ _ _ _ (by assumption)) hw
        · simp at h
      | binary op a b =>
        simp only [eval] at h
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .binary (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption)) hw
        · simp at h
      | land a b =>
        simp only [eval] at h
        split at h
        · rename_i x ha
          cases x
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
            subst h; exact .landF (ihE _ _ _ _ _ ha)
          · simp only [↓reduceIte] at h
            split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .landT (ihE _ _ _ _ _ ha) (ihE _ _ _ _ _ (by assumption))
            · simp at h
        · simp at h
      | lor a b =>
        simp only [eval] at h
        split at h
        · rename_i x ha
          cases x
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .lorF (ihE _ _ _ _ _ ha) (ihE _ _ _ _ _ (by assumption))
            · simp at h
          · simp only [↓reduceIte, Option.some.injEq] at h
            subst h; exact .lorT (ihE _ _ _ _ _ ha)
        · simp at h
      | cond c a b =>
        simp only [eval] at h
        split at h
        · rename_i x hc
          split at h
          · rename_i ra rb ha hb
            simp only [Option.some.injEq] at h; subst h
            cases x
            · exact .condF (ihE _ _ _ _ _ hc) (ihE _ _ _ _ _ hb)
            · exact .condT (ihE _ _ _ _ _ hc) (ihE _ _ _ _ _ ha)
          · cases x
            · simp only [Bool.false_eq_true, ↓reduceIte] at h
              exact .condF (ihE _ _ _ _ _ hc) (ihE _ _ _ _ _ h)
            · simp only [↓reduceIte] at h
              exact .condT (ihE _ _ _ _ _ hc) (ihE _ _ _ _ _ h)
        · simp at h
      | call f args =>
        simp only [eval] at h
        split at h
        · rename_i rs hrs
          split at h
          · rename_i v m' hc
            split at h
            · rename_i hm
              subst hm
              simp only [Option.some.injEq] at h; subst h
              exact .call (ihA _ _ _ _ _ hrs) (semCall_sound hc)
            · simp at h
          · simp at h
        · simp at h
      | copy a =>
        simp only [eval] at h
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .copy (ihE _ _ _ _ _ (by assumption)) hw
        · simp only [Option.some.injEq] at h; subst h
          exact .copyVal (ihE _ _ _ _ _ (by assumption))
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .copyGlob (ihE _ _ _ _ _ (by assumption)) hw
        · simp at h
      | global x =>
        simp only [eval, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        exact .global hv
      | subscript a i =>
        simp only [eval] at h
        split at h
        · split at h
          · split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .subscript (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption))
                (by assumption) (by assumption) (by assumption)
            · simp at h
          · simp at h
        · simp at h
      | initList t es =>
        simp only [eval] at h
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨w, hw, rfl⟩ := h
          exact .initList (ihL _ _ _ _ _ (by assumption)) hw
        · simp at h
      | paren a =>
        simp only [eval] at h
        exact .paren (ihE _ _ _ _ _ h)
      | listMatch xs onNil onCons =>
        simp only [eval] at h
        split at h
        · rename_i r hr
          split at h
          · split at h
            · rename_i fn hf
              split at h
              · rename_i e₀ m₀ hb
                split at h
                · rename_i o ho
                  split at h
                  · rename_i v m' hfin
                    split at h
                    · rename_i hm
                      subst hm
                      simp only [Option.some.injEq] at h; subst h
                      exact .matchNil (ihE _ _ _ _ _ hr) (by assumption) hf hb (ihX _ _ _ _ _ ho) hfin
                    · simp at h
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · split at h
            · rename_i fn hf
              split at h
              · rename_i e₀ m₀ hb
                split at h
                · rename_i o ho
                  split at h
                  · rename_i v m' hfin
                    split at h
                    · rename_i hm
                      subst hm
                      simp only [Option.some.injEq] at h; subst h
                      exact .matchCons (ihE _ _ _ _ _ hr) (by assumption) hf hb (ihX _ _ _ _ _ ho) hfin
                    · simp at h
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      | builtin f args =>
        cases f with
        | size =>
          match args with
          | [a] =>
            simp only [eval] at h
            split at h
            · split at h
              · simp only [Option.some.injEq] at h; subst h
                exact .size (ihE _ _ _ _ _ (by assumption)) (by assumption)
              · simp at h
            · simp at h
          | [] => simp [eval] at h
          | _ :: _ :: _ => simp [eval] at h
        | index =>
          match args with
          | [a, i] =>
            simp only [eval] at h
            split at h
            · split at h
              · split at h
                · simp only [Option.some.injEq] at h; subst h
                  exact .index (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption))
                    (by assumption) (by assumption)
                · simp at h
              · simp at h
            · simp at h
          | [] => simp [eval] at h
          | [_] => simp [eval] at h
          | _ :: _ :: _ :: _ => simp [eval] at h
        | vecEmpty =>
          match args with
          | [] =>
            simp only [eval, Option.some.injEq] at h; subst h; exact .vecEmpty
          | _ :: _ => simp [eval] at h
        | vecFill =>
          match args with
          | [a, x] =>
            simp only [eval] at h
            split at h
            · simp only [Option.map_eq_some_iff] at h
              obtain ⟨w, hw, rfl⟩ := h
              exact .vecFill (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption)) hw
            · simp at h
          | [] => simp [eval] at h
          | [_] => simp [eval] at h
          | _ :: _ :: _ :: _ => simp [eval] at h
        | listNil =>
          match args with
          | [] =>
            simp only [eval, Option.some.injEq] at h; subst h; exact .listNil
          | _ :: _ => simp [eval] at h
        | cons =>
          match args with
          | [a, b] =>
            simp only [eval] at h
            split at h
            · split at h
              · simp only [Option.some.injEq] at h; subst h
                exact .cons (ihE _ _ _ _ _ (by assumption)) (by assumption) (ihE _ _ _ _ _ (by assumption))
                  (by assumption)
              · simp at h
            · simp at h
          | [] => simp [eval] at h
          | [_] => simp [eval] at h
          | _ :: _ :: _ :: _ => simp [eval] at h
        | expects => simp [eval_expects] at h
        | decreases => simp [eval_decreases] at h
        | push => simp [eval_push] at h
        | other _ => simp [eval] at h
      | assign _ _ => simp [eval] at h
      | compound _ _ _ _ _ => simp [eval] at h
      | incdec _ _ _ => simp [eval] at h
      | other _ => simp [eval] at h
    · intro P e m as vs h
      cases as with
      | nil =>
        simp only [evalList, Option.some.injEq] at h
        subst h; exact .nil
      | cons a rest =>
        simp only [evalList] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .cons (ihE _ _ _ _ _ (by assumption)) (ihL _ _ _ _ _ (by assumption))
        · simp at h
    · intro P e m as rs h
      cases as with
      | nil =>
        simp only [evalArgs, Option.some.injEq] at h
        subst h; exact .nil
      | cons a rest =>
        simp only [evalArgs] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .cons (ihE _ _ _ _ _ (by assumption)) (ihA _ _ _ _ _ (by assumption))
        · simp at h
    · intro P e m a r m' h
      simp only [evalTop] at h
      split at h
      · split at h
        · rename_i rs hrs
          split at h
          · rename_i v m₁ hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .call (ihA _ _ _ _ _ hrs) (semCall_sound hc)
          · simp at h
        · simp at h
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨r', hr, rfl, rfl⟩ := h
        exact .pure (ihE _ _ _ _ _ hr)
    · intro P m f rs res m' h
      simp only [callFn] at h
      split at h
      · rename_i fn hf
        split at h
        · rename_i e₀ m₀ hb
          split at h
          · rename_i o ho
            exact .mk hf hb (ihX _ _ _ _ _ ho) h
          · simp at h
        · simp at h
      · simp at h
    · intro P e m st o h
      cases st with
      | decl x t a =>
        simp only [exec] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .decl (ihT _ _ _ _ _ _ (by assumption))
        · simp at h
      | expr a =>
        cases a with
        | call f args =>
          simp only [exec] at h
          split at h
          · split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .exprCall (ihA _ _ _ _ _ (by assumption)) (semCall_sound (by assumption))
            · simp at h
          · simp at h
        | assign a b =>
          simp only [exec] at h
          split at h
          · split at h
            · simp only [Option.map_eq_some_iff] at h
              obtain ⟨m', hw, rfl⟩ := h
              exact .assign (ihT _ _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption)) hw
            · simp at h
          · simp at h
        | compound op t comp a b =>
          simp only [exec] at h
          split at h
          · split at h
            · split at h
              · split at h
                · split at h
                  · simp only [Option.map_eq_some_iff] at h
                    obtain ⟨m', hw, rfl⟩ := h
                    exact .compound (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption))
                      (by assumption) (by assumption) (by assumption) (by assumption) hw
                  · simp at h
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        | incdec inc post a =>
          simp only [exec] at h
          split at h
          · split at h
            · split at h
              · split at h
                · simp only [Option.map_eq_some_iff] at h
                  obtain ⟨m', hw, rfl⟩ := h
                  exact .incdec (ihE _ _ _ _ _ (by assumption)) (by assumption) (by assumption)
                    (by assumption) hw
                · simp at h
              · simp at h
            · simp at h
          · simp at h
        | builtin f args =>
          cases f with
          | expects =>
            match args with
            | [c] =>
              simp only [exec] at h
              split at h
              · rename_i x hc
                cases x
                · simp at h
                · simp only [↓reduceIte, Option.some.injEq] at h; subst h
                  exact .expects (ihE _ _ _ _ _ hc)
              · simp at h
            | [] => simp [exec, eval_expects, eval_decreases, eval_push] at h
            | _ :: _ :: _ => simp [exec, eval_expects, eval_decreases, eval_push] at h
          | decreases =>
            match args with
            | [a] =>
              simp only [exec] at h
              split at h
              · simp only [Option.some.injEq] at h; subst h
                exact .decreases (ihE _ _ _ _ _ (by assumption))
              · simp at h
            | [] => simp [exec, eval_expects, eval_decreases, eval_push] at h
            | _ :: _ :: _ => simp [exec, eval_expects, eval_decreases, eval_push] at h
          | push =>
            match args with
            | [a, x] =>
              simp only [exec] at h
              split at h
              · split at h
                · split at h
                  · simp only [Option.map_eq_some_iff] at h
                    obtain ⟨m', hw, rfl⟩ := h
                    exact .push (ihE _ _ _ _ _ (by assumption)) (ihE _ _ _ _ _ (by assumption))
                      (by assumption) (by assumption) (by assumption) hw
                  · simp at h
                · simp at h
              · simp at h
            | [] => simp [exec, eval_push] at h
            | [_] => simp [exec, eval_push] at h
            | _ :: _ :: _ :: _ => simp [exec, eval_push] at h
          | _ =>
            simp only [exec] at h
            split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .expr (ihE _ _ _ _ _ (by assumption))
            · simp at h
        | _ =>
          simp only [exec] at h
          split at h
          · simp only [Option.some.injEq] at h; subst h
            exact .expr (ihE _ _ _ _ _ (by assumption))
          · simp at h
      | ret a =>
        simp only [exec] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .ret (ihT _ _ _ _ _ _ (by assumption))
        · simp at h
      | retVoid =>
        simp only [exec, Option.some.injEq] at h; subst h; exact .retVoid
      | ite c t f =>
        simp only [exec] at h
        split at h
        · rename_i x hc
          cases x
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            exact .iteF (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ h)
          · simp only [↓reduceIte] at h
            exact .iteT (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ h)
        · simp at h
      | block ss =>
        simp only [exec] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact .blockNormal (ihXL _ _ _ _ _ (by assumption))
        · simp only [Option.some.injEq] at h; subst h
          exact .blockBrk (ihXL _ _ _ _ _ (by assumption))
        · simp only [Option.some.injEq] at h; subst h
          exact .blockCont (ihXL _ _ _ _ _ (by assumption))
        · simp only [Option.some.injEq] at h; subst h
          exact .blockRet (ihXL _ _ _ _ _ (by assumption))
        · simp at h
      | switch c body =>
        simp only [exec] at h
        split at h
        · rename_i v hc
          split at h
          · rename_i i hp
            split at h
            · simp only [Option.some.injEq] at h; subst h
              exact .switchNormal (ihE _ _ _ _ _ hc) hp (ihXL _ _ _ _ _ (by assumption))
            · simp only [Option.some.injEq] at h; subst h
              exact .switchBrk (ihE _ _ _ _ _ hc) hp (ihXL _ _ _ _ _ (by assumption))
            · simp only [Option.some.injEq] at h; subst h
              exact .switchCont (ihE _ _ _ _ _ hc) hp (ihXL _ _ _ _ _ (by assumption))
            · simp only [Option.some.injEq] at h; subst h
              exact .switchRet (ihE _ _ _ _ _ hc) hp (ihXL _ _ _ _ _ (by assumption))
            · simp at h
          · simp only [Option.some.injEq] at h; subst h
            exact .switchNone (ihE _ _ _ _ _ hc) (by assumption)
        · simp at h
      | caseLabel _ =>
        simp only [exec, Option.some.injEq] at h; subst h; exact .caseLabel
      | defaultLabel =>
        simp only [exec, Option.some.injEq] at h; subst h; exact .defaultLabel
      | brk =>
        simp only [exec, Option.some.injEq] at h; subst h; exact .brk
      | cont =>
        simp only [exec, Option.some.injEq] at h; subst h; exact .cont
      | loop c body step =>
        simp only [exec] at h
        cases n with
        | zero => simp [execLoop] at h
        | succ n => exact ihLp _ _ _ _ _ _ _ h
      | other _ => simp [exec] at h
    · intro P e m ss o h
      cases ss with
      | nil =>
        simp only [execList, Option.some.injEq] at h
        subst h; exact .nil
      | cons st rest =>
        simp only [execList] at h
        split at h
        · exact .next (ihX _ _ _ _ _ (by assumption)) (ihXL _ _ _ _ _ h)
        · simp only [Option.some.injEq] at h; subst h
          exact .brk (ihX _ _ _ _ _ (by assumption))
        · simp only [Option.some.injEq] at h; subst h
          exact .cont (ihX _ _ _ _ _ (by assumption))
        · simp only [Option.some.injEq] at h; subst h
          exact .ret (ihX _ _ _ _ _ (by assumption))
        · simp at h
    · intro P e m c body step o h
      simp only [execLoop] at h
      split at h
      · rename_i x hc
        cases x
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; subst h
          exact .loopF (ihE _ _ _ _ _ hc)
        · simp only [↓reduceIte] at h
          split at h
          · split at h
            · exact .loopNext (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ (by assumption))
                (ihX _ _ _ _ _ (by assumption)) (ihLp _ _ _ _ _ _ _ h)
            · simp at h
          · split at h
            · exact .loopCont (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ (by assumption))
                (ihX _ _ _ _ _ (by assumption)) (ihLp _ _ _ _ _ _ _ h)
            · simp at h
          · simp only [Option.some.injEq] at h; subst h
            exact .loopBrk (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ (by assumption))
          · simp only [Option.some.injEq] at h; subst h
            exact .loopRet (ihE _ _ _ _ _ hc) (ihX _ _ _ _ _ (by assumption))
          · simp at h
      · simp at h

theorem call_of_callFn (h : callFn n P m f rs = some (res, m')) : Call P m f rs res m' :=
  (sound n).2.2.2.2.1 _ _ _ _ _ _ h

/- Validation proofs run the interpreter by rewriting with its equations.
Kept irreducible from here on, it cannot also be run by reduction, which
simp otherwise does to test a `match` on a call of it, one step of fuel
at a time. -/
attribute [irreducible] semCall eval evalList evalArgs evalTop callFn exec execList execLoop

end Claws.Sem
