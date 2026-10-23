import Claws.Validate

/-!
# Loops

`claws_loop f N` proves what the loop `f.loopN` does, as a lemma
`Proof.Loop.f.loopN`: whatever addresses hold the variables the loop
mentions, running the loop with enough fuel leaves each variable the
translation's loop function `Code.f.loopN` returns holding the value it
returns. The proof is by induction over `Code.f.loopN`
(`fun_induction`): one pass of the body runs through the interpreter, and
the induction hypothesis covers the rest.

A `for` loop's counter is the loop function's last parameter, and it
ends with some value the lemma does not name: the block around the loop
ends it.

`claws_loop_use` rewrites a loop in the goal with such a lemma, or with
the induction hypothesis inside the proof of one. The lemmas are proof
aids, not trusted: a wrong one fails to prove.
-/

namespace Claws.Sem

open Lean Meta Elab Tactic Command Term

initialize registerTraceClass `claws.loop

/-- The strings of a list literal definition, such as `f.loop1.mods`. -/
partial def listStrings (e : Lean.Expr) : List String :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, .lit (.strVal s), rest]) => s :: listStrings rest
  | _ => []

def constStrings (n : Name) : MetaM (List String) := do
  let some (.defnInfo d) := (← getEnv).find? n | throwError "claws_loop: no definition {n}"
  return listStrings d.value

def constString (n : Name) : MetaM String := do
  let some (.defnInfo d) := (← getEnv).find? n | throwError "claws_loop: no definition {n}"
  let .lit (.strVal s) := d.value | throwError "claws_loop: {n} is not a string"
  return s

/-- The encoding of a value of Lean type `t` as a `Val`. -/
partial def encoderOf (proj : Name) (t : Lean.Expr) : MetaM Lean.Expr := do
  let t ← whnfR t
  if t.isAppOfArity ``Array 1 then
    return ← mkAppOptM ``Val.ofArray #[t.getArg! 0, ← encoderOf proj (t.getArg! 0)]
  if t.isAppOfArity ``List 1 then
    return ← mkAppOptM ``Val.ofList #[t.getArg! 0, ← encoderOf proj (t.getArg! 0)]
  if t == Lean.mkConst ``Bool then return Lean.mkConst ``Val.bool
  if t.isAppOfArity ``BitVec 1 then
    let w ← whnf (t.getArg! 0)
    match w.rawNatLit? with
    | some 32 => return Lean.mkConst ``Val.uint
    | some 8 => return Lean.mkConst ``Val.uchar
    | _ => throwError "claws_loop: no encoding for {t}"
  let some n := t.constName? | throwError "claws_loop: no encoding for {t}"
  return Lean.mkConst (proj ++ `Ast ++ Name.mkSimple n.getString! ++ `toVal)

/-- A `false` branch of a safety check holds only when its condition
fails. -/
theorem ite_false_eq_true {c : Prop} [Decidable c] {x : Bool} :
    ((if c then false else x) = true) = (¬c ∧ x = true) := by
  by_cases h : c <;> simp [h]

/-- Unfold one step of a loop's safety `c`, in the hypothesis that states
it: `c` is recursive, so simp would unfold it forever. The step's
conditions, such as an index in bounds, become hypotheses. -/
elab "claws_unfold_safe " c:ident : tactic => do
  let cn ← realizeGlobalConstNoOverloadWithInfo c
  let g ← getMainGoal
  let some h ← g.withContext do
      return (← getLCtx).decls.toList.findSome? fun
        | some d =>
          if !d.isImplementationDetail && ((d.type.eq?.map (·.2.1.isAppOf cn)).getD false) then
            some d.fvarId
          else none
        | none => none
    | return
  let (_, g) ← g.revert #[h]
  replaceMainGoal [g]
  -- The preconditions of the functions the step calls, to unfold.
  -- A loop's safety is defined by well-founded recursion, so its body is
  -- in its equation, not its value.
  let some eqns ← getEqnsFor? cn | throwError "claws_unfold_safe: no equations for {cn}"
  let mut pres : Array Name := #[]
  for e in eqns do
    let some info := (← getEnv).find? e | continue
    for n in info.type.getUsedConstants do
      if n.getString! == "pre" && !pres.contains n then pres := pres.push n
  let preIds : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← pres.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  -- The list must not be empty: an empty splice leaves a stray comma.
  let bne ← `(Lean.Parser.Tactic.simpLemma| bne_iff_ne)
  let ls : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems (#[bne] ++ preIds)
  evalTactic (← `(tactic| (
    rw [$c:ident]
    intro hsafe
    -- The pass's path conditions, from the induction, in the form the
    -- check states its own (`a < b`, not `a.ult b = true`), so they settle
    -- its branches: on one path the check is facts, not implications,
    -- which simp would otherwise try at every step of the run.
    try simp only [↓reduceDIte, claws_safe] at *
    try simp only [*, $ls,*, ↓reduceDIte, claws_safe] at hsafe
    -- Each conjunct simplifies the next, which settles `A ∧ (A → B)`.
    try simp (config := { contextual := true }) only [↓reduceDIte, claws_safe] at hsafe
    repeat (obtain ⟨_, hsafe⟩ := hsafe)
    -- A few more rounds: the parts split off settle the premises of
    -- what is left. An implication left in the context is a rewrite with
    -- side conditions, tried at every step of the run.
    iterate 3 (try (
      simp only [*, ↓reduceDIte, claws_safe] at hsafe
      repeat (obtain ⟨_, hsafe⟩ := hsafe)))
    -- A path the check rules out ends here, before any run.
    try claws_absurd)))

/-- How a loop that may `return` ends: normally, or returning `v`; in
either case with the objects `m`. -/
def loopOutcome (r : Option Val) (e : Env) (m : Mem) : Outcome :=
  match r with
  | none => .normal e m
  | some v => .ret (some v) m

@[claws_interp] theorem loopOutcome_none (e : Env) (m : Mem) : loopOutcome none e m = .normal e m := rfl
@[claws_interp] theorem loopOutcome_some (v : Val) (e : Env) (m : Mem) :
    loopOutcome (some v) e m = .ret (some v) m := rfl

/-- The number of distinct loops in `e`. Each subterm is visited once: a
run's terms share subterms, and a walk of the tree they unfold to takes
exponential time. -/
def countLoops (e : Lean.Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo := [e]
  let mut n := 0
  for _ in [0:1000000] do
    let x :: rest := todo | break
    todo := rest
    if seen.contains x then continue
    seen := seen.insert x
    if x.isAppOfArity ``execLoop 7 then n := n + 1
    todo := match x with
      | .app f a => f :: a :: todo
      | .lam _ t b _ | .forallE _ t b _ => t :: b :: todo
      | .letE _ t v b _ => t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => b :: todo
      | _ => todo
  return n

/-- A loop's last pass, where its condition fails: run it once more. A
`while` loop's translation tests the condition again before it
recurses, so where it stops the semantics still takes this step. Fails
unless a loop is gone afterwards, so it never runs a body again where a
lemma should have applied. -/
elab "claws_loop_exit" : tactic => do
  let before := countLoops (← instantiateMVars (← getMainTarget))
  evalTactic (← `(tactic| (rw [Claws.Sem.execLoop]; (try claws_run [Claws.Sem.eval] at *))))
  let gs ← getGoals
  let after ← gs.foldlM (init := 0) fun n g => do return n + countLoops (← instantiateMVars (← g.getType))
  unless gs.length ≤ 1 && after < before do
    throwError "claws_loop_exit: the loop does not end here"

/-- `x.1`, `x.2.1`, ..., the k-th of `total` components of a tuple. -/
def component (x : Lean.Expr) (k total : Nat) : MetaM Lean.Expr := do
  if total == 1 then return x
  let mut y := x
  for _ in [0:k] do
    y ← mkAppM ``Prod.snd #[y]
  if k + 1 < total then mkAppM ``Prod.fst #[y] else return y

/-- Replace each `let` variable in the context by its value. -/
elab "claws_zeta" : tactic => do
  for _ in [0:32] do
    let g ← getMainGoal
    let some d ← g.withContext do
        return (← getLCtx).decls.toList.findSome? fun
          | some d => if d.isLet && !d.isImplementationDetail then some d else none
          | none => none
      | break
    let (fvars, g) ← g.revert #[d.fvarId] (preserveOrder := true)
    let t ← g.getType
    let .letE _ _ v b _ := t | throwError "claws_zeta: expected a let"
    let g ← g.replaceTargetDefEq (b.instantiate1 v)
    let (_, g) ← g.introNP (fvars.size - 1)
    replaceMainGoal [g]

/-- Rewrite the first loop in the goal with `pf`, a lemma (or induction
hypothesis) `∀ ..., ∃ v, execLoop f P e m c b s = some o`: unify it with
the loop, prove its hypotheses, and replace the loop by its outcome. -/
def useLoopLemma (pf : Lean.Expr) (isIH : Bool) (codeFn : Option Name := none) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let apps := (t.find? fun e => e.isAppOfArity ``execLoop 7 && !e.hasLooseBVars).toList
    for app in apps do
      let s ← saveState
      try
        let (args, _, body) ← forallMetaTelescopeReducing (← inferType pf)
        let some (_, ex) := body.app2? ``Exists | throwError "not an existential"
        let .lam _ _ eq _ := ex | throwError "not a lambda"
        let lhs := (eq.eq?.map (·.2.1)).getD eq
        unless ← withReducible (isDefEq lhs app) do
          -- lhs does not mention v; compare after instantiating it away
          unless ← isDefEq lhs app do throwError "no match"
        -- The goal states the translation's call of the loop, with the
        -- values the loop starts from. Take them from there: a value that
        -- memory holds as `.vec []` does not show which array it encodes.
        if let some cf := codeFn then
          let body ← instantiateMVars body
          if let some lemApp := body.find? (·.isAppOf cf) then
            let n := lemApp.getAppNumArgs
            for e in (t.find? fun e => e.isAppOfArity cf n && !e.hasLooseBVars).toList do
              let s' ← saveState
              unless ← isDefEq lemApp e do s'.restore
        -- Prove the hypotheses, in order: addresses first assign the
        -- address variables, then reads assign the values.
        for a in args do
          let a ← instantiateMVars a
          unless a.isMVar do continue
          if (← a.mvarId!.isAssigned) then continue
          let ty ← instantiateMVars (← inferType a)
          unless ← isProp ty do continue
          let goal := a.mvarId!
          -- A while loop's measure, in a fuel bound: the `toNat` of a bit
          -- vector, below 2^32 once unfolded.
          let measures := (← instantiateMVars ty).getUsedConstants.filter
            (·.getString! == "measure")
          let measureTac ← if measures.isEmpty then `(tactic| fail) else
            let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← measures.mapM fun n =>
              `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
            let ls : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := Syntax.TSepArray.ofElems ids
            `(tactic| (simp only [$ls,*]; bv_omega))
          -- Without error recovery: a failure must fail, not log an
          -- error and admit the goal.
          let gs ← Term.TermElabM.run' <| Tactic.run goal <| Tactic.withoutRecover <| evalTactic (← `(tactic| first
            | $measureTac:tactic
            | assumption
            | (exact Ne.symm (by assumption))
            | rfl
            | omega
            -- A fuel bound: the measure shrinks, which the safety check
            -- states on bit vectors.
            | (simp only [BitVec.lt_def, BitVec.le_def] at *; omega)
            | (claws_run [Claws.Sem.eval]; done)
            | (claws_run [Claws.Sem.eval]; rfl)
            | bv_omega))
          unless gs.isEmpty do throwError "unproven hypothesis"
        let pf' ← instantiateMVars (mkAppN pf args)
        if pf'.hasExprMVar then throwError "unassigned"
        let stx ← Term.exprToSyntax pf'
        let appStx ← Term.exprToSyntax app
        -- The lemma names the loop's parts by their definitions; the goal
        -- may have them unfolded. State the outcome at the goal's loop.
        -- Only the induction hypothesis is about the loop the goal's ∃
        -- describes; an inner loop's counter ends with its block.
        if isIH then
          evalTactic (← `(tactic| (
            obtain ⟨v, hv⟩ := $stx
            rw [show $appStx = _ from hv]
            try refine ⟨v, ?_⟩)))
        else
          evalTactic (← `(tactic| (
            obtain ⟨v, hv⟩ := $stx
            rw [show $appStx = _ from hv])))
        return true
      catch ex =>
        s.restore
        if (← getEnv).contains `Claws.debugLoop then
          IO.eprintln s!"claws_loop_use: {← ex.toMessageData.toString}"
    return false

/-- Rewrite a loop in the goal with its lemma from `claws_loop`, or, in the
proof of a loop lemma, with the induction hypothesis. -/
elab_rules : tactic | `(tactic| claws_loop_use) => do
  let g ← getMainGoal
  let cands ← g.withContext do
    let lctx ← getLCtx
    let hyps := lctx.decls.toList.filterMap fun d? => d?.bind fun d =>
      if d.isImplementationDetail then none else some d.toExpr
    let env ← getEnv
    let lemmas := env.constants.fold (init := #[]) fun acc n _ =>
      if n.components.contains `Loop && (n.toString.splitOn ".Proof.Loop.").length == 2 then acc.push (Lean.mkConst n)
      else acc
    return hyps.toArray.map (·, true) ++ lemmas.map (·, false)
  for (c, isIH) in cands do
    let ty ← g.withContext (do whnfR (← inferType c))
    unless ty.isForall do continue
    -- A lemma `P.Proof.Loop.f.loopN` is about `P.Code.f.loopN`.
    let codeFn := c.constName?.bind fun n =>
      match n.toString.splitOn ".Proof.Loop." with
      | [proj, rest] => some (proj ++ ".Code." ++ rest).toName
      | _ => none
    if ← useLoopLemma c isIH codeFn then return
  throwError "claws_loop_use: no lemma applies to a loop in the goal"

/-- The last hypothesis is a bound `b ≤ f` on the fuel f: write f as
`k + slack`, the form the interpreter's equations unfold. -/
elab "claws_loop_fuel" n:num : tactic => do
  let g ← getMainGoal
  let fstx ← g.withContext do
    let some d := (← getLCtx).lastDecl | throwError "claws_loop_fuel: no hypotheses"
    let t ← instantiateMVars d.type
    let some (_, _, _, f) := t.app4? ``LE.le | throwError "claws_loop_fuel: no bound"
    Term.exprToSyntax f
  evalTactic (← `(tactic| (
    obtain ⟨kf, hkf⟩ : ∃ kf, $fstx = kf + $n := ⟨$fstx - $n, by omega⟩
    subst hkf)))

/-- The memory a loop leaves equals the one its lemma states: compare
every address. -/
macro "claws_mem_eq" : tactic => `(tactic| (
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.length_set]
  repeat' split
  all_goals (first | rfl | (simp_all; done) | omega)))

/-- Before a loop proof runs a pass. With `Claws.loopStart` defined,
show the goal instead. -/
syntax "claws_loop_start" : tactic

elab_rules : tactic | `(tactic| claws_loop_start) => do
  if (← getEnv).contains `Claws.loopStart then
    evalTactic (← `(tactic| (trace_state; sorry)))

/-- Split each hypothesis that is a conjunction into its parts. -/
elab "claws_split_ands" : tactic => do
  replaceMainGoal [← (← getMainGoal).casesAnd]

/-- The last step of each case of a loop proof. With
`Claws.loopTrace` defined, show the goal instead. -/
syntax "claws_loop_finish" : tactic

elab_rules : tactic | `(tactic| claws_loop_finish) => do
  if (← getEnv).contains `Claws.loopTrace then
    evalTactic (← `(tactic| (trace_state; sorry)))
  else
    evalTactic (← `(tactic| first
      | exact ⟨default, trivial⟩
      -- A path the safety check rules out: the hypotheses contradict
      -- each other. On `False`, so simp_all leaves the goal's run alone.
      | (exfalso; claws_split_ands; simp_all; done)
      | exact ⟨_, (Claws.Sem.set_self_of (by assumption)).symm⟩
      | rfl
      | (congr 2; claws_mem_eq)
      | claws_mem_eq))

end Claws.Sem

namespace Claws

open Lean Meta Elab Command Term Tactic Claws.Sem

/-- `claws_loop f N [Code.g]` proves the lemma `Proof.Loop.f.loopN`
about the N-th loop of f; the list names translated functions the body
calls, to unfold. Prove a loop after the functions its body calls and
after any loop inside it. -/
syntax (name := clawsLoop) "claws_loop " ident num " [" Lean.Parser.Tactic.simpLemma,* "]" : command

@[command_elab clawsLoop] def elabClawsLoop : CommandElab := fun stx => do
  match stx with
  | `(claws_loop $f $n [$ls,*]) =>
    let ns ← getCurrNamespace
    let proj := ns.getPrefix
    let fname := f.getId
    let loopN := Name.mkSimple s!"loop{n.getNat}"
    let codeFn := proj ++ `Code ++ fname ++ loopN
    let astL := proj ++ `Ast ++ fname ++ loopN
    let lemmaName := ns ++ `Loop ++ fname ++ loopN
    let env ← getEnv
    let earlier := env.constants.fold (init := 0) fun k c _ =>
      if ((ns ++ `Loop).isPrefixOf c || (ns ++ `Run).isPrefixOf c) && !c.isInternal then k + 1 else k
    -- Fuel in reserve for what the body calls: any function or inner loop
    -- proven earlier. It appears only in bounds, which omega proves; the
    -- fuel the interpreter unfolds is the small slack, since the kernel
    -- unfolds `k + n` one step at a time.
    let reserve := 2 ^ 40 * (earlier + 1)
    -- Fuel to spare for the body of each pass, above any inner loop's.
    let slack := 1000
    let stmt ← liftTermElabM do
      let mods ← constStrings (codeFn ++ `mods)
      let vars ← constStrings (astL ++ `vars)
      let counter ← constString (astL ++ `counter)
      let some info := env.find? codeFn | throwError "claws_loop: no loop function {codeFn}"
      forallTelescope info.type fun ps res => do
        let names ← ps.mapM fun p => return (← p.fvarId!.getUserName).eraseMacroScopes.getString!
        let full ← names.mapM fun nm => do
          match vars.find? (·.startsWith (nm ++ "@")) with
          | some v => pure v
          | none => throwError "claws_loop: the loop does not mention {nm}"
        let encs ← ps.mapM fun p => do encoderOf proj (← inferType p)
        let mem := Lean.mkConst ``Mem
        withLocalDeclD `e (Lean.mkConst ``Env) fun e => withLocalDeclD `m mem fun m => do
        let qs ← (List.range ps.size).toArray.mapM fun i => pure (Name.mkSimple s!"q{i}")
        withLocalDecls (qs.map fun q => (q, .default, fun _ => pure (Lean.mkConst ``Nat))) fun qv => do
          let mut hyps : Array Lean.Expr := #[]
          for i in [0:ps.size] do
            let loc := mkApp2 (Lean.mkConst ``Loc.mk) qv[i]! (← mkAppOptM ``List.nil #[Lean.mkConst ``Step])
            hyps := hyps.push (← mkEq (← mkAppM ``List.lookup #[mkStrLit full[i]!, e]) (← mkAppM ``Option.some #[loc]))
          for i in [0:ps.size] do
            hyps := hyps.push (← mkEq (← mkAppM ``GetElem?.getElem? #[m, qv[i]!])
              (← mkAppM ``Option.some #[mkApp encs[i]! ps[i]!]))
          for i in [0:ps.size] do
            for j in [i+1:ps.size] do
              hyps := hyps.push (mkNot (← mkEq qv[i]! qv[j]!))
          -- Where the C++ would trap, the loop needs its safety.
          if env.contains (codeFn ++ `safe) then
            hyps := hyps.push (← mkEq (mkAppN (Lean.mkConst (codeFn ++ `safe)) ps) (Lean.mkConst ``Bool.true))
          withLocalDeclD `f (Lean.mkConst ``Nat) fun fv => do
            let ctr := ps[ps.size - 1]!
            let ctrNat ← mkAppM ``BitVec.toNat #[ctr]
            -- A for loop's passes are bounded by its counter; a while
            -- loop's by its measure, which claws-lean writes down.
            let meas ← if counter == "" && env.contains (codeFn ++ `measure) then
                pure (mkAppN (Lean.mkConst (codeFn ++ `measure)) ps)
              else mkAppM ``HSub.hSub #[mkNatLit (2 ^ 32), ctrNat]
            let need ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[meas, mkNatLit reserve], mkNatLit slack]
            let bound ← mkAppM ``LE.le #[need, fv]
            let r0 := mkAppN (Lean.mkConst codeFn) ps
            -- A loop that may return gives the returned value first.
            let returns := res.isAppOfArity ``Prod 2 && (res.getArg! 0).isAppOfArity ``Option 1
            let r ← if returns then mkAppM ``Prod.snd #[r0] else pure r0
            let mut final := m
            for k in [0:mods.length] do
              let some i := names.findIdx? (· == mods[k]!) | throwError "claws_loop: {mods[k]!} is not a parameter"
              let c ← component r k mods.length
              final ← mkAppM ``List.set #[final, qv[i]!, mkApp encs[i]! c]
            let isFor := counter != ""
            let concl ← withLocalDeclD `v (Lean.mkConst ``Val) fun v => do
              let fin ← if isFor then mkAppM ``List.set #[final, qv[ps.size - 1]!, v] else pure final
              let app := mkAppN (Lean.mkConst ``execLoop)
                #[fv, Lean.mkConst (proj ++ `Ast ++ `prog), e, m, Lean.mkConst (astL ++ `cond), Lean.mkConst (astL ++ `body),
                  Lean.mkConst (astL ++ `step)]
              let out ← if returns then do
                  let enc ← encoderOf proj ((res.getArg! 0).getArg! 0)
                  let rv ← mkAppM ``Option.map #[enc, ← mkAppM ``Prod.fst #[r0]]
                  pure (mkApp3 (Lean.mkConst ``loopOutcome) rv e fin)
                else pure (mkApp2 (Lean.mkConst ``Outcome.normal) e fin)
              let rhs ← mkAppM ``Option.some #[out]
              mkAppM ``Exists #[← mkLambdaFVars #[v] (← mkEq app rhs)]
            let body ← mkForallFVars #[fv] (← mkArrow bound concl)
            let mut acc := body
            for h in hyps.reverse do
              acc ← mkArrow h acc
            mkForallFVars (ps ++ #[e, m] ++ qv) acc
    let k := (← liftTermElabM <| forallTelescope (env.find? codeFn).get!.type fun ps _ => pure ps.size)
    let pnames := (List.range k).toArray.map fun i => mkIdent (Name.mkSimple s!"x{i}")
    let callee := mkIdent codeFn
    -- simp's list must not be empty: an empty splice leaves a stray comma.
    let evalId : TSyntax `Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| Claws.Sem.eval)
    let ls : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," :=
      Syntax.TSepArray.ofElems (#[evalId] ++ ls.getElems)
    -- The measure, unfolded, so the fuel bounds compare one pass with
    -- the next.
    let measTac ← if env.contains (codeFn ++ `measure) then
        `(tactic| try simp only [$(mkIdent (codeFn ++ `measure)):ident] at *)
      else `(tactic| skip)
    let safeTac ← if env.contains (codeFn ++ `safe) then
        `(tactic| claws_unfold_safe $(mkIdent (codeFn ++ `safe)))
      else `(tactic| skip)
    let pf ← liftTermElabM do
      let tac ← `(by
        intro $pnames*
        fun_induction $callee $pnames*
        all_goals (
          claws_zeta
          intros
          claws_loop_fuel $(Syntax.mkNumLit (toString slack))
          $measTac
          $safeTac
          -- A path the safety check rules out is closed by now.
          all_goals claws_bounds
          all_goals rw [Claws.Sem.execLoop]
          all_goals simp only [$(mkIdent (astL ++ `cond)):ident, $(mkIdent (astL ++ `body)):ident,
            $(mkIdent (astL ++ `step)):ident]
          all_goals claws_loop_start
          all_goals repeat' (first
            | (claws_run [$ls,*] at *; done)
            | ((try claws_run [$ls,*] at *); claws_loop_use)
            | ((try claws_run [$ls,*] at *); claws_case)
            | ((try claws_run [$ls,*] at *); claws_loop_exit)
            -- A pass that settles a condition, such as a push's bound,
            -- can leave more to run.
            | claws_run [$ls,*] at *)
          all_goals (try claws_run [$ls,*] at *)
          all_goals claws_loop_finish))
      -- A loop proof runs the body's interpreter twice over; allow it
      -- twenty times a command's time, which `set_option maxHeartbeats`
      -- raises for a loop that needs more.
      let pf ← withTheReader Core.Context (fun c => { c with maxHeartbeats := c.maxHeartbeats * 20 }) do
        let pf ← elabTermEnsuringType tac stmt
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
      pure pf
    liftCoreM <| addDecl <| .thmDecl { name := lemmaName, levelParams := [], type := stmt, value := pf }
  | _ => throwUnsupportedSyntax

end Claws
