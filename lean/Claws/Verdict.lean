import Lean

/-!
# The claws gate

`#claws_verdict Foo` checks a project's laws against its proofs, as
`bend PROOF.bend` does in Bend. A law is a `def` of type `Prop` in the
namespace `Foo.Laws`. Its proof is a theorem of the same name in
`Foo.Proof`. The command prints ALL PROOFS CHECK when every law has a
proof of the right type that uses no `sorry` and no axiom outside Lean's
standard three. Otherwise it fails with SOME PROOFS FAIL, which also
fails `lake build`.

When the project's `Ast.lean` (written by claws-ast) is imported, its
validation laws, `Foo.Laws.Valid.f`, are laws like any other: each says
the C++ function, run by the semantics in `Claws.Sem`, returns what its
translation computes. The verdict then reports the translation as
validated, and names any function the semantics cannot yet state a law
for. Without `Ast.lean` it reports the translation as trusted.

`bv_decide` proofs rest on an axiom it adds for each proof, named
`<theorem>._native.bv_decide.ax_..`, which trusts Lean's compiler to run
the SAT certificate checker. The verdict allows those axioms and names
every law that relies on one.
-/

namespace Claws

open Lean Elab Command Meta

/-- The axioms of Lean's logic. A proof may use these freely. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- An axiom that trusts Lean's compiler, as `bv_decide` adds. Allowed,
but reported. -/
def trustsCompiler (n : Name) : Bool :=
  n.components.contains `_native

/-- The laws of namespace `ns`, sorted by name. -/
def lawsOf (env : Environment) (ns : Name) : Array Name :=
  let laws := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if ns.isPrefixOf n && n != ns && !n.isInternal && d.type == .sort .zero then
        acc.push n
      else acc
    | _ => acc
  laws.qsort (·.toString < ·.toString)

/-- The strings of a list literal, such as `Foo.Ast.uncovered`. -/
partial def stringsOf (e : Expr) : List String :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, .lit (.strVal s), rest]) => s :: stringsOf rest
  | _ => []

/-- How far the project's translation is checked. -/
def translationLine (env : Environment) (proj : Name) : String :=
  if !env.contains (proj ++ `Ast ++ `prog) then
    "translation: trusted (no Ast.lean imported, so claws-lean is trusted)"
  else
    let valid := (lawsOf env (proj ++ `Laws ++ `Valid)).size
    let uncovered := match env.find? (proj ++ `Ast ++ `uncovered) with
      | some (.defnInfo d) => stringsOf d.value
      | _ => []
    let base := s!"translation: validated against Claws.Sem ({valid} functions)"
    if uncovered.isEmpty then base
    else base ++ s!"; not yet covered, so trusted: {", ".intercalate uncovered}"

elab "#claws_verdict " proj:ident : command => do
  let proj := proj.getId
  let lawsNs := proj ++ `Laws
  let proofNs := proj ++ `Proof
  let env ← getEnv
  let laws := lawsOf env lawsNs
  if laws.isEmpty then
    throwError "SOME PROOFS FAIL\nno laws found in namespace {lawsNs}"
  let mut lines : Array String := #[]
  let mut failed := false
  for law in laws do
    let short := law.replacePrefix lawsNs .anonymous
    let proof := proofNs ++ short
    match env.find? proof with
    | none =>
      failed := true
      lines := lines.push s!"OPEN    {short}: no theorem {proof}"
    | some ci =>
      let fits ← liftTermElabM <| isDefEq ci.type (mkConst law)
      if !fits then
        failed := true
        lines := lines.push s!"WRONG   {short}: {proof} does not prove {law}"
      else
        let axioms ← collectAxioms proof
        if axioms.contains ``sorryAx then
          failed := true
          lines := lines.push s!"SORRY   {short}: the proof uses sorry"
        else
          let extra := axioms.filter fun a =>
            !standardAxioms.contains a && !trustsCompiler a
          if !extra.isEmpty then
            failed := true
            lines := lines.push s!"AXIOM   {short}: relies on {extra.toList}"
          else if axioms.any trustsCompiler then
            lines := lines.push s!"OK      {short} (trusts Lean's compiler)"
          else
            lines := lines.push s!"OK      {short}"
  lines := lines.push (translationLine env proj)
  let report := "\n".intercalate lines.toList
  if failed then
    throwError "SOME PROOFS FAIL\n{report}"
  else
    logInfo m!"ALL PROOFS CHECK\n{report}"

end Claws
