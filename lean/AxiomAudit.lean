import ConjectureLab

/-!
# Axiom audit

Kernel-level check that every declaration under the `ConjectureLab` namespace
depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Unlike a text scan, this catches `sorryAx` (any `sorry`, however written),
`Lean.ofReduceBool` (`native_decide`) and custom axioms pulled in by imports.

Run with: `cd lean && lake env lean AxiomAudit.lean` (fails on any violation).
-/

open Lean Elab Command

elab "#audit_conjecture_lab_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let decls := env.constants.fold
    (fun acc n _ => if (`ConjectureLab).isPrefixOf n then acc.push n else acc) #[]
  if decls.isEmpty then
    throwError "axiom audit: no ConjectureLab declarations found (vacuous audit)"
  let mut bad : Array (Name × Name) := #[]
  for n in decls do
    for ax in ← collectAxioms n do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  unless bad.isEmpty do
    let lines := bad.toList.map fun (n, ax) => m!"\n  {n} depends on {ax}"
    throwError m!"axiom audit FAILED:{MessageData.joinSep lines ""}"
  logInfo m!"axiom audit OK: {decls.size} ConjectureLab declarations use only standard axioms"

#audit_conjecture_lab_axioms
