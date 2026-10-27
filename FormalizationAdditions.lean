import BPFixedPoints.Incidence.ResolutionTorRanks
import Lean.Util.CollectAxioms

/-! Audit entry point for the formalization additions. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    let publicName := (privateToUserName? n).getD n
    if (`BPFixedPoints).isPrefixOf publicName then
      count := count + 1
      let axs ← collectAxioms n
      let extra := axs.filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        throwError "unexpected axiom dependencies: {n}: {extra}"
  if count == 0 then throwError "no project declarations found"
  logInfo m!"Formalization additions audit PASS: {count} declarations; no sorryAx or additional axioms."

#print axioms BPFixedPoints.Multigraph.card_incBigradedBasis
#print axioms BPFixedPoints.CechProduct.contraction_matrices
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential_internal_degree
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential_entry_degree
#print axioms BPFixedPoints.Multigraph.incidenceTorEquivState
#print axioms BPFixedPoints.Multigraph.finrank_incidenceTor
#print axioms BPFixedPoints.Multigraph.sum_finrank_incidenceTor
