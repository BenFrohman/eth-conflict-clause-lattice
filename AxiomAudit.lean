/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- In-Kernel Metaprogramming Axiom Audit (`Lean.collectAxioms` over `ConstantInfo.thmInfo`).
-- Run: `lake env lean AxiomAudit.lean`
-- Fails with non-zero exit if any theorem in the `ConflictClauseLattice` module tree depends on
-- axioms outside {propext, Classical.choice, Quot.sound} (such as sorryAx or Lean.trustCompiler).

import Lean
import ConflictClauseLattice

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut stats : Std.HashMap Name (Nat × Nat) := {}
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`ConflictClauseLattice).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let nonstd := axs.filter (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound])
    let (c, b) := stats.getD mod (0, 0)
    stats := stats.insert mod (c + 1, if nonstd.isEmpty then b else b + 1)
    unless nonstd.isEmpty do bad := bad.push s!"{n} : {nonstd}"
  for (m, (c, b)) in stats.toList do
    IO.println s!"{m}: theorems={c} nonstandard={b}"
  for s in bad do
    IO.println s
  let total := stats.fold (fun acc _ (c, _) => acc + c) 0
  IO.println s!"TOTAL theorems={total} nonstandard={bad.size}"
  unless bad.isEmpty do
    throwError "axiom audit FAILED: {bad.size} theorem(s) use non-standard axioms"

-- Explicit #print axioms checks on all primary exported theorems:
#print axioms ConflictClauseLattice.card_allValidClauses3
#print axioms ConflictClauseLattice.layer0_count
#print axioms ConflictClauseLattice.layer1_count
#print axioms ConflictClauseLattice.layer2_count
#print axioms ConflictClauseLattice.layer3_count
#print axioms ConflictClauseLattice.layer_partition_sum_three
#print axioms ConflictClauseLattice.coveringEdges3_count
#print axioms ConflictClauseLattice.coveringEdges_by_layer
#print axioms ConflictClauseLattice.impliesPoset_refl
#print axioms ConflictClauseLattice.impliesPoset_trans
#print axioms ConflictClauseLattice.impliesPoset_antisymm
#print axioms ConflictClauseLattice.emptyClause3_minimal
#print axioms ConflictClauseLattice.clauseMeet_implies_left
#print axioms ConflictClauseLattice.clauseMeet_implies_right
#print axioms ConflictClauseLattice.implies_clauseMeet_iff
#print axioms ConflictClauseLattice.boundary1_comp_boundary2_eq_zero
#print axioms ConflictClauseLattice.boundary2_comp_boundary3_eq_zero
#print axioms ConflictClauseLattice.euler_poincare_L3
#print axioms ConflictClauseLattice.non_empty_euler_characteristic_L3
#print axioms ConflictClauseLattice.satisfiesClause_iff_not_implies_dualAtom
#print axioms ConflictClauseLattice.satisfiesFormula_eq_isUnobstructed_dualAtom
#print axioms ConflictClauseLattice.dualAtoms_eq_layer3
#print axioms ConflictClauseLattice.modelCount3_eq_unobstructedAtomCount3
#print axioms ConflictClauseLattice.tick_run
#print axioms ConflictClauseLattice.monad_reduction_two_ticks
#print axioms ConflictClauseLattice.simulateLatticeTraversal_run
#print axioms ConflictClauseLattice.simulateBlockHomologicalTraversal_run
#print axioms ConflictClauseLattice.state_injection_steps
#print axioms ConflictClauseLattice.lattice_traversal_complexity_bound
#print axioms ConflictClauseLattice.lattice_traversal_steps_exact
#print axioms ConflictClauseLattice.block_homological_traversal_bound
#print axioms ConflictClauseLattice.subexponential_exponent_strictly_smaller
#print axioms ConflictClauseLattice.eth_conflict_clause_lattice_master_product_theorem
#print axioms ConflictClauseLattice.exp_one_lt_three
#print axioms ConflictClauseLattice.one_lt_log_nat_of_ge_three
#print axioms ConflictClauseLattice.logDenominator_gt_one
#print axioms ConflictClauseLattice.subExponential_rpow_lt_two_pow
#print axioms ConflictClauseLattice.simulateLatticeTraversal_exceeds_subExponential_bound
#print axioms ConflictClauseLattice.block_homological_traversal_real_log_bound
#print axioms ConflictClauseLattice.simulateBlockHomologicalTraversal_at_logBlockSize_bound
