# Verification certificate

**Paper:** The Three-Variable Conflict-Clause Poset: Graded Structure, Model Counting by Unobstructed Atoms, and Step-Counter Bounds, Formalized in Lean~4
**Author:** Benjamin Stanley Frohman (frohmanbenjamin@gmail.com)
**PDF:** `paper/main.pdf`

| Item | Value |
|---|---|
| Verified commit | `8b03b20f6393c3c4dbc419b02932308fa99c116c` |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Mathlib | v4.30.0-rc1 (commit 0c154d67103f74be3a0f2c509f72ccbf5be9f2a7) |
| CI run (build + axiom audit + no-sorry scan, passed) | https://github.com/BenFrohman/eth-conflict-clause-lattice/actions/runs/41794839338 |
| Source tarball SHA-256 (verified commit) | `fd949b7876a66601ae0b5dc7a67cea9814c4823d62e84fad4a4dc934e4135798` |

- `lake build` succeeds with the pinned toolchain.
- No `sorry`, no `admit`, no `native_decide`, and no user-declared `axiom` in the Lean sources (enforced in CI by `scripts/check_no_sorry.py`).
- All 54 audited theorems depend only on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound` (or a subset).

## `#print axioms` output (`AxiomAudit.lean`)

```
'ConflictClauseLattice.eth_conflict_clause_lattice_master_product_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.boundary1_comp_boundary2_eq_zero' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.boundary2_comp_boundary3_eq_zero' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.dualAtoms_eq_layer3' does not depend on any axioms
'ConflictClauseLattice.euler_poincare_L3' does not depend on any axioms
'ConflictClauseLattice.modelCount3_eq_unobstructedAtomCount3' depends on axioms: [propext]
'ConflictClauseLattice.non_empty_euler_characteristic_L3' does not depend on any axioms
'ConflictClauseLattice.satisfiesClause_iff_not_implies_dualAtom' does not depend on any axioms
'ConflictClauseLattice.satisfiesFormula_eq_isUnobstructed_dualAtom' does not depend on any axioms
'ConflictClauseLattice.varStateSat_eq_not_varStateSub' does not depend on any axioms
'ConflictClauseLattice.card_allValidClauses3' does not depend on any axioms
'ConflictClauseLattice.clauseMeet_implies_left' depends on axioms: [propext]
'ConflictClauseLattice.clauseMeet_implies_right' depends on axioms: [propext]
'ConflictClauseLattice.coveringEdges3_count' does not depend on any axioms
'ConflictClauseLattice.coveringEdges_by_layer' does not depend on any axioms
'ConflictClauseLattice.emptyClause3_minimal' does not depend on any axioms
'ConflictClauseLattice.impliesPoset_antisymm' depends on axioms: [propext]
'ConflictClauseLattice.impliesPoset_iff' depends on axioms: [propext]
'ConflictClauseLattice.impliesPoset_refl' depends on axioms: [propext]
'ConflictClauseLattice.impliesPoset_trans' depends on axioms: [propext]
'ConflictClauseLattice.implies_clauseMeet_iff' depends on axioms: [propext]
'ConflictClauseLattice.layer0_count' does not depend on any axioms
'ConflictClauseLattice.layer1_count' does not depend on any axioms
'ConflictClauseLattice.layer2_count' does not depend on any axioms
'ConflictClauseLattice.layer3_count' does not depend on any axioms
'ConflictClauseLattice.layer_partition_sum_three' does not depend on any axioms
'ConflictClauseLattice.varStateMeet_sub_left' depends on axioms: [propext]
'ConflictClauseLattice.varStateMeet_sub_right' depends on axioms: [propext]
'ConflictClauseLattice.varStateSub_antisymm' does not depend on any axioms
'ConflictClauseLattice.varStateSub_meet_eq' depends on axioms: [propext]
'ConflictClauseLattice.varStateSub_refl' does not depend on any axioms
'ConflictClauseLattice.varStateSub_trans' does not depend on any axioms
'ConflictClauseLattice.block_homological_traversal_bound' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.block_homological_traversal_real_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.denominator_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.exp_one_lt_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.lattice_traversal_complexity_bound' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.lattice_traversal_steps_exact' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.logBlockSize_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.logBlockSize_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.logDenominator_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.logDenominator_le_logBlockSize' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.logDenominator_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.log_nat_pos_of_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.monad_reduction_two_ticks' does not depend on any axioms
'ConflictClauseLattice.one_lt_log_nat_of_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.simulateBlockHomologicalTraversal_at_logBlockSize_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.simulateBlockHomologicalTraversal_run' depends on axioms: [propext]
'ConflictClauseLattice.simulateLatticeTraversal_exceeds_subExponential_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.simulateLatticeTraversal_run' depends on axioms: [propext]
'ConflictClauseLattice.state_injection_steps' depends on axioms: [propext]
'ConflictClauseLattice.subExponential_rpow_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.subexponential_exponent_strictly_smaller' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.tick_run' does not depend on any axioms
```

The paper's claims correspond one-to-one with the Lean declarations listed in its "Correspondence between claims and Lean declarations" section; the Lean statements are the source of truth.
