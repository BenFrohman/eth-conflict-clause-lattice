# Kernel certificate: eth-conflict-clause-lattice

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/eth-conflict-clause-lattice |
| Certified commit | `559fd9ab5c9c105606786a591b4bf555be0e8b99` (branch `chore/kernel-certificate`) |
| Lean sources | identical to `main` at `4117e227755e7ed356ce377900f7977869432a48`: no `.lean`, lakefile, manifest or toolchain file differs; the certified commit only adds CI and the scripts in `certificates/tools/` |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Date (UTC) | 2026-11-16T19:19:24Z |
| CI run | https://github.com/BenFrohman/eth-conflict-clause-lattice/actions/runs/43937903749 |
| `lake build` | `Build completed successfully (1984 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 69 theorems in 4 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 5 of 5 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 5 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (69 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

Full `#print axioms` output (verbatim from `axioms.txt`):

```
'ConflictClauseLattice.eth_conflict_clause_lattice_master_product_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConflictClauseLattice.Assignment3.mk.inj' does not depend on any axioms
'ConflictClauseLattice.Assignment3.mk.injEq' depends on axioms: [propext]
'ConflictClauseLattice.Assignment3.mk.sizeOf_spec' does not depend on any axioms
'ConflictClauseLattice.Simplex1.mk.inj' does not depend on any axioms
'ConflictClauseLattice.Simplex1.mk.injEq' depends on axioms: [propext]
'ConflictClauseLattice.Simplex1.mk.sizeOf_spec' does not depend on any axioms
'ConflictClauseLattice.Simplex2.mk.inj' does not depend on any axioms
'ConflictClauseLattice.Simplex2.mk.injEq' depends on axioms: [propext]
'ConflictClauseLattice.Simplex2.mk.sizeOf_spec' does not depend on any axioms
'ConflictClauseLattice.boundary1_comp_boundary2_eq_zero' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.boundary2_comp_boundary3_eq_zero' depends on axioms: [propext, Quot.sound]
'ConflictClauseLattice.dualAtoms_eq_layer3' does not depend on any axioms
'ConflictClauseLattice.euler_poincare_L3' does not depend on any axioms
'ConflictClauseLattice.modelCount3_eq_unobstructedAtomCount3' depends on axioms: [propext]
'ConflictClauseLattice.non_empty_euler_characteristic_L3' does not depend on any axioms
'ConflictClauseLattice.satisfiesClause_iff_not_implies_dualAtom' does not depend on any axioms
'ConflictClauseLattice.satisfiesFormula_eq_isUnobstructed_dualAtom' does not depend on any axioms
'ConflictClauseLattice.varStateSat_eq_not_varStateSub' does not depend on any axioms
'ConflictClauseLattice.ValidClause3.mk.inj' does not depend on any axioms
'ConflictClauseLattice.ValidClause3.mk.injEq' depends on axioms: [propext]
'ConflictClauseLattice.ValidClause3.mk.sizeOf_spec' does not depend on any axioms
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
'ConflictClauseLattice.CountingState.mk.inj' does not depend on any axioms
'ConflictClauseLattice.CountingState.mk.injEq' depends on axioms: [propext]
'ConflictClauseLattice.CountingState.mk.sizeOf_spec' does not depend on any axioms
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

## Rebuild

```
git clone https://github.com/BenFrohman/eth-conflict-clause-lattice.git && cd eth-conflict-clause-lattice && git checkout 559fd9ab5c9c105606786a591b4bf555be0e8b99 && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
