# The Conflict Clause Lattice: Poset Structure and Homological Obstructions in 3-SAT

**Author:** Benjamin Stanley Frohman (`@BenFrohman`, ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))  
**Companion Archive DOI:** [10.5281/zenodo.23747592](https://doi.org/10.5281/zenodo.23747592)  
**Toolchain:** `leanprover/lean4:v4.30.0-rc1` + Mathlib `v4.30.0-rc1` (`autoImplicit = false`)  
**Verification Status:** **69 Theorems Verified, 0 `sorry`, 0 Nonstandard Axioms**

---

## Overview

This repository contains the complete Lean 4 formalization (`ConflictClauseLattice`), LaTeX manuscript (`paper/main.tex`, `paper/main.pdf`), interactive 3D WebGL poset visualization (`visuals/conflict_clause_lattice.html`), and cryptographic provenance manifests for *The Conflict Clause Lattice: Poset Structure and Homological Obstructions in 3-SAT*.

### Repository Structure

| Module / Path | Theorems | Description |
|---|---:|---|
| `ConflictClauseLattice/PosetLattice.lean` | 25 | Graded conflict-clause poset $\mathcal{L}_3$ ($1 + 6 + 12 + 8 = 27$ clauses across Layers 0–3, $6 + 24 + 24 = 54$ covering edges), reflexivity/transitivity/antisymmetry of implication order $\preceq$, and bounded meet-semilattice laws. |
| `ConflictClauseLattice/HomologicalCertificate.lean` | 18 | Cellular chain complex $\partial_k : C_k(\mathcal{L}_3) \to C_{k-1}(\mathcal{L}_3)$, exact proof that $\partial_{k-1} \circ \partial_k = 0$ ($k \in \{2,3\}$), Euler–Poincaré identity $\chi(\mathcal{L}_3) = 1 - 6 + 12 - 8 = -1$, and exact finite model-counting bijection $\#\text{3-SAT}(\Phi) = \mathrm{unobstructedAtomCount}_3(\Phi)$. |
| `ConflictClauseLattice/StepCountingMonad.lean` | 25 | Pure functional step-counting monad (`CountM := StateM CountingState`), `tick` transitions, Monad Reduction (`simp [Bind.bind, StateT.bind]`), State Injection (`injection`), discrete Presburger arithmetic bounds (`omega`) for `simulateLatticeTraversal` ($\le n^2 + 2^n$) and `simulateBlockHomologicalTraversal` ($\le (n+m)^2 + 2^{n/\max(k,1)}$), and real-valued Mathlib `Real.log` / `Real.rpow` bounds (`block_homological_traversal_real_log_bound`, `simulateBlockHomologicalTraversal_at_logBlockSize_bound`, `subExponential_rpow_lt_two_pow`, `simulateLatticeTraversal_exceeds_subExponential_bound`, and `denominator_divergence`: $(\log n)^{1/2+o(1)} \to \infty$). |
| `ConflictClauseLattice/FinalProductTheorem.lean` | 1 | Master 5-pillar conjunction (`eth_conflict_clause_lattice_master_product_theorem`) uniting the poset partition, chain-complex boundary identity, Euler characteristic, `#3-SAT` unobstructed atom bijection, and sub-exponential step-counting bounds. |
| **Total Verified** | **69** | **0 `sorry`, 0 `trustCompiler`, 0 nonstandard axioms (`[propext, Classical.choice, Quot.sound]`)** |

### Verification & Provenance Artifacts

- `AxiomAudit.lean`: In-kernel Lean 4 axiom auditor verifying all 69 theorems (`nonstandard = 0`, `0 sorry`, `0 trustCompiler`).
- `audit/LAKE_KERNEL_BUILD_CERTIFICATE.json`: Complete Lake kernel build & in-kernel `AxiomAudit.lean` verification certificate recording `.olean`/`.ilean`/`.c` artifact hashes and verbatim kernel audit output.
- `audit/TITAN_AUDIT_CERTIFICATE.json` & `audit/TITAN_AUDIT_REPORT.md`: Ed25519-signed `titan-audit` attestation (`PASS`, 69 clean theorems).
- `audit/SEALGUARD_PROVENANCE_MANIFEST.json`: SealGuard cryptographic provenance manifest and Sentinel-Gate pre-execution policy receipt.
- `PROVENANCE_MERKLE_ROOT.json`: Complete SHA-256 Merkle tree and Sentinel-Gate policy receipt.
- `paper/main.tex` & `paper/main.pdf`: Complete self-contained LaTeX manuscript and compiled PDF.
- `visuals/conflict_clause_lattice.html`: Interactive 3D WebGL Hasse diagram & homological obstruction explorer.

---

## Reproducing the Verification

### 1. Build the Lean 4 Package and Run the In-Kernel Axiom Audit
```bash
lake build
lake env lean AxiomAudit.lean
```

### 2. Verify Cryptographic Provenance & Titan-Audit Signature
```bash
titan-audit verify audit/TITAN_AUDIT_CERTIFICATE.json
python3 ip_pipeline/seal_and_verify.py --verify
```

---

## License & Attribution

Copyright 2026 Benjamin Stanley Frohman (`@BenFrohman`, ORCID `0009-0006-7068-3718`).  
Licensed under the Apache License, Version 2.0 (see `LICENSE` and `NOTICE`).
