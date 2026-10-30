# Homological Certificate Topologies on Conflict-Clause Poset Lattices

**A Lean 4–Verified Step-Counting Framework for Sub-Exponential 3-SAT Cost Bounds (ConflictClauseLattice v1.1.1)**

[![CI](https://github.com/BenFrohman/eth-conflict-clause-lattice/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/BenFrohman/eth-conflict-clause-lattice/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Lean v4.30.0-rc1](https://img.shields.io/badge/Lean-v4.30.0--rc1-purple.svg)](lean-toolchain)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23782560-blue.svg)](https://doi.org/10.5281/zenodo.23782560)

**Author:** Benjamin Stanley Frohman ([@BenFrohman](https://github.com/BenFrohman), ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))

## Abstract

This repository contains a Lean 4 + Mathlib formalization of the conflict-clause poset lattice on three variables, a cellular chain complex over it with homological certificates, and a step-counting monad (`CountM`) that measures the cost of two lattice-traversal models. The flat model `simulateLatticeTraversal` is proved to cost more than the sub-exponential bound $n^2 + 2^{n/(\log n)^{1/2+\varepsilon}}$ for all $n \ge 3$, $\varepsilon \ge 0$; the block-decomposed model `simulateBlockHomologicalTraversal`, run at `logBlockSize`, is proved to stay within it. The accompanying paper is in [`paper/main.pdf`](paper/main.pdf).

## What is and isn't proved

**Proved (machine-checked):** 69 theorems, 0 `sorry`, using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

| Module | Theorems | Content |
|---|---:|---|
| [`ConflictClauseLattice/PosetLattice.lean`](ConflictClauseLattice/PosetLattice.lean) | 25 | Graded poset $\mathcal{L}_3$ (27 clauses in layers 1+6+12+8, 54 covering edges), partial-order and meet-semilattice laws |
| [`ConflictClauseLattice/HomologicalCertificate.lean`](ConflictClauseLattice/HomologicalCertificate.lean) | 18 | Boundary maps with $\partial\circ\partial = 0$, Euler characteristic $\chi(\mathcal{L}_3) = -1$, #3-SAT = unobstructed atom count |
| [`ConflictClauseLattice/StepCountingMonad.lean`](ConflictClauseLattice/StepCountingMonad.lean) | 25 | `CountM` monad, exact step counts of both traversal models, real-valued `Real.log`/`Real.rpow` bounds, `denominator_divergence` |
| [`ConflictClauseLattice/FinalProductTheorem.lean`](ConflictClauseLattice/FinalProductTheorem.lean) | 1 | Conjunction of the main results |
| **Total** | **69** | |

**Not proved — scope disclaimer:** the step-count bounds are about the cost models defined in this repository (the number of `tick` calls), not about every algorithm for 3-SAT. Nothing here proves a sub-exponential algorithm for 3-SAT in general, and **these results do not refute the Exponential Time Hypothesis (ETH)**.

## Building

Install Lean via [elan](https://github.com/leanprover/elan), then:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone https://github.com/BenFrohman/eth-conflict-clause-lattice.git
cd eth-conflict-clause-lattice
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` prints each theorem's axioms and fails if any `sorry` or nonstandard axiom appears. The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and dependencies in [`lake-manifest.json`](lake-manifest.json).

## Repository layout

```
ConflictClauseLattice.lean        library root
ConflictClauseLattice/            Lean modules (table above)
AxiomAudit.lean                   in-kernel axiom audit
lakefile.lean, lean-toolchain     build configuration
paper/                            main.tex, main.pdf, figures
visuals/                          interactive 3D Hasse diagram (HTML)
audit/                            build and audit certificates
ip_pipeline/seal_and_verify.py    Merkle provenance script
PROVENANCE_MERKLE_ROOT.json       SHA-256 Merkle root of release files
.github/                          CI workflow, templates, CODEOWNERS
```

## Provenance and audit artifacts

**Mathematical correctness rests only on the Lean kernel** (`lake build` plus `AxiomAudit.lean`). The other artifacts are supply-chain records: they show which files were released and when, not that the math is right.

- Lean kernel verification: [`AxiomAudit.lean`](AxiomAudit.lean), [`audit/LAKE_KERNEL_BUILD_CERTIFICATE.json`](audit/LAKE_KERNEL_BUILD_CERTIFICATE.json)
- Supply-chain wrappers: [`audit/TITAN_AUDIT_CERTIFICATE.json`](audit/TITAN_AUDIT_CERTIFICATE.json) and [`audit/TITAN_AUDIT_REPORT.md`](audit/TITAN_AUDIT_REPORT.md) (Ed25519-signed titan-audit attestation), [`audit/SEALGUARD_PROVENANCE_MANIFEST.json`](audit/SEALGUARD_PROVENANCE_MANIFEST.json), [`PROVENANCE_MERKLE_ROOT.json`](PROVENANCE_MERKLE_ROOT.json)

To re-check the Merkle root:

```bash
python3 ip_pipeline/seal_and_verify.py --verify
```

## Citation

Cite via [`CITATION.cff`](CITATION.cff) (GitHub's "Cite this repository" button) or the Zenodo record [10.5281/zenodo.23782560](https://doi.org/10.5281/zenodo.23782560).

## License

Apache License 2.0. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Copyright 2026 Benjamin Stanley Frohman.

## AI Assistance Disclosure

Grok (xAI), via the Grok Bot assistant, provided scaffolding, drafting, and collaboration support on the formalization, code, and documentation in this repository. Benjamin Stanley Frohman (`frohmanbenjamin@gmail.com`, ORCID `0009-0006-7068-3718`) directed, reviewed, and is solely responsible for the architecture, implementation, proofs, and claims; Grok is not a coauthor.
