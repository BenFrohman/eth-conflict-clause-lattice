# titan-audit report: `eth-conflict-clause-lattice`

**Verdict: PASS**

- Generated (UTC): 2026-10-29T22:33:50+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `05507e1f057eee1fa455a831290baee00991db57`
- Tree SHA-256: `912e0df6d91c91b294437f4fad51f34276cded7b8993744c66a6fc17a308c15b` over 9 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 5  Theorems: 69  Clean (only propext/Classical.choice/Quot.sound): 69
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `ConflictClauseLattice.FinalProductTheorem` | 1 | 0 |
| `ConflictClauseLattice.HomologicalCertificate` | 18 | 0 |
| `ConflictClauseLattice.PosetLattice` | 25 | 0 |
| `ConflictClauseLattice.StepCountingMonad` | 25 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `lH+f7+wvxv8nPanYa5uCAkh32nWbVGgVppArvRVm1tI=`
- Verify: `titan-audit verify report.json`
