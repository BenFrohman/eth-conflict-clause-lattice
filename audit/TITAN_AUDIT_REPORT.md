# titan-audit report: `eth-conflict-clause-lattice`

**Verdict: PASS**

- Generated (UTC): 2026-10-28T20:01:35+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `f75610e3d1d53701d750801d850c72cd9c86df8d`
- Tree SHA-256: `21a8eb9d03dcf39258a14f1aeb8b5025ab81bfe1ecbdfa333903f410c7240145` over 9 files

## Build

- Success: True  Jobs: 7  Errors: 0
- `sorry` warnings: 0  Unused-variable warnings: 0

## Axiom audit

- Modules: 5  Theorems: 56  Clean (only propext/Classical.choice/Quot.sound): 56
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `ConflictClauseLattice.FinalProductTheorem` | 1 | 0 |
| `ConflictClauseLattice.HomologicalCertificate` | 18 | 0 |
| `ConflictClauseLattice.PosetLattice` | 25 | 0 |
| `ConflictClauseLattice.StepCountingMonad` | 12 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `lH+f7+wvxv8nPanYa5uCAkh32nWbVGgVppArvRVm1tI=`
- Verify: `titan-audit verify report.json`
