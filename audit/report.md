# titan-audit report: `eth-conflict-clause-lattice`

**Verdict: PASS**

- Generated (UTC): 2026-10-29T01:49:57+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `e06725246e557aadda69297fc8f638fceba9d125`
- Tree SHA-256: `b96bbdae6fc2877179dbb45cc53c468f6474abbdfd298f1348ed0d115db90b62` over 9 files

## Build

- Success: True  Jobs: 1980  Errors: 0
- `sorry` warnings: 0  Unused-variable warnings: 0

## Axiom audit

- Modules: 5  Theorems: 68  Clean (only propext/Classical.choice/Quot.sound): 68
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `ConflictClauseLattice.FinalProductTheorem` | 1 | 0 |
| `ConflictClauseLattice.HomologicalCertificate` | 18 | 0 |
| `ConflictClauseLattice.PosetLattice` | 25 | 0 |
| `ConflictClauseLattice.StepCountingMonad` | 24 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `4KR00Ud771GwnZ+sW+xE/WzGRzpVO2REI9ir/zuBr8U=`
- Verify: `titan-audit verify report.json`
