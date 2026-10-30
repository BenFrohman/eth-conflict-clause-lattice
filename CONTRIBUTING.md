# Contributing

1. Open an issue before large changes.
2. `lake build` and `lake env lean AxiomAudit.lean` must pass with 0 `sorry` and only standard axioms.
3. Do not weaken theorem statements; keep the Apache-2.0 header on new `.lean` files.
4. `main` is protected: changes go through pull requests with linear history.
