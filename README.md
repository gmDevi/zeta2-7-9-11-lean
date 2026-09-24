# zeta2-lean

Lean 4 + Mathlib formalisation project: at least one of the 2-adic zeta values ζ₂(7), ζ₂(9), ζ₂(11)
is irrational (assuming the prime number theorem and Andrews' hypergeometric transformation, both
cited as explicit hypotheses).

* `BLUEPRINT.md` — statement map, dependency graph, cited hypotheses, design decisions.
* `Zeta2Lean/Defs.lean`, `Zeta2Lean/Statements.lean` — definitions and statements.
* `Zeta2Lean/Assembly.lean` — the main theorem from the statements (complete).
* `Zeta2Lean/Proofs/*.lean` — one proof obligation per file.
* `Zeta2Lean/Main.lean` — final theorem `Zeta2.zeta2_7_9_11_not_all_rational` and `#print axioms`.
* `python/mirror.py` — exact-arithmetic mirror of the definitions and numerical checks of every statement.
* `scripts/` — `check.sh` (elaborate one file), `build.sh` (lake build, serialized), `audit.sh`.
