# Reference material for the Cited discharge

These files are **not** part of the Lean build (nothing under `docs/` is a module of the
`Zeta2Lean` library, and `scripts/audit.sh` does not scan it). They are the deliverables of the
Andrews scout (2026-09-24), kept so that provers of `Zeta2Lean/Cited/Proofs/*.lean` can copy from
them. Delete this directory once the Cited tree is complete and integrated.

| file | what it is |
|---|---|
| `AndrewsScout.lean` | The scout's complete proof of `Andrews_Stmt` (744 lines, 51 declarations, imports only `Zeta2Lean.Statements`). It was compiled against this project, with axioms `[propext, Classical.choice, Quot.sound]`. The architect's scratch check re-targeted its lemmas at the definitions of `Zeta2Lean/Cited/Defs.lean` and proved every Andrews-track `Stmt_*` of `Zeta2Lean/Cited/Statements.lean` with it. Line ranges quoted in the proof stubs refer to this file. |
| `pps_certificate.py`, `.out` | Symbolic (sympy) check of the Zeilberger certificate for the polynomial Pfaff–Saalschütz identity, including the multiplier λ for the `linear_combination` of the middle case. |
| `check_bailey_route.py`, `.out` | Exact-rational check of every step of the Bailey-chain route: 622 points, 54 of them degenerate with `(1+a)_{2N} = 0`. It found no failures. |

The project's own numerical mirror of the Cited statements is `python/cited_mirror.py`. It follows
Lean semantics, including `x / 0 = 0` and truncated subtraction. The log of a full run is
`python/cited_mirror_full.log`: 6340 checks, 0 failures.
