import Zeta2Lean.Cited.Statements

/-!
# The unit Bailey pair (Andrews track)

**Task.** Prove `Stmt_UnitPair`: in every field `K` of characteristic zero, for `a ≠ 0` and every
`n`, `BP a (unitα a) unitβ n`, i.e.
```
(1+a)_{2n} [n = 0] = ∑_{r=0}^{n} (a+2r)/a (a)_r (-1)^r / r! · (1+a+n+r)_{n-r} / (n-r)!.
```
No hypotheses.

**Informal proof.** `n = 0`: both sides are `1` (`(a+0)/a = 1`).  `n = n'+1`: the right side
vanishes.  Telescoping: for `k ≤ n'`, the partial sum `∑_{r ≤ k}` equals
```
T(k) = (-1)^k (1+a)_k (1+a+n+k)_{n-k} / (k! (n'-k)! n)          (n = n'+1)
```
(induction on `k`: `T(k) + term(k+1) = T(k+1)`, using `(a)_{k+1} = a (1+a)_k`,
`(1+a+n+k)_{n-k} = (1+a+n+k) (1+a+n+k+1)_{n-k-1}` and `field_simp; ring`).  At `k = n'` the last
term `r = n` cancels `T(n')` exactly.  Only `a ≠ 0` and `r! ≠ 0` are divided by; `(1+a)_k` may
vanish (e.g. `a = -1`), which is harmless since the relation is multiplied out.

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`, lines 328–382
(`unit_partial`, `bp_unit`); `UnitPair_proof := fun K _ _ a ha n => bp_unit a ha n` was checked
to typecheck against `Stmt_UnitPair`.  `BP`, `unitα`, `unitβ`, `fact_ne` and the Pochhammer API
(`rpoch_zero`, `rpoch_succ`, `rpoch_succ'`) are in `Cited/Defs.lean` with the same names and
bodies: do not redeclare them.  Put helpers in `namespace Zeta2.Cited.UnitPair` (or make them
`private`); only `Zeta2.Cited.UnitPair_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_UnitPair` (generic and
degenerate `a`, including `a ∈ {-1, -2, -3, -1/2, -3/2}`, `n ≤ 10`).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

theorem UnitPair_proof : Stmt_UnitPair := by
  sorry

end Zeta2.Cited

end
