import Zeta2Lean.Cited.Statements

/-!
# Polynomial Pfaff–Saalschütz (Andrews track)

**Task.** Prove `Stmt_PPS`: for every field `K`, all `x y z : K` and `M : ℕ`,
```
∑_{s=0}^{M} C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} = (z-x)_M (z-y)_M (z+M)_M.
```
No hypotheses.  (It is an identity in `ℤ[x,y,z]`; the field version is all that is needed.)

**Informal proof (Zeilberger certificate).** Let `F(M,s)` be the summand, `S(M) = ∑_s F(M,s)`,
`R(M)` the right side and `c(M) = (z-x+M)(z-y+M)(z+2M)(z+2M+1)`.  With the certificate
`G(M,0) = 0`, `G(M,s+1) = -(z+2M+1) C(M,s) (x)_{s+1} (y)_{s+1} (z-x-y)_{M-s} (z+s)_{2M+1-s}`:
1. *Telescoping*: `(z+M) F(M+1,s) - c(M) F(M,s) = G(M,s+1) - G(M,s)` for `s ≤ M+1`.  Cases
   `s = 0` and `s = M+1` close by `ring` after peeling `rpoch_succ`; the middle case `s = u+1`,
   `M = u+1+t` is `linear_combination λ * hrel` in the atoms `X = (x)_{u+1}`, `Y = (y)_{u+1}`,
   `P = (z-x-y)_t`, `Z = (z+u+1)_{u+2t+1}`, `C1 = C(M,u+1)`, `C2 = C(M,u)`, with the binomial
   relation `hrel : (u+1) C1 = (t+1) C2` (`Nat.choose_succ_right_eq`) and
   `λ = P X Y Z (x+y-z-t) (z+2u+2t+2) (z+2u+2t+3)`.
2. *Recurrence*: summing over `s ≤ M+1` (`Finset.sum_range_sub`, `G(M,M+2) = 0`,
   `F(M,M+1) = 0`): `(z+M) S(M+1) = c(M) S(M)` in every commutative ring.  `R` satisfies the same
   recurrence (`rpoch_succ`, `rpoch_succ'`).
3. *Cancellation*: in the domain `K[X]` with `z := X`, `X + M ≠ 0` (`Polynomial.X_add_C_ne_zero`),
   so induction on `M` with `mul_left_cancel₀` gives `S = R` there; evaluate at `z`
   (`Polynomial.evalRingHom`, `map_rpoch`).

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`, lines 120–289 (section `PPS`:
`ppsF`, `ppsS`, `ppsg`, `ppsG`, `ppsc`, `pps_tele_zero`, `pps_mid_core`, `pps_tele_mid`,
`pps_tele_last`, `pps_tele`, `pps_rec`, `pps_rhs_rec`, `pps_domain`, `pps_field`); `pps_field` is
`Stmt_PPS` up to unfolding `ppsS`/`ppsF` (`intro K _ x y z M; exact pps_field x y z M` was checked
to close the goal).  The Pochhammer API it uses (`rpoch_zero`, `rpoch_one`, `rpoch_succ`,
`rpoch_succ'`, `rpoch_add`, `map_rpoch`) is already proved in `Cited/Defs.lean` under the same
names: do not redeclare it.  Put all helpers in `namespace Zeta2.Cited.PPS` (or make them
`private`), so that `Cited/Main.lean` can import every proof file without name clashes; only
`Zeta2.Cited.PPS_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_PPS` (random rationals and
random elements of `GF(p)`, `p ∈ {2, 3, 5, 7}`, `M ≤ 8`); the scout's symbolic check of the
certificate is `docs/cited/pps_certificate.py` (needs sympy).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

theorem PPS_proof : Stmt_PPS := by
  sorry

end Zeta2.Cited

end
