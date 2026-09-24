import Zeta2Lean.Statements

/-!
# Symmetry and vanishing sums of the partial-fraction coefficients (proof.md §3, Lemma 1)

**Task.** Prove `Stmt_CoeffVanish` (fields `symm`, `c1`, `ceven`) from `Stmt_PF`.

**Informal proof.**
* `symm` (`r_{i,n-k} = (-1)^{i+1} r_{i,k}`, `k ≤ n`): purely from the definitions.  With
  `ρ := PowerSeries.rescale (-1)` (`ε ↦ -ε`, a ring hom): `ρ (psPoch c d k) = psPoch c (-d) k`, so
  `Psi n (n-k) = ρ (Psi n k)` (use `n - (n - k) = k`; `ρ` commutes with inverses of units), and
  `C(n - 2(n-k)) + 2X = -ρ (C(n-2k) + 2X)`.  Hence `Gser n (n-k) = -ρ (Gser n k)` and
  `coeff μ (Gser n (n-k)) = -(-1)^μ coeff μ (Gser n k)`; with `μ = 8 - i` this is
  `(-1)^{i+1} r_{i,k}`.  If `i = 0` or `i > 8` both sides are `0`.
* `c1` (`∑_k r_{1,k} = 0`, "degree `R_n = -7`"): compare the coefficients of `t^{8n+7}` in
  `Stmt_PF.poly`.  `Rnum n` has `natDegree ≤ 8n+1 < 8n+7`, so its coefficient is `0`.  In
  `PFpoly n`, the terms with `i ≥ 2` have `natDegree ≤ 8n+6`, and for `i = 1` the polynomial
  `(t+k)^7 ∏_{j≠k} (t+j)^8` is monic of `natDegree 8n+7`; so the coefficient is `∑_k r_{1,k}`.
* `ceven`: for even `i`, `symm` gives `r_{i,n-k} = -r_{i,k}`, so reflecting the sum
  (`Finset.sum_range_reflect`) gives `c_i = -c_i`, i.e. `c_i = 0`.

**Lean hints.** `PowerSeries.rescale`, `PowerSeries.coeff_rescale : coeff n (rescale a f) = a^n * coeff n f`,
`PowerSeries.rescale_X : rescale a X = C a * X`, `map_prod`, `map_pow`, `map_mul`,
`PowerSeries.inv_eq_iff_mul_eq_one`, `PowerSeries.constantCoeff_inv`, `Finset.sum_range_reflect`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.Monic.coeff_natDegree`,
`Polynomial.monic_prod_of_monic`, `Polynomial.monic_X_add_C`, `Polynomial.natDegree_prod_of_monic`,
`Polynomial.finsetSum_coeff`, `Polynomial.coeff_C_mul`, `Even.neg_one_pow`, `Odd.neg_one_pow`.

**Numerical check.** `python/mirror.py`, section "Stmt_CoeffVanish" (`n ≤ 30`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem CoeffVanish_proof (hPF : Stmt_PF) : Stmt_CoeffVanish := by
  sorry

end Zeta2

end
