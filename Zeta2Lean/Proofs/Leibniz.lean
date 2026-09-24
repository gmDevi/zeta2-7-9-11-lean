import Zeta2Lean.Statements

/-!
# Leibniz expansion of the integrand (proof.md §7 "Setup" and "Leibniz"; §5)

**Task.** Prove `Stmt_Leibniz` from `Stmt_PF`: for all `n, x ∈ ℕ`,
  `integrand n x = ∑_{γ<2} ∑_{β<4-γ} ∑_{M ∈ (Icc 1 n).finsuppAntidiag (3-γ-β)} leibTerm n γ β M x`.

**Informal proof.**
1. `integrand n x = -6 · [ε^3] Rser n (x + 1/2)`.  Apply `Stmt_PF.series` at `y = x + 1/2`
   (`y + j > 0`).  In `ℚ⟦ε⟧`, `((C a + X)^i)⁻¹ = ∑_j C(-i, j) a^{-i-j} ε^j`, so
   `[ε^3] ((C a + X)^i)⁻¹ = -C(i+2, 3) a^{-i-3} = -(i)₃/6 · a^{-i-3}`; with `a = x + k + 1/2` this
   is exactly `-1/6` times the `(i,k)` term of `integrand`.
2. Product form: with `y = x + 1/2`, `C(y + 1/2 + j) + X = C(x+1+j) + X` and
   `C(y + j) + X = (1/2)(C(2x+2j+1) + 2X)`, so
   `Rser n (x+1/2) = 2^{24n+8} · (C(2x+1+n) + 2X) · ∏_{l=1}^{n} (C(x+l) + X)^8 · H(2X)`,
   `H(δ) := ∏_{k≤n} ((C(2x+2k+1) + δ)^8)⁻¹`, and `H(2X) = rescale 2 H`, so
   `[ε^β] H(2ε) = 2^β hcoef n β x`.
3. `[ε^3]` of the triple product = `∑_{γ+a+β=3} [ε^γ](C(2x+1+n) + 2X) · [ε^a] ∏_l (C(x+l)+X)^8 · 2^β h_β`,
   `[ε^γ](C(2x+1+n) + 2X) = 2x+1+n` (γ = 0), `2` (γ = 1), `0` (γ ≥ 2).
4. `[ε^a] ∏_{l=1}^{n} (C(x+l) + X)^8 = ∑_{M ∈ (Icc 1 n).finsuppAntidiag a} ∏_l C(8, M l) (x+l)^{8 - M l}`
   (`PowerSeries.coeff_prod` + binomial theorem `[ε^j](C c + X)^8 = C(8,j) c^{8-j}`).
5. For `M` with `∑_l M l = a ≤ 3`:
   `∏_{l=1}^{n} (x+l)^{8 - M l} = n!^{8-a} C(x+n,n)^{8-a} ∏_l ((l-1)!(n-l)! Y_l(x))^{M l}`,
   because `∏_{l=1}^{n} (x+l) = n! C(x+n,n)` and `(x+l) · (l-1)!(n-l)! Y_l(x) = n! C(x+n,n)`
   (i.e. `(x+1)_n / (x+l) = (l-1)! C(x+l-1,l-1) · (n-l)! C(x+n,n-l)`).  Note `8 - a = 5 + γ + β`.
6. Collect: `-6 · 2^{24n+8} · (…)` is `leibTerm`.

**Lean hints.** `PowerSeries.coeff_mul`, `PowerSeries.coeff_prod`, `PowerSeries.coeff_pow`,
`PowerSeries.coeff_rescale`, `PowerSeries.rescale`, `map_prod`, `map_pow`, `map_inv`-for-units
(prove `rescale 2 (φ⁻¹) = (rescale 2 φ)⁻¹` via `PowerSeries.eq_inv_iff_mul_eq_one`),
`PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`, `add_pow`, `Finset.sum_range_succ`,
`Finset.mem_finsuppAntidiag : f ∈ s.finsuppAntidiag n ↔ s.sum f = n ∧ f.support ⊆ s`,
`Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `Nat.choose_mul_factorial_mul_factorial`,
`Nat.add_choose_mul_factorial_mul_factorial`, `Nat.factorial_mul_factorial_dvd_factorial_add`,
`Finset.prod_Ico_id_eq_factorial`, `Finset.prod_range_add_one_eq_factorial`.

**Numerical check.** `python/mirror.py`, section "Stmt_Leibniz" (`n ≤ 5`, `x ≤ 5`, exact).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem Leibniz_proof (hPF : Stmt_PF) : Stmt_Leibniz := by
  sorry

end Zeta2

end
