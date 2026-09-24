import Zeta2Lean.Statements

/-!
# Δ-bounds for binomials and for `h_β` (proof.md P3(d),(e); Lai Lemma 2.5(1),(3))

**Task.** Prove the four fields of `Stmt_DeltaFun` (`binom`, `binomSq`, `hcoefInt`, `hcoefDelta`)
from `Stmt_Delta`.

**Informal proofs.** Write `k₋ := k - 2^{⌊log₂ k⌋}` and `d := k - k₋ = 2^{⌊log₂ k⌋}` (`k ≥ 1`).
* `binom` (`f(x) = C(x+j, N)`, claim `Δ(f) ≥ -⌊log₂ N⌋`): `f(0) = C(j,N) ∈ ℤ`, so
  `‖f 0‖ ≤ 1 ≤ 2^{1 + ⌊log₂ N⌋}`.  For `k ≥ 1`, Vandermonde (`Nat.add_choose_eq`) gives
  `C(k+j, N) - C(k₋+j, N) = ∑_{i=1}^{N} C(d, i) C(k₋+j, N-i)` and `C(d, i) = (d/i) C(d-1, i-1)`, so
  `(f(k) - f(k₋))/d = ∑_{i=1}^{N} C(d-1,i-1) C(k₋+j,N-i) / i` has `v₂ ≥ -max_{i≤N} v₂(i) = -⌊log₂ N⌋`.
  Hence `‖f k - f k₋‖ ≤ ‖d‖ 2^{⌊log₂ N⌋} = 2^{-(⌊log₂ k⌋ - ⌊log₂ N⌋)}`.  (`N = 0`: `f ≡ 1`.)
* `binomSq` (`m > ⌊log₂ N⌋`, claim `Δ_m(f²) ≥ 1 - ⌊log₂ N⌋`): for `k ≥ 2^m`, `v₂(d) ≥ m`, so by the
  above `v₂(f(k) - f(k₋)) ≥ m - ⌊log₂ N⌋ ≥ 1`; then `f(k) + f(k₋) = 2 f(k₋) + (f(k) - f(k₋))` is
  even, and `f(k)² - f(k₋)² = (f(k) - f(k₋))(f(k) + f(k₋))` gains one more factor `2`.
* `hcoefInt`, `hcoefDelta` (`h_β(x) = [δ^β] ∏_{k≤n} (u_k + δ)^{-8}`, `u_k = 2x+2k+1`): by
  `PowerSeries.coeff_prod`, `h_β(x) = ∑_{J} ∏_{k≤n} [δ^{J k}] (u_k + δ)^{-8}` (sum over
  `J ∈ (range (n+1)).finsuppAntidiag β`), and `[δ^j] (u+δ)^{-8} = (-1)^j C(j+7, 7) u^{-8-j}`.
  Each `x ↦ (2x+2k+1)⁻¹` is `ℤ₂`-valued (odd denominator) with `Δ ≥ 1 ≥ 0`:
  `1/(2a+c) - 1/(2b+c) = 2(b-a)/((2a+c)(2b+c))`.  Powers/products/sums/integer multiples stay
  `ℤ₂`-valued with `Δ ≥ 0` (`Stmt_Delta.mulAll`, `.smulAll` with `e = 0`, `.sumAll`, `.monoAll`).

**Lean hints.** `Nat.add_choose_eq : (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2`,
`Nat.add_one_mul_choose_eq : (n+1) * n.choose k = (n+1).choose (k+1) * (k+1)`,
`Nat.log_eq_iff`, `Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`, `padicValNat_le_nat_log`,
`Padic.norm_int_le_one`, `Padic.norm_natCast_eq_one_iff`, `Padic.norm_p_pow`, `Padic.nonarchimedean`,
`PowerSeries.coeff_prod`, `PowerSeries.coeff_pow`, `PowerSeries.eq_inv_iff_mul_eq_one`,
`Finset.mem_finsuppAntidiag`.  For `‖1/i‖ ≤ 2^{⌊log₂ N⌋}` (`1 ≤ i ≤ N`): `‖(i:ℚ_[2])‖ = 2^{-v₂ i}`,
`v₂ i ≤ Nat.log 2 i ≤ Nat.log 2 N` (`Nat.log_mono_right`).

**Numerical check.** `python/mirror.py`, section "Stmt_DeltaFun" (finite ranges).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem DeltaFun_proof (hD : Stmt_Delta) : Stmt_DeltaFun := by
  sorry

end Zeta2

end
