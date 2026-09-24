import Zeta2Lean.Statements

/-!
# The exponent computation (proof.md §4.4 last line, §8; uses PNT)

**Task.** Prove `Stmt_Asymptotic`: assuming `PNT_Stmt` (`ψ(x)/x → 1`), for all `Cst : ℝ`, `A : ℕ`,
  `D_n · Cst (n+1)^A 2^{16n} · 2^{-target m} → 0`  along `n = 2^m - 1`, `m → ∞`,
where `target m = 32n + 14 - 11m`.  (Uses only the *upper* half of PNT, `ψ(x) ≤ (1+δ)x`.)

**Informal proof.** Let `n = 2^m - 1` (`n → ∞`).  `D_n ≤ d_n^{12}/Φ_n` (`Nat.cast_div_le`), so
  `log D_n ≤ 12 log d_n - log Φ_n`,  `log d_n = ψ(n)` (`Chebyshev.psi_eq_log_lcmUpto`),
  `log Φ_n = ∑_{p ≤ n, p ≥ 11, p² > 2n} log p ≥ θ(n) - θ(10) - θ(√(2n)) ≥ θ(n) - log 4 · (10 + √(2n))`
(the complement of the index set inside the primes `≤ n` consists of primes `≤ 10` or `≤ √(2n)`;
`Chebyshev.theta_le_log4_mul_x`), and `θ(n) ≥ ψ(n) - 2√n log n` (`Chebyshev.psi_sub_theta_le`).
Hence `log D_n ≤ 11 ψ(n) + 2√n log n + log 4 · (10 + √(2n))`.  By PNT, for `δ = 1/400` and `n`
large, `ψ(n) ≤ (1+δ) n`, so `log D_n ≤ 11.03 n + o(n)`.  The logarithm of the quantity is (for
`Cst > 0`; the cases `Cst ≤ 0` are trivial or follow by `|·|`)
  `log D_n + log Cst + A m log 2 + 16 n log 2 - (32 n + 14 - 11 m) log 2
     ≤ (11.03 - 16 log 2) n + o(n) → -∞`,
since `16 log 2 > 16 · 0.6931471803 > 11.09` (`Real.log_two_gt_d9`).  So the quantity tends to `0`.

**Lean hints.** `Chebyshev.psi`, `Chebyshev.theta`, `Chebyshev.psi_eq_log_lcmUpto`,
`Chebyshev.theta_eq_sum_primesLE`, `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_sub_theta_le`,
`Chebyshev.theta_le_psi`, `Chebyshev.theta_mono`, `Nat.primesLE`, `Nat.cast_div_le`, `Real.log_prod`,
`Real.log_le_log_iff`, `Real.log_pow`, `Real.exp_log`, `Real.tendsto_exp_atBot`,
`Real.log_two_gt_d9`,
`isLittleO_pow_exp_pos_mul_atTop`, `Real.isLittleO_log_id_atTop`,
`tendsto_pow_atTop_atTop_of_one_lt` (for `2^m → ∞`), `Filter.Tendsto.comp`,
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `squeeze_zero'`, `Tendsto.eventually_le_const`,
`(tendsto_order.1 hPNT).2` to get `∀ᶠ x, ψ x / x < 1 + δ`.
Suggested structure: (1) a real-analysis lemma `log D_n ≤ 11 ψ(n) + E(n)` with explicit
`E(n) = O(√n log n)`; (2) PNT ⇒ `log D_n ≤ (11 + 12δ) n` eventually; (3) the exponential decay.

**Numerical check.** `python/mirror.py`, section "Stmt_Asymptotic": slope `≈ -0.09 = 11 - 16 log 2`
from `m ≈ 17` on (with exact `ψ, θ`); positive for small `m` (so only the limit statement is true).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem Asymptotic_proof : Stmt_Asymptotic := by
  sorry

end Zeta2

end
