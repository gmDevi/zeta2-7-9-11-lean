import Zeta2Lean.Statements

/-!
# The 2-adic Δ-calculus (proof.md P3(a)–(c); Lai Def. 2.3, Lemmas 2.4, 2.5(2); LSZ Lemma 2.6)

**Task.** Prove every field of the structure `Stmt_Delta` (see `Statements.lean`): `riemann`,
`riemannAll`, `mono`, `monoAll`, `ofAll`, `sum`, `sumAll`, `smul`, `smulAll`, `mul`, `mulAll`.
No hypotheses.  Recall (`Defs.lean`):
`DeltaGe m c f :⇔ ∀ k ≥ 2^m, ‖f k - f (k - 2^{log₂ k})‖ ≤ 2^{-(c + log₂ k)}`,
`DeltaAll c f :⇔ DeltaGe 0 c f ∧ ‖f 0‖ ≤ 2^{1-c}`.

**Informal proofs.**
* `riemann` (Lai Lemma 2.4 (2.3)): for every `l`,
  `R_{l+1} - R_l = 2^{-(l+1)} ∑_{k=2^l}^{2^{l+1}-1} (f(k) - f(k - 2^l))`
  (`R_N := volkenbornSum f N`; split `range 2^{l+1}` as `range 2^l ∪ [2^l, 2^{l+1})` and shift the
  second part by `2^l`), and `Nat.log 2 k = l` on that range.  For `l ≥ m` each summand has norm
  `≤ 2^{l+1} · 2^{-(c+l)} = 2^{1-c}`; ultrametric ⇒ `‖R_{l+1} - R_l‖ ≤ 2^{1-c}`; telescoping
  `R_M - R_m = ∑_{l=m}^{M-1} (R_{l+1} - R_l)` and the ultrametric inequality again.
* `riemannAll`: `R_0 = f 0` and `‖f 0‖ ≤ 2^{1-c}`; apply `riemann` with `m = 0`.
* `mono`/`monoAll`/`ofAll`: monotonicity of `zpow` in the exponent (`2 > 1`), and `2^m ≤ k` for a
  larger `m'` implies it for `m`.
* `sum`/`sumAll`: `Finset.induction_on`; the zero function satisfies every bound; for sums use
  `(f+g)(k) - (f+g)(k₋) = (f(k)-f(k₋)) + (g(k)-g(k₋))` and `Padic.nonarchimedean`.
* `smul`/`smulAll`: `‖a (f k - f k₋)‖ = ‖a‖ ‖f k - f k₋‖ ≤ 2^{-e} 2^{-(c + log₂ k)}`, `zpow_add₀`.
* `mul`/`mulAll` (Lai 2.5(2)): `f(k)g(k) - f(k₋)g(k₋) = g(k₋)(f(k)-f(k₋)) + f(k)(g(k)-g(k₋))` with
  `‖f(k)‖, ‖g(k₋)‖ ≤ 1`; and `‖f 0 g 0‖ ≤ ‖f 0‖ ≤ 2^{1-c}`.

**Lean hints.** `Finset.range_eq_Ico`, `Finset.sum_range_add_sum_Ico`, `Finset.sum_Ico_eq_sum_range`,
`Finset.sum_range_succ`, `Nat.log_eq_iff : Nat.log b n = m ↔ b^m ≤ n ∧ n < b^(m+1)` (side
condition `m ≠ 0 ∨ 1 < b ∧ n ≠ 0`), `Padic.nonarchimedean`, `Padic.norm_p_pow`, `Padic.norm_p_zpow`,
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_mul`, `norm_inv`, `zpow_le_zpow_right₀`,
`zpow_add₀`, `zpow_natCast`, `Finset.induction_on`, `Finset.sum_insert`.
`(2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2])` (`Nat.cast_ofNat`) to use `Padic.norm_p_pow` with `p = 2`.

**Numerical check.** Consequences are checked in `python/mirror.py` ("Stmt_DeltaFun",
"Stmt_LeibTermBound", "Stmt_L5Dom").
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem Delta_proof : Stmt_Delta := by
  sorry

end Zeta2

end
