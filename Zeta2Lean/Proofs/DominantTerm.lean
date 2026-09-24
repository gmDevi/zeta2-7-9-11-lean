import Zeta2Lean.Statements

/-!
# The dominant term (proof.md §7 "Dominant term"; Lai (6.3), (6.5))

**Task.** Prove `Stmt_L5Dom` from `Stmt_Delta`, `Stmt_DeltaFun`, `Stmt_Digit`: for `m ≥ 2`,
(i) `DeltaGe m (target m + 2) domTerm`, and
(ii) `‖volkenbornSum domTerm m‖ = 2^{-target m}`, `target m = 32n + 14 - 11m`, `n = 2^m - 1`.

**Informal proof.** `domTerm m x = K · Φ(x)` with
`K = -336 · 2^{24n+8} · n!^6 · W^2` (`W = (k₀-1)!(n-k₀)!`, `k₀ = 2^{m-1}`) and
`Φ = C(x+n,n)^6 · Y_{k₀}(x)^2 · h₀(x)`,
`Y_{k₀}(x) = C(x+k₀-1, k₀-1) · C(x+n, k₀-1)` (note `n - k₀ = k₀ - 1 = 2^{m-1} - 1`).
`v₂(K) = 4 + 24n + 8 + 6(n-m) + 2(n+1-2m) = 32n + 14 - 10m` exactly (`336 = 2^4 · 21`,
`Digit.fact`, `Digit.dom`).
(i) `Φ = (C(x+n,n)^2)^3 · C(x+k₀-1,k₀-1)^2 · C(x+n,k₀-1)^2 · h₀`: `Δ_m(C(x+n,n)^2) ≥ 1-(m-1) = 2-m`
(`DeltaFun.binomSq`, `Nat.log 2 n = m-1 < m`); `Δ(C(·, k₀-1)) ≥ -(m-2)` (`Nat.log 2 (2^{m-1}-1) = m-2`);
`Δ(h₀) ≥ 0`; all `ℤ₂`-valued, so `Δ_m(Φ) ≥ 2 - m` (`Delta.mul`, `Delta.ofAll`, `Delta.mono`) and
`Δ_m(domTerm) ≥ 32n + 14 - 10m + 2 - m = target + 2` (`Delta.smul`).
(ii) `volkenbornSum domTerm m = 2^{-m} K ∑_{x<2^m} Φ(x)`.  `Φ(0) = C(n, k₀-1)^2 h₀(0)` is a
2-adic unit: `C(2^m - 1, j)` is odd for `j ≤ 2^m - 1` (no carries: Kummer/Lucas) and
`h₀(0) = ∏_{k≤n} (2k+1)^{-8}`.  For `1 ≤ x ≤ 2^m - 1`, `C(x + 2^m - 1, 2^m - 1)` is even (adding `x`
and `2^m - 1` in base 2 carries), so `‖Φ(x)‖ ≤ 1/2` (in fact `≤ 2^{-6}`).  Ultrametric:
`‖∑_{x<2^m} Φ(x)‖ = 1`, hence `‖volkenbornSum domTerm m‖ = 2^m · 2^{-(32n+14-10m)} = 2^{-target m}`.

**Lean hints.** `Stmt_Delta` (`mul`, `ofAll`, `mono`, `smul`), `Stmt_DeltaFun` (`binom`,
`binomSq`, `hcoefInt`, `hcoefDelta`), `Stmt_Digit` (`fact`, `dom`);
`padicValNat_choose` (Kummer, carries), `Choose.lucas_theorem`, `Nat.Prime.dvd_choose_pow`,
`Padic.norm_natCast_eq_one_iff`, `Padic.norm_eq_of_norm_add_lt_right`,
`Padic.norm_eq_of_norm_add_lt_left`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`,
`Finset.sum_range_succ'` (split off `x = 0`), `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
`Padic.norm_p_pow`, `PowerSeries.constantCoeff_inv` (for `hcoef n 0 x = ∏ (2x+2k+1)^{-8}`),
`Nat.log_eq_iff`.

**Numerical check.** `python/mirror.py`, section "Stmt_L5Dom": `v₂(R_m(domTerm)) = target m` for
`m = 2..5`, and the `Δ_m` bound on `k < 2^{m+4}`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem L5Dom_proof (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (hG : Stmt_Digit) : Stmt_L5Dom := by
  sorry

end Zeta2

end
