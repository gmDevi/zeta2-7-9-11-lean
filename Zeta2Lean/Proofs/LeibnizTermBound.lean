import Zeta2Lean.Statements

/-!
# Δ-bound for each Leibniz term, `n = 2^m - 1` (proof.md §7 "Valuations", "Key identity",
"All other terms"; Lai Lemma 6.2)

**Task.** Prove `Stmt_LeibTermBound` from `Stmt_Delta`, `Stmt_DeltaFun`, `Stmt_Digit`: for `m ≥ 2`,
`n = 2^m - 1`, `k₀ = 2^{m-1}`, `γ ≤ 1`, `γ + β ≤ 3`, `M ∈ (Icc 1 n).finsuppAntidiag a`
(`a = 3 - γ - β`):
  `DeltaAll (32n + 13 - 11m + βm + ∑_l v₂ C(8, M l) + ∑_{l ≠ k₀} M l) (leibTerm n γ β M)`.

**Informal proof.** Write `leibTerm = K · Φ` with a rational constant `K` and a `ℤ₂`-valued `Φ`;
then `Δ(K Φ) ≥ v₂(K) + Δ(Φ)` (`Stmt_Delta.smulAll`, `‖K‖ = 2^{-v₂ K}`).
*Key identity.* `u := x + k₀` satisfies `2x + 1 + n = 2u` and, since `x C(x+n,n) = (n+1) C(x+n,n+1)`
and `n + 1 = 2^m`,
  `u · C(x+n, n) = 2^{m-1} Λ(x)`,  `Λ(x) := C(x+n,n) + 2 C(x+n,n+1)`,
with `Λ` integer-valued and `Δ(Λ) ≥ 1 - m` (`DeltaFun.binom`: `Δ(C(x+n,n)) ≥ -(m-1)`,
`Δ(C(x+n,n+1)) ≥ -m`, times 2 gives `≥ 1-m`; `Delta.sumAll`).
*Case γ = 1.* `K = -6 · 2^{24n+8} · 2 · 2^β · ∏_l C(8,M l) · n!^{6+β} · ∏_l W_l^{M l}`,
`Φ = h_β · C(x+n,n)^{6+β} · ∏_l Y_l^{M l}`.  All binomials have lower index `≤ n < 2^m`, so
`Δ ≥ -(m-1)` each (`DeltaFun.binom`, `Nat.log 2 N ≤ m-1`); `Δ(h_β) ≥ 0` (`DeltaFun.hcoefDelta`);
products of `ℤ₂`-valued functions: `Δ(Φ) ≥ -(m-1)` (`Delta.mulAll`, `Delta.monoAll`).
*Case γ = 0.* `(2x+1+n) C(x+n,n)^{5+β} = 2u C(x+n,n) C(x+n,n)^{4+β} = 2^m Λ C(x+n,n)^{4+β}`, so
`K = -6 · 2^{24n+8} · 2^m · 2^β · ∏_l C(8,M l) · n!^{5+β} · ∏_l W_l^{M l}`,
`Φ = h_β · Λ · C(x+n,n)^{4+β} · ∏_l Y_l^{M l}`, `Δ(Φ) ≥ 1 - m`.
*Valuations.* `v₂(6) = 1`, `v₂(n!) = n - m` (`Digit.fact`), `v₂(W_l) ≥ n + 1 - 2m + [l ≠ k₀]`
(`Digit.dom`, `Digit.other`; `W_l = Wl n l = (l-1)!(n-l)!`), so
`v₂(∏_l W_l^{M l}) ≥ a(n+1-2m) + #`, `# := ∑_{l≠k₀} M l`.  With `c := ∑_l v₂ C(8, M l)`:
  γ = 1 (`a = 2 - β`): `v₂(K) + Δ(Φ) ≥ (1 + 24n+8 + 1 + β + c + (6+β)(n-m) + a(n+1-2m) + #) - (m-1)`
  γ = 0 (`a = 3 - β`): `v₂(K) + Δ(Φ) ≥ (1 + 24n+8 + m + β + c + (5+β)(n-m) + a(n+1-2m) + #) + (1-m)`
and both right-hand sides simplify to `32n + 13 - 11m + βm + c + #` (proof.md §7).
Since `leibTerm` has a sign and the constants are exact, it is convenient to prove the bound in
the form `‖K‖ ≤ 2^{-e}` with `e` the displayed lower bound minus `Δ(Φ)`.

**Lean hints.** `Stmt_Delta` fields `smulAll`, `mulAll`, `sumAll`, `monoAll`;
`Stmt_DeltaFun` fields `binom`, `hcoefInt`, `hcoefDelta`; `Stmt_Digit` fields;
`Padic.norm_p_pow`, `Padic.norm_natCast_eq_one_iff`, `Padic.norm_eq_zpow_neg_valuation`
(or directly `‖(2:ℚ_[2])^k * (odd : ℚ_[2])‖ = 2^{-k}`);
`padicValNat.mul`, `padicValNat.pow`, `padicValNat.prime_pow`, `Nat.factorial_ne_zero`,
`Finset.mem_finsuppAntidiag`, `Finset.prod_pow_eq_pow_sum`, `Finsupp.support`,
`Nat.add_one_mul_choose_eq` (for `x C(x+n,n) = (n+1) C(x+n,n+1)`), `Nat.log_eq_iff`,
`Nat.log_mono_right`.  A general helper worth proving first: for `q : ℚ` with
`q = 2^e * (a/b)`, `a, b` odd, `‖(q:ℚ_[2])‖ = 2^{-e}`; and for integers `‖(z:ℚ_[2])‖ ≤ 2^{-v₂ z}`.

**Numerical check.** `python/mirror.py`, section "Stmt_LeibTermBound" (all terms, `m = 2, 3`, and
random terms `m = 4`, checked on `k < 2^{m+4}`; the minimum slack over non-dominant terms is 0,
attained at `γ = 0, β = 0, M = 3·[k₀]` as predicted).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem LeibTermBound_proof (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (hG : Stmt_Digit) :
    Stmt_LeibTermBound := by
  sorry

end Zeta2

end
