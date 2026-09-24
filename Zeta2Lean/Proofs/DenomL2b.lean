import Zeta2Lean.Statements

/-!
# L2b: `d_n^{12} ρ₀ ∈ ℤ` — the root trick (proof.md §4.2; Lai Lemma 4.6, LLS Lemma 5.6)

**Task.** Prove `Stmt_L2b` from `Stmt_PF` and `Stmt_L2a`.

**Informal proof.** Write `ρ₀ = -∑_{k=1}^{n} ∑_{ℓ₀=0}^{k-1} X(k,ℓ₀)` with
`X(k,ℓ₀) := ∑_{i=1}^{8} (i)₄ r_{i,k} (ℓ₀ + 1/2)^{-(i+4)}` (unfold `Ahalf`, swap sums).
It suffices that `d_n^{12} X(k₀,ℓ₀)` is `q`-integral for every prime `q` and all `1 ≤ k₀ ≤ n`,
`ℓ₀ < k₀` (then so is `d_n^{12} ρ₀`, and a rational that is `q`-integral for all `q` is an integer).
* `q = 2`: `(ℓ₀+1/2)^{-(i+4)} = 2^{i+4} (2ℓ₀+1)^{-(i+4)}` and `d_n^{8-i} r_{i,k} ∈ ℤ` (L2a), so
  `v₂(d_n^{12} (i)₄ r_{i,k} (ℓ₀+1/2)^{-(i+4)}) ≥ (i+4) v₂(d_n) + i + 4 ≥ 0`.
* `q` odd: each term is `(i)₄ · [d_n^{8-i} r_{i,k₀}] · (d_n/(2ℓ₀+1))^{i+4} · 2^{i+4}`, so it is
  `q`-integral unless `v_q(2ℓ₀+1) > v_q(d_n)`.  Suppose that.  The point `t₀ := -k₀ + ℓ₀ + 1/2`
  satisfies `t₀ + 1/2 + j₀ = 0` for `j₀ = k₀ - ℓ₀ - 1 ∈ [0, n-1]`, so `R_n` has a zero of order 8
  at `t₀`.  Apply `Stmt_PF.series` at `y = t₀` (`t₀ + j ∈ 1/2 + ℤ` is never `0`): the left side
  `Rser n t₀` contains the factor `(C(t₀ + 1/2 + j₀) + X)^8 = X^8`, so its coefficient of `ε^4`
  vanishes; on the right, `[ε^4] ((C a + X)^i)⁻¹ = C(i+3,4) a^{-i-4} = (i)₄/24 · a^{-i-4}`.  Hence
  `∑_{k=0}^{n} ∑_i (i)₄ r_{i,k} (t₀ + k)^{-i-4} = 0`, i.e.
  `X(k₀,ℓ₀) = -∑_{k ≠ k₀} ∑_i (i)₄ r_{i,k} (ℓ₀ - k₀ + k + 1/2)^{-i-4}`.
  If `d_n^{12} X(k₀,ℓ₀)` were not `q`-integral, some `k₁ ≠ k₀` would have
  `v_q(2(ℓ₀-k₀+k₁)+1) > v_q(d_n)` too; subtracting, `q^{v_q(d_n)+1} ∣ 2(k₁ - k₀)`, hence
  `q^{v_q(d_n)+1} ∣ k₁ - k₀` with `0 < |k₁ - k₀| ≤ n < q^{v_q(d_n)+1}` — contradiction
  (`v_q(d_n) = ⌊log_q n⌋`).  [So in fact every `d_n^{12} X(k₀,ℓ₀)` is `q`-integral.]

**Lean hints.** `padicValRat.min_le_padicValRat_add`, `padicValRat.le_padicValRat_add_of_le`,
`padicValRat.mul`, `padicValRat.pow`, `padicValRat.inv`, `padicValRat.of_int`, `padicValRat_of_nat`,
`Nat.factorization_lcmUpto : (lcmUpto n).factorization p = Nat.log p n`,
`Nat.lt_pow_succ_log_self`, `Nat.pow_log_le_self`, `Rat.den_eq_one_iff`, `Rat.num_div_den`,
`Nat.eq_one_iff_not_exists_prime_dvd` ("no prime divides the denominator"), `PowerSeries.coeff_mul`,
`PowerSeries.X_pow_dvd_iff`, `Finset.prod_erase_mul`, `Finset.sum_comm`, `Finset.sum_sigma'`.
One clean route: prove `∀ q prime, 0 ≤ padicValRat q (d_n^{12} ρ₀)` (or `ρ₀ = 0`), then conclude
`(d_n^{12} ρ₀).den = 1` (a positive integer with no prime factor is `1`: `Nat.eq_one_iff_not_exists_prime_dvd`).

**Numerical check.** `python/mirror.py`, section "Stmt_BlockF, Stmt_L2a, Stmt_L2b".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem L2b_proof (hPF : Stmt_PF) (hL2a : Stmt_L2a) : Stmt_L2b := by
  sorry

end Zeta2

end
