import Zeta2Lean.Statements

/-!
# L4: archimedean size of the coefficients (proof.md §6)

**Task.** Prove `Stmt_L4`: there are constants `Cst`, `A` with
`|ρ₀|, |Z₇|, |Z₉|, |Z₁₁| ≤ Cst (n+1)^A 2^{16n}` for all `n`.  No hypotheses.  Any constants are
fine (the proof has an exponential margin; proof.md gets `Cst = 3.4·10⁸`, `A = 2` via Cauchy
estimates, but **elementary majorants** are recommended instead).

**Informal proof (majorants).** For `A, B ∈ ℚ⟦X⟧` write `A ≼ B` if `|[X^j] A| ≤ [X^j] B` for all
`j` (then `B` has non-negative coefficients).  If `A ≼ B` and `A' ≼ B'` then `A A' ≼ B B'` and
`A + A' ≼ B + B'`.  Basic majorants, for `c > 0`:
* `C c ± X ≼ C c + X`, and `c + X ≼ c (1 + 2X)` if `c ≥ 1/2`;
* `(C c ± X)⁻¹ ≼ c⁻¹ (1 - X)⁻¹` if `c ≥ 1` (coefficients `c^{-j-1} ≤ c^{-1}`).
Hence `(1/2 ∓ ε)_k ≼ (1/2)_k (1+2X)^k`, `((1 ∓ ε)_k)⁻¹ ≼ (1/k!) (1-X)^{-k}`, and
  `Ψ_k ≼ c_{k} (1+2X)^n (1-X)^{-n}`, `c_k = (1/2)_k (1/2)_{n-k} / (k! (n-k)!) = C(2k,k) C(2n-2k,n-k)/4^n ≤ 1`,
  `Gser n k ≼ 2^{16n} (n + 2X) (1+2X)^{8n} (1-X)^{-8n}`.
For `j ≤ 7`: `[X^j] (1+2X)^{8n} (1-X)^{-8n} = ∑_{a ≤ j} C(8n,a) 2^a C(8n+j-a-1, j-a) ≤ 8 (16n+16)^7`.
So `|r_{i,k}| ≤ 2^{16n} (n+2) · 8 · 16^7 (n+1)^7 ≤ 2^{36} (n+1)^8 2^{16n}`.  Then
`|Z₁₁| = 10321920 |∑_k r_{7,k}| ≤ 2^{24} (n+1) · 2^{36}(n+1)^8 2^{16n}`, similarly `Z₇, Z₉`, and with
`0 ≤ A_k^{(s)} ≤ k 2^s ≤ (n+1) 2^{12}` (`s ≤ 12`, each term `(ℓ+1/2)^{-s} ≤ 2^s`):
`|ρ₀| ≤ 8 · 7920 · (n+1) · 2^{36}(n+1)^8 2^{16n} · (n+1) 2^{12}`.  So `Cst = 2^{70}`, `A = 10` work.
(Only the shape `poly(n) · 2^{16n}` matters.)

**Lean hints.** `PowerSeries.coeff_mul`, `Finset.abs_sum_le_sum_abs`, `abs_mul`,
`Finset.sum_le_sum`, `mul_le_mul`, `PowerSeries.coeff_pow`, `PowerSeries.eq_inv_iff_mul_eq_one`
(identify `(C c + C d X)⁻¹` with `mk (fun j => (-d)^j / c^(j+1))`), `Nat.choose_le_pow`,
`Nat.choose_le_pow_div`, `Nat.cast_le`, `Rat.cast_abs`, `Rat.cast_le`, `pow_le_pow_left₀`,
`archBound` unfolds to `Cst * ((n:ℝ)+1)^A * 2^(16*n)`.  It is easiest to work in `ℚ` and cast to
`ℝ` at the end (`Rat.cast_le`, `abs` commutes with the cast).

**Numerical check.** `python/mirror.py`, section "Stmt_L4": with `C = 3.4e8`, `A = 2` the ratio is
`≤ 0.061` for `n ≤ 40` and `n ∈ {60, 100}`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem L4_proof : Stmt_L4 := by
  sorry

end Zeta2

end
