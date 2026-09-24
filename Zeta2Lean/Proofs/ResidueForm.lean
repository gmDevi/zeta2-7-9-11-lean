import Zeta2Lean.Statements

/-!
# Residue form of `ρ₀` (proof.md §4.3 Step 1; LSZ proof of Lemma 5.3)

**Task.** Prove `Stmt_ResidueForm : ρ₀ = -24 ∑_{ℓ=1}^{n} [ε^7] T_{n,ℓ}(ε)`.  No hypotheses.

**Informal proof.** Since `(x-ε)^{-5} = ∑_{j≥0} C(j+4,4) x^{-5-j} ε^j` and `C(i+3,4) = (i)₄/24`,
  `∑_{i=1}^{8} (i)₄ r_{i,k} x^{-(i+4)} = 24 [ε^7] ( G_k(ε) · (x - ε)^{-5} )`
(`r_{i,k} = [ε^{8-i}] G_k`, sum over `μ = 8 - i ∈ [0,7]`).  Take `x = ℓ - 1/2` with `1 ≤ ℓ ≤ k`:
`(1/2-ε)_k = (1/2-ε)_{ℓ-1} · (ℓ-1/2-ε) · (ℓ+1/2-ε)_{k-ℓ}` (`psPoch` splits:
`∏_{j<k} = ∏_{j<ℓ-1} · (j = ℓ-1) · ∏_{ℓ ≤ j < k}`), so `(ℓ-1/2-ε)^8 / (ℓ-1/2-ε)^5 = (ℓ-1/2-ε)^3` and
  `G_k(ε) (ℓ-1/2-ε)^{-5} = 2^{16n} (ℓ-1/2-ε)^3 (1/2-ε)_{ℓ-1}^8 · (n-2k+2ε) (ℓ+1/2-ε)_{k-ℓ}^8
     (1/2+ε)_{n-k}^8 / ((1-ε)_k^8 (1+ε)_{n-k}^8)`,
the `k`-th summand of `T_{n,ℓ}` (times the prefactor).  Finally
`ρ₀ = -∑_i ∑_{k=0}^{n} (i)₄ r_{i,k} ∑_{ℓ₀<k} (ℓ₀+1/2)^{-(i+4)}`; with `ℓ = ℓ₀ + 1` and exchanging
the order of summation over `{(ℓ,k) : 1 ≤ ℓ ≤ k ≤ n}`, `ρ₀ = -24 ∑_{ℓ=1}^{n} [ε^7] T_{n,ℓ}`.

**Lean hints.** `PowerSeries.coeff_mul`, `PowerSeries.mul_inv_cancel`, `PowerSeries.inv_mul_cancel`,
`PowerSeries.mul_inv_rev`, geometric-type expansion of `((C x - X)^5)⁻¹` (prove the coefficient
formula `coeff j ((C x - X)^5)⁻¹ = C(j+4,4) x^{-5-j}` by `PowerSeries.eq_inv_iff_mul_eq_one` and a
coefficient computation, or via `(C x - X)⁻¹ = mk (fun j => x^{-j-1})` and `coeff_pow`),
`Finset.prod_range_add`, `Finset.prod_Ico_eq_prod_range`, `Finset.sum_comm'`, `Finset.sum_sigma'`,
`Finset.range_eq_Ico`, `Finset.sum_Ico_eq_sum_range`, `Nat.cast_choose` (binomial arithmetic).
Check with `Ahalf`: `Ahalf k s = ∑_{ℓ₀ < k} (ℓ₀ + 1/2)⁻¹^s` and `ℓ₀ + 1/2 = ℓ - 1/2`.

**Numerical check.** `python/mirror.py`, section "Stmt_ResidueForm ..." (`n ≤ 8`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem ResidueForm_proof : Stmt_ResidueForm := by
  sorry

end Zeta2

end
