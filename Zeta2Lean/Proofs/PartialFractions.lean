import Zeta2Lean.Statements

/-!
# Partial fractions of `R_n` (proof.md §3, "useful formula")

**Task.** Prove `Stmt_PF` (two fields):
* `poly : Rnum n = PFpoly n`, i.e.
  `2^{16n}(2t+n)(t+1/2)_n^8 = ∑_{i=1}^{8} ∑_{k=0}^{n} r_{i,k} (t+k)^{8-i} ∏_{j≤n, j≠k} (t+j)^8`;
* `series`: for `y` with `y + j ≠ 0` (`j ≤ n`), in `PowerSeries ℚ`,
  `Rser n y = ∑_{i,k} C (r_{i,k}) * ((C (y+k) + X)^i)⁻¹`  (Taylor expansion of `R_n(y+ε)`).
No hypotheses; everything follows from the definition `r_{8-μ,k} = [ε^μ] G_k(ε)`.

**Informal proof of `poly`.** Let `P := Rnum n - PFpoly n ∈ ℚ[t]`.
1. `natDegree P ≤ 8n + 7` (`Rnum` has degree `8n+1`; each term of `PFpoly` has degree
   `(8-i) + 8n ≤ 8n+7`).
2. For each `k₀ ≤ n`, `(t + k₀)^8 ∣ P`.  Substitute `t = -k₀ + ε` (i.e. look at
   `Polynomial.taylor (-k₀) P = P.comp (X - C k₀)` coerced to `PowerSeries ℚ`):
   * sign identities (reindex `j ↦ j - k₀`):
     `∏_{j<n} (j - k₀ + 1/2 + ε) = (-1)^{k₀} (1/2-ε)_{k₀} (1/2+ε)_{n-k₀}` and
     `∏_{j≤n, j≠k₀} (j - k₀ + ε) = (-1)^{k₀} (1-ε)_{k₀} (1+ε)_{n-k₀}`;
   * hence `Rnum(-k₀+ε) = G_{k₀}(ε) · V(ε)` with `V := ∏_{j≠k₀} (j - k₀ + ε)^8` (the `Ψ`-inverse in
     `G_{k₀}` cancels against `V`; `2t+n ↦ n - 2k₀ + 2ε`);
   * `PFpoly(-k₀+ε) = V(ε) · ∑_{i=1}^{8} r_{i,k₀} ε^{8-i} + ε^8 · (…)`, since every term with
     `k ≠ k₀` contains the factor `(t + k₀)^8 = ε^8`;
   * `∑_{i=1}^{8} r_{i,k₀} ε^{8-i} = ∑_{μ<8} [ε^μ]G_{k₀} ε^μ` (definition of `rcoef`), so
     `P(-k₀+ε) = V · (G_{k₀} - trunc₈ G_{k₀}) - ε^8(…)` has all coefficients `< 8` equal to `0`.
   Therefore `X^8 ∣ taylor (-k₀) P`, i.e. `(X + C k₀)^8 ∣ P`.
3. The `(X + C k)^8`, `k ≤ n`, are pairwise coprime, so `∏_{k≤n} (X + C k)^8 ∣ P`; this product has
   degree `8n + 8 > natDegree P`, so `P = 0`.

**Informal proof of `series`.** Apply the ring hom `Polynomial.eval₂RingHom C (C y + X) :
ℚ[t] →+* ℚ⟦X⟧` to `poly` and multiply by the inverse of the unit `(∏_{j≤n} (C (y+j) + X))^8`
(constant coefficient `∏ (y+j)^8 ≠ 0`).  Note `C (y + 1/2 + j) + X` is the image of `t + (j+1/2)`,
and `(C(y+k)+X)^{8-i} ∏_{j≠k} (C(y+j)+X)^8 · (∏_j (C(y+j)+X))^{-8} = ((C(y+k)+X)^i)⁻¹`.

**Lean hints.** `Polynomial.taylor`, `Polynomial.taylor_coeff`, `Polynomial.rootMultiplicity_eq_natTrailingDegree`,
`Polynomial.le_rootMultiplicity_iff`, `Polynomial.pow_rootMultiplicity_dvd`,
`Polynomial.coeToPowerSeries.ringHom`, `Polynomial.coe_mul`, `Polynomial.coe_pow`,
`Polynomial.coe_X`, `Polynomial.coe_C`, `Polynomial.coeff_coe`, `PowerSeries.X_pow_dvd_iff`,
`PowerSeries.trunc`, `PowerSeries.coeff_trunc`, `PowerSeries.mul_inv_cancel`,
`PowerSeries.inv_mul_cancel`, `PowerSeries.constantCoeff_inv`, `PowerSeries.mul_inv_rev`,
`Polynomial.pairwise_coprime_X_sub_C`, `IsCoprime.pow`, `Finset.prod_dvd_of_coprime`,
`Polynomial.eq_zero_of_dvd_of_degree_lt`, `Polynomial.natDegree_prod_le`, `Polynomial.natDegree_pow_le`,
`Polynomial.eval₂RingHom`, `Finset.prod_erase_mul`, `Finset.prod_range_succ`.
The `if` in `rcoef` is `True` on `Icc 1 8 × range (n+1)`.

**Numerical check.** `python/mirror.py`, section "Stmt_PF" (`poly` for `n ≤ 6`, `series` at random
rational `y`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem PF_proof : Stmt_PF := by
  sorry

end Zeta2

end
