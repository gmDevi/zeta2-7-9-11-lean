import Zeta2Lean.Statements

/-!
# Symmetry and vanishing sums of the partial-fraction coefficients (proof.md §3, Lemma 1)

**Task.** Prove `Stmt_CoeffVanish` (fields `symm`, `c1`, `ceven`) from `Stmt_PF`.

**Informal proof.**
* `symm` (`r_{i,n-k} = (-1)^{i+1} r_{i,k}`, `k ≤ n`): purely from the definitions.  With
  `ρ := PowerSeries.rescale (-1)` (`ε ↦ -ε`, a ring hom): `ρ (psPoch c d k) = psPoch c (-d) k`, so
  `Psi n (n-k) = ρ (Psi n k)` (use `n - (n - k) = k`; `ρ` commutes with inverses of units), and
  `C(n - 2(n-k)) + 2X = -ρ (C(n-2k) + 2X)`.  Hence `Gser n (n-k) = -ρ (Gser n k)` and
  `coeff μ (Gser n (n-k)) = -(-1)^μ coeff μ (Gser n k)`; with `μ = 8 - i` this is
  `(-1)^{i+1} r_{i,k}`.  If `i = 0` or `i > 8` both sides are `0`.
* `c1` (`∑_k r_{1,k} = 0`, "degree `R_n = -7`"): compare the coefficients of `t^{8n+7}` in
  `Stmt_PF.poly`.  `Rnum n` has `natDegree ≤ 8n+1 < 8n+7`, so its coefficient is `0`.  In
  `PFpoly n`, the terms with `i ≥ 2` have `natDegree ≤ 8n+6`, and for `i = 1` the polynomial
  `(t+k)^7 ∏_{j≠k} (t+j)^8` is monic of `natDegree 8n+7`; so the coefficient is `∑_k r_{1,k}`.
* `ceven`: for even `i`, `symm` gives `r_{i,n-k} = -r_{i,k}`, so reflecting the sum
  (`Finset.sum_range_reflect`) gives `c_i = -c_i`, i.e. `c_i = 0`.

**Lean hints.** `PowerSeries.rescale`, `PowerSeries.coeff_rescale : coeff n (rescale a f) = a^n * coeff n f`,
`PowerSeries.rescale_X : rescale a X = C a * X`, `map_prod`, `map_pow`, `map_mul`,
`PowerSeries.inv_eq_iff_mul_eq_one`, `PowerSeries.constantCoeff_inv`, `Finset.sum_range_reflect`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.Monic.coeff_natDegree`,
`Polynomial.monic_prod_of_monic`, `Polynomial.monic_X_add_C`, `Polynomial.natDegree_prod_of_monic`,
`Polynomial.finsetSum_coeff`, `Polynomial.coeff_C_mul`, `Even.neg_one_pow`, `Odd.neg_one_pow`.

**Numerical check.** `python/mirror.py`, section "Stmt_CoeffVanish" (`n ≤ 30`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### `symm`: the reflection `ε ↦ -ε` -/

/-- `rescale a` fixes constants. -/
private lemma cv_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext m
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

/-- `rescale a` commutes with the power-series inverse (over a field; both sides are `0` when the
constant coefficient vanishes). -/
private lemma cv_rescale_inv (a : ℚ) (φ : PowerSeries ℚ) :
    rescale a φ⁻¹ = (rescale a φ)⁻¹ := by
  have hc : constantCoeff (rescale a φ) = constantCoeff φ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  by_cases h : constantCoeff φ = 0
  · rw [PowerSeries.inv_eq_zero.mpr h, map_zero, PowerSeries.inv_eq_zero.mpr (hc.trans h)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (hc ▸ h), ← map_mul, PowerSeries.inv_mul_cancel φ h,
      map_one]

/-- `ε ↦ -ε` sends `(c + dε)_k` to `(c - dε)_k`. -/
private lemma cv_rescale_psPoch (c d : ℚ) (k : ℕ) :
    rescale (-1 : ℚ) (psPoch c d k) = psPoch c (-d) k := by
  unfold psPoch
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [map_add, map_mul, cv_rescale_C, cv_rescale_C, rescale_X, ← mul_assoc, ← map_mul, mul_neg_one]

/-- `Ψ_{n-k}(ε) = Ψ_k(-ε)`. -/
private lemma cv_rescale_Psi (n k : ℕ) (hk : k ≤ n) :
    rescale (-1 : ℚ) (Psi n k) = Psi n (n - k) := by
  unfold Psi
  rw [Nat.sub_sub_self hk]
  simp only [map_mul, cv_rescale_inv, cv_rescale_psPoch, neg_neg, PowerSeries.mul_inv_rev]
  ring

/-- `G_{n-k}(ε) = -G_k(-ε)`. -/
private lemma cv_Gser_reflect (n k : ℕ) (hk : k ≤ n) :
    Gser n (n - k) = -rescale (-1 : ℚ) (Gser n k) := by
  unfold Gser
  simp only [map_mul, map_add, map_pow, cv_rescale_C, rescale_X, cv_rescale_Psi n k hk]
  have h1 : (C ((n : ℚ) - 2 * ((n - k : ℕ) : ℚ)) : PowerSeries ℚ) = -C ((n : ℚ) - 2 * k) := by
    rw [← map_neg]
    congr 1
    rw [Nat.cast_sub hk]
    ring
  rw [h1]
  simp only [map_neg, map_one]
  ring

/-- `[ε^μ] G_{n-k} = -(-1)^μ [ε^μ] G_k`. -/
private lemma cv_coeff_Gser_reflect (n k μ : ℕ) (hk : k ≤ n) :
    coeff μ (Gser n (n - k)) = -((-1 : ℚ) ^ μ * coeff μ (Gser n k)) := by
  rw [cv_Gser_reflect n k hk, map_neg, coeff_rescale]

/-- `r_{i,n-k} = (-1)^{i+1} r_{i,k}`. -/
private lemma cv_symm (n i k : ℕ) (hk : k ≤ n) :
    rcoef n i (n - k) = (-1) ^ (i + 1) * rcoef n i k := by
  unfold rcoef
  by_cases hi : 1 ≤ i ∧ i ≤ 8
  · rw [ite_eq_left ⟨hi.1, hi.2, Nat.sub_le n k⟩, ite_eq_left ⟨hi.1, hi.2, hk⟩,
      cv_coeff_Gser_reflect n k _ hk]
    obtain ⟨h1, h8⟩ := hi
    interval_cases i <;> norm_num
  · rw [ite_eq_right (fun h => hi ⟨h.1, h.2.1⟩), ite_eq_right (fun h => hi ⟨h.1, h.2.1⟩),
      mul_zero]

/-! ### `c1`: the top coefficient of `Stmt_PF.poly` -/

/-- `natDegree Rnum ≤ 8n + 1`. -/
private lemma cv_natDegree_Rnum (n : ℕ) : (Rnum n).natDegree ≤ 8 * n + 1 := by
  unfold Rnum
  have h1 : (∏ j ∈ range n, (Polynomial.X + Polynomial.C ((j : ℚ) + 1 / 2))).natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one]
  have hA : (Polynomial.C ((2 : ℚ) ^ (16 * n)) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ))).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_linear_le
  have hB : ((∏ j ∈ range n, (Polynomial.X + Polynomial.C ((j : ℚ) + 1 / 2))) ^ 8).natDegree ≤
      8 * n := by
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [h1]
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-- The `(i,k)` basis polynomial `(t+k)^{8-i} ∏_{j ≠ k} (t+j)^8` is monic ... -/
private lemma cv_monic_term (n i k : ℕ) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (8 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 8).Monic :=
  ((Polynomial.monic_X_add_C _).pow _).mul
    (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 8))

/-- ... of degree `(8 - i) + 8n` (for `k ≤ n`). -/
private lemma cv_natDegree_term (n i k : ℕ) (hk : k ∈ range (n + 1)) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (8 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 8).natDegree =
      (8 - i) + 8 * n := by
  rw [Polynomial.Monic.natDegree_mul ((Polynomial.monic_X_add_C _).pow _)
      (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 8)),
    Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 8)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one, Finset.sum_const,
    smul_eq_mul, Finset.card_erase_of_mem hk, Finset.card_range, Nat.add_sub_cancel]
  ring

/-- The coefficient of `t^{8n+7}` in `PFpoly n` is `c₁`. -/
private lemma cv_coeff_PFpoly (n : ℕ) : (PFpoly n).coeff (8 * n + 7) = csum n 1 := by
  unfold PFpoly csum
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_assoc, Polynomial.coeff_C_mul]
    have hdeg := cv_natDegree_term n 1 k hk
    rw [show 8 - 1 + 8 * n = 8 * n + 7 by omega] at hdeg
    rw [← hdeg, (cv_monic_term n 1 k).coeff_natDegree, mul_one]
  · intro i hi hi1
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [cv_natDegree_term n i k hk]
    have := (Finset.mem_Icc.mp hi).1
    omega
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, by norm_num⟩) h

/-- `c₁ = 0`. -/
private lemma cv_c1 (hPF : Stmt_PF) (n : ℕ) : csum n 1 = 0 := by
  rw [← cv_coeff_PFpoly n, ← hPF.poly n]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((cv_natDegree_Rnum n).trans_lt (by omega))

/-! ### `ceven` -/

/-- `c_i = 0` for even `i`. -/
private lemma cv_ceven (n i : ℕ) (hi : Even i) : csum n i = 0 := by
  have h := Finset.sum_range_reflect (fun k => rcoef n i k) (n + 1)
  have h2 : ∑ j ∈ range (n + 1), rcoef n i (n + 1 - 1 - j) = -csum n i := by
    unfold csum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_sub_cancel, cv_symm n i j hj', hi.add_one.neg_one_pow, neg_one_mul]
  have h3 : ∑ j ∈ range (n + 1), rcoef n i j = csum n i := rfl
  rw [h2, h3] at h
  linarith

theorem CoeffVanish_proof (hPF : Stmt_PF) : Stmt_CoeffVanish where
  symm := cv_symm
  c1 := cv_c1 hPF
  ceven := cv_ceven

end Zeta2

end
