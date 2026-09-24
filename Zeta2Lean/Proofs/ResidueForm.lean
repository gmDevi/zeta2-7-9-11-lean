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

**Formalisation.** The inverse `(x - ε)^{-5}` is never taken: we use the explicit series
`rfInvSer x 4 = ∑_j C(j+4,4) x^{-(j+5)} ε^j` and prove `(C x - X)^5 * rfInvSer x 4 = 1`
(`rf_pow_mul_invSer`, by induction on the exponent via Pascal's rule).  Then
`G_k · rfInvSer x 4` is the `k`-th summand of `T_{n,ℓ}` (`summand_eq`, using the split of
`psPoch (1/2) (-1) k` and `PowerSeries.inv_pow` for the denominator), `24 [ε^7] (G · rfInvSer x 4)`
is computed coefficientwise (`coeff7_mul_invSer`), and the double sum is reindexed
(`ℓ = ℓ₀ + 1`, `Finset.sum_nbij'`) and exchanged (`Finset.sum_comm'`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### The explicit inverse of `(x - ε)^{m+1}` -/

/-- `∑_j C(j+m, m) x^{-(j+m+1)} ε^j`, the expansion of `(x - ε)^{-(m+1)}`. -/
private def rfInvSer (x : ℚ) (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun j => ((j + m).choose m : ℚ) * x⁻¹ ^ (j + m + 1)

private lemma rf_mul_invSer_zero (x : ℚ) (hx : x ≠ 0) :
    (C x - X) * rfInvSer x 0 = 1 := by
  ext j
  rw [sub_mul, map_sub, coeff_C_mul, coeff_one]
  rcases j with _ | j
  · simp only [rfInvSer, coeff_mk, coeff_zero_X_mul]
    simp only [add_zero, Nat.choose_self, Nat.cast_one, one_mul, zero_add, pow_one, sub_zero,
      ite_true]
    exact mul_inv_cancel₀ hx
  · rw [coeff_succ_X_mul]
    simp only [rfInvSer, coeff_mk, Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero,
      Nat.add_one_ne_zero, ite_false]
    linear_combination x⁻¹ ^ (j + 1) * mul_inv_cancel₀ hx

private lemma rf_mul_invSer_succ (x : ℚ) (hx : x ≠ 0) (m : ℕ) :
    (C x - X) * rfInvSer x (m + 1) = rfInvSer x m := by
  ext j
  rw [sub_mul, map_sub, coeff_C_mul]
  rcases j with _ | j
  · simp only [rfInvSer, coeff_mk, coeff_zero_X_mul, zero_add, Nat.choose_self, Nat.cast_one,
      one_mul, sub_zero]
    linear_combination x⁻¹ ^ (m + 1) * mul_inv_cancel₀ hx
  · rw [coeff_succ_X_mul]
    simp only [rfInvSer, coeff_mk]
    have h1 : (((j + 1 + (m + 1)).choose (m + 1) : ℕ) : ℚ) =
        ((j + 1 + m).choose m : ℚ) + ((j + (m + 1)).choose (m + 1) : ℚ) := by
      have e : j + 1 + (m + 1) = (j + (m + 1)) + 1 := by omega
      rw [e, Nat.choose_succ_succ', show j + (m + 1) = j + 1 + m by omega]
      push_cast
      ring
    rw [h1]
    linear_combination
      (((j + 1 + m).choose m : ℚ) + ((j + (m + 1)).choose (m + 1) : ℚ)) * x⁻¹ ^ (j + m + 2) *
        mul_inv_cancel₀ hx

/-- `(x - ε)^{m+1} · ∑_j C(j+m, m) x^{-(j+m+1)} ε^j = 1`. -/
private lemma rf_pow_mul_invSer (x : ℚ) (hx : x ≠ 0) (m : ℕ) :
    (C x - X) ^ (m + 1) * rfInvSer x m = 1 := by
  induction m with
  | zero => simpa using rf_mul_invSer_zero x hx
  | succ m ih =>
    rw [pow_succ, mul_assoc, rf_mul_invSer_succ x hx m, ih]

/-- `24 [ε^7] (G · (x-ε)^{-5}) = ∑_{i=1}^{8} (i)₄ [ε^{8-i}] G · x^{-(i+4)}`. -/
private lemma coeff7_mul_invSer (G : PowerSeries ℚ) (x : ℚ) :
    24 * coeff 7 (G * rfInvSer x 4) =
      ∑ i ∈ Icc (1 : ℕ) 8,
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * coeff (8 - i) G * x⁻¹ ^ (i + 4) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  symm
  apply Finset.sum_nbij' (fun i => 8 - i) (fun p => 8 - p)
  · intro a ha
    simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨h1, h8⟩ := hi
    simp only [rfInvSer, coeff_mk]
    interval_cases i <;> norm_num [Nat.choose] <;> ring

/-! ### Splitting the Pochhammer symbol -/

private lemma psPoch_add' (c d : ℚ) (a b : ℕ) :
    psPoch c d (a + b) = psPoch c d a * psPoch (c + a) d b := by
  unfold psPoch
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  push_cast
  ring

private lemma psPoch_succ' (c d : ℚ) (a : ℕ) :
    psPoch c d (a + 1) = psPoch c d a * (C (c + a) + C d * X) := by
  unfold psPoch
  rw [Finset.prod_range_succ]

/-- `(1/2-ε)_{ℓ'+1+m} = (1/2-ε)_{ℓ'} (ℓ'+1/2-ε) (ℓ'+3/2-ε)_m`. -/
private lemma psPoch_half_split (l' m : ℕ) :
    psPoch (1 / 2) (-1) (l' + 1 + m) =
      psPoch (1 / 2) (-1) l' * (C (((l' + 1 : ℕ) : ℚ) - 1 / 2) - X) *
        psPoch (((l' + 1 : ℕ) : ℚ) + 1 / 2) (-1) m := by
  rw [psPoch_add', psPoch_succ']
  congr 2
  · rw [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg]
    congr 2
    push_cast
    ring
  · push_cast
    ring

/-! ### The `k`-th summand of `T_{n,ℓ}` -/

/-- `G_k(ε) · (ℓ - 1/2 - ε)^{-5}` is the `k`-th summand of `T_{n,ℓ}` (with its prefactor). -/
private lemma summand_eq (n l k : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    C ((2 : ℚ) ^ (16 * n)) * (C ((l : ℚ) - 1 / 2) - X) ^ 3 * psPoch (1 / 2) (-1) (l - 1) ^ 8 *
      ((C ((n : ℚ) - 2 * k) + C 2 * X) * psPoch ((l : ℚ) + 1 / 2) (-1) (k - l) ^ 8 *
        psPoch (1 / 2) 1 (n - k) ^ 8 * (psPoch 1 (-1) k ^ 8 * psPoch 1 1 (n - k) ^ 8)⁻¹) =
    Gser n k * rfInvSer ((l : ℚ) - 1 / 2) 4 := by
  have hx : ((l : ℚ) - 1 / 2) ≠ 0 := by
    have : (1 : ℚ) ≤ l := by exact_mod_cast hl
    intro h
    linarith
  have hH := rf_pow_mul_invSer ((l : ℚ) - 1 / 2) hx 4
  have hsplit : psPoch (1 / 2) (-1) k = psPoch (1 / 2) (-1) (l - 1) * (C ((l : ℚ) - 1 / 2) - X) *
      psPoch ((l : ℚ) + 1 / 2) (-1) (k - l) := by
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = l' + 1 + m := ⟨k - (l' + 1), by omega⟩
    rw [psPoch_half_split]
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  have hW : (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹ ^ 8 =
      (psPoch 1 (-1) k ^ 8 * psPoch 1 1 (n - k) ^ 8)⁻¹ := by
    rw [PowerSeries.inv_pow, mul_pow]
  unfold Gser Psi
  rw [hsplit, ← hW]
  calc _ = C ((2 : ℚ) ^ (16 * n)) * (C ((l : ℚ) - 1 / 2) - X) ^ 3 *
        psPoch (1 / 2) (-1) (l - 1) ^ 8 *
        ((C ((n : ℚ) - 2 * k) + C 2 * X) * psPoch ((l : ℚ) + 1 / 2) (-1) (k - l) ^ 8 *
          psPoch (1 / 2) 1 (n - k) ^ 8 * (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹ ^ 8) *
        ((C ((l : ℚ) - 1 / 2) - X) ^ (4 + 1) * rfInvSer ((l : ℚ) - 1 / 2) 4) := by
          rw [hH, mul_one]
    _ = _ := by ring

/-! ### Main theorem -/

theorem ResidueForm_proof : Stmt_ResidueForm := by
  intro n
  -- `24 [ε^7] T_{n,ℓ} = ∑_{k=ℓ}^{n} ∑_i (i)₄ r_{i,k} (ℓ - 1/2)^{-(i+4)}`
  have hT : ∀ l ∈ Icc 1 n, 24 * coeff 7 (Tser n l) =
      ∑ k ∈ Icc l n, ∑ i ∈ Icc (1 : ℕ) 8,
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * ((l : ℚ) - 1 / 2)⁻¹ ^ (i + 4) := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    have hTs : Tser n l = ∑ k ∈ Icc l n, Gser n k * rfInvSer ((l : ℚ) - 1 / 2) 4 := by
      unfold Tser
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      exact summand_eq n l k hl.1 hk.1
    rw [hTs, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [coeff7_mul_invSer]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    rw [rcoef, ite_eq_left ⟨hi.1, hi.2, hk.2⟩]
  have hR : -24 * ∑ l ∈ Icc 1 n, coeff 7 (Tser n l) =
      -∑ l ∈ Icc 1 n, ∑ k ∈ Icc l n, ∑ i ∈ Icc (1 : ℕ) 8,
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * ((l : ℚ) - 1 / 2)⁻¹ ^ (i + 4) := by
    rw [neg_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl hT
  rw [hR]
  unfold rho0 Ahalf
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ k ∈ range (n + 1),
      ∑ i ∈ Icc (1 : ℕ) 8, ∑ l0 ∈ range k,
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * ((l0 : ℚ) + 1 / 2)⁻¹ ^ (i + 4) =
      ∑ l ∈ Icc 1 k, ∑ i ∈ Icc (1 : ℕ) 8,
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * ((l : ℚ) - 1 / 2)⁻¹ ^ (i + 4) := by
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_nbij' (fun l0 => l0 + 1) (fun l => l - 1)
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢
      omega
    · intro a _
      simp
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      omega
    · intro a _
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring_nf
  rw [Finset.sum_congr rfl h1]
  apply Finset.sum_comm'
  intro k l
  simp only [Finset.mem_range, Finset.mem_Icc]
  omega

end Zeta2

end
