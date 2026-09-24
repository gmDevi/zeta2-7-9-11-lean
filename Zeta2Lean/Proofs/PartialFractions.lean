import Zeta2Lean.Statements

/-!
# Partial fractions of `R_n` (proof.md §3, "useful formula")

**Status: proved.**  `#print axioms Zeta2.PF_proof` gives
`[propext, Classical.choice, Quot.sound]`.

`Stmt_PF` has two fields:
* `poly : Rnum n = PFpoly n`, i.e.
  `2^{16n}(2t+n)(t+1/2)_n^8 = ∑_{i=1}^{8} ∑_{k=0}^{n} r_{i,k} (t+k)^{8-i} ∏_{j≤n, j≠k} (t+j)^8`;
* `series`: for `y` with `y + j ≠ 0` (`j ≤ n`), in `PowerSeries ℚ`,
  `Rser n y = ∑_{i,k} C (r_{i,k}) * ((C (y+k) + X)^i)⁻¹`  (Taylor expansion of `R_n(y+ε)`).
It has no hypotheses.  Everything follows from the definition `r_{8-μ,k} = [ε^μ] G_k(ε)`.

**Proof of `poly`** (`PFaux.poly_eq`).  Let `P := Rnum n - PFpoly n ∈ ℚ[t]`.
1. `natDegree P ≤ 8n + 7` (`PFaux.natDegree_Rnum_le`, `PFaux.natDegree_PFpoly_le`).
2. For each `k₀ ≤ n`, `(t + k₀)^8 ∣ P` (`PFaux.X_add_C_pow_dvd`).  `PFaux.subst a : ℚ[t] →+* ℚ⟦ε⟧`
   is the substitution `t ↦ a + ε`, and `subst (-k₀) P` is the coercion of the polynomial
   `P.comp (X - C k₀)` (`PFaux.coe_comp_eq_subst`).  `PFaux.dvd_subst` shows
   `ε^8 ∣ subst (-k₀) P` as follows.
   * Sign identities (`PFaux.prod_half_shift`, `PFaux.prod_int_shift`):
     `∏_{j<n} (j - k₀ + 1/2 + ε) = (-1)^{k₀} (1/2-ε)_{k₀} (1/2+ε)_{n-k₀}` and
     `∏_{j≤n, j≠k₀} (j - k₀ + ε) = (-1)^{k₀} (1-ε)_{k₀} (1+ε)_{n-k₀}`.
   * Hence `subst (-k₀) Rnum = G_{k₀} · V`, with `V := ∏_{j≠k₀} (j - k₀ + ε)^8`.  The inverse in
     `Ψ` cancels against `V`, since the constant coefficient `k₀! (n-k₀)!` is non-zero.
   * `subst (-k₀) PFpoly = T · V + E`, where `T := ∑_{i=1}^{8} r_{i,k₀} ε^{8-i}` and
     `ε^8 ∣ E`.  Every term with `k ≠ k₀` contains the factor `(t + k₀)^8 ↦ ε^8`.
   * `ε^8 ∣ G_{k₀} - T`: the coefficient of `ε^μ` for `μ < 8` is
     `[ε^μ] G_{k₀} - r_{8-μ,k₀} = 0`.
   The coefficients `< 8` of `P.comp (X - C k₀)` therefore vanish, and composing back with
   `X + C k₀` gives `(X + C k₀)^8 ∣ P`.
3. The `(X + C k)^8` for `k ≤ n` are pairwise coprime (`Polynomial.pairwise_coprime_X_sub_C`), so
   their product divides `P`.  That product is monic of degree `8n + 8 > natDegree P`, so
   `P = 0`.

**Proof of `series`** (`PFaux.series_eq`).  Apply `PFaux.subst y` to `poly`.  Multiply by the
inverse of `W := (∏_{j≤n} (C (y+j) + X))^8`, whose constant coefficient `∏ (y+j)^8` is non-zero.
Each term then becomes `(C(y+k)+X)^{8-i} ∏_{j≠k} (C(y+j)+X)^8 · W⁻¹ = ((C(y+k)+X)^i)⁻¹`, checked
with `PowerSeries.eq_inv_iff_mul_eq_one`.

**Numerical check.** `python/mirror.py`, section "Stmt_PF" (`poly` for `n ≤ 6`, `series` at
random rational `y`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

namespace PFaux

/-! ### Elementary power-series identities -/

private lemma C_add_X_add_C (a b : ℚ) : (C a + X : PowerSeries ℚ) + C b = C (a + b) + X := by
  rw [map_add]; ring

private lemma constantCoeff_psPoch (c d : ℚ) (k : ℕ) :
    constantCoeff (psPoch c d k) = ∏ j ∈ range k, (c + j) := by
  unfold psPoch
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp

private lemma factor_neg (a b : ℚ) (h : a = -b) :
    (C a + X : PowerSeries ℚ) = -(C b + C (-1) * X) := by
  subst h
  rw [map_neg, map_neg, map_one]
  ring

private lemma factor_pos (a b : ℚ) (h : a = b) :
    (C a + X : PowerSeries ℚ) = C b + C 1 * X := by
  subst h
  rw [map_one]
  ring

/-! ### The two sign identities -/

/-- `∏_{j<n} (j - k₀ + 1/2 + ε) = (-1)^{k₀} (1/2-ε)_{k₀} (1/2+ε)_{n-k₀}`. -/
private lemma prod_half_shift (n k₀ : ℕ) (hk : k₀ ≤ n) :
    ∏ j ∈ range n, ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C ((j : ℚ) + 1 / 2)) =
      (-1) ^ k₀ * (psPoch (1 / 2) (-1) k₀ * psPoch (1 / 2) 1 (n - k₀)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k₀ + m := ⟨n - k₀, by omega⟩
  rw [Nat.add_sub_cancel_left, Finset.prod_range_add, ← mul_assoc]
  congr 1
  · unfold psPoch
    rw [← Finset.prod_range_reflect (fun j => C ((1 / 2 : ℚ) + j) + C (-1) * X) k₀]
    have hc : ((-1 : PowerSeries ℚ)) ^ k₀ = (-1) ^ (range k₀).card := by simp
    rw [hc, ← Finset.prod_neg]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [C_add_X_add_C]
    apply factor_neg
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  · unfold psPoch
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [C_add_X_add_C]
    apply factor_pos
    push_cast
    ring

/-- `∏_{j≤n, j≠k₀} (j - k₀ + ε) = (-1)^{k₀} (1-ε)_{k₀} (1+ε)_{n-k₀}`. -/
private lemma prod_int_shift (n k₀ : ℕ) (hk : k₀ ≤ n) :
    ∏ j ∈ (range (n + 1)).erase k₀, ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (j : ℚ)) =
      (-1) ^ k₀ * (psPoch 1 (-1) k₀ * psPoch 1 1 (n - k₀)) := by
  have hmem : k₀ ∈ range (n + 1) := Finset.mem_range.2 (by omega)
  have hX : ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (k₀ : ℚ)) = X := by
    rw [C_add_X_add_C]; simp
  have hfull : ∏ j ∈ range (n + 1), ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (j : ℚ)) =
      X * ((-1) ^ k₀ * (psPoch 1 (-1) k₀ * psPoch 1 1 (n - k₀))) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = k₀ + m := ⟨n - k₀, by omega⟩
    rw [Nat.add_sub_cancel_left, add_assoc, Finset.prod_range_add, Finset.prod_range_succ']
    rw [Nat.add_zero, hX]
    have h1 : ∏ x ∈ range k₀, ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (x : ℚ)) =
        (-1) ^ k₀ * psPoch 1 (-1) k₀ := by
      unfold psPoch
      rw [← Finset.prod_range_reflect (fun j => C ((1 : ℚ) + j) + C (-1) * X) k₀]
      have hc : ((-1 : PowerSeries ℚ)) ^ k₀ = (-1) ^ (range k₀).card := by simp
      rw [hc, ← Finset.prod_neg]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [C_add_X_add_C]
      apply factor_neg
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have h2 : ∏ x ∈ range m,
        ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (((k₀ + (x + 1) : ℕ) : ℚ))) =
          psPoch 1 1 m := by
      unfold psPoch
      refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [C_add_X_add_C]
      apply factor_pos
      push_cast
      ring
    rw [h1, h2]
    ring
  rw [← Finset.mul_prod_erase _ _ hmem, hX] at hfull
  exact mul_left_cancel₀ PowerSeries.X_ne_zero hfull

/-! ### The substitution `t ↦ a + ε` -/

/-- The substitution `t ↦ a + ε`, as a ring hom `ℚ[t] →+* ℚ⟦ε⟧`. -/
private def subst (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (C a + X)

private lemma subst_X (a : ℚ) : subst a Polynomial.X = C a + X := by
  simp [subst]

private lemma subst_C (a c : ℚ) : subst a (Polynomial.C c) = C c := by
  simp [subst]

private lemma subst_X_add_C (a c : ℚ) :
    subst a (Polynomial.X + Polynomial.C c) = C a + X + C c := by
  rw [map_add, subst_X, subst_C]

/-- `Rnum(-k₀ + ε) = 2^{16n} (n - 2k₀ + 2ε) ((-1)^{k₀} (1/2-ε)_{k₀} (1/2+ε)_{n-k₀})^8`. -/
private lemma subst_Rnum (n k₀ : ℕ) (hk : k₀ ≤ n) :
    subst (-(k₀ : ℚ)) (Rnum n) = C ((2 : ℚ) ^ (16 * n)) * (C ((n : ℚ) - 2 * k₀) + C 2 * X) *
      ((-1) ^ k₀ * (psPoch (1 / 2) (-1) k₀ * psPoch (1 / 2) 1 (n - k₀))) ^ 8 := by
  unfold Rnum
  rw [map_mul, map_mul, map_pow (subst (-(k₀ : ℚ))), map_prod]
  simp_rw [subst_X_add_C]
  rw [prod_half_shift n k₀ hk, subst_C, map_add, map_mul, subst_C, subst_C, subst_X]
  congr 2
  rw [map_sub, map_mul, map_neg]
  ring

/-- Key step: `ε^8 ∣ (Rnum - PFpoly)(-k₀ + ε)`. -/
private lemma dvd_subst (n k₀ : ℕ) (hk : k₀ ≤ n) :
    (X : PowerSeries ℚ) ^ 8 ∣ subst (-(k₀ : ℚ)) (Rnum n - PFpoly n) := by
  have hmem : k₀ ∈ range (n + 1) := Finset.mem_range.2 (by omega)
  have hX : ((C (-(k₀ : ℚ)) + X : PowerSeries ℚ) + C (k₀ : ℚ)) = X := by
    rw [C_add_X_add_C, neg_add_cancel, map_zero, zero_add]
  set V : PowerSeries ℚ :=
    ∏ j ∈ (range (n + 1)).erase k₀, (C (-(k₀ : ℚ)) + X + C (j : ℚ)) ^ 8 with hV
  set T : PowerSeries ℚ := ∑ i ∈ Icc (1 : ℕ) 8, C (rcoef n i k₀) * X ^ (8 - i) with hT
  set E : PowerSeries ℚ := ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ (range (n + 1)).erase k₀,
      C (rcoef n i k) * (C (-(k₀ : ℚ)) + X + C (k : ℚ)) ^ (8 - i) *
        ∏ j ∈ (range (n + 1)).erase k, (C (-(k₀ : ℚ)) + X + C (j : ℚ)) ^ 8 with hE
  -- the `Rnum` side: `Rnum(-k₀+ε) = G_{k₀}(ε) · V(ε)`
  have hR : subst (-(k₀ : ℚ)) (Rnum n) = Gser n k₀ * V := by
    rw [subst_Rnum n k₀ hk, hV, Finset.prod_pow, prod_int_shift n k₀ hk]
    unfold Gser Psi
    set D := psPoch 1 (-1) k₀ * psPoch 1 1 (n - k₀) with hD
    have hD0 : constantCoeff D ≠ 0 := by
      rw [hD, map_mul, constantCoeff_psPoch, constantCoeff_psPoch]
      apply mul_ne_zero <;> (rw [Finset.prod_ne_zero_iff]; intro j _; positivity)
    have hDD : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel D hD0
    calc _ = C ((2 : ℚ) ^ (16 * n)) * (C ((n : ℚ) - 2 * k₀) + C 2 * X) *
          ((-1) ^ k₀ * (psPoch (1 / 2) (-1) k₀ * psPoch (1 / 2) 1 (n - k₀))) ^ 8 *
            (D⁻¹ * D) ^ 8 := by
            rw [hDD, one_pow, mul_one]
      _ = _ := by ring
  -- the `PFpoly` side: the `k = k₀` terms give `T · V`, the others are divisible by `ε^8`
  have hPF : subst (-(k₀ : ℚ)) (PFpoly n) = T * V + E := by
    unfold PFpoly
    simp only [map_sum, map_mul, map_pow, map_prod, subst_C, subst_X_add_C]
    rw [hT, hE, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.add_sum_erase _ _ hmem, hX]
  -- `T` is the degree-`< 8` truncation of `G_{k₀}` (definition of `rcoef`)
  have hTdvd : (X : PowerSeries ℚ) ^ 8 ∣ Gser n k₀ - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (8 - m)]
    · rw [ite_eq_left (by omega)]
      unfold rcoef
      rw [ite_eq_left ⟨by omega, by omega, hk⟩, Nat.sub_sub_self (by omega), sub_self]
    · intro i hi hne
      rw [Finset.mem_Icc] at hi
      rw [ite_eq_right (by omega)]
    · intro h
      exfalso; apply h; rw [Finset.mem_Icc]; omega
  have hEdvd : (X : PowerSeries ℚ) ^ 8 ∣ E := by
    rw [hE]
    apply Finset.dvd_sum
    intro i _
    apply Finset.dvd_sum
    intro k hk'
    have hk0 : k₀ ∈ (range (n + 1)).erase k :=
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hk').symm, hmem⟩
    apply Dvd.dvd.mul_left
    have := Finset.dvd_prod_of_mem
      (fun j : ℕ => (C (-(k₀ : ℚ)) + X + C (j : ℚ) : PowerSeries ℚ) ^ 8) hk0
    simp only [hX] at this
    exact this
  rw [map_sub, hR, hPF]
  have : Gser n k₀ * V - (T * V + E) = (Gser n k₀ - T) * V - E := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_left hTdvd V) hEdvd

/-- `subst (-k₀) P` is the power series of the polynomial `P(t - k₀)`. -/
private lemma coe_comp_eq_subst (k₀ : ℚ) (P : Polynomial ℚ) :
    ((P.comp (Polynomial.X - Polynomial.C k₀) : Polynomial ℚ) : PowerSeries ℚ) =
      subst (-k₀) P := by
  have h : (Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.compRingHom (Polynomial.X - Polynomial.C k₀)) = subst (-k₀) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [subst]
    · simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
        Polynomial.coeToPowerSeries.ringHom_apply, subst_X]
      rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg]
      ring
  exact RingHom.congr_fun h P

/-- `(t + k₀)^8 ∣ Rnum - PFpoly` for every `k₀ ≤ n`. -/
private lemma X_add_C_pow_dvd (n k₀ : ℕ) (hk : k₀ ≤ n) :
    (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ 8 ∣ Rnum n - PFpoly n := by
  set P := Rnum n - PFpoly n with hP
  set Q := P.comp (Polynomial.X - Polynomial.C (k₀ : ℚ)) with hQ
  have hQdvd : Polynomial.X ^ 8 ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 := dvd_subst n k₀ hk
    rw [← hP, ← coe_comp_eq_subst, ← hQ, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 d hd
    rwa [Polynomial.coeff_coe] at h2
  obtain ⟨S, hS⟩ := hQdvd
  have hPQ : P = Q.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
    rw [hQ, Polynomial.comp_assoc]
    simp
  refine ⟨S.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)), ?_⟩
  rw [hPQ, hS, Polynomial.mul_comp, Polynomial.X_pow_comp]

/-! ### Degree bounds -/

private lemma natDegree_Rnum_le (n : ℕ) : (Rnum n).natDegree ≤ 8 * n + 1 := by
  unfold Rnum
  have h1 : (Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have h2 : (∏ j ∈ range n, (Polynomial.X + Polynomial.C ((j : ℚ) + 1 / 2))).natDegree ≤ n := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun j _ => (Polynomial.natDegree_X_add_C _).le)).trans ?_
    simp
  refine Polynomial.natDegree_mul_le.trans ?_
  have h3 := (Polynomial.natDegree_mul_le (p := Polynomial.C ((2 : ℚ) ^ (16 * n)))
    (q := Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)))
  rw [Polynomial.natDegree_C, zero_add] at h3
  have h4 := (Polynomial.natDegree_pow_le (p := ∏ j ∈ range n,
    (Polynomial.X + Polynomial.C ((j : ℚ) + 1 / 2))) (n := 8))
  omega

private lemma natDegree_PFpoly_le (n : ℕ) : (PFpoly n).natDegree ≤ 8 * n + 7 := by
  unfold PFpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  rw [Finset.mem_Icc] at hi
  have hcard : ((range (n + 1)).erase k).card = n := by
    rw [Finset.card_erase_of_mem hk, Finset.card_range]; simp
  have h1 := (Polynomial.natDegree_mul_le (p := Polynomial.C (rcoef n i k))
    (q := (Polynomial.X + Polynomial.C (k : ℚ)) ^ (8 - i)))
  rw [Polynomial.natDegree_C, zero_add] at h1
  have h2 := (Polynomial.natDegree_pow_le (p := Polynomial.X + Polynomial.C (k : ℚ)) (n := 8 - i))
  rw [Polynomial.natDegree_X_add_C, mul_one] at h2
  have h3 : (∏ j ∈ (range (n + 1)).erase k,
      (Polynomial.X + Polynomial.C (j : ℚ)) ^ 8).natDegree ≤ 8 * n := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun j _ => (Polynomial.natDegree_pow_le (n := 8)).trans
      (by rw [Polynomial.natDegree_X_add_C]))).trans ?_
    rw [Finset.sum_const, smul_eq_mul, hcard, mul_one, mul_comm]
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-! ### The two fields of `Stmt_PF` -/

private theorem poly_eq (n : ℕ) : Rnum n = PFpoly n := by
  have hdvd : ∏ k ∈ range (n + 1), (Polynomial.X + Polynomial.C (k : ℚ)) ^ 8 ∣
      Rnum n - PFpoly n := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      have hinj : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
        intro a b h
        simpa using h
      have := Polynomial.pairwise_coprime_X_sub_C hinj hij
      simp only [Function.onFun, map_neg, sub_neg_eq_add] at this ⊢
      exact this.pow
    · intro k hk
      exact X_add_C_pow_dvd n k (by simpa [Nat.lt_succ_iff] using hk)
  have hdeg : (Rnum n - PFpoly n).natDegree <
      (∏ k ∈ range (n + 1), (Polynomial.X + Polynomial.C (k : ℚ)) ^ 8).natDegree := by
    have hmon : ∀ k ∈ range (n + 1), ((Polynomial.X + Polynomial.C (k : ℚ)) ^ 8).Monic :=
      fun k _ => (Polynomial.monic_X_add_C _).pow 8
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    have h1 := Polynomial.natDegree_sub_le (Rnum n) (PFpoly n)
    have h2 := natDegree_Rnum_le n
    have h3 := natDegree_PFpoly_le n
    have h4 : ∑ i ∈ range (n + 1), ((Polynomial.X + Polynomial.C (i : ℚ)) ^ 8).natDegree =
        8 * (n + 1) := by
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [(Polynomial.monic_X_add_C (k : ℚ)).natDegree_pow 8, Polynomial.natDegree_X_add_C])]
      rw [Finset.sum_const, smul_eq_mul, Finset.card_range, mul_one, mul_comm]
    rw [h4]
    omega
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg)

private theorem series_eq (n : ℕ) (y : ℚ) (hy : ∀ j ≤ n, y + (j : ℚ) ≠ 0) :
    Rser n y = ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
      C (rcoef n i k) * ((C (y + k) + X) ^ i)⁻¹ := by
  have hpoly := congrArg (subst y) (poly_eq n)
  have hF : ∀ c : ℚ, subst y (Polynomial.X + Polynomial.C c) = C (y + c) + X := by
    intro c; rw [subst_X_add_C, C_add_X_add_C]
  have hF0 : ∀ j ∈ range (n + 1), constantCoeff (C (y + (j : ℚ)) + X : PowerSeries ℚ) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simpa using hy j (by omega)
  set W : PowerSeries ℚ := (∏ j ∈ range (n + 1), (C (y + j) + X)) ^ 8 with hW
  have hW0 : constantCoeff W ≠ 0 := by
    rw [hW, map_pow, map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 hF0)
  have hRn : subst y (Rnum n) = C ((2 : ℚ) ^ (16 * n)) * (C 2 * (C y + X) + C (n : ℚ)) *
      (∏ j ∈ range n, (C (y + ((j : ℚ) + 1 / 2)) + X)) ^ 8 := by
    unfold Rnum
    simp only [map_add (subst y), map_mul (subst y), map_pow (subst y), map_prod (subst y),
      subst_C, subst_X, C_add_X_add_C]
  have hLHS : Rser n y = subst y (Rnum n) * W⁻¹ := by
    rw [hRn]
    unfold Rser
    have e1 : (C (2 * y + n) + C 2 * X : PowerSeries ℚ) = C 2 * (C y + X) + C (n : ℚ) := by
      rw [map_add, map_mul]; ring
    have e2 : ∏ j ∈ range n, (C (y + 1 / 2 + j) + X : PowerSeries ℚ) =
        ∏ j ∈ range n, (C (y + ((j : ℚ) + 1 / 2)) + X) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      congr 2
      ring
    rw [e1, e2]
  rw [hLHS, hpoly]
  unfold PFpoly
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [map_mul, map_mul, subst_C, map_pow (subst y), hF, map_prod]
  simp_rw [map_pow (subst y), hF]
  rw [mul_assoc, mul_assoc]
  congr 1
  have hFk : constantCoeff ((C (y + (k : ℚ)) + X) ^ i : PowerSeries ℚ) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ (hF0 k hk)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hFk]
  have hWk : W = (C (y + (k : ℚ)) + X) ^ 8 *
      ∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 8 := by
    rw [hW, ← Finset.prod_pow]
    exact (Finset.mul_prod_erase _
      (fun j : ℕ => (C (y + (j : ℚ)) + X : PowerSeries ℚ) ^ 8) hk).symm
  calc (C (y + (k : ℚ)) + X) ^ (8 - i) *
        ((∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 8) * W⁻¹) *
        (C (y + (k : ℚ)) + X) ^ i
      = ((C (y + (k : ℚ)) + X) ^ (8 - i) * (C (y + (k : ℚ)) + X) ^ i *
          ∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 8) * W⁻¹ := by ring
    _ = W * W⁻¹ := by rw [← pow_add, Nat.sub_add_cancel hi.2, hWk]
    _ = 1 := PowerSeries.mul_inv_cancel W hW0

end PFaux

theorem PF_proof : Stmt_PF := ⟨PFaux.poly_eq, PFaux.series_eq⟩

end Zeta2

end
