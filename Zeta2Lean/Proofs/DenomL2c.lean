import Zeta2Lean.Statements

/-!
# L2c: `v_p(ρ₀) ≥ -11` for primes `p ≥ 11` with `p² > 2n` (proof.md §4.3 Step 6)

**Task.** Prove `Stmt_L2c` from `Stmt_ResidueForm`, `Stmt_AndrewsApplied`, `Stmt_FJClosed`,
`Stmt_FJKummer`.

**Informal proof.** By ResidueForm and AndrewsApplied,
  `ρ₀ = -24 ∑_{ℓ=1}^{n} ∑_{J ∈ chains 8 (n-ℓ)} [ε^7] F_J(ε)`,
`v_p(24) = 0` (`p ≥ 5`), and `v_p` of a sum is at least the minimum (ultrametric).  So it suffices:
  (★) `v_p([ε^7] F_J) ≥ v_p(F_J(0)) - 7`, and `v_p(F_J(0)) ≥ -4` (FJClosed + FJKummer).
*Derivative lemma (★)* (Zudilin 2004 Lemma 17 style, but without logarithms).  Say a power series
`U` is *`p`-tame* if `v_p([ε^j] U) ≥ -j` for all `j` (`0` counts as `+∞`), i.e. `U(pε)` has
`p`-integral coefficients.  Tame series form a multiplicative monoid (Cauchy product) containing
`1`, and `(1 + βε)^{±1}` is tame whenever `v_p(β) ≥ -1` (coefficients `β^j`, resp. `(-β)^j`).  Now `F_J(ε) = F_J(0) · ∏_s (1 + β_s ε)^{e_s}`, `e_s = ±1`,
over the linear factors of `Fser` (see its definition): each factor is `c + dε` with
`d ∈ {±1, ±2}` and `c ∈ ½ℤ ∖ {0}` whose numerator has absolute value `≤ 2n < p²`:
`ℓ - 2ε`, `ℓ - 1/2 - ε`, `r + 1/2 ∓ ε` (`r < n`), `r + 1 ∓ ε` (`r < n`), `-N + r - ε` (`r < J_i ≤ N`),
`ℓ + 1/2 + r - ε`, `ℓ + 1 + r - ε`, `1/2 - N + r - ε`, `ℓ + 1 + r - 2ε` (all with `r < J_8 ≤ N`, so
`|numerator| ≤ 2n`).  Hence `β = d/c` has `v_p(β) ≥ -1` (`p` odd, `v_p(numerator) ≤ 1`).  So
`F_J / F_J(0)` is tame and `v_p([ε^7] F_J) ≥ v_p(F_J(0)) - 7 ≥ -11`.  (If `F_J(0) = 0` there is
nothing to prove, but it is never `0`.)

**Formalisation.**  Instead of normalising by `F(0)`, we use the predicate `L2cTame p F`:
`F(0) ≠ 0` and `v_p([ε^j] F) ≥ v_p(F(0)) - j` for all `j` (with `0` counting as `+∞`).  It is closed
under products, powers, finite products and inverses (`L2cTame.inv`, by strong induction on the
coefficient recursion `PowerSeries.coeff_inv`), and holds for non-zero constants `C a` and for linear
factors `C c + C d * X` with `c ≠ 0`, `v_p(c) ≤ 1`, `v_p(d) ≥ 0`.  Every factor of `Fser` is of this
kind, so `L2cTame p (Fser n l ch)` (`L2c_Fser_tame`), and FJClosed + FJKummer finish.
The bound `v_p(c) ≤ 1` comes from `2c = m ∈ ℤ ∖ {0}`, `|m| ≤ 2n < p²` (`L2c_small`).
Only `p` prime and `2n < p²` are used here (`p ≥ 11` is only needed by FJKummer).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### `v_p(x) ≥ c`, with `0` counting as `+∞` -/

/-- `x = 0` or `c ≤ v_p(x)`. -/
private def L2cVpGe (p : ℕ) (c : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ c ≤ padicValRat p x

/-- `F(0) ≠ 0` and `v_p([ε^j] F) ≥ v_p(F(0)) - j` for every `j` (so `F / F(0)` is `p`-tame). -/
private def L2cTame (p : ℕ) (F : PowerSeries ℚ) : Prop :=
  constantCoeff F ≠ 0 ∧ ∀ j : ℕ, L2cVpGe p (padicValRat p (constantCoeff F) - j) (coeff j F)

section Tame

variable {p : ℕ}

/-! #### Facts valid for every `p` -/

private lemma L2cVpGe.zero' (c : ℤ) : L2cVpGe p c 0 := Or.inl rfl

private lemma L2cVpGe.self (x : ℚ) : L2cVpGe p (padicValRat p x) x := Or.inr le_rfl

private lemma L2cVpGe.mono {c c' : ℤ} {x : ℚ} (h : L2cVpGe p c x) (hc : c' ≤ c) :
    L2cVpGe p c' x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hc.trans h)

private lemma L2cTame.one' : L2cTame p (1 : PowerSeries ℚ) := by
  refine ⟨by simp, fun j => ?_⟩
  rw [coeff_one]
  split_ifs with h
  · subst h; right; simp
  · exact Or.inl rfl

private lemma L2cTame.of_C {a : ℚ} (ha : a ≠ 0) : L2cTame p (C a) := by
  refine ⟨by rw [constantCoeff_C]; exact ha, fun j => ?_⟩
  rw [coeff_C, constantCoeff_C]
  split_ifs with h
  · subst h; right; simp
  · exact Or.inl rfl

private lemma L2cTame.of_lin {c0 d : ℚ} (hc : c0 ≠ 0) (hd : L2cVpGe p (padicValRat p c0 - 1) d) :
    L2cTame p (C c0 + C d * X) := by
  have h0 : constantCoeff (C c0 + C d * X) = c0 := by simp
  refine ⟨by rw [h0]; exact hc, fun j => ?_⟩
  rw [h0]
  match j with
  | 0 =>
    have e : coeff 0 (C c0 + C d * X) = c0 := by simp
    rw [e]; exact (L2cVpGe.self c0).mono (by simp)
  | 1 =>
    have e : coeff 1 (C c0 + C d * X) = d := by simp
    rw [e]; exact hd.mono (by simp)
  | j + 2 =>
    have e : coeff (j + 2) (C c0 + C d * X) = 0 := by simp
    rw [e]; exact L2cVpGe.zero' _

/-- A linear factor `c + d ε` with `c ≠ 0`, `v_p(c) ≤ 1`, `v_p(d) ≥ 0`. -/
private lemma L2cTame.of_lin' {c0 d : ℚ} (hc : c0 ≠ 0 ∧ padicValRat p c0 ≤ 1)
    (hdv : 0 ≤ padicValRat p d) : L2cTame p (C c0 + C d * X) :=
  L2cTame.of_lin hc.1 (Or.inr (by linarith [hc.2]))

private lemma L2cTame.of_sub_X {c0 : ℚ} (hc : c0 ≠ 0 ∧ padicValRat p c0 ≤ 1) :
    L2cTame p (C c0 - X) := by
  have e : (C c0 - X : PowerSeries ℚ) = C c0 + C (-1) * X := by simp [sub_eq_add_neg]
  rw [e]
  exact L2cTame.of_lin' hc (by simp)

private lemma L2cTame.of_sub_CX {c0 d : ℚ} (hc : c0 ≠ 0 ∧ padicValRat p c0 ≤ 1)
    (hdv : 0 ≤ padicValRat p d) : L2cTame p (C c0 - C d * X) := by
  have e : (C c0 - C d * X : PowerSeries ℚ) = C c0 + C (-d) * X := by simp [sub_eq_add_neg]
  rw [e]
  exact L2cTame.of_lin' hc (by rw [padicValRat.neg]; exact hdv)

/-! #### Facts needing `p` prime (ultrametric inequality, `v_p` multiplicative) -/

variable [hp : Fact p.Prime]

private lemma L2cVpGe.add {c : ℤ} {x y : ℚ} (hx : L2cVpGe p c x) (hy : L2cVpGe p c y) :
    L2cVpGe p c (x + y) := by
  rcases hx with hx | hx
  · rw [hx, zero_add]; exact hy
  rcases hy with hy | hy
  · rw [hy, add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr (le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hxy))

private lemma L2cVpGe.mul {c d : ℤ} {x y : ℚ} (hx : L2cVpGe p c x) (hy : L2cVpGe p d y) :
    L2cVpGe p (c + d) (x * y) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_mul]
  by_cases hy0 : y = 0
  · left; rw [hy0, mul_zero]
  have hx' : c ≤ padicValRat p x := hx.resolve_left hx0
  have hy' : d ≤ padicValRat p y := hy.resolve_left hy0
  right
  rw [padicValRat.mul hx0 hy0]
  omega

private lemma L2cVpGe.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {c : ℤ}
    (h : ∀ i ∈ s, L2cVpGe p c (f i)) : L2cVpGe p c (∑ i ∈ s, f i) :=
  Finset.sum_induction f (L2cVpGe p c) (fun _ _ ha hb => ha.add hb) (L2cVpGe.zero' c) h

private lemma L2cTame.mul {F G : PowerSeries ℚ} (hF : L2cTame p F) (hG : L2cTame p G) :
    L2cTame p (F * G) := by
  have h0 : constantCoeff (F * G) = constantCoeff F * constantCoeff G := map_mul _ _ _
  refine ⟨by rw [h0]; exact mul_ne_zero hF.1 hG.1, fun j => ?_⟩
  rw [h0, padicValRat.mul hF.1 hG.1, coeff_mul]
  refine L2cVpGe.sum _ _ (fun x hx => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  refine ((hF.2 x.1).mul (hG.2 x.2)).mono (le_of_eq ?_)
  rw [← hx]; push_cast; ring

private lemma L2cTame.pow {F : PowerSeries ℚ} (hF : L2cTame p F) (k : ℕ) : L2cTame p (F ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact L2cTame.one'
  | succ k ih => rw [pow_succ]; exact ih.mul hF

private lemma L2cTame.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, L2cTame p (f i)) : L2cTame p (∏ i ∈ s, f i) :=
  Finset.prod_induction f (L2cTame p) (fun _ _ ha hb => ha.mul hb) L2cTame.one' h

private lemma L2cTame.inv {F : PowerSeries ℚ} (hF : L2cTame p F) : L2cTame p F⁻¹ := by
  have h0 : constantCoeff F⁻¹ = (constantCoeff F)⁻¹ := constantCoeff_inv F
  refine ⟨by rw [h0]; exact inv_ne_zero hF.1, fun j => ?_⟩
  rw [h0, padicValRat.inv]
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [coeff_inv]
    split_ifs with hj
    · subst hj; right; simp
    · have hsum : L2cVpGe p (-(j : ℤ)) (∑ x ∈ antidiagonal j,
          if x.2 < j then coeff x.1 F * coeff x.2 F⁻¹ else 0) := by
        refine L2cVpGe.sum _ _ (fun x hx => ?_)
        rw [HasAntidiagonal.mem_antidiagonal] at hx
        split_ifs with hlt
        · refine ((hF.2 x.1).mul (ih x.2 hlt)).mono (le_of_eq ?_)
          rw [← hx]; push_cast; ring
        · exact Or.inl rfl
      have hc : L2cVpGe p (-padicValRat p (constantCoeff F)) (-(constantCoeff F)⁻¹) := by
        right; rw [padicValRat.neg, padicValRat.inv]
      refine (hc.mul hsum).mono (le_of_eq ?_)
      ring

private lemma L2cTame.of_psPoch {c d : ℚ} {k : ℕ} (hdv : 0 ≤ padicValRat p d)
    (hc : ∀ j < k, c + j ≠ 0 ∧ padicValRat p (c + j) ≤ 1) : L2cTame p (psPoch c d k) := by
  unfold psPoch
  exact L2cTame.prod _ _ (fun j hj => L2cTame.of_lin' (hc j (mem_range.1 hj)) hdv)

/-- If `2x = m ∈ ℤ ∖ {0}` and `|m| < p²`, then `x ≠ 0` and `v_p(x) ≤ 1`. -/
private lemma L2c_small {x : ℚ} (m : ℤ) (hx : 2 * x = m) (hm : m ≠ 0)
    (hlt : m.natAbs < p ^ 2) : x ≠ 0 ∧ padicValRat p x ≤ 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hm
    exact_mod_cast (hx.symm.trans (mul_zero (2 : ℚ)))
  refine ⟨hx0, ?_⟩
  have h2 : 0 ≤ padicValRat p 2 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    exact Nat.cast_nonneg _
  have hmul : padicValRat p (2 * x) = padicValRat p 2 + padicValRat p x :=
    padicValRat.mul two_ne_zero hx0
  have hm1 : padicValRat p (m : ℚ) ≤ 1 := by
    rw [padicValRat.of_int, padicValInt]
    have hk : 0 < m.natAbs := Int.natAbs_pos.2 hm
    have hle : p ^ padicValNat p m.natAbs ≤ m.natAbs := Nat.le_of_dvd hk pow_padicValNat_dvd
    have hv : padicValNat p m.natAbs ≤ 1 := by
      by_contra h
      have : p ^ 2 ≤ p ^ padicValNat p m.natAbs := Nat.pow_le_pow_right hp.out.pos (not_le.1 h)
      omega
    exact_mod_cast hv
  rw [hx] at hmul
  linarith

end Tame

/-! ### The factors of `F_J` -/

private lemma L2c_Pser_tame {n l p : ℕ} [Fact p.Prime] (hpn : 2 * n < p ^ 2) (hl1 : 1 ≤ l)
    (hln : l ≤ n) : L2cTame p (Pser n l) := by
  have hsm : ∀ (x : ℚ) (m : ℤ), 2 * x = m → m ≠ 0 → -(2 * (n : ℤ)) ≤ m → m ≤ 2 * n →
      x ≠ 0 ∧ padicValRat p x ≤ 1 := fun x m hx hm h1 h2 => L2c_small m hx hm (by omega)
  have hv1 : 0 ≤ padicValRat p (-1 : ℚ) := by simp
  have hv1' : 0 ≤ padicValRat p (1 : ℚ) := by simp
  unfold Pser
  refine ((((L2cTame.of_C (by positivity)).mul ((L2cTame.of_sub_X ?_).pow 3)).mul
    ((L2cTame.of_psPoch hv1 ?_).pow 8)).mul ((L2cTame.of_psPoch hv1' ?_).pow 8)).mul
    (((L2cTame.of_psPoch hv1 ?_).pow 8).mul ((L2cTame.of_psPoch hv1' ?_).pow 8)).inv
  · exact hsm _ (2 * (l : ℤ) - 1) (by push_cast; ring) (by omega) (by omega) (by omega)
  · intro j hj
    exact hsm _ (2 * (j : ℤ) + 1) (by push_cast; ring) (by omega) (by omega) (by omega)
  · intro j hj
    exact hsm _ (2 * (j : ℤ) + 1) (by push_cast; ring) (by omega) (by omega) (by omega)
  · intro j hj
    exact hsm _ (2 + 2 * (j : ℤ)) (by push_cast; ring) (by omega) (by omega) (by omega)
  · intro j hj
    exact hsm _ (2 + 2 * (j : ℤ)) (by push_cast; ring) (by omega) (by omega) (by omega)

private lemma L2c_Fser_tame {n l p : ℕ} [Fact p.Prime] (hpn : 2 * n < p ^ 2) (hl1 : 1 ≤ l)
    (hln : l ≤ n) {ch : Fin 8 → ℕ} (hch : ch ∈ chains 8 (n - l)) :
    L2cTame p (Fser n l ch) := by
  have hchN : ∀ i, ch i ≤ n - l := (mem_chains.1 hch).1
  have hsm : ∀ (x : ℚ) (m : ℤ), 2 * x = m → m ≠ 0 → -(2 * (n : ℤ)) ≤ m → m ≤ 2 * n →
      x ≠ 0 ∧ padicValRat p x ≤ 1 := fun x m hx hm h1 h2 => L2c_small m hx hm (by omega)
  have hv1 : 0 ≤ padicValRat p (-1 : ℚ) := by simp
  have hv2' : 0 ≤ padicValRat p (2 : ℚ) := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    exact Nat.cast_nonneg _
  have hv2 : 0 ≤ padicValRat p (-2 : ℚ) := by rw [padicValRat.neg]; exact hv2'
  have hN0 : (0 : ℚ) ≤ ((n - l : ℕ) : ℚ) := Nat.cast_nonneg _
  unfold Fser
  refine (((((L2cTame.of_C ?_).mul ?_).mul (L2c_Pser_tame hpn hl1 hln)).mul ?_).mul ?_).mul ?_
  · intro h; linarith
  · exact L2cTame.of_sub_CX
      (hsm _ (2 * (l : ℤ)) (by push_cast; ring) (by omega) (by omega) (by omega)) hv2'
  · refine L2cTame.prod _ _ (fun i _ => L2cTame.of_C ?_)
    refine div_ne_zero ?_ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    unfold rpoch
    exact Finset.prod_ne_zero_iff.2 (fun j _ => by positivity)
  · refine L2cTame.prod _ _ (fun i _ => ?_)
    have hi := hchN i.castSucc
    refine ((L2cTame.of_psPoch hv1 ?_).mul (L2cTame.of_psPoch hv1 ?_)).mul
      ((L2cTame.of_psPoch hv1 ?_).mul (L2cTame.of_psPoch hv1 ?_)).inv
    · intro j hj
      exact hsm _ (2 * (j : ℤ) - 2 * ((n - l : ℕ) : ℤ)) (by push_cast; ring) (by omega)
        (by omega) (by omega)
    · intro j hj
      exact hsm _ (2 * (l : ℤ) + 1 + 2 * j) (by push_cast; ring) (by omega) (by omega) (by omega)
    · intro j hj
      exact hsm _ (2 * (l : ℤ) + 2 + 2 * j) (by push_cast; ring) (by omega) (by omega) (by omega)
    · intro j hj
      exact hsm _ (1 - 2 * ((n - l : ℕ) : ℤ) + 2 * j) (by push_cast; ring) (by omega)
        (by omega) (by omega)
  · have hi := hchN 7
    refine ((L2cTame.of_psPoch hv2 ?_).mul (L2cTame.of_C ?_)).mul
      (((L2cTame.of_C ?_).mul (L2cTame.of_psPoch hv1 ?_)).mul (L2cTame.of_psPoch hv1 ?_)).inv
    · intro j hj
      exact hsm _ (2 * (l : ℤ) + 2 + 2 * j) (by push_cast; ring) (by omega) (by omega) (by omega)
    · unfold rpoch
      refine Finset.prod_ne_zero_iff.2 (fun j hj => ?_)
      have hj' : j < ch 7 := mem_range.1 hj
      have hjN : (j : ℚ) < ((n - l : ℕ) : ℚ) := by exact_mod_cast (by omega : j < n - l)
      intro h; linarith
    · positivity
    · intro j hj
      exact hsm _ (2 * (l : ℤ) + 2 + 2 * j) (by push_cast; ring) (by omega) (by omega) (by omega)
    · intro j hj
      exact hsm _ (1 - 2 * ((n - l : ℕ) : ℤ) + 2 * j) (by push_cast; ring) (by omega)
        (by omega) (by omega)

theorem L2c_proof (hR : Stmt_ResidueForm) (hA : Stmt_AndrewsApplied) (hC : Stmt_FJClosed)
    (hK : Stmt_FJKummer) : Stmt_L2c := by
  intro n p hp hp11 hpn
  have : Fact p.Prime := ⟨hp⟩
  have key : L2cVpGe p (-11) (rho0 n) := by
    rw [hR n]
    have h24 : L2cVpGe p 0 (-24 : ℚ) := by
      right
      rw [padicValRat.neg, show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
      exact Nat.cast_nonneg _
    have hsum : L2cVpGe p (-11) (∑ l ∈ Icc 1 n, coeff 7 (Tser n l)) := by
      refine L2cVpGe.sum _ _ (fun l hl => ?_)
      rw [mem_Icc] at hl
      rw [hA n l hl.1 hl.2, map_sum]
      refine L2cVpGe.sum _ _ (fun ch hch => ?_)
      have h7 := (L2c_Fser_tame hpn hl.1 hl.2 hch).2 7
      rw [hC n l ch hl.1 hl.2 hch] at h7
      have hk := hK n l ch p hp hp11 hpn hl.1 hl.2 hch
      exact h7.mono (by push_cast; linarith)
    exact (h24.mul hsum).mono (by norm_num)
  rcases key with h | h
  · rw [h, padicValRat.zero]; norm_num
  · exact h

end Zeta2

end
