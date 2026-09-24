import Zeta2Lean.Statements

/-!
# The 2-adic Δ-calculus (proof.md P3(a)–(c); Lai Def. 2.3, Lemmas 2.4, 2.5(2); LSZ Lemma 2.6)

We prove every field of the structure `Stmt_Delta` (see `Statements.lean`): `riemann`,
`riemannAll`, `mono`, `monoAll`, `ofAll`, `sum`, `sumAll`, `smul`, `smulAll`, `mul`, `mulAll`.
No hypotheses.  Recall (`Defs.lean`):
`DeltaGe m c f :⇔ ∀ k ≥ 2^m, ‖f k - f (k - 2^{log₂ k})‖ ≤ 2^{-(c + log₂ k)}`,
`DeltaAll c f :⇔ DeltaGe 0 c f ∧ ‖f 0‖ ≤ 2^{1-c}`.

**Proofs.**
* `riemann` (Lai Lemma 2.4 (2.3)): for every `l`,
  `R_{l+1} - R_l = 2^{-(l+1)} ∑_{y<2^l} (f(2^l + y) - f(y))` (`deltaCalc_sum_succ_sub`;
  `R_N := volkenbornSum f N`, split `range 2^{l+1} = range 2^l ∪ (2^l + range 2^l)`), and
  `Nat.log 2 (2^l + y) = l` for `y < 2^l`.  For `l ≥ m` each summand has norm `≤ 2^{-(c+l)}`,
  the ultrametric inequality bounds the sum by the same quantity, and `‖2^{-(l+1)}‖ = 2^{l+1}`,
  so `‖R_{l+1} - R_l‖ ≤ 2^{1-c}` (`deltaCalc_step`).  Induction on `M ≥ m` and the ultrametric
  inequality give `‖R_M - R_m‖ ≤ 2^{1-c}`.
* `riemannAll`: `R_0 = f 0` and `‖f 0‖ ≤ 2^{1-c}`; apply `riemann` with `m = 0`.
* `mono`/`monoAll`/`ofAll`: monotonicity of `zpow` in the exponent (`2 ≥ 1`), and `2^m ≤ 2^{m'}`.
* `sum`/`sumAll`: `∑ F i k - ∑ F i k₋ = ∑ (F i k - F i k₋)` and the ultrametric bound for finite sums
  (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`).
* `smul`/`smulAll`: `‖a (f k - f k₋)‖ = ‖a‖ ‖f k - f k₋‖ ≤ 2^{-e} 2^{-(c + log₂ k)}`, `zpow_add₀`.
* `mul`/`mulAll` (Lai 2.5(2)): `f(k)g(k) - f(k₋)g(k₋) = f(k)(g(k)-g(k₋)) + (f(k)-f(k₋))g(k₋)` with
  `‖f(k)‖, ‖g(k₋)‖ ≤ 1`; and `‖f 0 g 0‖ ≤ ‖f 0‖ ≤ 2^{1-c}`.

**Numerical check.** Consequences are checked in `python/mirror.py` ("Stmt_DeltaFun",
"Stmt_LeibTermBound", "Stmt_L5Dom").
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- `‖2^N‖ = 2^{-N}` in `ℚ_[2]`. -/
private lemma deltaCalc_norm_two_pow (N : ℕ) : ‖(2 : ℚ_[2]) ^ N‖ = (2 : ℝ) ^ (-(N : ℤ)) := by
  have h := Padic.norm_p_pow (p := 2) N
  push_cast at h
  exact h

/-- One telescoping step of the Riemann sums:
`R_{l+1} - R_l = 2^{-(l+1)} ∑_{y < 2^l} (f(2^l + y) - f(y))`. -/
private lemma deltaCalc_sum_succ_sub (f : ℕ → ℚ_[2]) (l : ℕ) :
    volkenbornSum f (l + 1) - volkenbornSum f l =
      ((2 : ℚ_[2]) ^ (l + 1))⁻¹ * ∑ y ∈ range (2 ^ l), (f (2 ^ l + y) - f y) := by
  unfold volkenbornSum
  have h2 : (2 : ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; ring
  rw [h2, Finset.sum_range_add, Finset.sum_sub_distrib]
  have h0 : (2 : ℚ_[2]) ^ l ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_succ]
  field_simp
  ring

/-- For `l ≥ m`, `Δ_m(f) ≥ c` gives `‖R_{l+1} - R_l‖ ≤ 2^{1-c}`. -/
private lemma deltaCalc_step (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ) (hf : DeltaGe m c f) (l : ℕ)
    (hl : m ≤ l) :
    ‖volkenbornSum f (l + 1) - volkenbornSum f l‖ ≤ (2 : ℝ) ^ (1 - c) := by
  rw [deltaCalc_sum_succ_sub, norm_mul, norm_inv, deltaCalc_norm_two_pow]
  have hsum : ‖∑ y ∈ range (2 ^ l), (f (2 ^ l + y) - f y)‖ ≤ (2 : ℝ) ^ (-(c + (l : ℤ))) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · positivity
    · intro y hy
      rw [Finset.mem_range] at hy
      have hk : 2 ^ m ≤ 2 ^ l + y :=
        le_trans (Nat.pow_le_pow_right (by norm_num) hl) (Nat.le_add_right _ _)
      have hlog : Nat.log 2 (2 ^ l + y) = l := by
        rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by positivity⟩)]
        constructor
        · omega
        · rw [pow_succ]; omega
      have := hf (2 ^ l + y) hk
      rw [hlog, Nat.add_sub_cancel_left] at this
      exact this
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_of_eq ?_)
  rw [← zpow_neg, neg_neg, ← zpow_add₀ two_ne_zero]
  congr 1
  push_cast
  ring

/-- `riemann`: `Δ_m(f) ≥ c ⇒ ‖R_M - R_m‖ ≤ 2^{1-c}` for `M ≥ m`. -/
private lemma deltaCalc_riemann (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ) (hf : DeltaGe m c f) :
    ∀ M, m ≤ M → ‖volkenbornSum f M - volkenbornSum f m‖ ≤ (2 : ℝ) ^ (1 - c) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rw [sub_self, norm_zero]; positivity
  | succ M hmM ih =>
    have h := deltaCalc_step f m c hf M hmM
    calc ‖volkenbornSum f (M + 1) - volkenbornSum f m‖
        = ‖(volkenbornSum f (M + 1) - volkenbornSum f M) +
            (volkenbornSum f M - volkenbornSum f m)‖ := by congr 1; ring
      _ ≤ max ‖volkenbornSum f (M + 1) - volkenbornSum f M‖
            ‖volkenbornSum f M - volkenbornSum f m‖ := Padic.nonarchimedean _ _
      _ ≤ (2 : ℝ) ^ (1 - c) := max_le h ih

/-- `R_0 = f 0`. -/
private lemma deltaCalc_sum_zero (f : ℕ → ℚ_[2]) : volkenbornSum f 0 = f 0 := by
  simp [volkenbornSum]

/-- `riemannAll`: `Δ(f) ≥ c ⇒ ‖R_M‖ ≤ 2^{1-c}`. -/
private lemma deltaCalc_riemannAll (f : ℕ → ℚ_[2]) (c : ℤ) (hf : DeltaAll c f) :
    ∀ M, ‖volkenbornSum f M‖ ≤ (2 : ℝ) ^ (1 - c) := by
  intro M
  have h0 := deltaCalc_riemann f 0 c hf.1 M (Nat.zero_le M)
  rw [deltaCalc_sum_zero] at h0
  calc ‖volkenbornSum f M‖ = ‖(volkenbornSum f M - f 0) + f 0‖ := by congr 1; ring
    _ ≤ max ‖volkenbornSum f M - f 0‖ ‖f 0‖ := Padic.nonarchimedean _ _
    _ ≤ (2 : ℝ) ^ (1 - c) := max_le h0 hf.2

private lemma deltaCalc_mono (f : ℕ → ℚ_[2]) (m m' : ℕ) (c c' : ℤ) (hm : m ≤ m') (hc : c' ≤ c)
    (hf : DeltaGe m c f) : DeltaGe m' c' f := by
  intro k hk
  have hk' : 2 ^ m ≤ k := le_trans (Nat.pow_le_pow_right (by norm_num) hm) hk
  refine le_trans (hf k hk') ?_
  apply zpow_le_zpow_right₀ (by norm_num)
  omega

private lemma deltaCalc_monoAll (f : ℕ → ℚ_[2]) (c c' : ℤ) (hc : c' ≤ c) (hf : DeltaAll c f) :
    DeltaAll c' f := by
  refine ⟨deltaCalc_mono f 0 0 c c' le_rfl hc hf.1, le_trans hf.2 ?_⟩
  apply zpow_le_zpow_right₀ (by norm_num)
  omega

private lemma deltaCalc_ofAll (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ) (hf : DeltaAll c f) :
    DeltaGe m c f :=
  deltaCalc_mono f 0 m c c (Nat.zero_le m) le_rfl hf.1

private lemma deltaCalc_sum {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (m : ℕ) (c : ℤ)
    (hF : ∀ i ∈ s, DeltaGe m c (F i)) : DeltaGe m c (fun x => ∑ i ∈ s, F i x) := by
  intro k hk
  show ‖∑ i ∈ s, F i k - ∑ i ∈ s, F i (k - 2 ^ Nat.log 2 k)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
  · positivity
  · intro i hi
    exact hF i hi k hk

private lemma deltaCalc_sumAll {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (c : ℤ)
    (hF : ∀ i ∈ s, DeltaAll c (F i)) : DeltaAll c (fun x => ∑ i ∈ s, F i x) := by
  refine ⟨deltaCalc_sum s F 0 c (fun i hi => (hF i hi).1), ?_⟩
  show ‖∑ i ∈ s, F i 0‖ ≤ _
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
  · positivity
  · intro i hi
    exact (hF i hi).2

private lemma deltaCalc_smul (f : ℕ → ℚ_[2]) (m : ℕ) (c e : ℤ) (a : ℚ_[2])
    (ha : ‖a‖ ≤ (2 : ℝ) ^ (-e)) (hf : DeltaGe m c f) : DeltaGe m (c + e) (fun x => a * f x) := by
  intro k hk
  show ‖a * f k - a * f (k - 2 ^ Nat.log 2 k)‖ ≤ _
  rw [← mul_sub, norm_mul]
  calc ‖a‖ * ‖f k - f (k - 2 ^ Nat.log 2 k)‖
      ≤ (2 : ℝ) ^ (-e) * (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ))) :=
        mul_le_mul ha (hf k hk) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (-(c + e + (Nat.log 2 k : ℤ))) := by
        rw [← zpow_add₀ two_ne_zero]
        congr 1
        ring

private lemma deltaCalc_smulAll (f : ℕ → ℚ_[2]) (c e : ℤ) (a : ℚ_[2])
    (ha : ‖a‖ ≤ (2 : ℝ) ^ (-e)) (hf : DeltaAll c f) : DeltaAll (c + e) (fun x => a * f x) := by
  refine ⟨deltaCalc_smul f 0 c e a ha hf.1, ?_⟩
  show ‖a * f 0‖ ≤ _
  rw [norm_mul]
  calc ‖a‖ * ‖f 0‖ ≤ (2 : ℝ) ^ (-e) * (2 : ℝ) ^ (1 - c) :=
        mul_le_mul ha hf.2 (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (1 - (c + e)) := by
        rw [← zpow_add₀ two_ne_zero]
        congr 1
        ring

private lemma deltaCalc_mul (f g : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ) (hfi : IntValued f)
    (hgi : IntValued g) (hf : DeltaGe m c f) (hg : DeltaGe m c g) :
    DeltaGe m c (fun x => f x * g x) := by
  intro k hk
  show ‖f k * g k - f (k - 2 ^ Nat.log 2 k) * g (k - 2 ^ Nat.log 2 k)‖ ≤ _
  have e : f k * g k - f (k - 2 ^ Nat.log 2 k) * g (k - 2 ^ Nat.log 2 k) =
      f k * (g k - g (k - 2 ^ Nat.log 2 k)) +
        (f k - f (k - 2 ^ Nat.log 2 k)) * g (k - 2 ^ Nat.log 2 k) := by ring
  rw [e]
  refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖f k‖ * ‖g k - g (k - 2 ^ Nat.log 2 k)‖
        ≤ 1 * (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ))) :=
          mul_le_mul (hfi k) (hg k hk) (norm_nonneg _) zero_le_one
      _ = (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ))) := one_mul _
  · rw [norm_mul]
    calc ‖f k - f (k - 2 ^ Nat.log 2 k)‖ * ‖g (k - 2 ^ Nat.log 2 k)‖
        ≤ (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ))) * 1 :=
          mul_le_mul (hf k hk) (hgi _) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ))) := mul_one _

private lemma deltaCalc_mulAll (f g : ℕ → ℚ_[2]) (c : ℤ) (hfi : IntValued f)
    (hgi : IntValued g) (hf : DeltaAll c f) (hg : DeltaAll c g) :
    DeltaAll c (fun x => f x * g x) := by
  refine ⟨deltaCalc_mul f g 0 c hfi hgi hf.1 hg.1, ?_⟩
  show ‖f 0 * g 0‖ ≤ _
  rw [norm_mul]
  calc ‖f 0‖ * ‖g 0‖ ≤ (2 : ℝ) ^ (1 - c) * 1 :=
        mul_le_mul hf.2 (hgi 0) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (1 - c) := mul_one _

theorem Delta_proof : Stmt_Delta :=
  { riemann := deltaCalc_riemann
    riemannAll := deltaCalc_riemannAll
    mono := deltaCalc_mono
    monoAll := deltaCalc_monoAll
    ofAll := deltaCalc_ofAll
    sum := deltaCalc_sum
    sumAll := deltaCalc_sumAll
    smul := deltaCalc_smul
    smulAll := deltaCalc_smulAll
    mul := deltaCalc_mul
    mulAll := deltaCalc_mulAll }

end Zeta2

end
