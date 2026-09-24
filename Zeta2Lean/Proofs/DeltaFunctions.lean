import Zeta2Lean.Statements

/-!
# Δ-bounds for binomials and for `h_β` (proof.md P3(d),(e); Lai Lemma 2.5(1),(3))

Proves the four fields of `Stmt_DeltaFun` (`binom`, `binomSq`, `hcoefInt`, `hcoefDelta`) from
`Stmt_Delta` (only `Stmt_Delta.mulAll` and `Stmt_Delta.sumAll` are used).

Write `L := ⌊log₂ k⌋`, `k₋ := k - 2^L` (`k ≥ 1`).

* **Key estimate** (`dfn_choose_add_two_pow_sub`): `‖C(a + 2^L, N) - C(a, N)‖ ≤ 2^{⌊log₂ N⌋ - L}`.
  Vandermonde (`Nat.add_choose_eq`) gives `C(a+2^L, N) - C(a, N) = ∑_{i=1}^{N} C(2^L, i) C(a, N-i)`,
  and `C(2^L, i) · i = 2^L · C(2^L - 1, i - 1)` (`Nat.add_one_mul_choose_eq`) together with
  `‖i‖ = 2^{-v₂ i} ≥ 2^{-⌊log₂ N⌋}` (`padicValNat_le_nat_log`) gives
  `‖C(2^L, i)‖ ≤ 2^{⌊log₂ N⌋ - L}` for `1 ≤ i ≤ N`; conclude by the ultrametric inequality.
* `binom`: apply the key estimate with `a = k₋ + j` (`k + j = (k₋ + j) + 2^L`); and
  `‖C(j, N)‖ ≤ 1 ≤ 2^{1 + ⌊log₂ N⌋}`.
* `binomSq`: for `k ≥ 2^m`, `L ≥ m > ⌊log₂ N⌋`, so `u := f k`, `w := f k₋` satisfy
  `‖u - w‖ ≤ 2^{⌊log₂ N⌋ - L} ≤ 1/2`, hence `‖u + w‖ = ‖(u - w) + 2w‖ ≤ 1/2` and
  `‖u² - w²‖ = ‖u - w‖ ‖u + w‖ ≤ 2^{⌊log₂ N⌋ - L - 1}`.
* `hcoefInt`, `hcoefDelta`: `(C u + X)⁻¹ = ∑_j (-1)^j u^{-(j+1)} X^j` (`dfn_inv_C_add_X`), so with
  `PowerSeries.inv_pow`, `PowerSeries.coeff_prod`, `PowerSeries.coeff_pow`:
  `h_β(x) = ∑_{l} ∏_{k ≤ n} ∑_{l'} ∏_{i < 8} (-1)^{l' i} (2x+2k+1)^{-(l' i + 1)}` with index sets
  independent of `x` (`dfn_hcoef_eq`).  The predicate `DfnGood f` (`ℤ₂`-valued and `Δ(f) ≥ 0`)
  holds for constants of norm `≤ 1` and for `x ↦ (2x+2k+1)⁻¹` (odd denominators;
  `1/B - 1/A = (A - B)/(AB)` with `A - B = -2^{L+1}`), and is closed under products
  (`Stmt_Delta.mulAll`), finite products, powers and finite sums (`Stmt_Delta.sumAll`).

**Numerical check.** `python/mirror.py`, section "Stmt_DeltaFun" (finite ranges).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### 2-adic norms of naturals -/

private lemma dfn_norm_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  have := Padic.norm_p (p := 2)
  simpa using this

private lemma dfn_norm_two_pow (L : ℕ) : ‖(2 : ℚ_[2]) ^ L‖ = (2 : ℝ) ^ (-(L : ℤ)) := by
  have := Padic.norm_p_pow (p := 2) L
  simpa using this

private lemma dfn_norm_nat_le_one (a : ℕ) : ‖(a : ℚ_[2])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 2) (a : ℤ)
  simpa using this

private lemma dfn_norm_nat_ge (i N : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (2 : ℝ) ^ (-(Nat.log 2 N : ℤ)) ≤ ‖(i : ℚ_[2])‖ := by
  have hi0 : (i : ℚ_[2]) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  rw [Padic.norm_eq_zpow_neg_valuation hi0, Padic.valuation_natCast]
  have h1 : padicValNat 2 i ≤ Nat.log 2 N :=
    (padicValNat_le_nat_log i).trans (Nat.log_mono_right hiN)
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2]
  apply zpow_le_zpow_right₀ (by norm_num)
  have : ((padicValNat 2 i : ℕ) : ℤ) ≤ (Nat.log 2 N : ℤ) := by exact_mod_cast h1
  omega

/-- `‖C(2^L, i)‖ ≤ 2^{log₂ N - L}` for `1 ≤ i ≤ N`. -/
private lemma dfn_norm_choose_two_pow (L i N : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    ‖((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - L) := by
  have key : Nat.choose (2 ^ L) i * i = 2 ^ L * Nat.choose (2 ^ L - 1) (i - 1) := by
    have h := Nat.add_one_mul_choose_eq (2 ^ L - 1) (i - 1)
    have h2 : 2 ^ L - 1 + 1 = 2 ^ L := by have := Nat.one_le_two_pow (n := L); omega
    have h3 : i - 1 + 1 = i := by omega
    rw [h2, h3] at h
    rw [← h]
  have keyQ : ((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2]) * (i : ℚ_[2]) =
      (2 : ℚ_[2]) ^ L * ((Nat.choose (2 ^ L - 1) (i - 1) : ℕ) : ℚ_[2]) := by
    exact_mod_cast key
  have hn := congrArg norm keyQ
  rw [norm_mul, norm_mul, dfn_norm_two_pow] at hn
  have hi_norm := dfn_norm_nat_ge i N hi hiN
  have hc := dfn_norm_nat_le_one (Nat.choose (2 ^ L - 1) (i - 1))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(Nat.log 2 N : ℤ)) := by positivity
  have hx0 : 0 ≤ ‖((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2])‖ := norm_nonneg _
  have hprod : ‖((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2])‖ * (2 : ℝ) ^ (-(Nat.log 2 N : ℤ)) ≤
      (2 : ℝ) ^ (-(L : ℤ)) := by
    calc ‖((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2])‖ * (2 : ℝ) ^ (-(Nat.log 2 N : ℤ))
        ≤ ‖((Nat.choose (2 ^ L) i : ℕ) : ℚ_[2])‖ * ‖(i : ℚ_[2])‖ :=
          mul_le_mul_of_nonneg_left hi_norm hx0
      _ = (2 : ℝ) ^ (-(L : ℤ)) * ‖((Nat.choose (2 ^ L - 1) (i - 1) : ℕ) : ℚ_[2])‖ := hn
      _ ≤ (2 : ℝ) ^ (-(L : ℤ)) * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (2 : ℝ) ^ (-(L : ℤ)) := mul_one _
  have heq : (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - L) * (2 : ℝ) ^ (-(Nat.log 2 N : ℤ)) =
      (2 : ℝ) ^ (-(L : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [← heq] at hprod
  exact le_of_mul_le_mul_right hprod hpos

/-- The key estimate: `v₂(C(a + 2^L, N) - C(a, N)) ≥ L - ⌊log₂ N⌋`. -/
private lemma dfn_choose_add_two_pow_sub (a L N : ℕ) :
    ‖((Nat.choose (a + 2 ^ L) N : ℕ) : ℚ_[2]) - ((Nat.choose a N : ℕ) : ℚ_[2])‖ ≤
      (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - L) := by
  have hV : Nat.choose (a + 2 ^ L) N =
      ∑ i ∈ range (N + 1), Nat.choose (2 ^ L) i * Nat.choose a (N - i) := by
    rw [add_comm a, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hV' : ((Nat.choose (a + 2 ^ L) N : ℕ) : ℚ_[2]) - ((Nat.choose a N : ℕ) : ℚ_[2]) =
      ∑ i ∈ range N, ((Nat.choose (2 ^ L) (i + 1) : ℕ) : ℚ_[2]) *
        ((Nat.choose a (N - (i + 1)) : ℕ) : ℚ_[2]) := by
    rw [hV, Finset.sum_range_succ']
    push_cast
    simp
  rw [hV']
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  rw [Finset.mem_range] at hi
  rw [norm_mul]
  have h1 := dfn_norm_choose_two_pow L (i + 1) N (by omega) (by omega)
  have h2 := dfn_norm_nat_le_one (Nat.choose a (N - (i + 1)))
  calc _ ≤ (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - L) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-! ### `binom` and `binomSq` -/

private lemma dfn_binom_step (j N k : ℕ) (hk : k ≠ 0) :
    ‖((Nat.choose (k + j) N : ℕ) : ℚ_[2]) -
        ((Nat.choose (k - 2 ^ Nat.log 2 k + j) N : ℕ) : ℚ_[2])‖ ≤
      (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - (Nat.log 2 k : ℕ)) := by
  have hL : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk
  have heq : k + j = (k - 2 ^ Nat.log 2 k + j) + 2 ^ Nat.log 2 k := by omega
  rw [heq]
  exact dfn_choose_add_two_pow_sub _ _ _

private lemma dfn_binom (j N : ℕ) :
    DeltaAll (-(Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2])) := by
  unfold DeltaAll DeltaGe
  refine ⟨?_, ?_⟩
  · intro k hk
    have hk0 : k ≠ 0 := by
      have : 1 ≤ k := by simpa using hk
      omega
    have h := dfn_binom_step j N k hk0
    have hexp : -(-(Nat.log 2 N : ℤ) + (Nat.log 2 k : ℤ)) =
        (Nat.log 2 N : ℤ) - (Nat.log 2 k : ℕ) := by
      ring
    rw [hexp]
    exact h
  · calc ‖((Nat.choose (0 + j) N : ℕ) : ℚ_[2])‖ ≤ 1 := dfn_norm_nat_le_one _
      _ ≤ (2 : ℝ) ^ (1 - -(Nat.log 2 N : ℤ)) := one_le_zpow₀ (by norm_num) (by omega)

private lemma dfn_binomSq (j N m : ℕ) (hm : Nat.log 2 N < m) :
    DeltaGe m (1 - (Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]) ^ 2) := by
  unfold DeltaGe
  intro k hk
  have hk0 : k ≠ 0 := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have hmL : m ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by norm_num) hk
  set u : ℚ_[2] := ((Nat.choose (k + j) N : ℕ) : ℚ_[2]) with hu
  set w : ℚ_[2] := ((Nat.choose (k - 2 ^ Nat.log 2 k + j) N : ℕ) : ℚ_[2]) with hw
  have hd : ‖u - w‖ ≤ (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - (Nat.log 2 k : ℕ)) :=
    dfn_binom_step j N k hk0
  have hd' : ‖u - w‖ ≤ 2⁻¹ := by
    refine hd.trans ?_
    have : (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - (Nat.log 2 k : ℕ)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    simpa using this
  have hw1 : ‖w‖ ≤ 1 := dfn_norm_nat_le_one _
  have hs : ‖u + w‖ ≤ 2⁻¹ := by
    have : u + w = (u - w) + 2 * w := by ring
    rw [this]
    refine (Padic.nonarchimedean _ _).trans (max_le hd' ?_)
    rw [norm_mul, dfn_norm_two]
    calc (2 : ℝ)⁻¹ * ‖w‖ ≤ 2⁻¹ * 1 := by gcongr
      _ = 2⁻¹ := mul_one _
  have hfac : u ^ 2 - w ^ 2 = (u - w) * (u + w) := by ring
  change ‖u ^ 2 - w ^ 2‖ ≤ _
  rw [hfac, norm_mul]
  calc ‖u - w‖ * ‖u + w‖ ≤ (2 : ℝ) ^ ((Nat.log 2 N : ℤ) - (Nat.log 2 k : ℕ)) * 2⁻¹ :=
        mul_le_mul hd hs (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (-(1 - (Nat.log 2 N : ℤ) + (Nat.log 2 k : ℤ))) := by
        rw [show (2 : ℝ)⁻¹ = (2 : ℝ) ^ (-1 : ℤ) by simp, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        ring

/-! ### `h_β` -/

/-- `(C u + X)⁻¹ = ∑_j (-1)^j u^{-(j+1)} X^j`. -/
private lemma dfn_inv_C_add_X (u : ℚ) (hu : u ≠ 0) :
    (C u + X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun j => (-1) ^ j * u⁻¹ ^ (j + 1)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hu])]
  ext n
  rcases n with _ | n
  · simp [hu]
  · rw [mul_add, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false]
    have h : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
    linear_combination (-(-1) ^ n * u⁻¹ ^ (n + 1)) * h

/-- `h_β(x)` as an explicit polynomial in the `(2x+2k+1)^{-1}` with integer coefficients. -/
private lemma dfn_hcoef_eq (n β x : ℕ) :
    hcoef n β x = ∑ l ∈ (range (n + 1)).finsuppAntidiag β, ∏ k ∈ range (n + 1),
      ∑ l' ∈ (range 8).finsuppAntidiag (l k), ∏ i ∈ range 8,
        ((-1 : ℚ) ^ (l' i) * ((((2 * x + 2 * k + 1 : ℕ) : ℚ))⁻¹) ^ (l' i + 1)) := by
  unfold hcoef
  have h : ∀ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8)⁻¹ =
      (PowerSeries.mk (fun j => (-1) ^ j * (((2 * x + 2 * k + 1 : ℕ) : ℚ))⁻¹ ^ (j + 1))) ^ 8 := by
    intro k _
    rw [← PowerSeries.inv_pow, dfn_inv_C_add_X _ (by positivity)]
  rw [Finset.prod_congr rfl h, PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro k _
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]

private lemma dfn_hcoef_cast (n β x : ℕ) :
    ((hcoef n β x : ℚ) : ℚ_[2]) = ∑ l ∈ (range (n + 1)).finsuppAntidiag β, ∏ k ∈ range (n + 1),
      ∑ l' ∈ (range 8).finsuppAntidiag (l k), ∏ i ∈ range 8,
        ((-1 : ℚ_[2]) ^ (l' i) * (((2 * x + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹ ^ (l' i + 1)) := by
  rw [dfn_hcoef_eq]
  push_cast
  rfl

/-- `ℤ₂`-valued with `Δ ≥ 0`. -/
private def DfnGood (f : ℕ → ℚ_[2]) : Prop := IntValued f ∧ DeltaAll 0 f

private lemma dfnGood_const (c : ℚ_[2]) (hc : ‖c‖ ≤ 1) : DfnGood (fun _ => c) := by
  refine ⟨fun _ => hc, ?_, ?_⟩
  · unfold DeltaGe
    intro k _
    simp only [sub_self, norm_zero]
    positivity
  · exact hc.trans (one_le_zpow₀ (by norm_num) (by norm_num))

private lemma dfnGood_mul (hD : Stmt_Delta) {f g : ℕ → ℚ_[2]} (hf : DfnGood f) (hg : DfnGood g) :
    DfnGood (fun x => f x * g x) :=
  ⟨fun k => by
      rw [norm_mul]
      exact (mul_le_mul (hf.1 k) (hg.1 k) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1)),
    hD.mulAll f g 0 hf.1 hg.1 hf.2 hg.2⟩

private lemma dfnGood_prod (hD : Stmt_Delta) {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ_[2])
    (h : ∀ i ∈ s, DfnGood (F i)) : DfnGood (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dfnGood_const 1 (by simp)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact dfnGood_mul hD (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi)))

private lemma dfnGood_sum (hD : Stmt_Delta) {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2])
    (h : ∀ i ∈ s, DfnGood (F i)) : DfnGood (fun x => ∑ i ∈ s, F i x) :=
  ⟨fun k => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun i hi => (h i hi).1 k),
    hD.sumAll s F 0 (fun i hi => (h i hi).2)⟩

private lemma dfnGood_pow (hD : Stmt_Delta) {f : ℕ → ℚ_[2]} (hf : DfnGood f) (p : ℕ) :
    DfnGood (fun x => f x ^ p) := by
  induction p with
  | zero => simpa using dfnGood_const 1 (by simp)
  | succ p ih => simpa [pow_succ] using dfnGood_mul hD ih hf

private lemma dfn_norm_odd (a : ℕ) (ha : Odd a) : ‖(a : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact Nat.coprime_two_left.mpr ha

private lemma dfnGood_inv_odd (k : ℕ) :
    DfnGood (fun x => (((2 * x + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹) := by
  have hodd : ∀ x : ℕ, ‖((2 * x + 2 * k + 1 : ℕ) : ℚ_[2])‖ = 1 := fun x =>
    dfn_norm_odd _ ⟨x + k, by ring⟩
  refine ⟨fun x => by rw [norm_inv, hodd x, inv_one], ?_, ?_⟩
  · unfold DeltaGe
    intro y hy
    have hy0 : y ≠ 0 := by
      have : 1 ≤ y := by simpa using hy
      omega
    have hL : 2 ^ Nat.log 2 y ≤ y := Nat.pow_log_le_self 2 hy0
    set L := Nat.log 2 y with hLdef
    have hB : ((2 * y + 2 * k + 1 : ℕ) : ℚ_[2]) =
        ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) + 2 * 2 ^ L := by
      have : 2 * y + 2 * k + 1 = (2 * (y - 2 ^ L) + 2 * k + 1) + 2 * 2 ^ L := by omega
      rw [this]
      push_cast
      ring
    have hA1 := hodd (y - 2 ^ L)
    have hB1 := hodd y
    have hA0 : ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hA1; exact zero_ne_one hA1
    have hB0 : ((2 * y + 2 * k + 1 : ℕ) : ℚ_[2]) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hB1; exact zero_ne_one hB1
    rw [inv_sub_inv hB0 hA0, norm_div, norm_mul, hA1, hB1, hB]
    have : ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) -
        (((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) + 2 * 2 ^ L) = -(2 : ℚ_[2]) ^ (L + 1) := by
      ring
    rw [this, norm_neg, dfn_norm_two_pow, mul_one, div_one]
    apply zpow_le_zpow_right₀ (by norm_num)
    push_cast
    omega
  · rw [norm_inv, hodd 0, inv_one]
    exact one_le_zpow₀ (by norm_num) (by norm_num)

private lemma dfnGood_hcoef (hD : Stmt_Delta) (n β : ℕ) :
    DfnGood (fun x => ((hcoef n β x : ℚ) : ℚ_[2])) := by
  have hfun : (fun x => ((hcoef n β x : ℚ) : ℚ_[2])) = fun x =>
      ∑ l ∈ (range (n + 1)).finsuppAntidiag β, ∏ k ∈ range (n + 1),
        ∑ l' ∈ (range 8).finsuppAntidiag (l k), ∏ i ∈ range 8,
          ((-1 : ℚ_[2]) ^ (l' i) * (((2 * x + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹ ^ (l' i + 1)) :=
    funext (dfn_hcoef_cast n β)
  rw [hfun]
  refine dfnGood_sum hD _ _ (fun l _ => ?_)
  refine dfnGood_prod hD _ _ (fun k _ => ?_)
  refine dfnGood_sum hD _ _ (fun l' _ => ?_)
  refine dfnGood_prod hD _ _ (fun i _ => ?_)
  exact dfnGood_mul hD (dfnGood_const _ (by simp)) (dfnGood_pow hD (dfnGood_inv_odd k) _)

theorem DeltaFun_proof (hD : Stmt_Delta) : Stmt_DeltaFun := by
  exact
    { binom := dfn_binom
      binomSq := dfn_binomSq
      hcoefInt := fun n β => (dfnGood_hcoef hD n β).1
      hcoefDelta := fun n β => (dfnGood_hcoef hD n β).2 }

end Zeta2

end
