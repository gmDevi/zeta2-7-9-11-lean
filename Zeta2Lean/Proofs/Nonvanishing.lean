import Zeta2Lean.Statements

/-!
# L5: `v₂(S_n) = 32n + 14 - 11m` along `n = 2^m - 1` (proof.md §7)

**Task.** Prove `Stmt_L5` from `Stmt_Delta`, `Stmt_Leibniz`, `Stmt_LeibTermBound`, `Stmt_L5Dom`:
for `m ≥ 2` and any `I` with `HasVolkenborn (integrand (2^m-1)) I`, `‖I‖ = 2^{-target m}`.

**Informal proof.** Let `n = 2^m - 1`, `k₀ = 2^{m-1}`, `t = target m`.
1. *Split off the dominant term.*  By `Stmt_Leibniz`, `integrand n x = domTerm m x + rest x`,
   `rest x := ∑_{(γ,β,M) ≠ (1,0,2·[k₀])} leibTerm n γ β M x`, using that
   `(1, 0, Finsupp.single k₀ 2)` is one of the indices (`k₀ ∈ Icc 1 n`) and
   `leibTerm n 1 0 (Finsupp.single k₀ 2) x = domTerm m x` (unfold: `∏_l C(8, M l) = C(8,2) = 28`,
   `-6 · 2 · 28 = -336`, exponent `5+1+0 = 6`, `∏_l (W_l Y_l)^{M l} = (W_{k₀} Y_{k₀})^2`).
2. *Combinatorics.*  For every other index, `βm + ∑_l v₂C(8, M l) + ∑_{l≠k₀} M l ≥ 3`:
   `v₂C(8,j) = 0, 3, 2, 3` for `j = 0, 1, 2, 3` and `M l ≤ 3`.  If `β ≥ 2`, `βm ≥ 4`.  If `β = 1`,
   some `M l ≥ 1`, so the middle sum is `≥ 2` and `m + 2 ≥ 4`.  If `β = 0` and some `l ≠ k₀` has
   `M l ≥ 1`, that `l` alone gives `2 + 1`.  Otherwise `M = single k₀ (3 - γ)`: `γ = 0` gives
   `v₂C(8,3) = 3`, and `γ = 1` is the dominant index.
   Hence by `Stmt_LeibTermBound` (and `Delta.monoAll`) every other term has `Δ ≥ t + 2`, and
   `Δ(rest) ≥ t + 2` (`Delta.sumAll`), so `‖volkenbornSum rest M‖ ≤ 2^{-(t+1)}` for all `M`
   (`Delta.riemannAll`).
3. *Dominant term.*  By `Stmt_L5Dom` and `Delta.riemann`, for `M ≥ m`:
   `‖volkenbornSum dom M - volkenbornSum dom m‖ ≤ 2^{-(t+1)}` and `‖volkenbornSum dom m‖ = 2^{-t}`.
4. Hence for `M ≥ m`, `volkenbornSum integrand M = volkenbornSum dom m + (small)` with
   `‖small‖ ≤ 2^{-(t+1)} < 2^{-t}`, so `‖volkenbornSum integrand M‖ = 2^{-t}`
   (`volkenbornSum_add` in `Defs.lean`, `Padic.add_eq_max_of_ne`).
5. The norm is continuous and eventually constant along the convergent sequence, so `‖I‖ = 2^{-t}`
   (`Filter.Tendsto.norm`, `tendsto_nhds_unique`, `Filter.Tendsto.congr'`).

**Lean.** `hD : Stmt_Delta`, `hL : Stmt_Leibniz`, `hB : Stmt_LeibTermBound`, `hDom : Stmt_L5Dom`.
The dominant/non-dominant parts of the Leibniz sum are the opaque functions `E`, `F` (introduced
by `obtain ⟨F, hF⟩ : ∃ F, F = …`, so that `simp only [hpt]` cannot loop).  Private helpers:
`L5nv_v2choose8`, `L5nv_v2choose83` (the values `v₂C(8,j)`), `L5nv_k0_mem`,
`L5nv_deltaAll_zero`, `L5nv_comb` (step 2).

**Numerical check.** `python/mirror.py`, section "Stmt_L5": exact `v₂(S_n) = target m` for
`m = 2..7` via the 17000-bit `J`-values; section "Stmt_LeibTermBound" checks `domTerm = leibTerm`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- `v₂ C(8, j) ≥ 2` for `1 ≤ j ≤ 3` (`C(8,1) = 2^3`, `C(8,2) = 2^2·7`, `C(8,3) = 2^3·7`). -/
private lemma L5nv_v2choose8 (j : ℕ) (h1 : 1 ≤ j) (h3 : j ≤ 3) :
    2 ≤ padicValNat 2 (Nat.choose 8 j) := by
  interval_cases j
  · have : Nat.choose 8 1 = 2 ^ 3 := by decide
    rw [this, padicValNat.prime_pow]; norm_num
  · have : Nat.choose 8 2 = 2 ^ 2 * 7 := by decide
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · have : Nat.choose 8 3 = 2 ^ 3 * 7 := by decide
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]; norm_num

/-- `v₂ C(8, 3) = 3`. -/
private lemma L5nv_v2choose83 : padicValNat 2 (Nat.choose 8 3) = 3 := by
  have : Nat.choose 8 3 = 2 ^ 3 * 7 := by decide
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- `k₀ = 2^{m-1} ∈ [1, 2^m - 1]` for `m ≥ 1`. -/
private lemma L5nv_k0_mem (m : ℕ) (hm : 1 ≤ m) : 2 ^ (m - 1) ∈ Icc 1 (2 ^ m - 1) := by
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  simp only [Finset.mem_Icc]
  omega

/-- The zero function has every Δ-bound. -/
private lemma L5nv_deltaAll_zero (c : ℤ) : DeltaAll c (fun _ => (0 : ℚ_[2])) := by
  refine ⟨fun k _ => ?_, ?_⟩
  · simp only [sub_self, norm_zero]
    positivity
  · simp only [norm_zero]
    positivity

/-- Combinatorial heart of L5 (proof.md §7, "All other terms"): every non-dominant Leibniz index
`(γ, β, M)` has slack `βm + ∑_l v₂C(8, M l) + ∑_{l ≠ k₀} M l ≥ 3`. -/
private lemma L5nv_comb (m : ℕ) (hm : 2 ≤ m) (γ β : ℕ) (hγ : γ ≤ 1) (hγβ : γ + β ≤ 3)
    (M : ℕ →₀ ℕ) (hM : M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β))
    (hnd : ¬ (γ = 1 ∧ β = 0 ∧ M = Finsupp.single (2 ^ (m - 1)) 2)) :
    3 ≤ (β : ℤ) * m + ∑ l ∈ Icc 1 (2 ^ m - 1), (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) +
      ∑ l ∈ (Icc 1 (2 ^ m - 1)).erase (2 ^ (m - 1)), (M l : ℤ) := by
  rw [Finset.mem_finsuppAntidiag] at hM
  obtain ⟨hsum, hsupp⟩ := hM
  have hk₀S := L5nv_k0_mem m (by omega)
  set S := Icc 1 (2 ^ m - 1) with hS
  set k₀ := 2 ^ (m - 1) with hk₀
  have hA0 : 0 ≤ ∑ l ∈ S, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hB0 : 0 ≤ ∑ l ∈ S.erase k₀, (M l : ℤ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hle3 : ∀ l ∈ S, M l ≤ 3 - γ - β := fun l hl =>
    hsum ▸ Finset.single_le_sum (f := fun l => M l) (fun _ _ => Nat.zero_le _) hl
  have hAl : ∀ l ∈ S, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) ≤
      ∑ l ∈ S, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) := fun l hl =>
    Finset.single_le_sum (f := fun l => (padicValNat 2 (Nat.choose 8 (M l)) : ℤ))
      (fun _ _ => by positivity) hl
  have hA2 : ∀ l ∈ S, 1 ≤ M l → 2 ≤ ∑ l ∈ S, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) := by
    intro l hl h1
    have h := L5nv_v2choose8 (M l) h1 (by have := hle3 l hl; omega)
    have := hAl l hl
    omega
  rcases Nat.lt_or_ge β 2 with hβ | hβ
  · interval_cases β
    · -- β = 0
      simp only [Nat.cast_zero, zero_mul, zero_add]
      by_cases hex : ∃ l ∈ S, l ≠ k₀ ∧ 1 ≤ M l
      · obtain ⟨l, hl, hne, h1⟩ := hex
        have hA := hA2 l hl h1
        have hB1 : (M l : ℤ) ≤ ∑ l ∈ S.erase k₀, (M l : ℤ) :=
          Finset.single_le_sum (f := fun l => (M l : ℤ)) (fun _ _ => by positivity)
            (Finset.mem_erase.2 ⟨hne, hl⟩)
        have : (1 : ℤ) ≤ M l := by exact_mod_cast h1
        linarith
      · push Not at hex
        have hMk : M k₀ = 3 - γ - 0 := by
          rw [← hsum, Finset.sum_eq_single_of_mem k₀ hk₀S
            (fun l hl hne => by have := hex l hl hne; omega)]
        rcases (show γ = 0 ∨ γ = 1 by omega) with rfl | rfl
        · have h3 : padicValNat 2 (Nat.choose 8 (M k₀)) = 3 := by
            rw [hMk]; exact L5nv_v2choose83
          have := hAl k₀ hk₀S
          rw [h3] at this
          have h3' : ((3 : ℕ) : ℤ) = 3 := by norm_num
          linarith
        · exfalso
          apply hnd
          refine ⟨rfl, rfl, ?_⟩
          ext l
          by_cases hl : l = k₀
          · subst hl; simp [hMk]
          · rw [Finsupp.single_eq_of_ne hl]
            by_cases hlS : l ∈ S
            · have := hex l hlS hl; omega
            · exact Finsupp.notMem_support_iff.1 (fun h => hlS (hsupp h))
    · -- β = 1
      simp only [Nat.cast_one, one_mul]
      obtain ⟨l, hl, h1⟩ : ∃ l ∈ S, 1 ≤ M l := by
        by_contra hcon
        push Not at hcon
        have h0 : ∑ l ∈ S, M l = 0 :=
          Finset.sum_eq_zero (fun l hl => by have := hcon l hl; omega)
        have h3 : ∑ l ∈ S, M l = 3 - γ - 1 := hsum
        omega
      have hA := hA2 l hl h1
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      linarith
  · -- β ≥ 2
    have h1 : (2 : ℤ) ≤ β := by exact_mod_cast hβ
    have h2 : (2 : ℤ) ≤ m := by exact_mod_cast hm
    have : (4 : ℤ) ≤ β * m := by nlinarith
    linarith

theorem L5_proof (hD : Stmt_Delta) (hL : Stmt_Leibniz) (hB : Stmt_LeibTermBound)
    (hDom : Stmt_L5Dom) : Stmt_L5 := by
  intro m hm I hI
  have hk₀mem := L5nv_k0_mem m (by omega)
  -- the non-dominant part of the Leibniz expansion
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → (ℕ →₀ ℕ) → ℕ → ℚ_[2], F = fun γ β M x =>
      if (γ = 1 ∧ β = 0 ∧ M = Finsupp.single (2 ^ (m - 1)) 2) then 0
      else ((leibTerm (2 ^ m - 1) γ β M x : ℚ) : ℚ_[2]) := ⟨_, rfl⟩
  -- the dominant part
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → (ℕ →₀ ℕ) → ℕ → ℚ_[2], E = fun γ β M x =>
      if (γ = 1 ∧ β = 0 ∧ M = Finsupp.single (2 ^ (m - 1)) 2) then
        ((leibTerm (2 ^ m - 1) γ β M x : ℚ) : ℚ_[2]) else 0 := ⟨_, rfl⟩
  -- the dominant Leibniz term is `domTerm`
  have hdomeq : ∀ x,
      leibTerm (2 ^ m - 1) 1 0 (Finsupp.single (2 ^ (m - 1)) 2) x = domTerm m x := by
    intro x
    unfold leibTerm domTerm
    rw [Finset.prod_eq_single_of_mem (2 ^ (m - 1)) hk₀mem
        (fun l _ hl => by rw [Finsupp.single_eq_of_ne hl]; simp),
      Finset.prod_eq_single_of_mem (2 ^ (m - 1)) hk₀mem
        (fun l _ hl => by rw [Finsupp.single_eq_of_ne hl]; simp)]
    have hc : Nat.choose 8 2 = 28 := by decide
    simp only [Finsupp.single_eq_same, hc, ite_eq_right one_ne_zero]
    push_cast
    ring
  have hsmem : Finsupp.single (2 ^ (m - 1)) 2 ∈
      (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - 1 - 0) := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, (Finsupp.support_single_subset).trans (Finset.singleton_subset_iff.2 hk₀mem)⟩
    rw [Finset.sum_eq_single_of_mem (2 ^ (m - 1)) hk₀mem
      (fun l _ hl => Finsupp.single_eq_of_ne hl)]
    simp
  -- step 1: `integrand = domTerm + rest`
  have hsplit : ∀ x, ((integrand (2 ^ m - 1) x : ℚ) : ℚ_[2]) =
      ((domTerm m x : ℚ) : ℚ_[2]) + ∑ γ ∈ range 2, ∑ β ∈ range (4 - γ),
        ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x := by
    intro x
    rw [hL (2 ^ m - 1) x]
    push_cast
    have hpt : ∀ γ β M,
        ((leibTerm (2 ^ m - 1) γ β M x : ℚ) : ℚ_[2]) = F γ β M x + E γ β M x := by
      intro γ β M
      simp only [hF, hE]
      split_ifs <;> simp
    simp only [hpt, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single_of_mem 1 (by simp)]
    · rw [Finset.sum_eq_single_of_mem 0 (by simp)]
      · rw [Finset.sum_eq_single_of_mem _ hsmem]
        · simp [hE, hdomeq]
        · intro M _ hM
          simp [hE, hM]
      · intro β _ hβ
        refine Finset.sum_eq_zero (fun M _ => ?_)
        simp [hE, hβ]
    · intro γ _ hγ
      refine Finset.sum_eq_zero (fun β _ => Finset.sum_eq_zero (fun M _ => ?_))
      simp [hE, hγ]
  -- step 2: Δ-bound for the non-dominant part
  have hrest : DeltaAll (target m + 2) (fun x => ∑ γ ∈ range 2, ∑ β ∈ range (4 - γ),
        ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x) := by
    refine hD.sumAll (range 2) (fun γ x => ∑ β ∈ range (4 - γ),
        ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x) _ ?_
    intro γ hγ
    refine hD.sumAll (range (4 - γ)) (fun β x =>
        ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x) _ ?_
    intro β hβ
    refine hD.sumAll ((Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β))
      (fun M x => F γ β M x) _ ?_
    intro M hM
    have hγ' : γ ≤ 1 := by simp at hγ; omega
    have hβ' : γ + β ≤ 3 := by simp at hβ; omega
    by_cases hP : (γ = 1 ∧ β = 0 ∧ M = Finsupp.single (2 ^ (m - 1)) 2)
    · have : (fun x => F γ β M x) = fun _ => 0 := by
        funext x; rw [hF]; simp only [ite_eq_left hP]
      rw [this]
      exact L5nv_deltaAll_zero _
    · have : (fun x => F γ β M x) =
          fun x => ((leibTerm (2 ^ m - 1) γ β M x : ℚ) : ℚ_[2]) := by
        funext x; rw [hF]; simp only [ite_eq_right hP]
      rw [this]
      refine hD.monoAll _ _ _ ?_ (hB m hm γ β hγ' hβ' M hM)
      have := L5nv_comb m hm γ β hγ' hβ' M hM hP
      unfold target
      linarith
  -- steps 3, 4: the Riemann sums of level `N ≥ m` have norm exactly `2^{-t}`
  obtain ⟨hdomΔ, hdomm⟩ := hDom m hm
  have hlt : (2 : ℝ) ^ (1 - (target m + 2)) < (2 : ℝ) ^ (-target m) :=
    zpow_lt_zpow_right₀ (by norm_num) (by linarith)
  have hval : ∀ N, m ≤ N →
      ‖volkenbornSum (fun x => ((integrand (2 ^ m - 1) x : ℚ) : ℚ_[2])) N‖ =
        (2 : ℝ) ^ (-target m) := by
    intro N hN
    rw [show (fun x => ((integrand (2 ^ m - 1) x : ℚ) : ℚ_[2])) = fun x =>
        ((domTerm m x : ℚ) : ℚ_[2]) + ∑ γ ∈ range 2, ∑ β ∈ range (4 - γ),
          ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x from funext hsplit,
      volkenbornSum_add]
    set a := volkenbornSum (fun x => ((domTerm m x : ℚ) : ℚ_[2])) m with ha
    set b := volkenbornSum (fun x => ((domTerm m x : ℚ) : ℚ_[2])) N with hb
    set c := volkenbornSum (fun x => ∑ γ ∈ range 2, ∑ β ∈ range (4 - γ),
          ∑ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β), F γ β M x) N with hc
    have hbN : ‖b - a‖ ≤ (2 : ℝ) ^ (1 - (target m + 2)) := hD.riemann _ m _ hdomΔ N hN
    have hcN : ‖c‖ ≤ (2 : ℝ) ^ (1 - (target m + 2)) := hD.riemannAll _ _ hrest N
    have hsmall : ‖(b - a) + c‖ < (2 : ℝ) ^ (-target m) :=
      lt_of_le_of_lt (Padic.nonarchimedean _ _)
        (max_lt (lt_of_le_of_lt hbN hlt) (lt_of_le_of_lt hcN hlt))
    have heq : b + c = a + ((b - a) + c) := by ring
    rw [heq, Padic.add_eq_max_of_ne (by rw [hdomm]; exact ne_of_gt hsmall), hdomm]
    exact max_eq_left hsmall.le
  -- step 5: pass to the limit
  have h2 : Tendsto
      (fun N => ‖volkenbornSum (fun x => ((integrand (2 ^ m - 1) x : ℚ) : ℚ_[2])) N‖)
      atTop (𝓝 ((2 : ℝ) ^ (-target m))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop m] with N hN
      exact (hval N hN).symm)
  exact tendsto_nhds_unique hI.norm h2

end Zeta2

end
