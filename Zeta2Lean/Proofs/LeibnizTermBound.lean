import Zeta2Lean.Statements

/-!
# Δ-bound for each Leibniz term, `n = 2^m - 1` (proof.md §7 "Valuations", "Key identity",
"All other terms"; Lai Lemma 6.2)

**Task.** Prove `Stmt_LeibTermBound` from `Stmt_Delta`, `Stmt_DeltaFun`, `Stmt_Digit`: for `m ≥ 2`,
`n = 2^m - 1`, `k₀ = 2^{m-1}`, `γ ≤ 1`, `γ + β ≤ 3`, `M ∈ (Icc 1 n).finsuppAntidiag a`
(`a = 3 - γ - β`):
  `DeltaAll (32n + 13 - 11m + βm + ∑_l v₂ C(8, M l) + ∑_{l ≠ k₀} M l) (leibTerm n γ β M)`.

**Informal proof.** Write `leibTerm = K · Φ` with a rational constant `K` and a `ℤ₂`-valued `Φ`;
then `Δ(K Φ) ≥ v₂(K) + Δ(Φ)` (`Stmt_Delta.smulAll`, `‖K‖ = 2^{-v₂ K}`).
*Key identity.* `u := x + k₀` satisfies `2x + 1 + n = 2u` and, since `x C(x+n,n) = (n+1) C(x+n,n+1)`
and `n + 1 = 2^m`,
  `u · C(x+n, n) = 2^{m-1} Λ(x)`,  `Λ(x) := C(x+n,n) + 2 C(x+n,n+1)`,
with `Λ` integer-valued and `Δ(Λ) ≥ 1 - m` (`DeltaFun.binom`: `Δ(C(x+n,n)) ≥ -(m-1)`,
`Δ(C(x+n,n+1)) ≥ -m`, times 2 gives `≥ 1-m`; `Delta.sumAll`).
*Case γ = 1.* `K = -6 · 2^{24n+8} · 2 · 2^β · ∏_l C(8,M l) · n!^{6+β} · ∏_l W_l^{M l}`,
`Φ = h_β · C(x+n,n)^{6+β} · ∏_l Y_l^{M l}`.  All binomials have lower index `≤ n < 2^m`, so
`Δ ≥ -(m-1)` each (`DeltaFun.binom`, `Nat.log 2 N ≤ m-1`); `Δ(h_β) ≥ 0` (`DeltaFun.hcoefDelta`);
products of `ℤ₂`-valued functions: `Δ(Φ) ≥ -(m-1)` (`Delta.mulAll`, `Delta.monoAll`).
*Case γ = 0.* `(2x+1+n) C(x+n,n)^{5+β} = 2u C(x+n,n) C(x+n,n)^{4+β} = 2^m Λ C(x+n,n)^{4+β}`, so
`K = -6 · 2^{24n+8} · 2^m · 2^β · ∏_l C(8,M l) · n!^{5+β} · ∏_l W_l^{M l}`,
`Φ = h_β · Λ · C(x+n,n)^{4+β} · ∏_l Y_l^{M l}`, `Δ(Φ) ≥ 1 - m`.
*Valuations.* `v₂(6) = 1`, `v₂(n!) = n - m` (`Digit.fact`), `v₂(W_l) ≥ n + 1 - 2m + [l ≠ k₀]`
(`Digit.dom`, `Digit.other`; `W_l = Wl n l = (l-1)!(n-l)!`), so
`v₂(∏_l W_l^{M l}) ≥ a(n+1-2m) + #`, `# := ∑_{l≠k₀} M l`.  With `c := ∑_l v₂ C(8, M l)`:
  γ = 1 (`a = 2 - β`): `v₂(K) + Δ(Φ) ≥ (1 + 24n+8 + 1 + β + c + (6+β)(n-m) + a(n+1-2m) + #) - (m-1)`
  γ = 0 (`a = 3 - β`): `v₂(K) + Δ(Φ) ≥ (1 + 24n+8 + m + β + c + (5+β)(n-m) + a(n+1-2m) + #) + (1-m)`
and both right-hand sides simplify to `32n + 13 - 11m + βm + c + #` (proof.md §7).
Since `leibTerm` has a sign and the constants are exact, it is convenient to prove the bound in
the form `‖K‖ ≤ 2^{-e}` with `e` the displayed lower bound minus `Δ(Φ)`.

**Lean hints.** Above, `Delta.x`, `DeltaFun.x`, `Digit.x` denote the fields `hD.x`, `hF.x`, `hG.x`
of the hypotheses `hD : Stmt_Delta`, `hF : Stmt_DeltaFun`, `hG : Stmt_Digit` (e.g.
`hF.binom j N : DeltaAll (-(Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]))`).
`Stmt_Delta` fields `smulAll`, `mulAll`, `sumAll`, `monoAll`;
`Stmt_DeltaFun` fields `binom`, `hcoefInt`, `hcoefDelta`; `Stmt_Digit` fields;
`Padic.norm_p_pow`, `Padic.norm_natCast_eq_one_iff`, `Padic.norm_eq_zpow_neg_valuation`
(or directly `‖(2:ℚ_[2])^k * (odd : ℚ_[2])‖ = 2^{-k}`);
`padicValNat.mul`, `padicValNat.pow`, `padicValNat.prime_pow`, `Nat.factorial_ne_zero`,
`Finset.mem_finsuppAntidiag`, `Finset.prod_pow_eq_pow_sum`, `Finsupp.support`,
`Nat.add_one_mul_choose_eq` (for `x C(x+n,n) = (n+1) C(x+n,n+1)`), `Nat.log_eq_iff`,
`Nat.log_mono_right`.  A general helper worth proving first: for `q : ℚ` with
`q = 2^e * (a/b)`, `a, b` odd, `‖(q:ℚ_[2])‖ = 2^{-e}`; and for integers `‖(z:ℚ_[2])‖ ≤ 2^{-v₂ z}`.

**Numerical check.** `python/mirror.py`, section "Stmt_LeibTermBound" (all terms, `m = 2, 3`, and
random terms `m = 4`, checked on `k < 2^{m+4}`; the minimum slack over non-dominant terms is 0,
attained at `γ = 0, β = 0, M = 3·[k₀]` as predicted).

**Formal proof (status: complete; axioms `propext, Classical.choice, Quot.sound` only).**
* `ltb_*`: a small calculus for `‖z‖ ≤ 2^{-e}` in `ℚ_[2]` (products, powers, finite products,
  monotonicity; `‖N‖ ≤ 2^{-v₂ N}` for `N ≠ 0` via `Padic.norm_eq_zpow_neg_valuation`).
* `dAll_*`: `IntValued ∧ DeltaAll c` is closed under products, powers and finite products
  (`hD.mulAll`, needs `c ≤ 1` for the empty product); `C(x+j, N)` with `N < 2^m` has
  `DeltaAll (1-m)`; so do `Y_l` and `Λ(x) = C(x+n,n) + 2 C(x+n,n+1)` (`hD.smulAll`, `hD.sumAll`).
* `leib_main` works with a general `n` and `hn : n = 2^m - 1`; it writes `leibTerm = K * Φ` with `K`,
  `Φ` introduced as opaque variables with defining equations, bounds `‖K‖` by the exact exponent,
  applies `hD.smulAll`, and closes the exponent comparison by `ring` (it is an identity).
  `LeibTermBound_proof` specialises it, rewriting `((2^m - 1 : ℕ) : ℤ) = 2^m - 1`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### Norm bounds `‖z‖ ≤ 2^{-e}` in `ℚ_[2]` -/

private lemma ltb_mul {a b : ℚ_[2]} {e f : ℤ} (ha : ‖a‖ ≤ (2:ℝ) ^ (-e))
    (hb : ‖b‖ ≤ (2:ℝ) ^ (-f)) : ‖a * b‖ ≤ (2:ℝ) ^ (-(e + f)) := by
  rw [norm_mul, neg_add, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  exact mul_le_mul ha hb (norm_nonneg _) (by positivity)

private lemma ltb_pow {a : ℚ_[2]} {e : ℤ} (ha : ‖a‖ ≤ (2:ℝ) ^ (-e)) (k : ℕ) :
    ‖a ^ k‖ ≤ (2:ℝ) ^ (-((k : ℤ) * e)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h := ltb_mul ih ha
    have e1 : -((k : ℤ) * e + e) = -(((k + 1 : ℕ) : ℤ) * e) := by push_cast; ring
    rw [e1] at h
    exact h

private lemma ltb_prod {ι : Type*} (s : Finset ι) (F : ι → ℚ_[2]) (E : ι → ℤ)
    (h : ∀ i ∈ s, ‖F i‖ ≤ (2:ℝ) ^ (-E i)) :
    ‖∏ i ∈ s, F i‖ ≤ (2:ℝ) ^ (-(∑ i ∈ s, E i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact ltb_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

private lemma ltb_mono {a : ℚ_[2]} {e e' : ℤ} (ha : ‖a‖ ≤ (2:ℝ) ^ (-e)) (h : e' ≤ e) :
    ‖a‖ ≤ (2:ℝ) ^ (-e') :=
  ha.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))

private lemma ltb_nat (N : ℕ) (hN : N ≠ 0) :
    ‖(N : ℚ_[2])‖ ≤ (2:ℝ) ^ (-(padicValNat 2 N : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast]
  norm_num

private lemma ltb_natCast_le_one (N : ℕ) : ‖(N : ℚ_[2])‖ ≤ (2:ℝ) ^ (-(0:ℤ)) := by
  simpa using Padic.norm_int_le_one (p := 2) (N : ℤ)

private lemma ltb_two : ‖(2 : ℚ_[2])‖ ≤ (2:ℝ) ^ (-(1:ℤ)) := by
  have h := Padic.norm_p (p := 2)
  simp only [Nat.cast_ofNat] at h
  rw [h]; norm_num

private lemma ltb_neg_six : ‖(-6 : ℚ_[2])‖ ≤ (2:ℝ) ^ (-(1:ℤ)) := by
  rw [norm_neg, show (6 : ℚ_[2]) = 2 * ((3 : ℕ) : ℚ_[2]) by norm_num]
  have h := ltb_mul ltb_two (ltb_natCast_le_one 3)
  rw [add_zero] at h
  exact h

/-! ### Δ-calculus helpers -/

private lemma intValued_natCast' (g : ℕ → ℕ) : IntValued (fun x => ((g x : ℕ) : ℚ_[2])) :=
  fun k => by simpa using Padic.norm_int_le_one (p := 2) (g k : ℤ)

private lemma deltaAll_one' {c : ℤ} (hc : c ≤ 1) : DeltaAll c (fun _ => (1 : ℚ_[2])) := by
  refine ⟨fun k _ => ?_, ?_⟩
  · simp only [sub_self, norm_zero]; positivity
  · rw [norm_one]; exact one_le_zpow₀ (by norm_num) (by omega)

private lemma dAll_mul (hD : Stmt_Delta) {c : ℤ} {f g : ℕ → ℚ_[2]}
    (hf : IntValued f ∧ DeltaAll c f) (hg : IntValued g ∧ DeltaAll c g) :
    IntValued (fun x => f x * g x) ∧ DeltaAll c (fun x => f x * g x) := by
  refine ⟨fun k => ?_, hD.mulAll f g c hf.1 hg.1 hf.2 hg.2⟩
  rw [norm_mul]
  calc ‖f k‖ * ‖g k‖ ≤ 1 * 1 := mul_le_mul (hf.1 k) (hg.1 k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private lemma dAll_prod (hD : Stmt_Delta) {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ_[2])
    {c : ℤ} (hc : c ≤ 1) (h : ∀ i ∈ s, IntValued (F i) ∧ DeltaAll c (F i)) :
    IntValued (fun x => ∏ i ∈ s, F i x) ∧ DeltaAll c (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact ⟨fun k => by simp, deltaAll_one' hc⟩
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact dAll_mul hD (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

private lemma dAll_pow (hD : Stmt_Delta) {f : ℕ → ℚ_[2]} {c : ℤ} (hc : c ≤ 1)
    (hf : IntValued f ∧ DeltaAll c f) (k : ℕ) :
    IntValued (fun x => f x ^ k) ∧ DeltaAll c (fun x => f x ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact ⟨fun k => by simp, deltaAll_one' hc⟩
  | succ k ih =>
    simp only [pow_succ]
    exact dAll_mul hD ih hf

private lemma dAll_add (hD : Stmt_Delta) {c : ℤ} {f g : ℕ → ℚ_[2]} (hf : DeltaAll c f)
    (hg : DeltaAll c g) : DeltaAll c (fun x => f x + g x) := by
  have h := hD.sumAll (Finset.univ : Finset Bool) (fun b => if b then f else g) c
    (by intro b _; cases b <;> simpa)
  simpa [Fintype.sum_bool] using h

private lemma dAll_binom (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (j N m : ℕ) (hm : 1 ≤ m)
    (hN : N < 2 ^ m) :
    IntValued (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2])) ∧
      DeltaAll (1 - m) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2])) := by
  refine ⟨intValued_natCast' _, hD.monoAll _ _ _ ?_ (hF.binom j N)⟩
  have : Nat.log 2 N < m := Nat.log_lt_of_lt_pow' (by omega) hN
  omega

private lemma dAll_Yl (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (n l m : ℕ) (hm : 1 ≤ m)
    (hn : n < 2 ^ m) (hl : 1 ≤ l) (hln : l ≤ n) :
    IntValued (fun x => ((Yl n l x : ℕ) : ℚ_[2])) ∧
      DeltaAll (1 - m) (fun x => ((Yl n l x : ℕ) : ℚ_[2])) := by
  have e : (fun x => ((Yl n l x : ℕ) : ℚ_[2])) = fun x =>
      ((Nat.choose (x + (l - 1)) (l - 1) : ℕ) : ℚ_[2]) *
        ((Nat.choose (x + n) (n - l) : ℕ) : ℚ_[2]) := by
    funext x
    rw [Yl, Nat.cast_mul, Nat.add_sub_assoc hl]
  rw [e]
  exact dAll_mul hD (dAll_binom hD hF _ _ m hm (by omega)) (dAll_binom hD hF _ _ m hm (by omega))

private lemma dAll_Lam (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (n m : ℕ) (hm : 1 ≤ m)
    (hn : n + 1 = 2 ^ m) :
    IntValued (fun x => ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) +
        2 * ((Nat.choose (x + n) (n + 1) : ℕ) : ℚ_[2])) ∧
      DeltaAll (1 - m) (fun x => ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) +
        2 * ((Nat.choose (x + n) (n + 1) : ℕ) : ℚ_[2])) := by
  constructor
  · intro k
    have := intValued_natCast' (fun x => Nat.choose (x + n) n + 2 * Nat.choose (x + n) (n + 1)) k
    simpa using this
  · have h1 := (dAll_binom hD hF n n m hm (by omega)).2
    have hlog : Nat.log 2 (n + 1) = m := by rw [hn, Nat.log_pow (by norm_num)]
    have h2 := hD.smulAll _ _ 1 2 ltb_two (hF.binom n (n + 1))
    rw [hlog, show -(m : ℤ) + 1 = 1 - m by ring] at h2
    exact dAll_add hD h1 h2

/-! ### The main computation, for a general `n = 2^m - 1` -/

private lemma leib_main (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (hG : Stmt_Digit) (m : ℕ)
    (hm : 2 ≤ m) (n : ℕ) (hn : n = 2 ^ m - 1) (γ β : ℕ) (hγ : γ ≤ 1) (hγβ : γ + β ≤ 3)
    (M : ℕ →₀ ℕ) (hM : M ∈ (Icc 1 n).finsuppAntidiag (3 - γ - β)) :
    DeltaAll (32 * (n : ℤ) + 13 - 11 * (m : ℤ) + (β : ℤ) * m +
        ∑ l ∈ Icc 1 n, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) +
        ∑ l ∈ (Icc 1 n).erase (2 ^ (m - 1)), (M l : ℤ))
      (fun x => ((leibTerm n γ β M x : ℚ) : ℚ_[2])) := by
  -- arithmetic facts
  have hP1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hnP : n + 1 = 2 ^ m := by omega
  have hk : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']; congr 1; omega
  have hk1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have hmk : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
  have h2m : 2 * m ≤ 2 ^ m := by omega
  have hmn : m ≤ n := by omega
  have hnlt : n < 2 ^ m := by omega
  -- the multiplicities
  rw [Finset.mem_finsuppAntidiag] at hM
  obtain ⟨hMsum0, -⟩ := hM
  have hMsum : ∑ l ∈ Icc 1 n, M l = 3 - γ - β := hMsum0
  have hMle : ∀ l ∈ Icc 1 n, M l ≤ 3 := by
    intro l hl
    have := Finset.single_le_sum (f := fun l => M l) (fun i _ => Nat.zero_le _) hl
    omega
  have hMsumZ : ∑ l ∈ Icc 1 n, (M l : ℤ) = 3 - γ - β := by
    have := congrArg (Nat.cast : ℕ → ℤ) hMsum
    push_cast at this
    rw [this]
    omega
  -- valuations
  have hfact : (padicValNat 2 n.factorial : ℤ) = n - m := by
    have := hG.fact m
    rw [← hn] at this
    rw [this]; omega
  have hW : ∀ l ∈ Icc 1 n, (n : ℤ) + 1 - 2 * m + (if l = 2 ^ (m - 1) then 0 else 1) ≤
      padicValNat 2 (Wl n l) := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    split_ifs with h
    · have := hG.dom m hm
      rw [← hn] at this
      rw [h, Wl, this]; omega
    · have := hG.other m hm l hl.1 (by omega) h
      rw [← hn] at this
      rw [Wl]; omega
  have hk0mem : 2 ^ (m - 1) ∈ Icc 1 n := by rw [Finset.mem_Icc]; omega
  have hsplit : ∑ l ∈ Icc 1 n, (M l : ℤ) * ((n : ℤ) + 1 - 2 * m +
      (if l = 2 ^ (m - 1) then 0 else 1)) =
      ((n : ℤ) + 1 - 2 * m) * ∑ l ∈ Icc 1 n, (M l : ℤ) +
        ∑ l ∈ (Icc 1 n).erase (2 ^ (m - 1)), (M l : ℤ) := by
    rw [← Finset.add_sum_erase _ _ hk0mem, ← Finset.add_sum_erase _ (fun l => (M l : ℤ)) hk0mem]
    rw [Finset.sum_congr rfl (g := fun l => (M l : ℤ) * ((n : ℤ) + 1 - 2 * m + 1))
      (fun l hl => by rw [ite_eq_right (Finset.ne_of_mem_erase hl)])]
    rw [ite_eq_left rfl, ← Finset.sum_mul]
    ring
  have hC : ∀ l ∈ Icc 1 n, Nat.choose 8 (M l) ≠ 0 := fun l hl =>
    (Nat.choose_pos (by have := hMle l hl; omega)).ne'
  have hWne : ∀ l, Wl n l ≠ 0 := fun l => by
    rw [Wl]; exact Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  -- the `ℤ₂`-valued factors
  have hH : IntValued (fun x => ((hcoef n β x : ℚ) : ℚ_[2])) ∧
      DeltaAll (1 - m) (fun x => ((hcoef n β x : ℚ) : ℚ_[2])) :=
    ⟨hF.hcoefInt n β, hD.monoAll _ _ _ (by omega) (hF.hcoefDelta n β)⟩
  have hB := dAll_binom hD hF n n m (by omega) hnlt
  have hY : IntValued (fun x => ∏ l ∈ Icc 1 n, ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l)) ∧
      DeltaAll (1 - m) (fun x => ∏ l ∈ Icc 1 n, ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l)) :=
    dAll_prod hD _ (fun l x => ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l)) (by omega) (fun l hl => by
      rw [Finset.mem_Icc] at hl
      exact dAll_pow hD (by omega) (dAll_Yl hD hF n l m (by omega) hnlt hl.1 hl.2) _)
  -- the constant parts
  have hPC : ‖∏ l ∈ Icc 1 n, ((Nat.choose 8 (M l) : ℕ) : ℚ_[2])‖ ≤
      (2:ℝ) ^ (-(∑ l ∈ Icc 1 n, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ))) :=
    ltb_prod _ _ _ (fun l hl => ltb_nat _ (hC l hl))
  have hPW : ‖∏ l ∈ Icc 1 n, ((Wl n l : ℕ) : ℚ_[2]) ^ (M l)‖ ≤
      (2:ℝ) ^ (-(((n : ℤ) + 1 - 2 * m) * (3 - γ - β) +
        ∑ l ∈ (Icc 1 n).erase (2 ^ (m - 1)), (M l : ℤ))) := by
    have h := ltb_prod (Icc 1 n) (fun l => ((Wl n l : ℕ) : ℚ_[2]) ^ (M l))
      (fun l => (M l : ℤ) * ((n : ℤ) + 1 - 2 * m + (if l = 2 ^ (m - 1) then 0 else 1)))
      (fun l hl => ltb_pow (ltb_mono (ltb_nat _ (hWne l)) (hW l hl)) _)
    rw [hsplit, hMsumZ] at h
    exact h
  have hFa : ‖((n.factorial : ℕ) : ℚ_[2])‖ ≤ (2:ℝ) ^ (-((n : ℤ) - m)) := by
    have h := ltb_nat _ (Nat.factorial_ne_zero n)
    rw [hfact] at h
    exact h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hγ with rfl | rfl
  · -- γ = 0: use `(2x+1+n) C(x+n,n) = 2^m Λ(x)`
    have hid : ∀ x : ℕ, (2 * x + 1 + n) * Nat.choose (x + n) n =
        2 ^ m * (Nat.choose (x + n) n + 2 * Nat.choose (x + n) (n + 1)) := by
      intro x
      have h := Nat.choose_succ_right_eq (x + n) n
      rw [Nat.add_sub_cancel] at h
      rw [← hnP]
      calc (2 * x + 1 + n) * Nat.choose (x + n) n
          = 2 * (Nat.choose (x + n) n * x) + (n + 1) * Nat.choose (x + n) n := by ring
        _ = 2 * (Nat.choose (x + n) (n + 1) * (n + 1)) + (n + 1) * Nat.choose (x + n) n := by
          rw [h]
        _ = (n + 1) * (Nat.choose (x + n) n + 2 * Nat.choose (x + n) (n + 1)) := by ring
    have hidQ : ∀ x : ℕ, (2 * (x : ℚ_[2]) + 1 + n) * ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) =
        2 ^ m * (((Nat.choose (x + n) n : ℕ) : ℚ_[2]) +
          2 * ((Nat.choose (x + n) (n + 1) : ℕ) : ℚ_[2])) := by
      intro x
      exact_mod_cast hid x
    obtain ⟨K, hKdef⟩ : ∃ K : ℚ_[2], K = -6 * 2 ^ (24 * n + 8) * 2 ^ m * 2 ^ β *
        (∏ l ∈ Icc 1 n, ((Nat.choose 8 (M l) : ℕ) : ℚ_[2])) *
        ((n.factorial : ℕ) : ℚ_[2]) ^ (5 + β) * ∏ l ∈ Icc 1 n, ((Wl n l : ℕ) : ℚ_[2]) ^ (M l) :=
      ⟨_, rfl⟩
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → ℚ_[2], Φ = fun x => ((hcoef n β x : ℚ) : ℚ_[2]) *
        (((Nat.choose (x + n) n : ℕ) : ℚ_[2]) + 2 * ((Nat.choose (x + n) (n + 1) : ℕ) : ℚ_[2])) *
        ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) ^ (4 + β) *
        ∏ l ∈ Icc 1 n, ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l) := ⟨_, rfl⟩
    have hfun : (fun x => ((leibTerm n 0 β M x : ℚ) : ℚ_[2])) = fun x => K * Φ x := by
      funext x
      rw [hKdef, hΦdef]
      simp only [leibTerm, Bn, ite_true]
      push_cast
      simp only [mul_pow, prod_mul_distrib]
      linear_combination (-6 * (2 : ℚ_[2]) ^ (24 * n + 8) * 2 ^ β * ((hcoef n β x : ℚ) : ℚ_[2]) *
        (∏ l ∈ Icc 1 n, ((Nat.choose 8 (M l) : ℕ) : ℚ_[2])) *
        ((n.factorial : ℕ) : ℚ_[2]) ^ (5 + β) * (∏ l ∈ Icc 1 n, ((Wl n l : ℕ) : ℚ_[2]) ^ (M l)) *
        (∏ l ∈ Icc 1 n, ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l)) *
        ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) ^ (4 + β)) * hidQ x
    have hΦ : IntValued Φ ∧ DeltaAll (1 - m) Φ := by
      rw [hΦdef]
      exact dAll_mul hD (dAll_mul hD (dAll_mul hD hH (dAll_Lam hD hF n m (by omega) hnP))
        (dAll_pow hD (by omega) hB _)) hY
    have hK : ‖K‖ ≤ (2:ℝ) ^ (-(1 + ((24 * n + 8 : ℕ) : ℤ) * 1 + (m : ℤ) * 1 + (β : ℤ) * 1 +
        ∑ l ∈ Icc 1 n, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) +
        ((5 + β : ℕ) : ℤ) * ((n : ℤ) - m) +
        (((n : ℤ) + 1 - 2 * m) * (3 - ((0 : ℕ) : ℤ) - β) +
          ∑ l ∈ (Icc 1 n).erase (2 ^ (m - 1)), (M l : ℤ)))) := by
      rw [hKdef]
      exact ltb_mul (ltb_mul (ltb_mul (ltb_mul (ltb_mul (ltb_mul ltb_neg_six (ltb_pow ltb_two _))
        (ltb_pow ltb_two _)) (ltb_pow ltb_two _)) hPC) (ltb_pow hFa _)) hPW
    have h := hD.smulAll Φ (1 - m) _ K hK hΦ.2
    rw [hfun]
    refine hD.monoAll _ _ _ ?_ h
    push_cast
    apply le_of_eq
    ring
  · -- γ = 1
    obtain ⟨K, hKdef⟩ : ∃ K : ℚ_[2], K = -6 * 2 ^ (24 * n + 8) * 2 * 2 ^ β *
        (∏ l ∈ Icc 1 n, ((Nat.choose 8 (M l) : ℕ) : ℚ_[2])) *
        ((n.factorial : ℕ) : ℚ_[2]) ^ (6 + β) * ∏ l ∈ Icc 1 n, ((Wl n l : ℕ) : ℚ_[2]) ^ (M l) :=
      ⟨_, rfl⟩
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → ℚ_[2], Φ = fun x => ((hcoef n β x : ℚ) : ℚ_[2]) *
        ((Nat.choose (x + n) n : ℕ) : ℚ_[2]) ^ (6 + β) *
        ∏ l ∈ Icc 1 n, ((Yl n l x : ℕ) : ℚ_[2]) ^ (M l) := ⟨_, rfl⟩
    have hfun : (fun x => ((leibTerm n 1 β M x : ℚ) : ℚ_[2])) = fun x => K * Φ x := by
      funext x
      rw [hKdef, hΦdef]
      simp only [leibTerm, Bn, one_ne_zero, ite_false]
      push_cast
      simp only [mul_pow, prod_mul_distrib]
      ring
    have hΦ : IntValued Φ ∧ DeltaAll (1 - m) Φ := by
      rw [hΦdef]
      exact dAll_mul hD (dAll_mul hD hH (dAll_pow hD (by omega) hB _)) hY
    have hK : ‖K‖ ≤ (2:ℝ) ^ (-(1 + ((24 * n + 8 : ℕ) : ℤ) * 1 + 1 + (β : ℤ) * 1 +
        ∑ l ∈ Icc 1 n, (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) +
        ((6 + β : ℕ) : ℤ) * ((n : ℤ) - m) +
        (((n : ℤ) + 1 - 2 * m) * (3 - ((1 : ℕ) : ℤ) - β) +
          ∑ l ∈ (Icc 1 n).erase (2 ^ (m - 1)), (M l : ℤ)))) := by
      rw [hKdef]
      exact ltb_mul (ltb_mul (ltb_mul (ltb_mul (ltb_mul (ltb_mul ltb_neg_six (ltb_pow ltb_two _))
        ltb_two) (ltb_pow ltb_two _)) hPC) (ltb_pow hFa _)) hPW
    have h := hD.smulAll Φ (1 - m) _ K hK hΦ.2
    rw [hfun]
    refine hD.monoAll _ _ _ ?_ h
    push_cast
    apply le_of_eq
    ring

theorem LeibTermBound_proof (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (hG : Stmt_Digit) :
    Stmt_LeibTermBound := by
  intro m hm γ β hγ hγβ M hM
  have h := leib_main hD hF hG m hm (2 ^ m - 1) rfl γ β hγ hγβ M hM
  have hc : ((2 ^ m - 1 : ℕ) : ℤ) = (2 : ℤ) ^ m - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [hc] at h
  exact h

end Zeta2

end
