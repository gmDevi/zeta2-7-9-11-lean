import Zeta2Lean.Statements

/-!
# L2b: `d_n^{12} ρ₀ ∈ ℤ` — the root trick (proof.md §4.2; Lai Lemma 4.6, LLS Lemma 5.6)

**Task.** Prove `Stmt_L2b` from `Stmt_PF` and `Stmt_L2a`.

**Informal proof.** Write `ρ₀ = -∑_{k=1}^{n} ∑_{ℓ₀=0}^{k-1} X(k,ℓ₀)` with
`X(k,ℓ₀) := ∑_{i=1}^{8} (i)₄ r_{i,k} (ℓ₀ + 1/2)^{-(i+4)}` (unfold `Ahalf`, swap sums).
It suffices that `d_n^{12} X(k₀,ℓ₀)` is `q`-integral for every prime `q` and all `1 ≤ k₀ ≤ n`,
`ℓ₀ < k₀` (then so is `d_n^{12} ρ₀`, and a rational that is `q`-integral for all `q` is an integer).
* `q = 2`: `(ℓ₀+1/2)^{-(i+4)} = 2^{i+4} (2ℓ₀+1)^{-(i+4)}` and `d_n^{8-i} r_{i,k} ∈ ℤ` (L2a), so
  `v₂(d_n^{12} (i)₄ r_{i,k} (ℓ₀+1/2)^{-(i+4)}) ≥ (i+4) v₂(d_n) + i + 4 ≥ 0`.
* `q` odd: each term is `(i)₄ · [d_n^{8-i} r_{i,k₀}] · (d_n/(2ℓ₀+1))^{i+4} · 2^{i+4}`, so it is
  `q`-integral unless `v_q(2ℓ₀+1) > v_q(d_n)`.  Suppose that.  The point `t₀ := -k₀ + ℓ₀ + 1/2`
  satisfies `t₀ + 1/2 + j₀ = 0` for `j₀ = k₀ - ℓ₀ - 1 ∈ [0, n-1]`, so `R_n` has a zero of order 8
  at `t₀`.  Apply `Stmt_PF.series` at `y = t₀` (`t₀ + j ∈ 1/2 + ℤ` is never `0`): the left side
  `Rser n t₀` contains the factor `(C(t₀ + 1/2 + j₀) + X)^8 = X^8`, so its coefficient of `ε^4`
  vanishes; on the right, `[ε^4] ((C a + X)^i)⁻¹ = C(i+3,4) a^{-i-4} = (i)₄/24 · a^{-i-4}`.  Hence
  `∑_{k=0}^{n} ∑_i (i)₄ r_{i,k} (t₀ + k)^{-i-4} = 0`, i.e.
  `X(k₀,ℓ₀) = -∑_{k ≠ k₀} ∑_i (i)₄ r_{i,k} (ℓ₀ - k₀ + k + 1/2)^{-i-4}`.
  If `d_n^{12} X(k₀,ℓ₀)` were not `q`-integral, some `k₁ ≠ k₀` would have
  `v_q(2(ℓ₀-k₀+k₁)+1) > v_q(d_n)` too; subtracting, `q^{v_q(d_n)+1} ∣ 2(k₁ - k₀)`, hence
  `q^{v_q(d_n)+1} ∣ k₁ - k₀` with `0 < |k₁ - k₀| ≤ n < q^{v_q(d_n)+1}` — contradiction
  (`v_q(d_n) = ⌊log_q n⌋`).  [So in fact every `d_n^{12} X(k₀,ℓ₀)` is `q`-integral.]

**Formal proof (this file, complete).**
* `L2b_Zq q` is the subring `{x : ℚ | padicNorm q x ≤ 1}`; `L2b_int_of_forall`: a rational lying in
  every `L2b_Zq q` is an integer (`Rat.num_or_den_zero_padicVal`,
  `Nat.eq_one_iff_not_exists_prime_dvd`, `Rat.den_eq_one_iff`).
* `L2b_coeff_inv`: `[ε^m] ((a + ε)^{d+1})⁻¹ = (-1)^m C(d+m,d) a^{-(d+1+m)}`, from
  `a + ε = a · rescale(-1/a) (1 - X)` and `PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one`.
* `L2b_root`: the root identity, from `Stmt_PF.series` (coefficient of `ε^4`; `X^8 ∣ Rser n t₀`
  via `PowerSeries.X_pow_dvd_iff`).
* `L2b_div_mem` / `L2b_term_mem`: `d_n^{12} (i)₄ r_{i,k} (m/2)^{-(i+4)} ∈ L2b_Zq q` whenever
  `q^{⌊log_q n⌋+1} ∤ m` (`v_q(d_n) = ⌊log_q n⌋` is `Nat.factorization_lcmUpto`).  Since `m` is odd,
  this also covers `q = 2`, so no separate 2-adic case is needed.
* `L2b_X_mem`: case split on `q^{⌊log_q n⌋+1} ∣ 2ℓ₀+1`; `L2b_proof` assembles.

**Numerical check.** `python/mirror.py`, section "Stmt_BlockF, Stmt_L2a, Stmt_L2b".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-- The subring of `q`-integral rationals (`padicNorm q x ≤ 1`). -/
private def L2b_Zq (q : ℕ) [Fact q.Prime] : Subring ℚ where
  carrier := {x | padicNorm q x ≤ 1}
  mul_mem' {a b} ha hb := by
    show padicNorm q (a * b) ≤ 1
    rw [padicNorm.mul]
    exact (mul_le_of_le_one_left (padicNorm.nonneg _) ha).trans hb
  one_mem' := by
    show padicNorm q 1 ≤ 1
    rw [padicNorm.one]
  add_mem' {a b} ha hb := padicNorm.nonarchimedean.trans (max_le ha hb)
  zero_mem' := by
    show padicNorm q 0 ≤ 1
    rw [padicNorm.zero]
    norm_num
  neg_mem' {a} ha := by
    show padicNorm q (-a) ≤ 1
    rw [padicNorm.neg]
    exact ha

/-- A rational that is `q`-integral for every prime `q` is an integer. -/
private lemma L2b_int_of_forall (x : ℚ)
    (h : ∀ q : ℕ, q.Prime → padicNorm q x ≤ 1) : ∃ z : ℤ, x = z := by
  refine ⟨x.num, ?_⟩
  have hden : x.den = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    have := Fact.mk hp
    have hx : x ≠ 0 := by
      rintro rfl
      simp only [Rat.den_zero, Nat.dvd_one] at hdvd
      exact hp.one_lt.ne' hdvd
    have h1 := h p hp
    rw [padicNorm.eq_zpow_of_nonzero hx] at h1
    have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    have hv : 0 ≤ padicValRat p x := by
      have := (zpow_le_one_iff_right₀ hp1).mp h1
      omega
    have hden0 : padicValNat p x.den ≠ 0 := (dvd_iff_padicValNat_ne_zero x.den_nz).mp hdvd
    rcases Rat.num_or_den_zero_padicVal x hp with h0 | h0
    · rw [padicValRat_def, h0] at hv
      omega
    · exact hden0 h0
  exact ((Rat.den_eq_one_iff x).mp hden).symm

/-- `[ε^m] (a + ε)^{-(d+1)} = (-1)^m C(d+m, d) a^{-(d+1+m)}`. -/
private lemma L2b_coeff_inv (a : ℚ) (ha : a ≠ 0) (d m : ℕ) :
    coeff m (((C a + X : PowerSeries ℚ) ^ (d + 1))⁻¹) =
      (-1) ^ m * ((d + m).choose d : ℚ) * (a⁻¹) ^ (d + 1 + m) := by
  have hCX : (C a + X : PowerSeries ℚ) = C a * rescale (-a⁻¹) (1 - X) := by
    rw [map_sub, map_one, rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_neg,
      mul_inv_cancel₀ ha, map_neg, map_one]
    ring
  have h1 : (mk fun n => ((d + n).choose d : ℚ)) * (1 - X) ^ (d + 1) = 1 :=
    mk_add_choose_mul_one_sub_pow_eq_one ℚ d
  have h2 : C ((a⁻¹) ^ (d + 1)) * (C a) ^ (d + 1) = (1 : PowerSeries ℚ) := by
    rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]
  have key : ((C a + X : PowerSeries ℚ) ^ (d + 1))⁻¹ =
      C ((a⁻¹) ^ (d + 1)) * rescale (-a⁻¹) (mk fun n => ((d + n).choose d : ℚ)) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [ha])]
    rw [hCX, mul_pow, ← map_pow (rescale (-a⁻¹)), mul_mul_mul_comm, ← map_mul, h1, h2, map_one,
      one_mul]
  rw [key, coeff_C_mul, coeff_rescale, coeff_mk, neg_pow]
  ring

/-- `C(d+4, d) · 24 = (d+1)(d+2)(d+3)(d+4)`. -/
private lemma L2b_choose_four_nat (d : ℕ) :
    (d + 4).choose d * 24 = (d + 1) * (d + 2) * (d + 3) * (d + 4) := by
  rw [Nat.choose_symm_add]
  have h := Nat.add_choose_mul_factorial_mul_factorial d 4
  rw [show (d + 4).factorial = (d + 1) * (d + 2) * (d + 3) * (d + 4) * d.factorial by
    simp only [Nat.factorial_succ]; ring] at h
  rw [show Nat.factorial 4 = 24 by rfl] at h
  apply Nat.eq_of_mul_eq_mul_right d.factorial_pos
  linarith

private lemma L2b_choose_four (d : ℕ) :
    ((d + 4).choose d : ℚ) * 24 = ((d : ℚ) + 1) * (d + 2) * (d + 3) * (d + 4) := by
  exact_mod_cast L2b_choose_four_nat d

/-- The root identity (proof.md §4.2): `R_n` has a zero of order `8 > 4` at
`t₀ = -k + ℓ + 1/2`, so `∑_{i,k'} (i)₄ r_{i,k'} (t₀ + k')^{-i-4} = 0`. -/
private lemma L2b_root (hPF : Stmt_PF) (n k l : ℕ) (hk : k ≤ n) (hl : l < k) :
    ∑ i ∈ Icc (1 : ℕ) 8, ∑ k' ∈ range (n + 1),
      ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k' *
        ((((l : ℚ) - k + 1 / 2) + k')⁻¹) ^ (i + 4) = 0 := by
  set y : ℚ := (l : ℚ) - k + 1 / 2 with hy_def
  have hy : ∀ j ≤ n, y + (j : ℚ) ≠ 0 := by
    intro j _ h
    have h2 : ((2 * ((l : ℤ) - k + j) + 1 : ℤ) : ℚ) = 0 := by
      push_cast
      linarith
    have h3 : (2 * ((l : ℤ) - k + j) + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  have hser := hPF.series n y hy
  have hL : coeff 4 (Rser n y) = 0 := by
    have hdvd : (X : PowerSeries ℚ) ^ 8 ∣ Rser n y := by
      have hj : k - l - 1 ∈ range n := by
        rw [Finset.mem_range]
        omega
      have hX : (X : PowerSeries ℚ) ∣ ∏ j ∈ range n, (C (y + 1 / 2 + (j : ℚ)) + X) := by
        have h0 : C (y + 1 / 2 + ((k - l - 1 : ℕ) : ℚ)) + X = (X : PowerSeries ℚ) := by
          have : y + 1 / 2 + ((k - l - 1 : ℕ) : ℚ) = 0 := by
            rw [hy_def]
            have hc : ((k - l - 1 : ℕ) : ℚ) = (k : ℚ) - l - 1 := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
              push_cast
              ring
            rw [hc]
            ring
          rw [this, map_zero, zero_add]
        have := Finset.dvd_prod_of_mem (fun j : ℕ => C (y + 1 / 2 + (j : ℚ)) + X) hj
        rwa [h0] at this
      unfold Rser
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hX 8) _) _
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) 4 (by norm_num)
  rw [hser] at hL
  simp only [map_sum, coeff_C_mul] at hL
  have hcoef : ∀ i ∈ Icc (1 : ℕ) 8, ∀ k' ∈ range (n + 1),
      ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k' * ((y + k')⁻¹) ^ (i + 4) =
        24 * (rcoef n i k' * coeff 4 (((C (y + k') + X) ^ i)⁻¹)) := by
    intro i hi k' hk'
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hne : y + (k' : ℚ) ≠ 0 := hy k' (by rw [Finset.mem_range] at hk'; omega)
    obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
    rw [L2b_coeff_inv _ hne d 4]
    have hc := L2b_choose_four d
    push_cast
    linear_combination (-(rcoef n (d + 1) k' * (y + (k' : ℚ))⁻¹ ^ (d + 1 + 4))) * hc
  calc ∑ i ∈ Icc (1 : ℕ) 8, ∑ k' ∈ range (n + 1),
        ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k' * ((y + k')⁻¹) ^ (i + 4)
      = 24 * ∑ i ∈ Icc (1 : ℕ) 8, ∑ k' ∈ range (n + 1),
          rcoef n i k' * coeff 4 (((C (y + k') + X) ^ i)⁻¹) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k' hk' => hcoef i hi k' hk'
    _ = 0 := by rw [hL, mul_zero]

/-- `v_q(d_n) = ⌊log_q n⌋`. -/
private lemma L2b_padicValNat_dn (n q : ℕ) (hq : q.Prime) :
    padicValNat q (dn n) = Nat.log q n := by
  rw [← Nat.factorization_def _ hq]
  exact Nat.factorization_lcmUpto n hq

/-- If `q^{⌊log_q n⌋+1} ∤ m` then `d_n / m` is `q`-integral. -/
private lemma L2b_div_mem (n q : ℕ) [hq : Fact q.Prime] (m : ℤ)
    (hm : ¬ (q : ℤ) ^ (Nat.log q n + 1) ∣ m) :
    ((dn n : ℚ) / (m : ℚ)) ∈ L2b_Zq q := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero _)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hd0 : (dn n : ℚ) ≠ 0 := by exact_mod_cast Nat.lcmUpto_ne_zero n
  have hv : padicValInt q m ≤ Nat.log q n := by
    by_contra h
    rw [not_le] at h
    exact hm ((padicValInt_dvd_iff _ m).mpr (Or.inr (by omega)))
  show padicNorm q ((dn n : ℚ) / (m : ℚ)) ≤ 1
  rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hd0 hm0'), padicValRat.div hd0 hm0',
    padicValRat.of_nat, padicValRat.of_int, L2b_padicValNat_dn n q hq.out]
  apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hq.out.one_lt.le)
  omega

/-- One term: `d_n^{12} (i)₄ r_{i,k} (m/2)^{-(i+4)}` is `q`-integral when `q^{⌊log_q n⌋+1} ∤ m`
(uses L2a: `d_n^{8-i} r_{i,k} ∈ ℤ`). -/
private lemma L2b_term_mem (hL2a : Stmt_L2a) (n q : ℕ) [Fact q.Prime] (i k : ℕ)
    (hi1 : 1 ≤ i) (hi8 : i ≤ 8) (hk : k ≤ n) (m : ℤ)
    (hm : ¬ (q : ℤ) ^ (Nat.log q n + 1) ∣ m) :
    (dn n : ℚ) ^ 12 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k *
      (((m : ℚ) / 2)⁻¹) ^ (i + 4)) ∈ L2b_Zq q := by
  obtain ⟨z, hz⟩ := hL2a n i k hi1 hi8 hk
  have hm0 : (m : ℚ) ≠ 0 := by
    have : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero _)
    exact_mod_cast this
  have key : (dn n : ℚ) ^ 12 * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k *
      (((m : ℚ) / 2)⁻¹) ^ (i + 4)) =
      ((i * (i + 1) * (i + 2) * (i + 3) * 2 ^ (i + 4) : ℕ) : ℚ) * (z : ℚ) *
        ((dn n : ℚ) / m) ^ (i + 4) := by
    rw [← hz, show (dn n : ℚ) ^ 12 = (dn n : ℚ) ^ (8 - i) * (dn n : ℚ) ^ (i + 4) by
      rw [← pow_add]
      congr 1
      omega]
    push_cast
    rw [inv_div, div_pow, div_pow]
    field_simp
  rw [key]
  exact mul_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (pow_mem (L2b_div_mem n q m hm) _)

/-- `ρ₀ = -∑_{k} ∑_{ℓ < k} X(k, ℓ)`, `X(k,ℓ) = ∑_i (i)₄ r_{i,k} (ℓ + 1/2)^{-(i+4)}`. -/
private lemma L2b_rho0_eq (n : ℕ) : rho0 n = -∑ k ∈ range (n + 1), ∑ l ∈ range k,
    ∑ i ∈ Icc (1 : ℕ) 8, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k *
      (((l : ℚ) + 1 / 2)⁻¹) ^ (i + 4) := by
  unfold rho0 Ahalf
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- The heart of L2b: `d_n^{12} X(k, ℓ)` is `q`-integral for every prime `q`. -/
private lemma L2b_X_mem (hPF : Stmt_PF) (hL2a : Stmt_L2a) (n q : ℕ) [hq : Fact q.Prime]
    (k l : ℕ) (hk : k ≤ n) (hl : l < k) :
    (dn n : ℚ) ^ 12 * ∑ i ∈ Icc (1 : ℕ) 8, ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k *
      (((l : ℚ) + 1 / 2)⁻¹) ^ (i + 4) ∈ L2b_Zq q := by
  by_cases hbad : (q : ℤ) ^ (Nat.log q n + 1) ∣ (2 * l + 1 : ℤ)
  · -- bad case: rewrite `X(k, ℓ)` with the root identity
    have hroot := L2b_root hPF n k l hk hl
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : k < n + 1))]
      at hroot
    have e : ((l : ℚ) - k + 1 / 2) + k = (l : ℚ) + 1 / 2 := by ring
    rw [e] at hroot
    rw [eq_neg_of_add_eq_zero_left hroot, mul_neg, Finset.mul_sum]
    refine neg_mem (sum_mem fun k' hk' => ?_)
    rw [Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    obtain ⟨hk'k, hk'n⟩ := Finset.mem_erase.mp hk'
    have hk'n' : k' ≤ n := by
      rw [Finset.mem_range] at hk'n
      omega
    have e2 : ((l : ℚ) - k + 1 / 2) + k' = (((2 * ((l : ℤ) - k + k') + 1 : ℤ) : ℚ) / 2) := by
      push_cast
      ring
    rw [e2]
    apply L2b_term_mem hL2a n q i k' (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 hk'n'
    intro hdvd
    set A : ℤ := (q : ℤ) ^ (Nat.log q n + 1) with hA
    have hA3 : A ∣ 2 * ((k' : ℤ) - k) := by
      have := dvd_sub hdvd hbad
      convert this using 1
      ring
    have hA4 : A ∣ (k' : ℤ) - k := by
      have := dvd_sub (dvd_mul_of_dvd_left hbad ((k' : ℤ) - k)) (dvd_mul_of_dvd_right hA3 (l : ℤ))
      convert this using 1
      ring
    have hnA : (n : ℤ) < A := by
      rw [hA]
      exact_mod_cast Nat.lt_pow_succ_log_self hq.out.one_lt n
    have habs : |(k' : ℤ) - k| < A := abs_lt.mpr ⟨by omega, by omega⟩
    have := Int.eq_zero_of_abs_lt_dvd hA4 habs
    omega
  · -- good case: `v_q(2ℓ+1) ≤ v_q(d_n)`, every term is fine
    rw [Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have e : (l : ℚ) + 1 / 2 = (((2 * (l : ℤ) + 1 : ℤ) : ℚ) / 2) := by
      push_cast
      ring
    rw [e]
    exact L2b_term_mem hL2a n q i k (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2 hk _ hbad

theorem L2b_proof (hPF : Stmt_PF) (hL2a : Stmt_L2a) : Stmt_L2b := by
  intro n
  apply L2b_int_of_forall
  intro q hq
  have := Fact.mk hq
  show (dn n : ℚ) ^ 12 * rho0 n ∈ L2b_Zq q
  rw [L2b_rho0_eq n, mul_neg, Finset.mul_sum]
  refine neg_mem (sum_mem fun k hk => ?_)
  rw [Finset.mul_sum]
  refine sum_mem fun l hl => ?_
  rw [Finset.mem_range] at hk hl
  exact L2b_X_mem hPF hL2a n q k l (by omega) hl

end Zeta2

end
