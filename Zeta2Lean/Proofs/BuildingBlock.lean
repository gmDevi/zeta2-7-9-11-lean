import Zeta2Lean.Statements

/-!
# Building block `F` (proof.md P5; Lai–Yu Lemma 4.2, Zudilin 2004 Lemma 16)

**Statement.** `Stmt_BlockF`: for `k ≤ n` and all `j`,
`d_n^j · [ε^j] ( 4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k} ) ∈ ℤ`.  No hypotheses.

**Proof (as formalised below).** Write `(r)^{\underline m} := r(r-1)⋯(r-m+1)` (`bfFall r m`) and
`t := n - k`, so `n = t + k`.

1. *Reindexing* (`bfPoch_eq`): `(1/2-ε)_k (1/2+ε)_t = (-1)^k (ε + t - 1/2)^{\underline n}`.
2. *Chu–Vandermonde* (`bfFall_add`, from Mathlib's `Ring.descPochhammer_smeval_add`):
   `(ε + s)^{\underline n} = ∑_{a+m=n} C(n,a) ε^{\underline a} s^{\underline m}`, `s = t - 1/2`.
   Hence `4^n/n! · (ε+s)^{\underline n} = ∑_{a+m=n} (4^m s^{\underline m}/m!) · 4^a · (ε^{\underline a}/a!)`.
3. *Integrality of the constants* (`bfE_int`): `E_m(t) := 4^m (t-1/2)^{\underline m}/m! ∈ ℤ` for
   `t ∈ ℕ`, by induction on `t` via Pascal's rule `E_{m+1}(t+1) = 4 E_m(t) + E_{m+1}(t)`
   (`bfFall_succ_succ`), starting from `E_m(0) = (-1)^m C(2m,m)` (`bfFall_neg_half`).
4. *`d`-integral series* (`bfDInt d`): the subring of `ℚ⟦X⟧` of series with
   `d^j [X^j] A ∈ ℤ` for all `j` (closed under `*` by the Cauchy product).  It contains the integer
   constants and `X/i` for `i ∣ d`.
5. *Binomial basis* (`bfBinom_mem`): for `1 ≤ a ≤ n`,
   `ε^{\underline a}/a! = (ε/a) ∏_{i=1}^{a-1} (ε/i - 1)`, a product of `d_n`-integral factors.

So `4^n/n! (1/2-ε)_k (1/2+ε)_{n-k} = (-1)^k ∑_{a+m=n} E_m(t) · 4^a · ε^{\underline a}/a!` is
`d_n`-integral, which is the claim.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### `d`-integral power series -/

/-- The subring of `ℚ⟦X⟧` of `d`-integral series: `d^j · [X^j] A ∈ ℤ` for every `j`. -/
private def bfDInt (d : ℚ) : Subring (PowerSeries ℚ) where
  carrier := {A | ∀ j : ℕ, ∃ z : ℤ, d ^ j * coeff j A = z}
  mul_mem' := by
    intro A B hA hB j
    simp only [Set.mem_ofPred_eq] at hA hB
    choose zA hzA using hA
    choose zB hzB using hB
    refine ⟨∑ p ∈ antidiagonal j, zA p.1 * zB p.2, ?_⟩
    rw [coeff_mul, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hzA, ← hzB, ← (mem_antidiagonal.1 hp), pow_add]
    ring
  one_mem' := by
    intro j
    rcases j with _ | j
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [coeff_one]⟩
  add_mem' := by
    intro A B hA hB j
    obtain ⟨a, ha⟩ := hA j
    obtain ⟨b, hb⟩ := hB j
    exact ⟨a + b, by rw [map_add, mul_add, ha, hb]; push_cast; ring⟩
  zero_mem' := fun j => ⟨0, by simp⟩
  neg_mem' := by
    intro A hA j
    obtain ⟨a, ha⟩ := hA j
    exact ⟨-a, by rw [map_neg, mul_neg, ha]; push_cast; ring⟩

private lemma bfDInt_mem {d : ℚ} {A : PowerSeries ℚ} :
    A ∈ bfDInt d ↔ ∀ j : ℕ, ∃ z : ℤ, d ^ j * coeff j A = z := Iff.rfl

private lemma bfDInt_C_int (d : ℚ) (z : ℤ) : C (z : ℚ) ∈ bfDInt d := by
  rw [map_intCast]
  exact intCast_mem _ z

private lemma bfDInt_C_inv_mul_X {d i : ℕ} (hi : i ∣ d) :
    C (1 / (i : ℚ)) * X ∈ bfDInt (d : ℚ) := by
  rw [bfDInt_mem]
  intro j
  rw [coeff_C_mul, coeff_X]
  split_ifs with hj
  · subst hj
    obtain ⟨q, rfl⟩ := hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact ⟨0, by simp⟩
    · refine ⟨q, ?_⟩
      have : (i : ℚ) ≠ 0 := by exact_mod_cast h.ne'
      push_cast
      field_simp
  · exact ⟨0, by simp⟩

private lemma bf_dvd_dn {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : i ∣ dn n := by
  unfold dn Nat.lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.2 ⟨h1, h2⟩)

/-! ### Falling factorials -/

/-- Falling factorial `r (r-1) ⋯ (r-n+1)`. -/
private def bfFall {R : Type*} [CommRing R] (r : R) (n : ℕ) : R :=
  ∏ j ∈ range n, (r - (j : R))

private lemma bfFall_eq_smeval {R : Type*} [CommRing R] (r : R) (n : ℕ) :
    (descPochhammer ℤ n).smeval r = bfFall r n := by
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, ← Polynomial.eval_map,
    descPochhammer_map, descPochhammer_eval_eq_prod_range]
  rfl

/-- Chu–Vandermonde for falling factorials. -/
private lemma bfFall_add {R : Type*} [CommRing R] (r s : R) (k : ℕ) :
    bfFall (r + s) k =
      ∑ ij ∈ antidiagonal k, (k.choose ij.1 : R) * (bfFall r ij.1 * bfFall s ij.2) := by
  have h := Ring.descPochhammer_smeval_add (R := R) k (Commute.all r s)
  simp only [bfFall_eq_smeval] at h
  exact h

private lemma bfFall_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) (n : ℕ) :
    f (bfFall r n) = bfFall (f r) n := by
  simp [bfFall, map_prod, map_sub, map_natCast]

private lemma bfFall_succ {R : Type*} [CommRing R] (z : R) (m : ℕ) :
    bfFall z (m + 1) = bfFall z m * (z - m) := by
  simp [bfFall, Finset.prod_range_succ]

/-- Pascal's rule for falling factorials. -/
private lemma bfFall_succ_succ {R : Type*} [CommRing R] (z : R) (m : ℕ) :
    bfFall (z + 1) (m + 1) = (m + 1 : R) * bfFall z m + bfFall z (m + 1) := by
  unfold bfFall
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  have : ∀ j ∈ range m, (z + 1 - ((j + 1 : ℕ) : R)) = z - (j : R) := by
    intro j _
    push_cast
    ring
  rw [Finset.prod_congr rfl this]
  push_cast
  ring

/-! ### The constants `E_m(t) = 4^m binom(t - 1/2, m)` are integers -/

/-- `4^m binom(-1/2, m) = (-1)^m C(2m, m)`. -/
private lemma bfFall_neg_half (m : ℕ) :
    (4 : ℚ) ^ m / (m.factorial : ℚ) * bfFall (-(1 / 2 : ℚ)) m =
      (-1) ^ m * (m.centralBinom : ℚ) := by
  induction m with
  | zero => simp [bfFall]
  | succ m ih =>
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h1 : ((m : ℚ) + 1) * ((m + 1).centralBinom : ℚ) =
        2 * (2 * m + 1) * (m.centralBinom : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hf : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
      push_cast [Nat.factorial_succ]
      ring
    have hmf : (m.factorial : ℚ) ≠ 0 := by positivity
    rw [bfFall_succ, hf]
    have hcb : ((m + 1).centralBinom : ℚ) = 2 * (2 * m + 1) * (m.centralBinom : ℚ) / (m + 1) := by
      field_simp
      linarith [h1]
    rw [hcb]
    calc (4 : ℚ) ^ (m + 1) / ((m + 1) * (m.factorial : ℚ)) *
          (bfFall (-(1 / 2 : ℚ)) m * (-(1 / 2) - m))
        = ((4 : ℚ) ^ m / (m.factorial : ℚ) * bfFall (-(1 / 2 : ℚ)) m) *
            (4 * (-(1 / 2) - m) / (m + 1)) := by
          field_simp
          ring
      _ = (-1) ^ m * (m.centralBinom : ℚ) * (4 * (-(1 / 2) - m) / (m + 1)) := by rw [ih]
      _ = (-1) ^ (m + 1) * (2 * (2 * m + 1) * (m.centralBinom : ℚ) / (m + 1)) := by
          field_simp
          ring

/-- `4^m binom(t - 1/2, m) ∈ ℤ` for `t ∈ ℕ`. -/
private lemma bfE_int (t m : ℕ) :
    ∃ z : ℤ, (4 : ℚ) ^ m / (m.factorial : ℚ) * bfFall ((t : ℚ) - 1 / 2) m = z := by
  induction t generalizing m with
  | zero =>
    refine ⟨(-1) ^ m * m.centralBinom, ?_⟩
    have := bfFall_neg_half m
    simp only [Nat.cast_zero, zero_sub]
    rw [this]
    push_cast
    ring
  | succ t ih =>
    rcases m with _ | m
    · exact ⟨1, by simp [bfFall]⟩
    · obtain ⟨a, ha⟩ := ih m
      obtain ⟨b, hb⟩ := ih (m + 1)
      refine ⟨4 * a + b, ?_⟩
      have hp := bfFall_succ_succ ((t : ℚ) - 1 / 2) m
      have e : ((t + 1 : ℕ) : ℚ) - 1 / 2 = ((t : ℚ) - 1 / 2) + 1 := by push_cast; ring
      rw [e, hp]
      push_cast
      rw [← ha, ← hb]
      have hmf : (m.factorial : ℚ) ≠ 0 := by positivity
      have hf : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
        push_cast [Nat.factorial_succ]
        ring
      rw [hf]
      field_simp
      ring

/-! ### Reindexing and the binomial basis -/

private lemma bf_neg_one_pow_mul_self (k : ℕ) :
    ((-1 : PowerSeries ℚ) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow]
  norm_num

/-- `(1/2-ε)_k (1/2+ε)_t = (-1)^k (ε+t-1/2)(ε+t-3/2)⋯(ε+t-1/2-(t+k-1))`. -/
private lemma bfPoch_eq (k t : ℕ) :
    psPoch (1 / 2) (-1) k * psPoch (1 / 2) 1 t =
      (-1) ^ k * bfFall (X + C ((t : ℚ) - 1 / 2)) (t + k) := by
  unfold psPoch bfFall
  rw [Finset.prod_range_add]
  have h1 : ∏ j ∈ range t, (X + C ((t : ℚ) - 1 / 2) - (j : PowerSeries ℚ)) =
      ∏ j ∈ range t, (C (1 / 2 + (j : ℚ)) + C 1 * X) := by
    conv_lhs => rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < t := Finset.mem_range.1 hj
    have e : ((t - 1 - j : ℕ) : ℚ) = (t : ℚ) - 1 - j := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    have e2 : C ((t : ℚ) - 1 / 2) - ((t - 1 - j : ℕ) : PowerSeries ℚ) = C (1 / 2 + (j : ℚ)) := by
      rw [← map_natCast (C : ℚ →+* PowerSeries ℚ), e, ← map_sub]
      congr 1
      ring
    rw [map_one]
    linear_combination e2
  have h2 : ∏ j ∈ range k, (X + C ((t : ℚ) - 1 / 2) - ((t + j : ℕ) : PowerSeries ℚ)) =
      (-1) ^ k * ∏ j ∈ range k, (C (1 / 2 + (j : ℚ)) + C (-1) * X) := by
    have : (-1 : PowerSeries ℚ) ^ k * ∏ j ∈ range k, (C (1 / 2 + (j : ℚ)) + C (-1) * X) =
        ∏ j ∈ range k, ((-1) * (C (1 / 2 + (j : ℚ)) + C (-1) * X)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [this]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e2 : C ((t : ℚ) - 1 / 2) - ((t + j : ℕ) : PowerSeries ℚ) = -C (1 / 2 + (j : ℚ)) := by
      rw [← map_natCast (C : ℚ →+* PowerSeries ℚ), ← map_sub, ← map_neg]
      congr 1
      push_cast
      ring
    rw [map_neg, map_one]
    linear_combination e2
  rw [h1, h2]
  linear_combination (-((∏ j ∈ range k, (C (1 / 2 + (j : ℚ)) + C (-1) * X)) *
    (∏ j ∈ range t, (C (1 / 2 + (j : ℚ)) + C 1 * X)))) * (bf_neg_one_pow_mul_self k)

/-- `binom(ε, a) = ε(ε-1)⋯(ε-a+1)/a!` is `d_n`-integral for `a ≤ n`. -/
private lemma bfBinom_mem {n a : ℕ} (ha : a ≤ n) :
    C (1 / (a.factorial : ℚ)) * bfFall (X : PowerSeries ℚ) a ∈ bfDInt (dn n : ℚ) := by
  rcases a with _ | b
  · simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul, bfFall,
      Finset.range_zero, Finset.prod_empty]
    exact one_mem _
  · have hfac : (1 / ((b + 1).factorial : ℚ)) =
        1 / ((b + 1 : ℕ) : ℚ) * ∏ j ∈ range b, (1 / ((j + 1 : ℕ) : ℚ)) := by
      rw [Nat.factorial_succ, ← Finset.prod_range_add_one_eq_factorial]
      push_cast
      simp only [one_div, mul_inv, Finset.prod_inv_distrib]
    have h1 : ∀ j ∈ range b, C (1 / ((j + 1 : ℕ) : ℚ)) * X - 1 =
        C (1 / ((j + 1 : ℕ) : ℚ)) * (X - ((j + 1 : ℕ) : PowerSeries ℚ)) := by
      intro j _
      rw [mul_sub, ← map_natCast (C : ℚ →+* PowerSeries ℚ) (j + 1), ← map_mul]
      rw [show 1 / ((j + 1 : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ) = 1 by
        have : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp]
      rw [map_one]
    have key : C (1 / ((b + 1).factorial : ℚ)) * bfFall (X : PowerSeries ℚ) (b + 1) =
        (C (1 / ((b + 1 : ℕ) : ℚ)) * X) *
          ∏ j ∈ range b, (C (1 / ((j + 1 : ℕ) : ℚ)) * X - 1) := by
      rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, hfac, map_mul, map_prod]
      unfold bfFall
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, sub_zero]
      ring
    rw [key]
    refine mul_mem (bfDInt_C_inv_mul_X (bf_dvd_dn (by omega) ha)) (prod_mem fun j hj => ?_)
    have hj := Finset.mem_range.1 hj
    exact sub_mem (bfDInt_C_inv_mul_X (bf_dvd_dn (by omega) (by omega))) (one_mem _)

/-! ### Main result -/

theorem BlockF_proof : Stmt_BlockF := by
  intro n k hk j
  have hmem : C ((4 : ℚ) ^ n / (n.factorial : ℚ)) * psPoch (1 / 2) (-1) k *
      psPoch (1 / 2) 1 (n - k) ∈ bfDInt (dn n : ℚ) := by
    obtain ⟨t, rfl⟩ : ∃ t, n = t + k := ⟨n - k, by omega⟩
    rw [show t + k - k = t by omega, mul_assoc, bfPoch_eq, bfFall_add,
      mul_left_comm (C _) ((-1 : PowerSeries ℚ) ^ k), Finset.mul_sum]
    refine mul_mem (pow_mem (neg_mem (one_mem _)) _) (sum_mem fun ij hij => ?_)
    have hsum : ij.1 + ij.2 = t + k := mem_antidiagonal.1 hij
    obtain ⟨z, hz⟩ := bfE_int t ij.2
    have hscal : (4 : ℚ) ^ (t + k) / ((t + k).factorial : ℚ) * ((t + k).choose ij.1 : ℚ) *
        bfFall ((t : ℚ) - 1 / 2) ij.2 = (z : ℚ) * (4 : ℚ) ^ ij.1 * (1 / (ij.1.factorial : ℚ)) := by
      rw [← hz]
      have hfac := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ t + k by omega)
      rw [show t + k - ij.1 = ij.2 by omega] at hfac
      have hfac' : ((t + k).choose ij.1 : ℚ) * (ij.1.factorial : ℚ) * (ij.2.factorial : ℚ) =
          ((t + k).factorial : ℚ) := by exact_mod_cast hfac
      rw [← hfac', ← hsum, pow_add]
      have h1 : ((ij.1 + ij.2).choose ij.1 : ℚ) ≠ 0 := by
        have := Nat.choose_pos (show ij.1 ≤ ij.1 + ij.2 by omega)
        positivity
      have h2 : (ij.1.factorial : ℚ) ≠ 0 := by positivity
      have h3 : (ij.2.factorial : ℚ) ≠ 0 := by positivity
      field_simp
    have hR : C (z : ℚ) * C ((4 : ℚ) ^ ij.1) *
        (C (1 / (ij.1.factorial : ℚ)) * bfFall (X : PowerSeries ℚ) ij.1) ∈
          bfDInt (dn (t + k) : ℚ) := by
      refine mul_mem (mul_mem (bfDInt_C_int _ z) ?_) (bfBinom_mem (by omega))
      have e4 : (((4 ^ ij.1 : ℤ)) : ℚ) = (4 : ℚ) ^ ij.1 := by norm_num
      rw [← e4]
      exact bfDInt_C_int _ _
    convert hR using 1
    rw [← bfFall_map (C : ℚ →+* PowerSeries ℚ), ← map_natCast (C : ℚ →+* PowerSeries ℚ)]
    have := congrArg (C : ℚ →+* PowerSeries ℚ) hscal
    simp only [map_mul] at this ⊢
    linear_combination (bfFall (X : PowerSeries ℚ) ij.1) * this
  exact hmem j

end Zeta2

end
