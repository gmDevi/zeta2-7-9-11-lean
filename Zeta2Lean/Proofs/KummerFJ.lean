import Zeta2Lean.Statements

/-!
# The one-power saving at `ε = 0`: `v_p(F_J(0)) ≥ -4` (proof.md §4.3 Step 5; LSZ (5.4))

**Task.** Prove `Stmt_FJKummer`: for a prime `p ≥ 11` with `p² > 2n`, `1 ≤ ℓ ≤ n`,
`J ∈ chains 8 (n-ℓ)`: `-4 ≤ padicValRat p (FJ0 n ℓ J)`.  No hypotheses (pure number theory on the
explicit formula `FJ0`).

**Informal proof.** Write `N = n - ℓ`.  All binomial coefficients and `N+1` are positive integers
(`v_p ≥ 0`), `-64` is a `p`-unit, and the only denominators are `(2ℓ-1)^4` and `J_8 + 1`, both
integers in `[1, 2n] ⊂ [1, p²)`, hence of valuation `≤ 1`.  So trivially `v_p(FJ0) ≥ -5`, and
`≥ -4` unless `p ∣ 2ℓ-1` **and** `p ∣ J_8+1`, i.e. `ℓ ≡ (p+1)/2`, `J_8 ≡ -1 (mod p)`.
(⋆) Kummer: if `(m mod p) ≥ (p+1)/2` then `p ∣ C(2m, m)` (the lowest base-`p` digit carries in
`m + m`).  Let `x := J_1 mod p`.
* `x ≥ (p+1)/2`: `p ∣ C(2J_1, J_1) = C(2d_1, d_1)` (`d_1 = J_1`).
* `x ≤ (p-3)/2`: `(ℓ + J_1) mod p = (p+1)/2 + x ∈ [(p+1)/2, p-1]`, so `p ∣ C(2(ℓ+J_1), ℓ+J_1)`.
* `x = (p-1)/2`: then `N - J_1 ≡ n - ℓ - J_1 ≡ n (mod p)`.
  - `(n mod p) ≥ (p+1)/2`: `p ∣ C(2(N-J_1), N-J_1)`.
  - `(n mod p) = (p-1)/2`: `N + 1 = n - ℓ + 1 ≡ 0 (mod p)`, so `p ∣ N+1`.
  - `(n mod p) ≤ (p-3)/2`: `N - J_8 ≡ n - (p+1)/2 + 1 ≡ n + (p+1)/2 (mod p)` lies in
    `[(p+1)/2, p-1]` (mod `p`), so `p ∣ C(2(N-J_8), N-J_8)`.
Each of these factors occurs in `FJ0` (the factor `i = 1` of the first and second products, the
factor `i = 1` or `i = 8` of the third product, or `N+1`).  Hence `v_p(FJ0) ≥ -4`.
[The value `-4` is attained; `p ≥ 11` is not needed by this argument — any odd `p` works — but it
is the hypothesis used downstream.]

**Formal proof (this file).**
* `kummerFJ_dvd_choose` — (⋆) via Lucas' theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`):
  if `p ≤ 2 (m % p)` then `(2m) % p = 2 (m % p) - p < m % p`, so the Lucas factor
  `C((2m) % p, m % p)` vanishes.
* `kummerFJ_critical` — the residue bookkeeping, done in `ZMod p` with `linear_combination`
  (`p = 2h+1`, `2ℓ ≡ 1` gives `ℓ ≡ h+1`), converted back to `%` by `ZMod.natCast_eq_natCast_iff'`.
* `kummerFJ_FJ0_eq` — `FJ0 = -(64 M)/D` with natural numbers `M` (all binomials and `N+1`) and
  `D = (2ℓ-1)^4 (J_8+1)`; then `padicValRat.div`, `padicValRat.neg`, `padicValRat.of_nat`,
  `padicValNat.mul`, `padicValNat.pow`, and `v_p ≤ 1` below `p²` (`padicValNat_dvd_iff_le`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- (⋆) Kummer/Lucas: if the lowest base-`p` digit `r = m % p` of `m` satisfies `p ≤ 2r`
(a carry in `m + m`), then `p ∣ C(2m, m)`. -/
private theorem kummerFJ_dvd_choose {p m : ℕ} (hp : p.Prime) (h : p ≤ 2 * (m % p)) :
    p ∣ Nat.choose (2 * m) m := by
  have := Fact.mk hp
  have hr : m % p < p := Nat.mod_lt _ hp.pos
  have hdecomp : 2 * m = (2 * (m % p) - p) + p * (2 * (m / p) + 1) := by
    have := Nat.div_add_mod m p
    rw [mul_add, mul_one, mul_left_comm]
    omega
  have hmod : 2 * m % p = 2 * (m % p) - p := by
    rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hL := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 * m) m p _
  rw [hmod, Nat.choose_eq_zero_of_lt (by omega : 2 * (m % p) - p < m % p), zero_mul] at hL
  exact Nat.modEq_zero_iff_dvd.mp hL

/-- Reading off a residue from an equality in `ZMod p`. -/
private theorem kummerFJ_mod_eq {p m r : ℕ} (hr : r < p) (h : (m : ZMod p) = (r : ZMod p)) :
    m % p = r := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [h, Nat.mod_eq_of_lt hr]

/-- A non-zero natural number below `p²` has `p`-adic valuation at most `1`. -/
private theorem kummerFJ_padicValNat_le_one {p a : ℕ} [Fact p.Prime] (ha : a ≠ 0)
    (hlt : a < p ^ 2) : padicValNat p a ≤ 1 := by
  by_contra hc
  have h1 : p ^ 2 ∣ a := (padicValNat_dvd_iff_le ha).2 (by omega)
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h1) (not_le.mpr hlt)

/-- The critical case `p ∣ 2ℓ-1`, `p ∣ J_8+1`: one of five factors of `FJ0` is divisible by `p`. -/
private theorem kummerFJ_critical {n l p : ℕ} {ch : Fin 8 → ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hl1 : 1 ≤ l) (hln : l ≤ n) (hJ18 : ch 0 ≤ ch 7) (hJ8N : ch 7 ≤ n - l)
    (hA : p ∣ 2 * l - 1) (hB : p ∣ ch 7 + 1) :
    p ∣ Nat.choose (2 * ch 0) (ch 0) ∨ p ∣ Nat.choose (2 * (l + ch 0)) (l + ch 0) ∨
      p ∣ Nat.choose (2 * (n - l - ch 0)) (n - l - ch 0) ∨ p ∣ n - l + 1 ∨
      p ∣ Nat.choose (2 * (n - l - ch 7)) (n - l - ch 7) := by
  obtain ⟨h, hph⟩ : ∃ h, p = 2 * h + 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact absurd h2 hp2
    · exact ⟨p / 2, by omega⟩
  have E0 : 2 * (h : ZMod p) + 1 = 0 := by
    have : ((2 * h + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, ← hph]
    push_cast at this
    exact this
  have E1 : 2 * (l : ZMod p) - 1 = 0 := by
    have : ((2 * l - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hA
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    exact this
  have El : (l : ZMod p) = h + 1 := by linear_combination ((h : ZMod p) + 1) * E1 - (l : ZMod p) * E0
  have E2 : (ch 7 : ZMod p) + 1 = 0 := by
    have : ((ch 7 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hB
    push_cast at this
    exact this
  have hx : ch 0 % p < p := Nat.mod_lt _ hp.pos
  rcases (show h + 1 ≤ ch 0 % p ∨ ch 0 % p + 1 ≤ h ∨ ch 0 % p = h by omega) with hx1 | hx2 | hx3
  · -- `x ≥ (p+1)/2`
    left
    exact kummerFJ_dvd_choose hp (by omega)
  · -- `x ≤ (p-3)/2`
    right; left
    apply kummerFJ_dvd_choose hp
    have : (l + ch 0) % p = h + 1 + ch 0 % p := by
      apply kummerFJ_mod_eq (by omega)
      rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_mod, El]
      push_cast
      ring
    omega
  · -- `x = (p-1)/2`
    have EJ1 : (ch 0 : ZMod p) = h := by rw [← ZMod.natCast_mod, hx3]
    have hy : n % p < p := Nat.mod_lt _ hp.pos
    rcases (show h + 1 ≤ n % p ∨ n % p = h ∨ n % p + 1 ≤ h by omega) with hy1 | hy2 | hy3
    · right; right; left
      apply kummerFJ_dvd_choose hp
      have : (n - l - ch 0) % p = n % p := by
        apply kummerFJ_mod_eq hy
        rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub hln]
        linear_combination -El - EJ1 - E0
      omega
    · right; right; right; left
      rw [← ZMod.natCast_eq_zero_iff]
      have En : (n : ZMod p) = h := by rw [← ZMod.natCast_mod, hy2]
      rw [Nat.cast_add, Nat.cast_sub hln, Nat.cast_one]
      linear_combination En - El
    · right; right; right; right
      apply kummerFJ_dvd_choose hp
      have : (n - l - ch 7) % p = n % p + h + 1 := by
        apply kummerFJ_mod_eq (by omega)
        rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_mod, Nat.cast_sub hJ8N, Nat.cast_sub hln,
          Nat.cast_one]
        linear_combination -El - E2 - E0
      omega

/-- `FJ0` as `-(64 M) / D` with natural numbers `M` (binomials and `N + 1`) and
`D = (2ℓ-1)^4 (J_8+1)`. -/
private theorem kummerFJ_FJ0_eq (n l : ℕ) (ch : Fin 8 → ℕ) (hl : 1 ≤ l) :
    FJ0 n l ch =
      -(((64 * (Nat.choose (2 * l - 2) (l - 1) * (n - l + 1) *
          (∏ i : Fin 8, Nat.choose (2 * (ch i - chainPrev ch i)) (ch i - chainPrev ch i)) *
          (∏ i : Fin 7, Nat.choose (2 * (l + ch i.castSucc)) (l + ch i.castSucc)) *
          (∏ i : Fin 8, Nat.choose (2 * (n - l - ch i)) (n - l - ch i))) : ℕ) : ℚ)) /
        (((2 * l - 1) ^ 4 * (ch 7 + 1) : ℕ) : ℚ) := by
  have h2l : ((2 * l - 1 : ℕ) : ℚ) = 2 * (l : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  unfold FJ0
  push_cast [h2l]
  rw [← div_div]
  ring

theorem FJKummer_proof : Stmt_FJKummer := by
  intro n l ch p hp hp11 hpn hl1 hln hch
  have := Fact.mk hp
  obtain ⟨hbd, hmono⟩ := mem_chains.1 hch
  have hJ18 : ch 0 ≤ ch 7 := hmono 0 7 (by decide)
  have hJ8N : ch 7 ≤ n - l := hbd 7
  rw [kummerFJ_FJ0_eq n l ch hl1]
  set C1 := Nat.choose (2 * l - 2) (l - 1) with hC1
  set P1 := ∏ i : Fin 8, Nat.choose (2 * (ch i - chainPrev ch i)) (ch i - chainPrev ch i) with hP1
  set P2 := ∏ i : Fin 7, Nat.choose (2 * (l + ch i.castSucc)) (l + ch i.castSucc) with hP2
  set P3 := ∏ i : Fin 8, Nat.choose (2 * (n - l - ch i)) (n - l - ch i) with hP3
  set M := C1 * (n - l + 1) * P1 * P2 * P3 with hM
  -- non-vanishing
  have hchoose : ∀ m : ℕ, Nat.choose (2 * m) m ≠ 0 := fun m => (Nat.choose_pos (by omega)).ne'
  have hC10 : C1 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hP10 : P1 ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hchoose _)
  have hP20 : P2 ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hchoose _)
  have hP30 : P3 ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hchoose _)
  have hM0 : M ≠ 0 := by
    simp only [hM, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨hC10, by omega⟩, hP10⟩, hP20⟩, hP30⟩
  have hA0 : 2 * l - 1 ≠ 0 := by omega
  have hB0 : ch 7 + 1 ≠ 0 := by omega
  have h64M : 64 * M ≠ 0 := mul_ne_zero (by norm_num) hM0
  have hD0 : (2 * l - 1) ^ 4 * (ch 7 + 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hA0) hB0
  rw [padicValRat.div (neg_ne_zero.2 (Nat.cast_ne_zero.2 h64M)) (Nat.cast_ne_zero.2 hD0),
    padicValRat.neg, padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.mul (pow_ne_zero _ hA0) hB0, padicValNat.pow]
  -- the two denominators have valuation `≤ 1`
  have hA1 : padicValNat p (2 * l - 1) ≤ 1 := kummerFJ_padicValNat_le_one hA0 (by omega)
  have hB1 : padicValNat p (ch 7 + 1) ≤ 1 := kummerFJ_padicValNat_le_one hB0 (by omega)
  -- the critical case gains one power of `p` in the numerator
  have key : ¬ p ∣ 2 * l - 1 ∨ ¬ p ∣ ch 7 + 1 ∨ p ∣ M := by
    by_cases hA : p ∣ 2 * l - 1
    · by_cases hB : p ∣ ch 7 + 1
      · right; right
        have hprev : chainPrev ch 0 = 0 := by simp [chainPrev]
        have hP1dvd : Nat.choose (2 * ch 0) (ch 0) ∣ P1 := by
          have := Finset.dvd_prod_of_mem
            (fun i : Fin 8 => Nat.choose (2 * (ch i - chainPrev ch i)) (ch i - chainPrev ch i))
            (Finset.mem_univ 0)
          simpa [hprev] using this
        have hP2dvd : Nat.choose (2 * (l + ch 0)) (l + ch 0) ∣ P2 :=
          Finset.dvd_prod_of_mem
            (fun i : Fin 7 => Nat.choose (2 * (l + ch i.castSucc)) (l + ch i.castSucc))
            (Finset.mem_univ 0)
        have hP3dvd0 : Nat.choose (2 * (n - l - ch 0)) (n - l - ch 0) ∣ P3 :=
          Finset.dvd_prod_of_mem
            (fun i : Fin 8 => Nat.choose (2 * (n - l - ch i)) (n - l - ch i)) (Finset.mem_univ 0)
        have hP3dvd7 : Nat.choose (2 * (n - l - ch 7)) (n - l - ch 7) ∣ P3 :=
          Finset.dvd_prod_of_mem
            (fun i : Fin 8 => Nat.choose (2 * (n - l - ch i)) (n - l - ch i)) (Finset.mem_univ 7)
        rcases kummerFJ_critical hp (by omega) hl1 hln hJ18 hJ8N hA hB with h | h | h | h | h
        · exact (((h.trans hP1dvd).mul_left _).mul_right _).mul_right _
        · exact ((h.trans hP2dvd).mul_left _).mul_right _
        · exact (h.trans hP3dvd0).mul_left _
        · exact (((h.mul_left _).mul_right _).mul_right _).mul_right _
        · exact (h.trans hP3dvd7).mul_left _
      · right; left; exact hB
    · left; exact hA
  rcases key with h | h | h
  · rw [padicValNat.eq_zero_of_not_dvd h]
    omega
  · rw [padicValNat.eq_zero_of_not_dvd h]
    omega
  · have h1 : 1 ≤ padicValNat p (64 * M) := one_le_padicValNat_of_dvd h64M (h.mul_left _)
    omega

end Zeta2

end
