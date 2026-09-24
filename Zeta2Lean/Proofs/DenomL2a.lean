import Zeta2Lean.Statements

/-!
# L2a: `d_n^{8-i} r_{i,k} ∈ ℤ` (proof.md §4.1)

**Task.** Prove `Stmt_L2a` from `Stmt_BlockF`.

**Informal proof.** Call `A ∈ ℚ⟦X⟧` *`d`-integral* if `∀ j, ∃ z : ℤ, d^j * coeff j A = z`.  This
class is closed under `+`, `*` (Cauchy product `d^j ∑_{a+b=j} A_a B_b = ∑ (d^a A_a)(d^b B_b)`),
powers, and contains `C z` (`z ∈ ℤ`) and `X`.  Take `d = d_n = lcm(1..n)`.  Since
`2^{16n} = (4^n)^8`,
  `Gser n k = (C(n-2k) + 2X) · (4^n Ψ_k)^8`,
  `4^n Ψ_k = [4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k}] · [n! / ((1-ε)_k (1+ε)_{n-k})]`.
The first bracket is `d_n`-integral by `Stmt_BlockF`.  For the second,
`(1-ε)_k = k! ∏_{i=1}^{k} (1 - ε/i)` and `(1+ε)_{n-k} = (n-k)! ∏_{i=1}^{n-k} (1 + ε/i)`, so
  `n!/((1-ε)_k (1+ε)_{n-k}) = C(n,k) ∏_{i=1}^{k} (1-ε/i)⁻¹ ∏_{i=1}^{n-k} (1+ε/i)⁻¹`,
and `(1 ∓ ε/i)⁻¹ = ∑_j (±1/i)^j ε^j` is `d_n`-integral because `i ∣ d_n` (`i ≤ n`).  Hence
`Gser n k` is `d_n`-integral, and `r_{i,k} = coeff (8-i) (Gser n k)` gives the claim.

**Lean hints.** `PowerSeries.coeff_mul`, `Finset.sum_mul_sum`, `Finset.mem_antidiagonal`, `PowerSeries.mk`, `PowerSeries.coeff_mk`,
`PowerSeries.eq_inv_iff_mul_eq_one` (to identify `(1 - ε/i)⁻¹` with a geometric series),
`PowerSeries.mul_inv_rev`, `Finset.prod_range_succ`, `Nat.choose_mul_factorial_mul_factorial`,
`Finset.dvd_lcm`, `Nat.lcmUpto`, `Int.cast_mul`, `Int.cast_sum`.

**Numerical check.** `python/mirror.py`, section "Stmt_BlockF, Stmt_L2a, Stmt_L2b" (`n ≤ 20`).

**Formalisation (complete; axioms: propext, Classical.choice, Quot.sound).** `l2aDInt d` is the subring `(map Int.cast).range.comap (rescale d)`
of `ℚ⟦X⟧`, so closure under `+`, `*`, powers is free (`Subring.mul_mem`, `Subring.pow_mem`);
`l2a_mem_DInt_iff` unfolds it to `∀ j, ∃ z : ℤ, d^j * coeff j A = z`.  `l2a_geom_mem` identifies
`c (c + e X)⁻¹` with `mk (fun j => (-e/c)^j)` via `PowerSeries.inv_eq_iff_mul_eq_one`;
`l2a_invPoch_mem` inducts on `m` for `m! / (1 + e ε)_m`; `l2a_H_mem` splits
`n! = C(n,k) k! (n-k)!`.  Nothing here uses `a = 8` beyond `Gser`'s shape: the same argument gives
`d_n^μ [ε^μ] (n-2k+2ε)(4^n Ψ_k)^a ∈ ℤ` for every exponent `a`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-- Power series over `ℚ` with integer coefficients (the image of `ℤ⟦X⟧`), a subring. -/
private def l2aIntPS : Subring (PowerSeries ℚ) :=
  (PowerSeries.map (Int.castRingHom ℚ)).range

private lemma l2a_mem_intPS_iff (B : PowerSeries ℚ) :
    B ∈ l2aIntPS ↔ ∀ j, ∃ z : ℤ, coeff j B = z := by
  constructor
  · rintro ⟨B', rfl⟩ j
    exact ⟨coeff j B', by simp [coeff_map]⟩
  · intro h
    choose z hz using h
    refine ⟨PowerSeries.mk z, ?_⟩
    ext j
    rw [coeff_map, coeff_mk, hz j, eq_intCast]

/-- `d`-integral power series (`d^j · [X^j] A ∈ ℤ` for all `j`): the preimage of `l2aIntPS`
under the ring homomorphism `rescale d`, hence a subring. -/
private def l2aDInt (d : ℚ) : Subring (PowerSeries ℚ) :=
  l2aIntPS.comap (rescale d)

private lemma l2a_mem_DInt_iff (d : ℚ) (A : PowerSeries ℚ) :
    A ∈ l2aDInt d ↔ ∀ j, ∃ z : ℤ, d ^ j * coeff j A = z := by
  simp only [l2aDInt, Subring.mem_comap, l2a_mem_intPS_iff, coeff_rescale]

private lemma l2a_C_int_mem (d : ℚ) (z : ℤ) : C (z : ℚ) ∈ l2aDInt d := by
  rw [map_intCast]
  exact intCast_mem _ z

private lemma l2a_X_mem (N : ℕ) : (X : PowerSeries ℚ) ∈ l2aDInt (N : ℚ) := by
  rw [l2a_mem_DInt_iff]
  intro j
  by_cases hj : j = 1
  · subst hj
    exact ⟨N, by simp⟩
  · exact ⟨0, by simp [coeff_X, hj]⟩

/-- The geometric series `c · (c + e X)⁻¹ = ∑_j (-e/c)^j X^j` is `N`-integral when `c ∣ N`. -/
private lemma l2a_geom_mem (N c : ℕ) (e : ℤ) (hc : c ≠ 0) (hcN : c ∣ N) :
    C (c : ℚ) * (C (c : ℚ) + C (e : ℚ) * X)⁻¹ ∈ l2aDInt (N : ℚ) := by
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  set G : PowerSeries ℚ := PowerSeries.mk fun j => (-(e : ℚ) / c) ^ j with hG
  have hGmul : G * (C (c : ℚ) + C (e : ℚ) * X) = C (c : ℚ) := by
    have h1 : G * (C (c : ℚ) + C (e : ℚ) * X) = C (c : ℚ) * G + C (e : ℚ) * (G * X) := by ring
    rw [h1]
    ext j
    rcases j with _ | j
    · simp [hG]
    · rw [map_add, coeff_C_mul, coeff_C_mul, coeff_succ_mul_X, coeff_C]
      simp only [hG, coeff_mk, Nat.succ_ne_zero, ite_false]
      have hce : (c : ℚ) * (-(e : ℚ) / c) = -e := by field_simp
      calc (c : ℚ) * (-(e : ℚ) / c) ^ (j + 1) + e * (-(e : ℚ) / c) ^ j
          = (-(e : ℚ) / c) ^ j * ((c : ℚ) * (-(e : ℚ) / c) + e) := by ring
        _ = 0 := by rw [hce]; ring
  have hconst : constantCoeff (C (c : ℚ) + C (e : ℚ) * X) ≠ 0 := by simp [hcq]
  have hinv : (C (c : ℚ) + C (e : ℚ) * X)⁻¹ = C ((c : ℚ)⁻¹) * G := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hconst, mul_assoc, hGmul, ← map_mul,
      inv_mul_cancel₀ hcq, map_one]
  rw [hinv, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcq, map_one, one_mul,
    l2a_mem_DInt_iff]
  intro j
  obtain ⟨q, rfl⟩ := hcN
  refine ⟨(-e * q) ^ j, ?_⟩
  simp only [hG, coeff_mk]
  rw [← mul_pow]
  push_cast
  congr 1
  field_simp

/-- `m! / (1 + e ε)_m` is `N`-integral when `1, …, m` all divide `N`. -/
private lemma l2a_invPoch_mem (N : ℕ) (e : ℤ) (m : ℕ) (hm : ∀ i ∈ Icc 1 m, i ∣ N) :
    C ((m.factorial : ℕ) : ℚ) * (psPoch 1 (e : ℚ) m)⁻¹ ∈ l2aDInt (N : ℚ) := by
  induction m with
  | zero =>
    have h1 : (psPoch 1 (e : ℚ) 0)⁻¹ = 1 := by
      rw [psPoch, Finset.prod_range_zero, ← map_one C, PowerSeries.C_inv, inv_one]
    rw [h1, mul_one, Nat.factorial_zero, Nat.cast_one, map_one]
    exact Subring.one_mem _
  | succ m ih =>
    have ih' := ih (fun i hi => hm i (by simp only [Finset.mem_Icc] at hi ⊢; omega))
    have hgeom := l2a_geom_mem N (m + 1) e (Nat.succ_ne_zero m) (hm (m + 1) (by simp))
    have heq : C (((m + 1).factorial : ℕ) : ℚ) * (psPoch 1 (e : ℚ) (m + 1))⁻¹ =
        (C ((m.factorial : ℕ) : ℚ) * (psPoch 1 (e : ℚ) m)⁻¹) *
        (C (((m + 1 : ℕ)) : ℚ) * (C (((m + 1 : ℕ)) : ℚ) + C (e : ℚ) * X)⁻¹) := by
      have hL : C (((m + 1 : ℕ)) : ℚ) + C (e : ℚ) * X = C (1 + (m : ℚ)) + C (e : ℚ) * X := by
        push_cast
        ring_nf
      rw [hL, psPoch, psPoch, Finset.prod_range_succ, PowerSeries.mul_inv_rev,
        Nat.factorial_succ]
      push_cast
      simp only [map_mul, map_add, map_one, map_natCast]
      ring
    rw [heq]
    exact Subring.mul_mem _ ih' hgeom

/-- `n! / ((1-ε)_k (1+ε)_{n-k})` is `d_n`-integral. -/
private lemma l2a_H_mem (n k : ℕ) (hk : k ≤ n) :
    C ((n.factorial : ℕ) : ℚ) * (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹ ∈
      l2aDInt (dn n : ℚ) := by
  have hdvd : ∀ m ≤ n, ∀ i ∈ Icc 1 m, i ∣ dn n := by
    intro m hm i hi
    simp only [Finset.mem_Icc] at hi
    unfold dn Nat.lcmUpto
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hi.1, hi.2.trans hm⟩)
  have h1 := l2a_invPoch_mem (dn n) (-1) k (hdvd k hk)
  have h2 := l2a_invPoch_mem (dn n) 1 (n - k) (hdvd (n - k) (Nat.sub_le n k))
  have heq : C ((n.factorial : ℕ) : ℚ) * (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹ =
      C ((n.choose k : ℕ) : ℚ) * (C ((k.factorial : ℕ) : ℚ) * (psPoch 1 ((-1 : ℤ) : ℚ) k)⁻¹) *
        (C (((n - k).factorial : ℕ) : ℚ) * (psPoch 1 ((1 : ℤ) : ℚ) (n - k))⁻¹) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk, PowerSeries.mul_inv_rev]
    push_cast
    simp only [map_mul]
    ring
  rw [heq]
  refine Subring.mul_mem _ (Subring.mul_mem _ ?_ h1) h2
  have := l2a_C_int_mem (dn n : ℚ) (n.choose k : ℤ)
  exact_mod_cast this

theorem L2a_proof (hF : Stmt_BlockF) : Stmt_L2a := by
  intro n i k hi1 hi8 hk
  -- the building block `4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k}` (Stmt_BlockF)
  have hB : C ((4 : ℚ) ^ n / (n.factorial : ℚ)) * psPoch (1 / 2) (-1) k *
      psPoch (1 / 2) 1 (n - k) ∈ l2aDInt (dn n : ℚ) :=
    (l2a_mem_DInt_iff _ _).2 (hF n k hk)
  have hH := l2a_H_mem n k hk
  have hfac : ((n.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hPsi : C ((4 : ℚ) ^ n) * Psi n k =
      (C ((4 : ℚ) ^ n / (n.factorial : ℚ)) * psPoch (1 / 2) (-1) k * psPoch (1 / 2) 1 (n - k)) *
      (C ((n.factorial : ℕ) : ℚ) * (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹) := by
    unfold Psi
    have h4 : C ((4 : ℚ) ^ n) = C ((4 : ℚ) ^ n / (n.factorial : ℚ)) * C ((n.factorial : ℕ) : ℚ) := by
      rw [← map_mul, div_mul_cancel₀ _ hfac]
    rw [h4]
    ring
  have h2 : C ((2 : ℚ) ^ (16 * n)) = C ((4 : ℚ) ^ n) ^ 8 := by
    rw [← map_pow, ← pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have hG : Gser n k = (C ((n : ℚ) - 2 * k) + C 2 * X) * (C ((4 : ℚ) ^ n) * Psi n k) ^ 8 := by
    unfold Gser
    rw [h2]
    ring
  have hlin : C ((n : ℚ) - 2 * k) + C 2 * X ∈ l2aDInt (dn n : ℚ) := by
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ ?_ (l2a_X_mem _))
    · have := l2a_C_int_mem (dn n : ℚ) ((n : ℤ) - 2 * k)
      push_cast at this
      exact this
    · have := l2a_C_int_mem (dn n : ℚ) 2
      push_cast at this
      exact this
  have hGmem : Gser n k ∈ l2aDInt (dn n : ℚ) := by
    rw [hG, hPsi]
    exact Subring.mul_mem _ hlin (Subring.pow_mem _ (Subring.mul_mem _ hB hH) 8)
  obtain ⟨z, hz⟩ := (l2a_mem_DInt_iff _ _).1 hGmem (8 - i)
  refine ⟨z, ?_⟩
  simp only [rcoef, hi1, hi8, hk, and_self, ↓reduceIte]
  exact hz

end Zeta2

end
