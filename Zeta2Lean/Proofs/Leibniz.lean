import Zeta2Lean.Statements

/-!
# Leibniz expansion of the integrand (proof.md §7 "Setup" and "Leibniz"; §5)

**Task.** Prove `Stmt_Leibniz` from `Stmt_PF`: for all `n, x ∈ ℕ`,
  `integrand n x = ∑_{γ<2} ∑_{β<4-γ} ∑_{M ∈ (Icc 1 n).finsuppAntidiag (3-γ-β)} leibTerm n γ β M x`.

**Status.** Complete; `#print axioms Zeta2.Leibniz_proof` gives
`[propext, Classical.choice, Quot.sound]`.

**Informal proof.**
1. `integrand n x = -6 · [ε^3] Rser n (x + 1/2)`.  Apply `Stmt_PF.series` at `y = x + 1/2`
   (`y + j > 0`).  In `ℚ⟦ε⟧`, `((C a + X)^i)⁻¹ = ∑_j C(-i, j) a^{-i-j} ε^j`, so
   `[ε^3] ((C a + X)^i)⁻¹ = -C(i+2, 3) a^{-i-3} = -(i)₃/6 · a^{-i-3}`; with `a = x + k + 1/2` this
   is exactly `-1/6` times the `(i,k)` term of `integrand`.
2. Product form: with `y = x + 1/2`, `C(y + 1/2 + j) + X = C(x+1+j) + X` and
   `C(y + j) + X = (1/2)(C(2x+2j+1) + 2X)`, so
   `Rser n (x+1/2) = 2^{24n+8} · (C(2x+1+n) + 2X) · ∏_{l=1}^{n} (C(x+l) + X)^8 · H(2X)`,
   `H(δ) := ∏_{k≤n} ((C(2x+2k+1) + δ)^8)⁻¹`, and `H(2X) = rescale 2 H`, so
   `[ε^β] H(2ε) = 2^β hcoef n β x`.
3. `[ε^3]` of the triple product
   `= ∑_{γ+a+β=3} [ε^γ](C(2x+1+n) + 2X) · [ε^a] ∏_l (C(x+l)+X)^8 · 2^β h_β`,
   `[ε^γ](C(2x+1+n) + 2X) = 2x+1+n` (γ = 0), `2` (γ = 1), `0` (γ ≥ 2).
4. `[ε^a] ∏_{l=1}^{n} (C(x+l) + X)^8
     = ∑_{M ∈ (Icc 1 n).finsuppAntidiag a} ∏_l C(8, M l) (x+l)^{8 - M l}`
   (`PowerSeries.coeff_prod` + binomial theorem `[ε^j](C c + X)^8 = C(8,j) c^{8-j}`).
5. For `M` with `∑_l M l = a ≤ 3`:
   `∏_{l=1}^{n} (x+l)^{8 - M l} = n!^{8-a} C(x+n,n)^{8-a} ∏_l ((l-1)!(n-l)! Y_l(x))^{M l}`,
   because `∏_{l=1}^{n} (x+l) = n! C(x+n,n)` and `(x+l) · (l-1)!(n-l)! Y_l(x) = n! C(x+n,n)`
   (i.e. `(x+1)_n / (x+l) = (l-1)! C(x+l-1,l-1) · (n-l)! C(x+n,n-l)`).  Note `8 - a = 5 + γ + β`.
6. Collect: `-6 · 2^{24n+8} · (…)` is `leibTerm`.

**Lean proof map.**
* Step 1: `leib_inv_C_add_X_pow` (`((c+ε)^{d+1})⁻¹ = c^{-d-1} · rescale (-1/c) (invOneSubPow)`),
  `leib_coeff3_inv`, `leib_integrand_eq`.
* Step 2: `leib_prod_shift`, `leib_den` (via `PowerSeries.eq_inv_iff_mul_eq_one`), `leib_Rser_prod`.
* Steps 3–4: `leib_coeff_lin`, `leib_coeff_B` (`PowerSeries.coeff_prod`), `leib_coeff_C_add_X_pow`.
* Step 5: `leib_key1` (`Nat.ascFactorial_eq_factorial_mul_choose`), `leib_key2`, `leib_prod_M`.
* Step 6: `leib_sum_M` (one `(γ, β)` block), `Leibniz_proof` (expand the finitely many blocks).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### Power-series helpers -/

private theorem leib_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

private theorem leib_rescale_lin (c : ℚ) : rescale (2 : ℚ) (C c + X) = C c + C 2 * X := by
  rw [map_add, leib_rescale_C, rescale_X]

/-- `[ε^j] (c + ε)^m = C(m, j) c^{m-j}`. -/
private theorem leib_coeff_C_add_X_pow (c : ℚ) (m j : ℕ) :
    coeff j ((C c + X : PowerSeries ℚ) ^ m) = (m.choose j : ℚ) * c ^ (m - j) := by
  have h : ((C c + X : PowerSeries ℚ)) ^ m =
      (((Polynomial.X + Polynomial.C c) ^ m : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, add_comm]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow, mul_comm]

/-- `((c + ε)^{d+1})⁻¹ = c^{-(d+1)} ∑_j C(d+j, d) (-ε/c)^j`. -/
private theorem leib_inv_C_add_X_pow (a : ℚ) (ha : a ≠ 0) (d : ℕ) :
    ((C a + X : PowerSeries ℚ) ^ (d + 1))⁻¹ =
      C (a⁻¹ ^ (d + 1)) * rescale (-a⁻¹) (mk fun j => ((d + j).choose d : ℚ)) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · have h1 : (C a + X : PowerSeries ℚ) = C a * rescale (-a⁻¹) (1 - X) := by
      rw [map_sub, map_one, rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul]
      rw [mul_neg, mul_inv_cancel₀ ha, map_neg, map_one]
      ring
    rw [h1, mul_pow, ← map_pow, ← map_pow]
    calc C (a⁻¹ ^ (d + 1)) * rescale (-a⁻¹) (mk fun j => ((d + j).choose d : ℚ)) *
          (C (a ^ (d + 1)) * rescale (-a⁻¹) ((1 - X) ^ (d + 1)))
        = C (a⁻¹ ^ (d + 1) * a ^ (d + 1)) *
            rescale (-a⁻¹) ((mk fun j => ((d + j).choose d : ℚ)) * (1 - X) ^ (d + 1)) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by
          rw [mk_add_choose_mul_one_sub_pow_eq_one, map_one, ← mul_pow, inv_mul_cancel₀ ha,
            one_pow, map_one, mul_one]
  · simp [ha]

private theorem leib_choose3 (d : ℕ) :
    ((d + 3).choose d : ℚ) = (d + 1) * (d + 2) * (d + 3) / 6 := by
  rw [Nat.cast_choose ℚ (by omega : d ≤ d + 3)]
  rw [show d + 3 - d = 3 by omega]
  rw [show d + 3 = (d + 2) + 1 by ring, Nat.factorial_succ, show d + 2 = (d + 1) + 1 by ring,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `[ε^3] ((a + ε)^i)⁻¹ = -(i)₃/6 · a^{-i-3}` (`i ≥ 1`, `a ≠ 0`). -/
private theorem leib_coeff3_inv (a : ℚ) (ha : a ≠ 0) (i : ℕ) (hi : 1 ≤ i) :
    coeff 3 ((C a + X : PowerSeries ℚ) ^ i)⁻¹ =
      -((i : ℚ) * (i + 1) * (i + 2) / 6) * (a⁻¹) ^ (i + 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  rw [leib_inv_C_add_X_pow a ha d, coeff_C_mul, coeff_rescale, coeff_mk, leib_choose3]
  push_cast
  ring

/-! ### Step 1: the integrand as a Taylor coefficient -/

/-- `integrand n x = -6 [ε^3] R_n(x + 1/2 + ε)`. -/
private theorem leib_integrand_eq (hPF : Stmt_PF) (n x : ℕ) :
    integrand n x = -6 * coeff 3 (Rser n ((x : ℚ) + 1 / 2)) := by
  rw [hPF.series n ((x : ℚ) + 1 / 2) (fun j _ => by positivity)]
  simp only [map_sum, coeff_C_mul]
  unfold integrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hpos : ((x : ℚ) + 1 / 2 + k) ≠ 0 := by positivity
  rw [leib_coeff3_inv _ hpos i hi1]
  have e : ((x : ℚ) + 1 / 2 + k) = (((x + k : ℕ) : ℚ) + 1 / 2) := by push_cast; ring
  rw [e]
  ring

/-! ### Step 2: product form of `R_n(x + 1/2 + ε)` -/

/-- The inverse-product factor of `hcoef`: `H(δ) = ∏_{k ≤ n} (2x+2k+1+δ)^{-8}`. -/
private def leibH (n x : ℕ) : PowerSeries ℚ :=
  ∏ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8)⁻¹

private theorem leib_hcoef_eq (n β x : ℕ) : hcoef n β x = coeff β (leibH n x) := rfl

private theorem leib_prod_shift (n x : ℕ) :
    (∏ j ∈ range n, (C ((x : ℚ) + 1 / 2 + 1 / 2 + j) + X)) ^ 8 =
      ∏ l ∈ Icc 1 n, (C (((x + l : ℕ) : ℚ)) + X) ^ 8 := by
  rw [← Finset.prod_pow, ← Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    show n + 1 - 1 = n by omega]
  apply Finset.prod_congr rfl
  intro j _
  congr 3
  push_cast
  ring

private theorem leib_den (n x : ℕ) :
    ((∏ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X)) ^ 8)⁻¹ =
      C ((2 : ℚ) ^ (8 * n + 8)) * rescale 2 (leibH n x) := by
  have hφ : ∀ k : ℕ, constantCoeff ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8) ≠ 0 := by
    intro k
    simp only [map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
    positivity
  have hD : (∏ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X)) ^ 8 =
      C (((1 : ℚ) / 2) ^ (8 * n + 8)) *
        rescale 2 (∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8) := by
    have hj : ∀ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X) ^ 8 =
        C (((1 : ℚ) / 2) ^ 8) * rescale 2 ((C (((2 * x + 2 * j + 1 : ℕ) : ℚ)) + X) ^ 8) := by
      intro j _
      rw [map_pow (rescale (2 : ℚ)), leib_rescale_lin, map_pow C, ← mul_pow]
      congr 1
      have e1 : (1 / 2 : ℚ) * ((2 * x + 2 * j + 1 : ℕ) : ℚ) = (x : ℚ) + 1 / 2 + j := by
        push_cast; ring
      have e2 : (1 / 2 : ℚ) * 2 = 1 := by norm_num
      rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, e1, e2, map_one, one_mul]
    rw [map_prod, ← Finset.prod_pow, Finset.prod_congr rfl hj, Finset.prod_mul_distrib,
      Finset.prod_const, card_range, ← map_pow, ← pow_mul, show 8 * (n + 1) = 8 * n + 8 by ring]
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [hD]
    calc C ((2 : ℚ) ^ (8 * n + 8)) * rescale 2 (leibH n x) *
          (C (((1 : ℚ) / 2) ^ (8 * n + 8)) *
            rescale 2 (∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8))
        = C ((2 : ℚ) ^ (8 * n + 8) * ((1 : ℚ) / 2) ^ (8 * n + 8)) *
            rescale 2 (leibH n x *
              ∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by
          rw [← mul_pow, show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_pow, map_one, one_mul]
          unfold leibH
          rw [← Finset.prod_mul_distrib,
            Finset.prod_eq_one (fun k _ => PowerSeries.inv_mul_cancel _ (hφ k)), map_one]
  · rw [map_pow, map_prod]
    apply pow_ne_zero
    rw [Finset.prod_ne_zero_iff]
    intro j _
    simp only [map_add, constantCoeff_C, constantCoeff_X, add_zero]
    positivity

/-- `R_n(x + 1/2 + ε) = 2^{24n+8} (2x+1+n+2ε) ∏_{l=1}^n (x+l+ε)^8 · H(2ε)`. -/
private theorem leib_Rser_prod (n x : ℕ) :
    Rser n ((x : ℚ) + 1 / 2) =
      C ((2 : ℚ) ^ (24 * n + 8)) * ((C (((2 * x + 1 + n : ℕ) : ℚ)) + C 2 * X) *
        ((∏ l ∈ Icc 1 n, (C (((x + l : ℕ) : ℚ)) + X) ^ 8) * rescale 2 (leibH n x))) := by
  unfold Rser
  rw [leib_prod_shift, leib_den]
  have e1 : (2 : ℚ) * ((x : ℚ) + 1 / 2) + n = ((2 * x + 1 + n : ℕ) : ℚ) := by push_cast; ring
  rw [e1]
  have e2 : (2 : ℚ) ^ (24 * n + 8) = 2 ^ (16 * n) * 2 ^ (8 * n + 8) := by
    rw [← pow_add]; ring_nf
  rw [e2, map_mul]
  ring

/-! ### Steps 3–4: extracting `[ε^3]` -/

/-- `[ε^3] ((c + 2ε) E) = c [ε^3] E + 2 [ε^2] E`. -/
private theorem leib_coeff_lin (a0 : ℚ) (E : PowerSeries ℚ) :
    coeff 3 ((C a0 + C 2 * X) * E) = a0 * coeff 3 E + 2 * coeff 2 E := by
  have h3 : coeff 3 (X * E) = coeff 2 E := coeff_succ_X_mul 2 E
  rw [add_mul, map_add, mul_assoc, coeff_C_mul, coeff_C_mul, h3]

/-- `[ε^a] ∏_{l=1}^n (x+l+ε)^8 = ∑_M ∏_l C(8, M l) (x+l)^{8 - M l}`. -/
private theorem leib_coeff_B (n x a : ℕ) :
    coeff a (∏ l ∈ Icc 1 n, (C (((x + l : ℕ) : ℚ)) + X) ^ 8) =
      ∑ M ∈ (Icc 1 n).finsuppAntidiag a, ∏ l ∈ Icc 1 n,
        (((Nat.choose 8 (M l) : ℕ) : ℚ) * (((x + l : ℕ) : ℚ)) ^ (8 - M l)) := by
  rw [coeff_prod]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.prod_congr rfl
  intro l _
  rw [leib_coeff_C_add_X_pow]

/-! ### Step 5: the factorial/binomial bookkeeping -/

/-- `∏_{l=1}^n (x+l) = n! C(x+n, n)`. -/
private theorem leib_key1 (n x : ℕ) :
    ∏ l ∈ Icc 1 n, (((x + l : ℕ) : ℚ)) = ((n.factorial : ℕ) : ℚ) * ((Bn n x : ℕ) : ℚ) := by
  have h : ∏ l ∈ Icc 1 n, (x + l) = n.factorial * Bn n x := by
    rw [← Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, show n + 1 - 1 = n by omega]
    unfold Bn
    rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _
    ring
  exact_mod_cast h

/-- `(l-1)! (n-l)! Y_l(x) (x+l) = n! C(x+n, n)` for `1 ≤ l ≤ n`. -/
private theorem leib_key2 (n l x : ℕ) (hl1 : 1 ≤ l) (hln : l ≤ n) :
    Wl n l * Yl n l x * (x + l) = n.factorial * Bn n x := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = l + 1 + r := ⟨n - (l + 1), by omega⟩
  unfold Wl Yl Bn
  rw [show x + (l + 1) - 1 = x + l by omega, show l + 1 - 1 = l by omega,
    show l + 1 + r - (l + 1) = r by omega, show x + (l + 1 + r) = x + l + 1 + r by ring]
  have e1 : (x + l).choose l * x.factorial * l.factorial = (x + l).factorial :=
    Nat.add_choose_mul_factorial_mul_factorial x l
  have e2 : (x + l + 1 + r).choose r * (x + l + 1).factorial * r.factorial =
      (x + l + 1 + r).factorial :=
    Nat.add_choose_mul_factorial_mul_factorial (x + l + 1) r
  have e3 : (x + (l + 1 + r)).choose (l + 1 + r) * x.factorial * (l + 1 + r).factorial =
      (x + (l + 1 + r)).factorial :=
    Nat.add_choose_mul_factorial_mul_factorial x (l + 1 + r)
  have e4 : (x + l + 1).factorial = (x + l + 1) * (x + l).factorial := Nat.factorial_succ _
  rw [show x + (l + 1 + r) = x + l + 1 + r by ring] at e3
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos x)
  calc x.factorial * (l.factorial * r.factorial *
          ((x + l).choose l * (x + l + 1 + r).choose r) * (x + (l + 1)))
      = (x + l + 1) * ((x + l).choose l * x.factorial * l.factorial) *
          ((x + l + 1 + r).choose r * r.factorial) := by ring
    _ = (x + l + 1 + r).choose r * (x + l + 1).factorial * r.factorial := by rw [e1, e4]; ring
    _ = (x + l + 1 + r).factorial := e2
    _ = x.factorial * ((l + 1 + r).factorial * (x + l + 1 + r).choose (l + 1 + r)) := by
        rw [← e3]; ring

private theorem leib_key2Q (n l x : ℕ) (hl1 : 1 ≤ l) (hln : l ≤ n) :
    ((Wl n l : ℕ) : ℚ) * ((Yl n l x : ℕ) : ℚ) * (((x + l : ℕ) : ℚ)) =
      ((n.factorial : ℕ) : ℚ) * ((Bn n x : ℕ) : ℚ) := by
  exact_mod_cast leib_key2 n l x hl1 hln

/-- `∏_l (x+l)^{8 - M l} = n!^{8-a} C(x+n,n)^{8-a} ∏_l (W_l Y_l)^{M l}` when `∑ M = a ≤ 8`. -/
private theorem leib_prod_M (n x a : ℕ) (ha : a ≤ 8) (M : ℕ →₀ ℕ)
    (hM : ∑ l ∈ Icc 1 n, M l = a) :
    ∏ l ∈ Icc 1 n, (((x + l : ℕ) : ℚ)) ^ (8 - M l) =
      ((n.factorial : ℕ) : ℚ) ^ (8 - a) * ((Bn n x : ℕ) : ℚ) ^ (8 - a) *
        ∏ l ∈ Icc 1 n, (((Wl n l : ℕ) : ℚ) * ((Yl n l x : ℕ) : ℚ)) ^ (M l) := by
  have hMl : ∀ l ∈ Icc 1 n, M l ≤ 8 := by
    intro l hl
    have := Finset.single_le_sum (f := fun l => M l) (fun _ _ => Nat.zero_le _) hl
    omega
  have hQ : ∏ l ∈ Icc 1 n, (((x + l : ℕ) : ℚ)) ^ (M l) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have := (Finset.mem_Icc.1 hl).1
    apply pow_ne_zero
    exact_mod_cast (by omega : x + l ≠ 0)
  apply mul_right_cancel₀ hQ
  rw [← Finset.prod_mul_distrib,
    Finset.prod_congr rfl (fun l hl => by rw [← pow_add, Nat.sub_add_cancel (hMl l hl)]),
    Finset.prod_pow, leib_key1, mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl (fun l hl => by
      rw [← mul_pow, leib_key2Q n l x (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2]),
    Finset.prod_pow_eq_pow_sum, hM, ← mul_pow, ← pow_add, Nat.sub_add_cancel ha]

/-! ### Step 6: assembly -/

/-- One `(γ, β)` block: `∑_M leibTerm = -6 · 2^{24n+8} · [ε^γ](lin) · 2^β h_β · [ε^{3-γ-β}] P^8`. -/
private theorem leib_sum_M (n x γ β : ℕ) (h : γ + β ≤ 3) :
    ∑ M ∈ (Icc 1 n).finsuppAntidiag (3 - γ - β), leibTerm n γ β M x =
      -6 * (2 : ℚ) ^ (24 * n + 8) * (if γ = 0 then ((2 * x + 1 + n : ℕ) : ℚ) else 2) *
        (2 : ℚ) ^ β * hcoef n β x *
          coeff (3 - γ - β) (∏ l ∈ Icc 1 n, (C (((x + l : ℕ) : ℚ)) + X) ^ 8) := by
  rw [leib_coeff_B, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [Finset.mem_finsuppAntidiag] at hM
  unfold leibTerm
  rw [Finset.prod_mul_distrib, leib_prod_M n x (3 - γ - β) (by omega) M hM.1,
    show 8 - (3 - γ - β) = 5 + γ + β by omega]
  ring

theorem Leibniz_proof (hPF : Stmt_PF) : Stmt_Leibniz := by
  intro n x
  rw [Finset.sum_congr rfl (fun γ hγ => Finset.sum_congr rfl (fun β hβ =>
    leib_sum_M n x γ β (by simp only [Finset.mem_range] at hγ hβ; omega)))]
  rw [leib_integrand_eq hPF n x, leib_Rser_prod n x, coeff_C_mul, leib_coeff_lin]
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, Finset.sum_range_succ, Finset.sum_range_zero, coeff_rescale,
    leib_hcoef_eq]
  norm_num
  ring

end Zeta2

end
