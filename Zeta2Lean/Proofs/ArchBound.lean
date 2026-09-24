import Zeta2Lean.Statements

/-!
# L4: archimedean size of the coefficients (proof.md §6)

**Task.** Prove `Stmt_L4`: there are constants `Cst`, `A` with
`|ρ₀|, |Z₇|, |Z₉|, |Z₁₁| ≤ Cst (n+1)^A 2^{16n}` for all `n`.  No hypotheses.  Any constants are
fine (the proof has an exponential margin; proof.md gets `Cst = 3.4·10⁸`, `A = 2` via Cauchy
estimates, but **elementary majorants** are recommended instead).

**Informal proof (majorants).** For `A, B ∈ ℚ⟦X⟧` write `A ≼ B` if `|[X^j] A| ≤ [X^j] B` for all
`j` (then `B` has non-negative coefficients).  If `A ≼ B` and `A' ≼ B'` then `A A' ≼ B B'` and
`A + A' ≼ B + B'`.  Basic majorants, for `c > 0`:
* `C c ± X ≼ C c + X`, and `c + X ≼ c (1 + 2X)` if `c ≥ 1/2`;
* `(C c ± X)⁻¹ ≼ c⁻¹ (1 - X)⁻¹` if `c ≥ 1` (coefficients `c^{-j-1} ≤ c^{-1}`).
Hence `(1/2 ∓ ε)_k ≼ (1/2)_k (1+2X)^k`, `((1 ∓ ε)_k)⁻¹ ≼ (1/k!) (1-X)^{-k}`, and
  `Ψ_k ≼ c_{k} (1+2X)^n (1-X)^{-n}`, `c_k = (1/2)_k (1/2)_{n-k} / (k! (n-k)!) = C(2k,k) C(2n-2k,n-k)/4^n ≤ 1`,
  `Gser n k ≼ 2^{16n} (n + 2X) (1+2X)^{8n} (1-X)^{-8n}`.
For `j ≤ 7`: `[X^j] (1+2X)^{8n} (1-X)^{-8n} = ∑_{a ≤ j} C(8n,a) 2^a C(8n+j-a-1, j-a) ≤ 8 (16n+16)^7`.
So `|r_{i,k}| ≤ 2^{16n} (n+2) · 8 · 16^7 (n+1)^7 ≤ 2^{36} (n+1)^8 2^{16n}`.  Then
`|Z₁₁| = 10321920 |∑_k r_{7,k}| ≤ 2^{24} (n+1) · 2^{36}(n+1)^8 2^{16n}`, similarly `Z₇, Z₉`, and with
`0 ≤ A_k^{(s)} ≤ k 2^s ≤ (n+1) 2^{12}` (`s ≤ 12`, each term `(ℓ+1/2)^{-s} ≤ 2^s`):
`|ρ₀| ≤ 8 · 7920 · (n+1) · 2^{36}(n+1)^8 2^{16n} · (n+1) 2^{12}`.  So `Cst = 2^{70}`, `A = 10` work.
(Only the shape `poly(n) · 2^{16n}` matters.)

**Lean hints.** `PowerSeries.coeff_mul`, `Finset.abs_sum_le_sum_abs`, `abs_mul`,
`Finset.sum_le_sum`, `mul_le_mul`, `PowerSeries.coeff_pow`, `PowerSeries.eq_inv_iff_mul_eq_one`
(identify `(C c + C d X)⁻¹` with `mk (fun j => (-d)^j / c^(j+1))`), `Nat.choose_le_pow`,
`Nat.choose_le_pow_div`, `Nat.cast_le`, `Rat.cast_abs`, `Rat.cast_le`, `pow_le_pow_left₀`,
`archBound` unfolds to `Cst * ((n:ℝ)+1)^A * 2^(16*n)`.  It is easiest to work in `ℚ` and cast to
`ℝ` at the end (`Rat.cast_le`, `abs` commutes with the cast).

**Numerical check.** `python/mirror.py`, section "Stmt_L4": with `C = 3.4e8`, `A = 2` the ratio is
`≤ 0.061` for `n ≤ 40` and `n ∈ {60, 100}`.

**Proof as formalised (weighted `ℓ¹` norm = algebraic Cauchy estimate at radius `1/4`).**
Instead of majorant series we use the functional `l4W f = ∑_{j<8} |[X^j] f| 4^{-j}` on `ℚ⟦X⟧`.
It is submultiplicative (`l4W_mul`, via `coeff_mul` and `Finset.sum_range_diag_flip`), so it is
bounded on products and powers by the product of the factor values.  For the factors:
* `l4W (C c + C d X) = |c| + |d|/4` (`l4W_lin`);
* `(C c + C d X)⁻¹ = mk (fun i => (-d)^i / c^(i+1))` (`inv_lin_eq`), hence
  `l4W ((C c + C d X)⁻¹) · (c - 1/4) ≤ 1 - (4c)^{-8} ≤ 1` for `c ≥ 1`, `|d| ≤ 1` (`l4W_inv_lin`).
Pairing the factor `1/2 + j ∓ ε` of `(1/2 ∓ ε)_k` with `(1 + j ∓ ε)⁻¹` gives
`(j + 3/4) · l4W((1+j ∓ ε)⁻¹) ≤ 1`, so `l4W (Psi n k) ≤ 1` (`l4W_Psi`) and
`l4W (Gser n k) ≤ 2^{16n} (|n-2k| + 1/2) ≤ 2^{16n} (n+1)` (`l4W_Gser`).  Therefore
`|r_{i,k}| ≤ 4^{8-i} (n+1) 2^{16n} ≤ 4^7 (n+1) 2^{16n}` (essentially the Cauchy bound of proof.md §6),
`|c_i| ≤ 4^7 (n+1)^2 2^{16n}`, `0 ≤ A_k^{(s)} ≤ k 2^s`, and
`|ρ₀| ≤ 8 · 7920 · 4^7 · 2^12 (n+1)^3 2^{16n}`.  Constants: `Cst = 2^50`, `A = 3`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-- Weighted truncated `ℓ¹` norm `∑_{j<8} |[X^j] f| 4^{-j}` (an algebraic Cauchy estimate at
radius `1/4`). -/
private def l4W (f : PowerSeries ℚ) : ℚ :=
  ∑ j ∈ range 8, |coeff j f| * (1 / 4 : ℚ) ^ j

private lemma l4W_nonneg (f : PowerSeries ℚ) : 0 ≤ l4W f := by
  unfold l4W
  exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity)

private lemma l4W_coeff_le (f : PowerSeries ℚ) {j : ℕ} (hj : j < 8) :
    |coeff j f| ≤ 4 ^ j * l4W f := by
  have h : |coeff j f| * (1 / 4 : ℚ) ^ j ≤ l4W f := by
    unfold l4W
    exact Finset.single_le_sum (f := fun j => |coeff j f| * (1 / 4 : ℚ) ^ j)
      (fun i _ => mul_nonneg (abs_nonneg _) (by positivity)) (Finset.mem_range.2 hj)
  have h4 : (0 : ℚ) < 4 ^ j := by positivity
  calc |coeff j f| = 4 ^ j * (|coeff j f| * (1 / 4 : ℚ) ^ j) := by
        rw [one_div, inv_pow]; field_simp
    _ ≤ 4 ^ j * l4W f := mul_le_mul_of_nonneg_left h h4.le

private lemma l4W_mul (f g : PowerSeries ℚ) : l4W (f * g) ≤ l4W f * l4W g := by
  let x : ℕ → ℚ := fun a => |coeff a f| * (1 / 4 : ℚ) ^ a
  let y : ℕ → ℚ := fun b => |coeff b g| * (1 / 4 : ℚ) ^ b
  have hx0 : ∀ a, 0 ≤ x a := fun a => mul_nonneg (abs_nonneg _) (by positivity)
  have hy0 : ∀ b, 0 ≤ y b := fun b => mul_nonneg (abs_nonneg _) (by positivity)
  have step1 : ∀ j, |coeff j (f * g)| * (1 / 4 : ℚ) ^ j ≤
      ∑ a ∈ range (j + 1), x a * y (j - a) := by
    intro j
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a f * coeff b g)]
    calc |∑ a ∈ range (j + 1), coeff a f * coeff (j - a) g| * (1 / 4 : ℚ) ^ j
        ≤ (∑ a ∈ range (j + 1), |coeff a f * coeff (j - a) g|) * (1 / 4 : ℚ) ^ j := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ range (j + 1), x a * y (j - a) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          have haj : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
          have hp : (1 / 4 : ℚ) ^ j = (1 / 4 : ℚ) ^ a * (1 / 4 : ℚ) ^ (j - a) := by
            rw [← pow_add, Nat.add_sub_cancel' haj]
          simp only [x, y, abs_mul]
          rw [hp]; ring
  calc l4W (f * g) = ∑ j ∈ range 8, |coeff j (f * g)| * (1 / 4 : ℚ) ^ j := rfl
    _ ≤ ∑ j ∈ range 8, ∑ a ∈ range (j + 1), x a * y (j - a) :=
        Finset.sum_le_sum fun j _ => step1 j
    _ = ∑ a ∈ range 8, ∑ b ∈ range (8 - a), x a * y b :=
        Finset.sum_range_diag_flip 8 (fun a b => x a * y b)
    _ ≤ ∑ a ∈ range 8, ∑ b ∈ range 8, x a * y b := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb; simp only [Finset.mem_range] at hb ⊢; omega
        · intro b _ _; exact mul_nonneg (hx0 a) (hy0 b)
    _ = (∑ a ∈ range 8, x a) * (∑ b ∈ range 8, y b) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = l4W f * l4W g := rfl

private lemma l4W_one : l4W 1 = 1 := by
  unfold l4W
  simp [Finset.sum_range_succ, coeff_one]

private lemma l4W_pow (f : PowerSeries ℚ) (k : ℕ) : l4W (f ^ k) ≤ l4W f ^ k := by
  induction k with
  | zero => simp [l4W_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc l4W (f ^ k * f) ≤ l4W (f ^ k) * l4W f := l4W_mul _ _
      _ ≤ l4W f ^ k * l4W f := mul_le_mul_of_nonneg_right ih (l4W_nonneg f)

private lemma l4W_prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ) :
    l4W (∏ i ∈ s, F i) ≤ ∏ i ∈ s, l4W (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l4W_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    calc l4W (F a * ∏ i ∈ s, F i) ≤ l4W (F a) * l4W (∏ i ∈ s, F i) := l4W_mul _ _
      _ ≤ l4W (F a) * ∏ i ∈ s, l4W (F i) := mul_le_mul_of_nonneg_left ih (l4W_nonneg _)

private lemma l4W_C (c : ℚ) : l4W (C c) = |c| := by
  unfold l4W
  simp [Finset.sum_range_succ, coeff_C]

private lemma l4W_lin (c d : ℚ) : l4W (C c + C d * X) = |c| + |d| / 4 := by
  unfold l4W
  simp [Finset.sum_range_succ, coeff_C, coeff_C_mul, coeff_X]
  ring

private lemma inv_lin_eq (c d : ℚ) (hc : c ≠ 0) :
    (C c + C d * X : PowerSeries ℚ)⁻¹ = mk (fun i => (-d) ^ i / c ^ (i + 1)) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · ext n
    rcases n with _ | n
    · simp [mul_add]
      field_simp
    · rw [mul_add, ← mul_assoc, map_add, coeff_mul_C, coeff_succ_mul_X, coeff_mul_C, coeff_one,
        coeff_mk, coeff_mk]
      rw [ite_eq_right (Nat.add_one_ne_zero n)]
      field_simp
      ring
  · simp [hc]

private lemma l4W_inv_lin (c d : ℚ) (hc : 1 ≤ c) (hd : |d| ≤ 1) :
    l4W ((C c + C d * X)⁻¹) * (c - 1 / 4) ≤ 1 := by
  have hc0 : (0 : ℚ) < c := by linarith
  rw [inv_lin_eq c d hc0.ne']
  unfold l4W
  simp only [coeff_mk]
  have key : ∀ i ∈ range 8, |(-d) ^ i / c ^ (i + 1)| * (1 / 4 : ℚ) ^ i ≤
      (1 / (4 * c)) ^ i / c := by
    intro i _
    rw [abs_div, abs_pow, abs_neg, abs_of_pos (pow_pos hc0 _)]
    have h1 : |d| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg d) hd
    have h2 : |d| ^ i / c ^ (i + 1) * (1 / 4 : ℚ) ^ i = |d| ^ i * ((1 / (4 * c)) ^ i / c) := by
      ring
    rw [h2]
    calc |d| ^ i * ((1 / (4 * c)) ^ i / c) ≤ 1 * ((1 / (4 * c)) ^ i / c) := by gcongr
      _ = (1 / (4 * c)) ^ i / c := one_mul _
  set q : ℚ := 1 / (4 * c) with hq
  calc (∑ i ∈ range 8, |(-d) ^ i / c ^ (i + 1)| * (1 / 4 : ℚ) ^ i) * (c - 1 / 4)
      ≤ (∑ i ∈ range 8, q ^ i / c) * (c - 1 / 4) := by
        apply mul_le_mul_of_nonneg_right (Finset.sum_le_sum key); linarith
    _ = (∑ i ∈ range 8, q ^ i) * (1 - q) := by
        rw [← Finset.sum_div, hq]; field_simp
    _ = 1 - q ^ 8 := geom_sum_mul_neg _ _
    _ ≤ 1 := by
        have : 0 ≤ q ^ 8 := by positivity
        linarith

private lemma inv_prod_range (F : ℕ → PowerSeries ℚ) (k : ℕ) :
    (∏ j ∈ range k, F j)⁻¹ = ∏ j ∈ range k, (F j)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, PowerSeries.mul_inv_rev, ih, mul_comm]

private lemma l4W_pair (k : ℕ) (d : ℚ) (hd : |d| = 1) :
    l4W (psPoch (1 / 2) d k) * l4W ((psPoch 1 d k)⁻¹) ≤ 1 := by
  unfold psPoch
  rw [inv_prod_range]
  calc l4W (∏ j ∈ range k, (C (1 / 2 + (j : ℚ)) + C d * X)) *
        l4W (∏ j ∈ range k, (C (1 + (j : ℚ)) + C d * X)⁻¹)
      ≤ (∏ j ∈ range k, l4W (C (1 / 2 + (j : ℚ)) + C d * X)) *
          (∏ j ∈ range k, l4W ((C (1 + (j : ℚ)) + C d * X)⁻¹)) :=
        mul_le_mul (l4W_prod _ _) (l4W_prod _ _) (l4W_nonneg _)
          (Finset.prod_nonneg fun _ _ => l4W_nonneg _)
    _ = ∏ j ∈ range k, (l4W (C (1 / 2 + (j : ℚ)) + C d * X) *
          l4W ((C (1 + (j : ℚ)) + C d * X)⁻¹)) := (Finset.prod_mul_distrib).symm
    _ ≤ ∏ j ∈ range k, (1 : ℚ) := by
        apply Finset.prod_le_prod₀
        · intro j _; exact mul_nonneg (l4W_nonneg _) (l4W_nonneg _)
        · intro j _
          have hj : (0 : ℚ) ≤ j := j.cast_nonneg
          rw [l4W_lin, hd]
          have h1 : |(1 / 2 : ℚ) + j| = (1 + j) - 1 / 2 := by
            rw [abs_of_pos (by positivity)]; ring
          rw [h1]
          have := l4W_inv_lin (1 + j) d (by linarith) hd.le
          calc ((1 + (j : ℚ)) - 1 / 2 + 1 / 4) * l4W ((C (1 + (j : ℚ)) + C d * X)⁻¹)
              = l4W ((C (1 + (j : ℚ)) + C d * X)⁻¹) * ((1 + j) - 1 / 4) := by ring
            _ ≤ 1 := this
    _ = 1 := Finset.prod_const_one

private lemma l4W_Psi (n k : ℕ) : l4W (Psi n k) ≤ 1 := by
  unfold Psi
  rw [PowerSeries.mul_inv_rev]
  have hA := l4W_pair k (-1) (by norm_num)
  have hB := l4W_pair (n - k) 1 (by norm_num)
  set A := psPoch (1 / 2) (-1) k
  set B := psPoch (1 / 2) 1 (n - k)
  set D := psPoch 1 (-1) k
  set E := psPoch 1 1 (n - k)
  calc l4W (A * B * (E⁻¹ * D⁻¹)) ≤ l4W (A * B) * l4W (E⁻¹ * D⁻¹) := l4W_mul _ _
    _ ≤ (l4W A * l4W B) * (l4W E⁻¹ * l4W D⁻¹) :=
        mul_le_mul (l4W_mul _ _) (l4W_mul _ _) (l4W_nonneg _)
          (mul_nonneg (l4W_nonneg _) (l4W_nonneg _))
    _ = (l4W A * l4W D⁻¹) * (l4W B * l4W E⁻¹) := by ring
    _ ≤ 1 * 1 := mul_le_mul hA hB (mul_nonneg (l4W_nonneg _) (l4W_nonneg _)) zero_le_one
    _ = 1 := one_mul 1

private lemma l4W_Gser (n k : ℕ) (hk : k ≤ n) :
    l4W (Gser n k) ≤ 2 ^ (16 * n) * ((n : ℚ) + 1) := by
  unfold Gser
  have hP : l4W (Psi n k ^ 8) ≤ 1 :=
    (l4W_pow _ _).trans (pow_le_one₀ (l4W_nonneg _) (l4W_Psi n k))
  have hnk : |(n : ℚ) - 2 * k| ≤ n := by
    have : (k : ℚ) ≤ n := by exact_mod_cast hk
    have : (0 : ℚ) ≤ k := k.cast_nonneg
    rw [abs_le]; constructor <;> linarith
  calc l4W (C ((2 : ℚ) ^ (16 * n)) * (C ((n : ℚ) - 2 * k) + C 2 * X) * Psi n k ^ 8)
      ≤ l4W (C ((2 : ℚ) ^ (16 * n)) * (C ((n : ℚ) - 2 * k) + C 2 * X)) * l4W (Psi n k ^ 8) :=
        l4W_mul _ _
    _ ≤ (l4W (C ((2 : ℚ) ^ (16 * n))) * l4W (C ((n : ℚ) - 2 * k) + C 2 * X)) * 1 :=
        mul_le_mul (l4W_mul _ _) hP (l4W_nonneg _)
          (mul_nonneg (l4W_nonneg _) (l4W_nonneg _))
    _ = 2 ^ (16 * n) * (|(n : ℚ) - 2 * k| + 1 / 2) := by
        rw [l4W_C, l4W_lin, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ (16 * n))]
        norm_num
    _ ≤ 2 ^ (16 * n) * ((n : ℚ) + 1) := by
        gcongr; linarith

private lemma abs_rcoef_le (n i k : ℕ) :
    |rcoef n i k| ≤ 4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) := by
  unfold rcoef
  split_ifs with h
  · obtain ⟨h1, h8, hk⟩ := h
    calc |coeff (8 - i) (Gser n k)| ≤ 4 ^ (8 - i) * l4W (Gser n k) := l4W_coeff_le _ (by omega)
      _ ≤ 4 ^ 7 * (2 ^ (16 * n) * ((n : ℚ) + 1)) :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) (l4W_Gser n k hk)
            (l4W_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [abs_zero]; positivity

private lemma abs_csum_le (n i : ℕ) :
    |csum n i| ≤ 4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 2 := by
  unfold csum
  calc |∑ k ∈ range (n + 1), rcoef n i k| ≤ ∑ k ∈ range (n + 1), |rcoef n i k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), 4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) :=
        Finset.sum_le_sum fun k _ => abs_rcoef_le n i k
    _ = 4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

private lemma abs_Ahalf_le (k s : ℕ) : |Ahalf k s| ≤ k * 2 ^ s := by
  unfold Ahalf
  calc |∑ l ∈ range k, (((l : ℚ) + 1 / 2)⁻¹) ^ s| ≤ ∑ l ∈ range k, |(((l : ℚ) + 1 / 2)⁻¹) ^ s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ range k, (2 : ℚ) ^ s := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_pow]
        apply pow_le_pow_left₀ (abs_nonneg _)
        have hl : (0 : ℚ) ≤ l := l.cast_nonneg
        rw [abs_of_pos (by positivity), inv_le_comm₀ (by positivity) (by norm_num)]
        linarith
    _ = k * 2 ^ s := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private lemma abs_rho0_le (n : ℕ) :
    |rho0 n| ≤ 8 * 7920 * 4 ^ 7 * 2 ^ 12 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3 := by
  unfold rho0
  rw [abs_neg]
  calc |∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
          ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * Ahalf k (i + 4)|
      ≤ ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
          |((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * Ahalf k (i + 4)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
          (7920 : ℚ) * (4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1)) * (((n : ℚ) + 1) * 2 ^ 12) := by
        apply Finset.sum_le_sum; intro i hi
        apply Finset.sum_le_sum; intro k hk
        rw [abs_mul, abs_mul]
        have hi' := Finset.mem_Icc.1 hi
        have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        have h1 : |(i : ℚ) * (i + 1) * (i + 2) * (i + 3)| ≤ 7920 := by
          obtain ⟨hi1, hi8⟩ := hi'
          interval_cases i <;> norm_num
        have h2 := abs_rcoef_le n i k
        have h3 : |Ahalf k (i + 4)| ≤ ((n : ℚ) + 1) * 2 ^ 12 := by
          calc |Ahalf k (i + 4)| ≤ k * 2 ^ (i + 4) := abs_Ahalf_le k (i + 4)
            _ ≤ ((n : ℚ) + 1) * 2 ^ 12 := by
              have hkn : (k : ℚ) ≤ n + 1 := by
                have : (k : ℚ) ≤ n := by exact_mod_cast hk'
                linarith
              gcongr
              · norm_num
              · omega
        exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
          (by positivity)
    _ = 8 * 7920 * 4 ^ 7 * 2 ^ 12 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

theorem L4_proof : Stmt_L4 := by
  refine ⟨2 ^ 50, 3, fun n => ?_⟩
  have hn1 : (1 : ℚ) ≤ (n : ℚ) + 1 := by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  have hpow : ((n : ℚ) + 1) ^ 2 ≤ ((n : ℚ) + 1) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hZ : ∀ (c : ℚ) (i : ℕ), 0 ≤ c → c ≤ 10321920 →
      |c * csum n i| ≤ 2 ^ 50 * ((n : ℚ) + 1) ^ 3 * 2 ^ (16 * n) := by
    intro c i hc0 hc
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |csum n i| ≤ 10321920 * (4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 2) :=
          mul_le_mul hc (abs_csum_le n i) (abs_nonneg _) (by norm_num)
      _ ≤ 10321920 * (4 ^ 7 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3) := by gcongr
      _ ≤ 2 ^ 50 * ((n : ℚ) + 1) ^ 3 * 2 ^ (16 * n) := by
          have : (0 : ℚ) ≤ 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3 := by positivity
          nlinarith
  have hR : |rho0 n| ≤ 2 ^ 50 * ((n : ℚ) + 1) ^ 3 * 2 ^ (16 * n) := by
    calc |rho0 n| ≤ 8 * 7920 * 4 ^ 7 * 2 ^ 12 * 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3 := abs_rho0_le n
      _ ≤ 2 ^ 50 * ((n : ℚ) + 1) ^ 3 * 2 ^ (16 * n) := by
          have : (0 : ℚ) ≤ 2 ^ (16 * n) * ((n : ℚ) + 1) ^ 3 := by positivity
          nlinarith
  have h7 := hZ 46080 3 (by norm_num) (by norm_num)
  have h9 := hZ 860160 5 (by norm_num) (by norm_num)
  have h11 := hZ 10321920 7 (by norm_num) (by norm_num)
  unfold archBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hR
  · unfold Z7; exact_mod_cast h7
  · unfold Z9; exact_mod_cast h9
  · unfold Z11; exact_mod_cast h11

end Zeta2

end
