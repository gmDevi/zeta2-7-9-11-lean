import Zeta2Lean.Statements

/-!
# Andrews' transformation applied to `T_{n,ℓ}` (proof.md §4.3 Steps 2–3; LSZ Lemma 5.3)

**Task.** Prove `Stmt_AndrewsApplied` from the cited `Andrews_Stmt`:
for `1 ≤ ℓ ≤ n`, `Tser n ℓ = ∑_{J ∈ chains 8 (n-ℓ)} Fser n ℓ J` in `PowerSeries ℚ`.

**Informal proof.** Put `N := n - ℓ`, `k = ℓ + κ` (`0 ≤ κ ≤ N`), and (in a field containing
`ℚ⟦ε⟧`, see below) `a := -n + 2ℓ - 2ε`, `b := -N - ε`, `c := ℓ + 1/2 - ε`, so
`1+a-b = ℓ+1-ε`, `1+a-c = 1/2-N-ε`, `1+a-b-c = 1/2`, `1+a+N = ℓ+1-2ε`, `a+N = ℓ-2ε`,
`n-2k+2ε = -(a+2κ)`.
*Step 2 (VWP form).* Using `(x)_{N-κ} = (-1)^κ (x)_N / (1-x-N)_κ` for `x = 1/2+ε` and `x = 1+ε`, and
`(1-ε)_{ℓ+κ} = (1-ε)_ℓ (ℓ+1-ε)_κ`, `(ℓ+1/2-ε)_{k-ℓ} = (c)_κ`:
  `T_{n,ℓ} = -a · P_ℓ · ∑_{κ=0}^{N} (a+2κ)/a · [(b)_κ (c)_κ / ((1+a-b)_κ (1+a-c)_κ)]^8`
(`P_ℓ = Pser n ℓ`).
*Step 3 (Andrews).* Apply `Andrews_Stmt` with `m = 8`, `(b_k, c_k) = (b, c)` for `k < 8` and
`(b_8, c_8) = (1, 1 + a + N)` (this is the `δ = 0` value of proof.md's `c₉ = ℓ+1-2ε-δ`; at `δ = 0`
all denominators are non-zero, so no limit is needed).  Left side, term `κ ≤ N`: the pair
`(1, 1+a+N)` contributes `κ! (1+a+N)_κ / ((a)_κ (-N)_κ)`, which cancels `(a)_κ/κ!` and
`(-N)_κ/(1+a+N)_κ`, leaving `(a+2κ)/a · [...]^8`.  Right side: the prefactor is
`(1+a)_N (-1-N)_N / ((a)_N (-N)_N) = (N+1)(a+N)/a`; `b_8 + c_8 - a - N = 2`, `(2)_J = (J+1)!`;
the `k = 8` factor is `(1/2)_{d_8}/d_8! · J_8! (ℓ+1-2ε)_{J_8} / ((ℓ+1-ε)_{J_8} (1/2-N-ε)_{J_8})`.
Multiplying by `-a P_ℓ` gives exactly `∑_J F_J` (see the docstring of `Fser`).
Hypotheses of `Andrews_Stmt`: `a ≠ 0`, `(ℓ+1-ε)_N ≠ 0`, `(1/2-N-ε)_N ≠ 0`, `(a)_N ≠ 0`,
`(-N)_N = (-1)^N N! ≠ 0`, `(ℓ+1-2ε)_N ≠ 0`, `(2)_N ≠ 0` — each factor has non-zero `ε`-coefficient
or is a non-zero rational.

## Formal proof (complete)

Everything happens in `K := FractionRing ℚ⟦X⟧` (`AndrewsAppliedAux.KK`), a field of characteristic
zero (the `CharZero` instance is supplied locally, it is not found by instance search), through the
injective ring hom `φ = algebraMap ℚ⟦X⟧ K` (`phiA`), with `ε ↦ e := φ X` (`epsA`).  Linear
elements are written `LA c d := c + d·e` (`c d : ℚ`); `LA c d ≠ 0` for `d ≠ 0` by injectivity.

1. *Transfer* (`phiA_psPoch`, `phiA_inv_*`, `phiA_Pser`, `phiA_Tser`, `phiA_Fser`):
   `φ (psPoch c d k) = rpoch (LA c d) k`, and `φ (u⁻¹) = (φ u)⁻¹` whenever `constantCoeff u ≠ 0`
   (the constant coefficients are `k!`, `(ℓ+1)_k > 0` and `(1/2-N)_k ≠ 0`).
2. *Step 2* (`stepA`): `φ T = -a · φ P · ∑_κ (a+2κ)/a · Q_κ^8`, by reindexing `k = ℓ + κ`, the
   reflection formula `rpoch_reflect` and `rpoch_add'`, and field algebra (`stepA_alg`).
3. *Andrews left side* (`stepB`): `∑_κ (a+2κ)/a · Q_κ^8 = andrewsLHS …` (`Fin.prod_univ_castSucc`,
   the last pair cancels, `stepB_alg`).
4. `andrews_apply` is `Andrews_Stmt` at `K`, `m = 8`, `a`, `b = bA N`, `c = cA N ℓ` (hypotheses:
   `andrews_hyps`).
5. *Andrews right side* (`stepC`): prefactor `(N+1)(a+N)/a` (`prefactor_eq`), then chain by chain
   `-a · φ P · (…) = φ (Fser n ℓ J)` (`prod_split8`, `prodA_eq`, `prodB_eq`, `stepC_alg`).
6. Pull back along the injective `φ`.

The hypothesis `1 ≤ ℓ` is not needed.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

namespace AndrewsAppliedAux

/-- The ambient field `K = Frac(ℚ⟦X⟧)`. -/
private abbrev KK := FractionRing (PowerSeries ℚ)

/-- `CharZero K` is not found by instance search; supply it locally. -/
private theorem charZero_KK : CharZero KK :=
  charZero_of_injective_algebraMap (algebraMap ℚ KK).injective

attribute [local instance] charZero_KK

/-- The embedding `φ : ℚ⟦X⟧ → K`. -/
private abbrev phiA : PowerSeries ℚ →+* KK := algebraMap (PowerSeries ℚ) KK

/-- `ε` in `K`. -/
private def epsA : KK := phiA X

/-- The linear element `c + d ε` of `K`. -/
private def LA (c d : ℚ) : KK := (c : KK) + (d : KK) * epsA

/-! ### Transfer from `ℚ⟦X⟧` to `K` -/

private lemma phiA_injective : Function.Injective phiA :=
  IsFractionRing.injective (PowerSeries ℚ) KK

private lemma phiA_C (q : ℚ) : phiA (C q) = (q : KK) := eq_ratCast (phiA.comp C) q

private lemma phiA_inv (u : PowerSeries ℚ) (h : constantCoeff u ≠ 0) :
    phiA u⁻¹ = (phiA u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, PowerSeries.inv_mul_cancel _ h, map_one])

private lemma phiA_psPoch (c d : ℚ) (k : ℕ) : phiA (psPoch c d k) = rpoch (LA c d) k := by
  unfold psPoch rpoch LA epsA
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [map_add, map_mul, phiA_C, phiA_C]
  push_cast
  ring

private lemma constantCoeff_psPoch (c d : ℚ) (k : ℕ) :
    constantCoeff (psPoch c d k) = rpoch c k := by
  unfold psPoch rpoch
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp

private lemma LA_ne_zero (c d : ℚ) (hd : d ≠ 0) : LA c d ≠ 0 := by
  have h : LA c d = phiA (C c + C d * X) := by
    simp only [LA, epsA, map_add, map_mul, phiA_C]
  rw [h]
  intro h0
  have h2 : C c + C d * X = (0 : PowerSeries ℚ) := phiA_injective (by rw [h0, map_zero])
  have h1 : d = 0 := by simpa using congrArg (coeff 1) h2
  exact hd h1

private lemma LA_add_nat (c d : ℚ) (j : ℕ) : LA c d + j = LA (c + j) d := by
  unfold LA; push_cast; ring

private lemma rpoch_LA_ne_zero (c d : ℚ) (hd : d ≠ 0) (k : ℕ) : rpoch (LA c d) k ≠ 0 := by
  unfold rpoch
  rw [Finset.prod_ne_zero_iff]
  intro j _
  rw [LA_add_nat]
  exact LA_ne_zero _ _ hd

/-! ### Pochhammer algebra (any commutative ring) -/

private lemma rpoch_zero' {R : Type*} [CommRing R] (x : R) : rpoch x 0 = 1 := by simp [rpoch]

private lemma rpoch_succ' {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    rpoch x (k + 1) = rpoch x k * (x + k) := by
  simp [rpoch, Finset.prod_range_succ]

private lemma rpoch_add' {R : Type*} [CommRing R] (x : R) (a b : ℕ) :
    rpoch x (a + b) = rpoch x a * rpoch (x + a) b := by
  unfold rpoch
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  push_cast
  ring

/-- Reflection: `(x)_{N-κ} (1-x-N)_κ = (-1)^κ (x)_N` for `κ ≤ N`. -/
private lemma rpoch_reflect {R : Type*} [CommRing R] (x : R) (N κ : ℕ) (h : κ ≤ N) :
    rpoch x (N - κ) * rpoch (1 - x - N) κ = (-1) ^ κ * rpoch x N := by
  induction κ with
  | zero => simp [rpoch_zero']
  | succ κ ih =>
    have h' : κ ≤ N := by omega
    have hN : N - κ = (N - (κ + 1)) + 1 := by omega
    have e1 : rpoch x (N - κ) = rpoch x (N - (κ + 1)) * (x + ((N - (κ + 1) : ℕ) : R)) := by
      rw [hN, rpoch_succ']
    have e2 : ((N - (κ + 1) : ℕ) : R) = (N : R) - κ - 1 := by
      rw [Nat.cast_sub (by omega : κ + 1 ≤ N)]
      push_cast
      ring
    rw [rpoch_succ', pow_succ,
      show (-1 : R) ^ κ * -1 * rpoch x N = -((-1) ^ κ * rpoch x N) by ring, ← ih h', e1, e2]
    ring

private lemma rpoch_one_eq {R : Type*} [CommRing R] (k : ℕ) :
    rpoch (1 : R) k = (k.factorial : R) := by
  induction k with
  | zero => simp [rpoch]
  | succ k ih =>
    rw [rpoch_succ', ih, Nat.factorial_succ]
    push_cast
    ring

private lemma rpoch_two_eq {R : Type*} [CommRing R] (k : ℕ) :
    rpoch (2 : R) k = ((k + 1).factorial : R) := by
  induction k with
  | zero => simp [rpoch]
  | succ k ih =>
    rw [rpoch_succ', ih, Nat.factorial_succ (k + 1)]
    push_cast
    ring

private lemma neg_one_pow_mul_self' {R : Type*} [CommRing R] (N : ℕ) :
    ((-1 : R) ^ N) * ((-1) ^ N) = 1 := by
  rw [← mul_pow]; simp

private lemma rpoch_negN {R : Type*} [CommRing R] (N : ℕ) :
    rpoch (-(N : R)) N = (-1) ^ N * (N.factorial : R) := by
  have h := rpoch_reflect (-(N : R)) N N le_rfl
  rw [Nat.sub_self, rpoch_zero', one_mul, show (1 : R) - -(N : R) - N = 1 by ring,
    rpoch_one_eq] at h
  rw [h, ← mul_assoc, neg_one_pow_mul_self', one_mul]

private lemma rpoch_negN1 {R : Type*} [CommRing R] (N : ℕ) :
    rpoch (-1 - (N : R)) N = (-1) ^ N * ((N + 1).factorial : R) := by
  have h := rpoch_reflect (-1 - (N : R)) N N le_rfl
  rw [Nat.sub_self, rpoch_zero', one_mul, show (1 : R) - (-1 - (N : R)) - N = 2 by ring,
    rpoch_two_eq] at h
  rw [h, ← mul_assoc, neg_one_pow_mul_self', one_mul]

/-- `(1+a)_N · a = (a)_N · (a+N)` (both are `(a)_{N+1}`). -/
private lemma rpoch_shift_ratio {R : Type*} [CommRing R] (a : R) (N : ℕ) :
    rpoch (1 + a) N * a = rpoch a N * (a + N) := by
  have h1 := rpoch_add' a 1 N
  have h2 := rpoch_succ' a N
  rw [add_comm 1 N] at h1
  rw [h2] at h1
  rw [h1]
  simp [rpoch, add_comm]
  ring

private lemma rpoch_ne_zero_of_le {R : Type*} [CommRing R] (x : R) {N κ : ℕ}
    (h : rpoch x N ≠ 0) (hk : κ ≤ N) : rpoch x κ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [rpoch_add', h0, zero_mul]

private lemma ratCast_rpoch (q : ℚ) (k : ℕ) : ((rpoch q k : ℚ) : KK) = rpoch (q : KK) k := by
  unfold rpoch
  push_cast
  rfl

private lemma rpoch_negN_ne_zero (N κ : ℕ) (h : κ ≤ N) : rpoch (-(N : KK)) κ ≠ 0 := by
  refine rpoch_ne_zero_of_le _ ?_ h
  rw [rpoch_negN]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))

/-! ### Inverses of power series with non-zero constant term -/

private lemma rpoch_rat_pos (c : ℚ) (hc : 0 < c) (k : ℕ) : 0 < rpoch c k := by
  unfold rpoch
  apply Finset.prod_pos
  intro j _
  positivity

private lemma rpoch_half_ne_zero (N k : ℕ) : rpoch ((1 : ℚ) / 2 - (N : ℚ)) k ≠ 0 := by
  unfold rpoch
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have h2 : (1 : ℚ) = 2 * ((N : ℚ) - j) := by linarith
  have h3 : (1 : ℤ) = 2 * ((N : ℤ) - j) := by exact_mod_cast h2
  omega

private lemma phiA_inv_11 (a b : ℕ) :
    phiA ((psPoch 1 (-1) a ^ 8 * psPoch 1 1 b ^ 8)⁻¹) =
      (rpoch (LA 1 (-1)) a ^ 8 * rpoch (LA 1 1) b ^ 8)⁻¹ := by
  rw [phiA_inv, map_mul, map_pow, map_pow, phiA_psPoch, phiA_psPoch]
  rw [map_mul, map_pow, map_pow, constantCoeff_psPoch, constantCoeff_psPoch]
  exact mul_ne_zero (pow_ne_zero _ (rpoch_rat_pos 1 one_pos a).ne')
    (pow_ne_zero _ (rpoch_rat_pos 1 one_pos b).ne')

private lemma phiA_inv_x1x2 (l N k : ℕ) :
    phiA ((psPoch ((l : ℚ) + 1) (-1) k * psPoch (1 / 2 - (N : ℚ)) (-1) k)⁻¹) =
      (rpoch (LA ((l : ℚ) + 1) (-1)) k * rpoch (LA (1 / 2 - (N : ℚ)) (-1)) k)⁻¹ := by
  rw [phiA_inv, map_mul, phiA_psPoch, phiA_psPoch]
  rw [map_mul, constantCoeff_psPoch, constantCoeff_psPoch]
  exact mul_ne_zero (rpoch_rat_pos _ (by positivity) k).ne' (rpoch_half_ne_zero N k)

private lemma phiA_inv_last (l N k : ℕ) :
    phiA ((C ((k : ℚ) + 1) * psPoch ((l : ℚ) + 1) (-1) k *
        psPoch (1 / 2 - (N : ℚ)) (-1) k)⁻¹) =
      ((((k : ℚ) + 1 : ℚ) : KK) * rpoch (LA ((l : ℚ) + 1) (-1)) k *
        rpoch (LA (1 / 2 - (N : ℚ)) (-1)) k)⁻¹ := by
  rw [phiA_inv, map_mul, map_mul, phiA_C, phiA_psPoch, phiA_psPoch]
  rw [map_mul, map_mul, constantCoeff_C, constantCoeff_psPoch, constantCoeff_psPoch]
  exact mul_ne_zero (mul_ne_zero (by positivity) (rpoch_rat_pos _ (by positivity) k).ne')
    (rpoch_half_ne_zero N k)

/-! ### `Pser`, `Tser`, `Fser` in `K` -/

/-- The common prefix `2^{16n} (ℓ-1/2-ε)^3 (1/2-ε)_{ℓ-1}^8` of `Tser` and `Pser`, in `K`. -/
private def preA (n l : ℕ) : KK :=
  phiA (C ((2 : ℚ) ^ (16 * n)) * (C ((l : ℚ) - 1 / 2) - X) ^ 3 * psPoch (1 / 2) (-1) (l - 1) ^ 8)

private lemma phiA_Pser (N l : ℕ) :
    phiA (Pser (l + N) l) = preA (l + N) l * rpoch (LA (1 / 2) 1) N ^ 8 *
      (rpoch (LA 1 (-1)) l ^ 8 * rpoch (LA 1 1) N ^ 8)⁻¹ := by
  unfold Pser preA
  rw [Nat.add_sub_cancel_left, map_mul phiA, map_mul phiA, map_pow phiA, phiA_psPoch,
    phiA_inv_11]

private lemma phiA_Tser (N l : ℕ) :
    phiA (Tser (l + N) l) = preA (l + N) l * ∑ k ∈ Icc l (l + N),
      LA (((l + N : ℕ) : ℚ) - 2 * k) 2 * rpoch (LA ((l : ℚ) + 1 / 2) (-1)) (k - l) ^ 8 *
        rpoch (LA (1 / 2) 1) (l + N - k) ^ 8 *
        (rpoch (LA 1 (-1)) k ^ 8 * rpoch (LA 1 1) (l + N - k) ^ 8)⁻¹ := by
  unfold Tser preA
  rw [map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul phiA, map_mul phiA, map_mul phiA, map_pow phiA, map_pow phiA, phiA_psPoch,
    phiA_psPoch, phiA_inv_11, map_add phiA, map_mul phiA, phiA_C, phiA_C]
  rfl

private lemma phiA_Fser (N l : ℕ) (ch : Fin 8 → ℕ) :
    phiA (Fser (l + N) l ch) =
      ((-(N : ℚ) - 1 : ℚ) : KK) * (((l : ℚ) : KK) - ((2 : ℚ) : KK) * epsA) *
        phiA (Pser (l + N) l) *
      (∏ i : Fin 8, ((rpoch (1 / 2 : ℚ) (ch i - chainPrev ch i) /
        ((ch i - chainPrev ch i).factorial : ℚ) : ℚ) : KK)) *
      (∏ i : Fin 7, rpoch (LA (-(N : ℚ)) (-1)) (ch i.castSucc) *
        rpoch (LA ((l : ℚ) + 1 / 2) (-1)) (ch i.castSucc) *
        (rpoch (LA ((l : ℚ) + 1) (-1)) (ch i.castSucc) *
          rpoch (LA (1 / 2 - (N : ℚ)) (-1)) (ch i.castSucc))⁻¹) *
      (rpoch (LA ((l : ℚ) + 1) (-2)) (ch 7) * ((rpoch (-(N : ℚ)) (ch 7) : ℚ) : KK) *
        ((((ch 7 : ℚ) + 1 : ℚ) : KK) * rpoch (LA ((l : ℚ) + 1) (-1)) (ch 7) *
          rpoch (LA (1 / 2 - (N : ℚ)) (-1)) (ch 7))⁻¹) := by
  unfold Fser
  rw [Nat.add_sub_cancel_left]
  simp only [map_mul phiA, map_prod phiA, map_sub phiA, phiA_C, phiA_psPoch, phiA_inv_x1x2,
    phiA_inv_last]
  rfl

/-! ### Step 2: `T_{n,ℓ}` in very-well-poised form -/

private lemma stepA_alg {K : Type*} [Field K] (pre a t s u U v w W z P0 y sg : K)
    (hU : u * v = sg * U) (hW : w * z = sg * W)
    (ha : a ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0) (hP0 : P0 ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hsg : sg ≠ 0) :
    pre * (-(a + t) * s ^ 8 * u ^ 8 * ((P0 * y) ^ 8 * w ^ 8)⁻¹) =
      -a * (pre * U ^ 8 * (P0 ^ 8 * W ^ 8)⁻¹) * ((a + t) / a * (z * s / (y * v)) ^ 8) := by
  have hU' : U = u * v / sg := by rw [eq_div_iff hsg, hU]; ring
  have hW' : W = w * z / sg := by rw [eq_div_iff hsg, hW]; ring
  subst hU' hW'
  field_simp

/-- proof.md §4.3 Step 2: `T = -a P ∑_κ (a+2κ)/a [(b)_κ (c)_κ / ((1+a-b)_κ (1+a-c)_κ)]^8`. -/
private lemma stepA (N l : ℕ) :
    phiA (Tser (l + N) l) = -LA ((l : ℚ) - N) (-2) * phiA (Pser (l + N) l) *
      ∑ κ ∈ range (N + 1), (LA ((l : ℚ) - N) (-2) + 2 * κ) / LA ((l : ℚ) - N) (-2) *
        (rpoch (LA (-(N : ℚ)) (-1)) κ * rpoch (LA ((l : ℚ) + 1 / 2) (-1)) κ /
          (rpoch (LA ((l : ℚ) + 1) (-1)) κ * rpoch (LA (1 / 2 - (N : ℚ)) (-1)) κ)) ^ 8 := by
  rw [phiA_Tser, phiA_Pser]
  have hre : ∀ f : ℕ → KK, ∑ k ∈ Icc l (l + N), f k = ∑ κ ∈ range (N + 1), f (l + κ) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    congr 2
    omega
  rw [hre, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun κ hκ => ?_)
  have hκ' : κ ≤ N := by simp at hκ; omega
  rw [Nat.add_sub_cancel_left, Nat.add_sub_add_left, rpoch_add' (LA 1 (-1)) l κ]
  have hU := rpoch_reflect (LA (1 / 2) 1) N κ hκ'
  have hW := rpoch_reflect (LA 1 1) N κ hκ'
  rw [show 1 - LA (1 / 2) 1 - N = LA (1 / 2 - (N : ℚ)) (-1) by unfold LA; push_cast; ring] at hU
  rw [show 1 - LA 1 1 - N = LA (-(N : ℚ)) (-1) by unfold LA; push_cast; ring] at hW
  rw [show LA 1 (-1) + (l : KK) = LA ((l : ℚ) + 1) (-1) by unfold LA; push_cast; ring]
  rw [show LA (((l + N : ℕ) : ℚ) - 2 * ((l + κ : ℕ) : ℚ)) 2 = -(LA ((l : ℚ) - N) (-2) + 2 * κ) by
    unfold LA; push_cast; ring]
  exact stepA_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hU hW (LA_ne_zero _ _ (by norm_num))
    (rpoch_LA_ne_zero _ _ (by norm_num) _) (rpoch_LA_ne_zero _ _ (by norm_num) _)
    (rpoch_LA_ne_zero _ _ (by norm_num) _) (rpoch_LA_ne_zero _ _ (by norm_num) _)
    (rpoch_LA_ne_zero _ _ (by norm_num) _) (pow_ne_zero _ (by norm_num))

/-! ### Step 3: the two sides of `Andrews_Stmt` -/

/-- The left side of `Andrews_Stmt`. -/
private def andrewsLHS (K : Type) [Field K] (m N : ℕ) (a : K) (b c : Fin (m + 1) → K) : K :=
  ∑ κ ∈ range (N + 1),
    (a + 2 * κ) / a * (rpoch a κ / (κ.factorial : K)) *
    (∏ k, rpoch (b k) κ * rpoch (c k) κ / (rpoch (1 + a - b k) κ * rpoch (1 + a - c k) κ)) *
    (rpoch (-(N : K)) κ / rpoch (1 + a + N) κ)

/-- The right side of `Andrews_Stmt`. -/
private def andrewsRHS (K : Type) [Field K] (m N : ℕ) (a : K) (b c : Fin (m + 1) → K) : K :=
  rpoch (1 + a) N * rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) N /
      (rpoch (1 + a - b (Fin.last m)) N * rpoch (1 + a - c (Fin.last m)) N) *
    ∑ i ∈ chains m N,
      rpoch (-(N : K)) (chainLast i) /
          rpoch (b (Fin.last m) + c (Fin.last m) - a - N) (chainLast i) *
        ∏ k : Fin m,
          rpoch (1 + a - b k.castSucc - c k.castSucc) (i k - chainPrev i k) *
              rpoch (b k.succ) (i k) * rpoch (c k.succ) (i k) /
            (((i k - chainPrev i k).factorial : K) * rpoch (1 + a - b k.castSucc) (i k) *
              rpoch (1 + a - c k.castSucc) (i k))

private lemma andrews_apply (hA : Andrews_Stmt) (K : Type) [Field K] [CharZero K] (m N : ℕ)
    (a : K) (b c : Fin (m + 1) → K) (h1 : a ≠ 0) (h2 : ∀ k, rpoch (1 + a - b k) N ≠ 0)
    (h3 : ∀ k, rpoch (1 + a - c k) N ≠ 0) (h4 : rpoch (1 + a + N) N ≠ 0)
    (h5 : rpoch (b (Fin.last m) + c (Fin.last m) - a - N) N ≠ 0) :
    andrewsLHS K m N a b c = andrewsRHS K m N a b c :=
  hA K m N a b c h1 h2 h3 h4 h5

/-- `b` of the Andrews application: `(-N-ε, …, -N-ε, 1)`. -/
private def bA (N : ℕ) : Fin 9 → KK := Fin.snoc (fun _ : Fin 8 => LA (-(N : ℚ)) (-1)) 1

/-- `c` of the Andrews application: `(ℓ+1/2-ε, …, ℓ+1/2-ε, 1+a+N)`. -/
private def cA (N l : ℕ) : Fin 9 → KK :=
  Fin.snoc (fun _ : Fin 8 => LA ((l : ℚ) + 1 / 2) (-1)) (1 + LA ((l : ℚ) - N) (-2) + N)

private lemma bA_last (N : ℕ) : bA N (Fin.last 8) = 1 := by simp only [bA, Fin.snoc_last]

private lemma bA_castSucc (N : ℕ) (k : Fin 8) : bA N k.castSucc = LA (-(N : ℚ)) (-1) := by
  simp [bA]

private lemma cA_last (N l : ℕ) : cA N l (Fin.last 8) = 1 + LA ((l : ℚ) - N) (-2) + N := by
  simp only [cA, Fin.snoc_last]

private lemma cA_castSucc (N l : ℕ) (k : Fin 8) :
    cA N l k.castSucc = LA ((l : ℚ) + 1 / 2) (-1) := by
  simp [cA]

private lemma stepB_alg {K : Type*} [Field K] (A Q r f m t : K) (hr : r ≠ 0) (hf : f ≠ 0)
    (hm : m ≠ 0) (ht : t ≠ 0) : A * (r / f) * (Q * (f * t / (r * m))) * (m / t) = A * Q := by
  field_simp

/-- The left side of Andrews' identity is the κ-sum of Step 2 (the ninth pair cancels). -/
private lemma stepB (N l : ℕ) :
    ∑ κ ∈ range (N + 1), (LA ((l : ℚ) - N) (-2) + 2 * κ) / LA ((l : ℚ) - N) (-2) *
        (rpoch (LA (-(N : ℚ)) (-1)) κ * rpoch (LA ((l : ℚ) + 1 / 2) (-1)) κ /
          (rpoch (LA ((l : ℚ) + 1) (-1)) κ * rpoch (LA (1 / 2 - (N : ℚ)) (-1)) κ)) ^ 8 =
      andrewsLHS KK 8 N (LA ((l : ℚ) - N) (-2)) (bA N) (cA N l) := by
  unfold andrewsLHS
  refine Finset.sum_congr rfl (fun κ hκ => ?_)
  have hκ' : κ ≤ N := by simp at hκ; omega
  rw [Fin.prod_univ_castSucc]
  simp only [bA, cA, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [show 1 + LA ((l : ℚ) - N) (-2) - LA (-(N : ℚ)) (-1) = LA ((l : ℚ) + 1) (-1) by
      unfold LA; push_cast; ring,
    show 1 + LA ((l : ℚ) - N) (-2) - LA ((l : ℚ) + 1 / 2) (-1) = LA (1 / 2 - (N : ℚ)) (-1) by
      unfold LA; push_cast; ring,
    show 1 + LA ((l : ℚ) - N) (-2) - 1 = LA ((l : ℚ) - N) (-2) by ring,
    show 1 + LA ((l : ℚ) - N) (-2) - (1 + LA ((l : ℚ) - N) (-2) + N) = -(N : KK) by ring,
    rpoch_one_eq]
  have ht : rpoch (1 + LA ((l : ℚ) - N) (-2) + N) κ ≠ 0 := by
    rw [show 1 + LA ((l : ℚ) - N) (-2) + N = LA ((l : ℚ) + 1) (-2) by
      unfold LA; push_cast; ring]
    exact rpoch_LA_ne_zero _ _ (by norm_num) _
  exact (stepB_alg _ _ _ _ _ _ (rpoch_LA_ne_zero _ _ (by norm_num) _)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero κ)) (rpoch_negN_ne_zero N κ hκ') ht).symm

/-- All hypotheses of `Andrews_Stmt` hold for `a = ℓ-N-2ε`, `b = bA N`, `c = cA N ℓ`. -/
private lemma andrews_hyps (N l : ℕ) :
    LA ((l : ℚ) - N) (-2) ≠ 0 ∧
    (∀ k, rpoch (1 + LA ((l : ℚ) - N) (-2) - bA N k) N ≠ 0) ∧
    (∀ k, rpoch (1 + LA ((l : ℚ) - N) (-2) - cA N l k) N ≠ 0) ∧
    rpoch (1 + LA ((l : ℚ) - N) (-2) + N) N ≠ 0 ∧
    rpoch (bA N (Fin.last 8) + cA N l (Fin.last 8) - LA ((l : ℚ) - N) (-2) - N) N ≠ 0 := by
  refine ⟨LA_ne_zero _ _ (by norm_num), ?_, ?_, ?_, ?_⟩
  · intro k
    induction k using Fin.lastCases with
    | last =>
      rw [bA_last, show 1 + LA ((l : ℚ) - N) (-2) - 1 = LA ((l : ℚ) - N) (-2) by ring]
      exact rpoch_LA_ne_zero _ _ (by norm_num) _
    | cast j =>
      rw [bA_castSucc, show 1 + LA ((l : ℚ) - N) (-2) - LA (-(N : ℚ)) (-1) =
        LA ((l : ℚ) + 1) (-1) by unfold LA; push_cast; ring]
      exact rpoch_LA_ne_zero _ _ (by norm_num) _
  · intro k
    induction k using Fin.lastCases with
    | last =>
      rw [cA_last, show 1 + LA ((l : ℚ) - N) (-2) - (1 + LA ((l : ℚ) - N) (-2) + N) =
        -(N : KK) by ring]
      exact rpoch_negN_ne_zero N N le_rfl
    | cast j =>
      rw [cA_castSucc, show 1 + LA ((l : ℚ) - N) (-2) - LA ((l : ℚ) + 1 / 2) (-1) =
        LA (1 / 2 - (N : ℚ)) (-1) by unfold LA; push_cast; ring]
      exact rpoch_LA_ne_zero _ _ (by norm_num) _
  · rw [show 1 + LA ((l : ℚ) - N) (-2) + N = LA ((l : ℚ) + 1) (-2) by
      unfold LA; push_cast; ring]
    exact rpoch_LA_ne_zero _ _ (by norm_num) _
  · rw [bA_last, cA_last, show (1 : KK) + (1 + LA ((l : ℚ) - N) (-2) + N) -
      LA ((l : ℚ) - N) (-2) - N = 2 by ring, rpoch_two_eq]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-! ### The right side of Andrews' identity is `∑_J F_J` -/

/-- The prefactor `(1+a)_N (-1-N)_N / ((a)_N (-N)_N) = (N+1)(a+N)/a`. -/
private lemma prefactor_eq (a : KK) (N : ℕ) (ha : a ≠ 0) (haN : rpoch a N ≠ 0) :
    rpoch (1 + a) N * rpoch (1 + a - 1 - (1 + a + N)) N /
      (rpoch (1 + a - 1) N * rpoch (1 + a - (1 + a + N)) N) = ((N : KK) + 1) * (a + N) / a := by
  rw [show 1 + a - 1 - (1 + a + N) = -1 - (N : KK) by ring, show 1 + a - 1 = a by ring,
    show 1 + a - (1 + a + N) = -(N : KK) by ring, rpoch_negN1, rpoch_negN, Nat.factorial_succ]
  have h := rpoch_shift_ratio a N
  have hf : (N.factorial : KK) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hs : ((-1 : KK) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_div_iff (mul_ne_zero haN (mul_ne_zero hs hf)) ha]
  push_cast
  linear_combination ((-1 : KK) ^ N * ((N : KK) + 1) * (N.factorial : KK)) * h

private lemma prod_split8 (A B C D E F : Fin 8 → KK) :
    ∏ k, A k * B k * C k / (D k * E k * F k) =
      (∏ k, A k / D k) * ∏ k, B k * C k / (E k * F k) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  ring

private lemma prodA_eq (ch : Fin 8 → ℕ) :
    ∏ k : Fin 8, rpoch (1 / 2 : KK) (ch k - chainPrev ch k) /
        ((ch k - chainPrev ch k).factorial : KK) =
      ∏ i : Fin 8, ((rpoch (1 / 2 : ℚ) (ch i - chainPrev ch i) /
        ((ch i - chainPrev ch i).factorial : ℚ) : ℚ) : KK) := by
  refine Finset.prod_congr rfl (fun k _ => ?_)
  push_cast [ratCast_rpoch]
  rfl

private lemma prodB_eq (N l : ℕ) (ch : Fin 8 → ℕ) :
    ∏ k : Fin 8, rpoch (bA N k.succ) (ch k) * rpoch (cA N l k.succ) (ch k) /
        (rpoch (LA ((l : ℚ) + 1) (-1)) (ch k) * rpoch (LA (1 / 2 - (N : ℚ)) (-1)) (ch k)) =
      (∏ i : Fin 7, rpoch (LA (-(N : ℚ)) (-1)) (ch i.castSucc) *
        rpoch (LA ((l : ℚ) + 1 / 2) (-1)) (ch i.castSucc) *
        (rpoch (LA ((l : ℚ) + 1) (-1)) (ch i.castSucc) *
          rpoch (LA (1 / 2 - (N : ℚ)) (-1)) (ch i.castSucc))⁻¹) *
      (((ch 7).factorial : KK) * rpoch (1 + LA ((l : ℚ) - N) (-2) + N) (ch 7) /
        (rpoch (LA ((l : ℚ) + 1) (-1)) (ch 7) * rpoch (LA (1 / 2 - (N : ℚ)) (-1)) (ch 7))) := by
  rw [Fin.prod_univ_castSucc]
  simp only [bA, cA, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last,
    rpoch_one_eq, div_eq_mul_inv]
  rfl

private lemma stepC_alg {K : Type*} [Field K] (a P n1 m m' F1 f J1 j PA PB r r' y v cN cl : K)
    (hF1 : F1 = (j + 1) * f) (hJ1 : J1 = j + 1) (hm : m' = m) (hr : r = r')
    (hcN : cN = -n1 - 1) (hcl : cl = a + n1) (ha : a ≠ 0) (hf : f ≠ 0) (hj : j + 1 ≠ 0)
    (hy : y ≠ 0) (hv : v ≠ 0) :
    -a * P * ((n1 + 1) * (a + n1) / a * (m / F1 * (PA * (PB * (f * r / (y * v)))))) =
      cN * cl * P * PA * PB * (r' * m' * (J1 * y * v)⁻¹) := by
  subst hF1 hJ1 hm hr hcN hcl
  field_simp
  ring

/-- `-a P_ℓ` times the right side of Andrews' identity is `∑_J φ(F_J)`. -/
private lemma stepC (N l : ℕ) :
    -LA ((l : ℚ) - N) (-2) * phiA (Pser (l + N) l) *
        andrewsRHS KK 8 N (LA ((l : ℚ) - N) (-2)) (bA N) (cA N l) =
      ∑ ch ∈ chains 8 N, phiA (Fser (l + N) l ch) := by
  have ha : LA ((l : ℚ) - N) (-2) ≠ 0 := LA_ne_zero _ _ (by norm_num)
  have haN : rpoch (LA ((l : ℚ) - N) (-2)) N ≠ 0 := rpoch_LA_ne_zero _ _ (by norm_num) _
  unfold andrewsRHS
  simp only [bA_last, cA_last, bA_castSucc, cA_castSucc]
  rw [prefactor_eq _ N ha haN]
  rw [show (1 : KK) + (1 + LA ((l : ℚ) - N) (-2) + N) - LA ((l : ℚ) - N) (-2) - N = 2 by ring]
  rw [show 1 + LA ((l : ℚ) - N) (-2) - LA (-(N : ℚ)) (-1) - LA ((l : ℚ) + 1 / 2) (-1) =
    (1 / 2 : KK) by unfold LA; push_cast; ring]
  rw [show 1 + LA ((l : ℚ) - N) (-2) - LA (-(N : ℚ)) (-1) = LA ((l : ℚ) + 1) (-1) by
    unfold LA; push_cast; ring]
  rw [show 1 + LA ((l : ℚ) - N) (-2) - LA ((l : ℚ) + 1 / 2) (-1) = LA (1 / 2 - (N : ℚ)) (-1) by
    unfold LA; push_cast; ring]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ch _ => ?_)
  rw [phiA_Fser, prod_split8, prodA_eq, prodB_eq, rpoch_two_eq]
  refine stepC_alg (j := ((ch 7 : ℕ) : KK)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ha
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) ?_ (rpoch_LA_ne_zero _ _ (by norm_num) _)
    (rpoch_LA_ne_zero _ _ (by norm_num) _)
  · change (((ch 7 + 1).factorial : ℕ) : KK) = _
    rw [Nat.factorial_succ]
    push_cast
    ring
  · push_cast
    ring
  · rw [ratCast_rpoch]
    push_cast
    rfl
  · congr 1
    unfold LA
    push_cast
    ring
  · push_cast
    ring
  · unfold LA epsA
    push_cast
    ring
  · exact_mod_cast Nat.succ_ne_zero (ch 7)

end AndrewsAppliedAux

open AndrewsAppliedAux in
theorem AndrewsApplied_proof (hA : Andrews_Stmt) : Stmt_AndrewsApplied := by
  have : CharZero KK := charZero_KK
  intro n l _ hln
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hln
  rw [Nat.add_sub_cancel_left]
  apply phiA_injective
  obtain ⟨h1, h2, h3, h4, h5⟩ := andrews_hyps N l
  rw [map_sum, stepA N l, stepB N l, andrews_apply hA KK 8 N _ _ _ h1 h2 h3 h4 h5]
  exact stepC N l

end Zeta2

end
