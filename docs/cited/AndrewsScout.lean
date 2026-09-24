import Zeta2Lean.Statements

/-!
# Andrews' transformation (Krattenthaler–Rivoal, Théorème 8) — proof of `Andrews_Stmt`

`Andrews_proof : Andrews_Stmt` proves the cited hypothesis `Andrews_Stmt` of the main theorem
(Andrews 1975, Thm 4, at `q = 1`), over every field of characteristic zero, under exactly the
non-vanishing hypotheses of the statement (no genericity assumption).

## Route: the `q = 1` Bailey chain in a polynomial normalisation

Write `(x)_k = rpoch x k`.  Call `(α, β)` a *Bailey pair at level `n`* (relative to `a`) if
```
  BP(n):   (1+a)_{2n} β_n = ∑_{r=0}^{n} α_r (1+a+n+r)_{n-r} / (n-r)!
```
(this is `β_n = ∑_r α_r / ((n-r)! (1+a)_{n+r})` multiplied by `(1+a)_{2n}`; the multiplied form
never divides by `(1+a)_k`, which `Andrews_Stmt` does not assume non-zero).

1. **Polynomial Pfaff–Saalschütz** (`pps_field`): for all `x y z` in any field and all `M`,
   `∑_{s=0}^{M} C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} = (z-x)_M (z-y)_M (z+M)_M`.
   Proof: explicit Zeilberger certificate
   `G(M,s+1) = -(z+2M+1) C(M,s) (x)_{s+1} (y)_{s+1} (z-x-y)_{M-s} (z+s)_{2M+1-s}`, `G(M,0) = 0`,
   giving `(z+M) S(M+1) = (z-x+M)(z-y+M)(z+2M)(z+2M+1) S(M)` in every commutative ring
   (`pps_rec`); cancel `z+M` in `K[X]` (`z := X`, a domain where `X + M ≠ 0`), evaluate at `z`.
2. **Unit Bailey pair** (`bp_unit`): `α_r = (a+2r)/a (a)_r (-1)^r / r!`, `β_n = [n = 0]`
   (telescoping, `a ≠ 0`).
3. **Bailey's lemma** (`bailey_step`): if `BP(j)` holds for all `j ≤ n` and
   `(1+a-ρ)_n, (1+a-σ)_n ≠ 0`, then `BP(n)` holds for
   `α'_r = (ρ)_r (σ)_r / ((1+a-ρ)_r (1+a-σ)_r) α_r` and
   `β'_n = ∑_{j≤n} (ρ)_j (σ)_j (1+a-ρ-σ)_{n-j} / ((1+a-ρ)_n (1+a-σ)_n (n-j)!) β_j`
   (exchange of summation + PPS with `x = ρ+r`, `y = σ+r`, `z = 1+a+2r`, `M = n-r`).
4. **Chains** (`Bchain_succ`, `sum_chains_succ`): `m + 1` Bailey steps with the pairs
   `(b_k, c_k)` give the chain sum of `Andrews_Stmt` (`bp_chain`).
5. **Assembly** (`Andrews_proof`): `LHS = N! (1+a)_N β_N = RHS`, using only `a ≠ 0`,
   `(1+a+N)_N ≠ 0`, `(b_L+c_L-a-N)_N ≠ 0` and `(1+a-b_k)_N, (1+a-c_k)_N ≠ 0`.
-/

open Finset

noncomputable section

namespace Zeta2

namespace CitedAndrews

/-! ### Pochhammer API (any commutative ring) -/

section Poch

variable {R : Type*} [CommRing R]

lemma rpoch_zero (x : R) : rpoch x 0 = 1 := by simp [rpoch]

lemma rpoch_one (x : R) : rpoch x 1 = x := by simp [rpoch]

lemma rpoch_succ (x : R) (k : ℕ) : rpoch x (k + 1) = rpoch x k * (x + k) := by
  simp [rpoch, Finset.prod_range_succ]

lemma rpoch_succ' (x : R) (k : ℕ) : rpoch x (k + 1) = x * rpoch (x + 1) k := by
  unfold rpoch
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by ring)

lemma rpoch_add (x : R) (a b : ℕ) : rpoch x (a + b) = rpoch x a * rpoch (x + a) b := by
  unfold rpoch
  rw [Finset.prod_range_add]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by push_cast; ring)

lemma map_rpoch {S : Type*} [CommRing S] (f : R →+* S) (x : R) (k : ℕ) :
    f (rpoch x k) = rpoch (f x) k := by
  simp [rpoch, map_prod]

lemma rpoch_ne_zero_of_le (x : R) {N κ : ℕ} (h : rpoch x N ≠ 0) (hk : κ ≤ N) :
    rpoch x κ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [rpoch_add, h0, zero_mul]

/-- `(-N)_κ (N-κ)! = (-1)^κ N!` for `κ ≤ N`. -/
lemma rpoch_negN_mul (N κ : ℕ) (h : κ ≤ N) :
    rpoch (-(N : R)) κ * ((N - κ).factorial : R) = (-1) ^ κ * (N.factorial : R) := by
  induction κ with
  | zero => simp [rpoch_zero]
  | succ κ ih =>
    have h' : κ ≤ N := by omega
    have e : N - κ = (N - (κ + 1)) + 1 := by omega
    have ih' := ih h'
    rw [e, Nat.factorial_succ] at ih'
    rw [rpoch_succ, pow_succ]
    have e2 : ((N - (κ + 1) + 1 : ℕ) : R) = (N : R) - κ := by
      rw [← e, Nat.cast_sub h']
    push_cast at ih' e2
    linear_combination (-1 : R) * ih' + (rpoch (-(N : R)) κ * ((N - (κ + 1)).factorial : R)) * e2

/-- Reflection: `(x)_{N-κ} (1-x-N)_κ = (-1)^κ (x)_N` for `κ ≤ N`. -/
lemma rpoch_reflect (x : R) (N κ : ℕ) (h : κ ≤ N) :
    rpoch x (N - κ) * rpoch (1 - x - N) κ = (-1) ^ κ * rpoch x N := by
  induction κ with
  | zero => simp [rpoch_zero]
  | succ κ ih =>
    have h' : κ ≤ N := by omega
    have hN : N - κ = (N - (κ + 1)) + 1 := by omega
    have e1 : rpoch x (N - κ) = rpoch x (N - (κ + 1)) * (x + ((N - (κ + 1) : ℕ) : R)) := by
      rw [hN, rpoch_succ]
    have e2 : ((N - (κ + 1) : ℕ) : R) = (N : R) - κ - 1 := by
      rw [Nat.cast_sub (by omega : κ + 1 ≤ N)]
      push_cast
      ring
    rw [rpoch_succ, pow_succ,
      show (-1 : R) ^ κ * -1 * rpoch x N = -((-1) ^ κ * rpoch x N) by ring, ← ih h', e1, e2]
    ring

end Poch

/-! ### 1. Polynomial Pfaff–Saalschütz with a Zeilberger certificate -/

section PPS

variable {R : Type*} [CommRing R]

/-- Summand `C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s}`. -/
def ppsF (x y z : R) (M s : ℕ) : R :=
  (M.choose s : R) * rpoch x s * rpoch y s * rpoch (z - x - y) (M - s) * rpoch (z + s) (2 * M - s)

/-- The polynomial Pfaff–Saalschütz sum `S(M)`. -/
def ppsS (x y z : R) (M : ℕ) : R := ∑ s ∈ range (M + 1), ppsF x y z M s

/-- Zeilberger certificate, `G(M, s+1)`. -/
def ppsg (x y z : R) (M s : ℕ) : R :=
  -(z + 2 * M + 1) * (M.choose s : R) * rpoch x (s + 1) * rpoch y (s + 1) *
    rpoch (z - x - y) (M - s) * rpoch (z + s) (2 * M + 1 - s)

/-- Zeilberger certificate `G(M, s)` (`G(M, 0) = 0`). -/
def ppsG (x y z : R) (M : ℕ) : ℕ → R
  | 0 => 0
  | s + 1 => ppsg x y z M s

/-- Recurrence coefficient `(z-x+M)(z-y+M)(z+2M)(z+2M+1)`. -/
def ppsc (x y z : R) (M : ℕ) : R := (z - x + M) * (z - y + M) * (z + 2 * M) * (z + 2 * M + 1)

lemma pps_tele_zero (x y z : R) (M : ℕ) :
    (z + M) * ppsF x y z (M + 1) 0 - ppsc x y z M * ppsF x y z M 0 =
      ppsG x y z M 1 - ppsG x y z M 0 := by
  simp only [ppsF, ppsG, ppsg, ppsc, Nat.choose_zero_right, rpoch_zero, Nat.sub_zero,
    Nat.cast_zero, add_zero, Nat.cast_one, zero_add, rpoch_one, sub_zero]
  rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, rpoch_succ z (2 * M + 1), rpoch_succ z (2 * M),
    rpoch_succ (z - x - y) M]
  push_cast
  ring

/-- Algebraic core of the middle case (atoms `X Y P Z C1 C2`, binomial relation `hrel`). -/
lemma pps_mid_core (x y z u t X Y P Z C1 C2 : R) (hrel : (u + 1) * C1 = (t + 1) * C2) :
    (z + (u + 1 + t)) * ((C2 + C1) * X * Y * (P * (z - x - y + t)) *
        (Z * (z + (u + 1) + (u + 2 * t + 1)) * (z + (u + 1) + (u + 2 * t + 1 + 1)))) -
      (z - x + (u + 1 + t)) * (z - y + (u + 1 + t)) * (z + 2 * (u + 1 + t)) *
        (z + 2 * (u + 1 + t) + 1) * (C1 * X * Y * P * Z) =
    -(z + 2 * (u + 1 + t) + 1) * C1 * (X * (x + (u + 1))) * (Y * (y + (u + 1))) * P *
        (Z * (z + (u + 1) + (u + 2 * t + 1))) -
      -(z + 2 * (u + 1 + t) + 1) * C2 * X * Y * (P * (z - x - y + t)) *
        ((z + u) * (Z * (z + (u + 1) + (u + 2 * t + 1)))) := by
  linear_combination (P * X * Y * Z * (x + y - z - t) * (2 * t + 2 * u + z + 2) *
    (2 * t + 2 * u + z + 3)) * hrel

lemma pps_tele_mid (x y z : R) (M u : ℕ) (hu : u + 1 ≤ M) :
    (z + M) * ppsF x y z (M + 1) (u + 1) - ppsc x y z M * ppsF x y z M (u + 1) =
      ppsG x y z M (u + 1 + 1) - ppsG x y z M (u + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, M = u + 1 + t := ⟨M - (u + 1), by omega⟩
  simp only [ppsF, ppsG, ppsg, ppsc]
  have e1 : rpoch (z - x - y) (u + 1 + t + 1 - (u + 1)) =
      rpoch (z - x - y) t * (z - x - y + t) := by
    rw [show u + 1 + t + 1 - (u + 1) = t + 1 by omega, rpoch_succ]
  have e2 : u + 1 + t - (u + 1) = t := by omega
  have e3 : rpoch (z - x - y) (u + 1 + t - u) = rpoch (z - x - y) t * (z - x - y + t) := by
    rw [show u + 1 + t - u = t + 1 by omega, rpoch_succ]
  have e4 : rpoch (z + ((u + 1 : ℕ) : R)) (2 * (u + 1 + t + 1) - (u + 1)) =
      rpoch (z + ((u + 1 : ℕ) : R)) (u + 2 * t + 1) *
        (z + ((u + 1 : ℕ) : R) + ((u + 2 * t + 1 : ℕ) : R)) *
        (z + ((u + 1 : ℕ) : R) + ((u + 2 * t + 1 + 1 : ℕ) : R)) := by
    rw [show 2 * (u + 1 + t + 1) - (u + 1) = u + 2 * t + 1 + 1 + 1 by omega, rpoch_succ,
      rpoch_succ]
  have e5 : 2 * (u + 1 + t) - (u + 1) = u + 2 * t + 1 := by omega
  have e6 : rpoch (z + ((u + 1 : ℕ) : R)) (2 * (u + 1 + t) + 1 - (u + 1)) =
      rpoch (z + ((u + 1 : ℕ) : R)) (u + 2 * t + 1) *
        (z + ((u + 1 : ℕ) : R) + ((u + 2 * t + 1 : ℕ) : R)) := by
    rw [show 2 * (u + 1 + t) + 1 - (u + 1) = u + 2 * t + 1 + 1 by omega, rpoch_succ]
  have e7 : rpoch (z + (u : R)) (2 * (u + 1 + t) + 1 - u) =
      (z + u) * (rpoch (z + ((u + 1 : ℕ) : R)) (u + 2 * t + 1) *
        (z + ((u + 1 : ℕ) : R) + ((u + 2 * t + 1 : ℕ) : R))) := by
    rw [show 2 * (u + 1 + t) + 1 - u = u + 2 * t + 1 + 1 + 1 by omega, rpoch_succ', rpoch_succ,
      show z + (u : R) + 1 = z + ((u + 1 : ℕ) : R) by push_cast; ring]
  have e8 : rpoch x (u + 1 + 1) = rpoch x (u + 1) * (x + ((u + 1 : ℕ) : R)) := rpoch_succ _ _
  have e9 : rpoch y (u + 1 + 1) = rpoch y (u + 1) * (y + ((u + 1 : ℕ) : R)) := rpoch_succ _ _
  have hC : (((u + 1 + t + 1).choose (u + 1) : ℕ) : R) =
      (((u + 1 + t).choose u : ℕ) : R) + (((u + 1 + t).choose (u + 1) : ℕ) : R) := by
    rw [Nat.choose_succ_succ]; push_cast; ring
  have hrel : ((u : R) + 1) * (((u + 1 + t).choose (u + 1) : ℕ) : R) =
      ((t : R) + 1) * (((u + 1 + t).choose u : ℕ) : R) := by
    have h := Nat.choose_succ_right_eq (u + 1 + t) u
    rw [show u + 1 + t - u = t + 1 by omega] at h
    have h' : (((u + 1 + t).choose (u + 1) * (u + 1) : ℕ) : R) =
        (((u + 1 + t).choose u * (t + 1) : ℕ) : R) := by rw [h]
    push_cast at h'
    linear_combination h'
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, hC]
  have core := pps_mid_core x y z (u : R) (t : R) (rpoch x (u + 1)) (rpoch y (u + 1))
    (rpoch (z - x - y) t) (rpoch (z + ((u + 1 : ℕ) : R)) (u + 2 * t + 1))
    (((u + 1 + t).choose (u + 1) : ℕ) : R) (((u + 1 + t).choose u : ℕ) : R) hrel
  convert core using 2 <;> push_cast <;> ring

lemma pps_tele_last (x y z : R) (M : ℕ) :
    (z + M) * ppsF x y z (M + 1) (M + 1) - ppsc x y z M * ppsF x y z M (M + 1) =
      ppsG x y z M (M + 1 + 1) - ppsG x y z M (M + 1) := by
  simp only [ppsF, ppsG, ppsg, ppsc, Nat.choose_self, Nat.choose_succ_self, Nat.sub_self,
    rpoch_zero, Nat.cast_zero, Nat.cast_one]
  rw [show 2 * (M + 1) - (M + 1) = M + 1 by omega, show 2 * M + 1 - M = M + 1 by omega]
  have h : (z + (M : R)) * rpoch (z + ((M + 1 : ℕ) : R)) (M + 1) =
      (z + 2 * M + 1) * rpoch (z + (M : R)) (M + 1) := by
    have h1 := rpoch_succ' (z + (M : R)) (M + 1)
    rw [rpoch_succ (z + (M : R)) (M + 1)] at h1
    rw [show z + (M : R) + 1 = z + ((M + 1 : ℕ) : R) by push_cast; ring] at h1
    rw [← h1]
    push_cast
    ring
  linear_combination (rpoch x (M + 1) * rpoch y (M + 1)) * h

/-- Telescoping identity `(z+M) F(M+1,s) - c(M) F(M,s) = G(M,s+1) - G(M,s)`, `s ≤ M+1`. -/
lemma pps_tele (x y z : R) (M s : ℕ) (hs : s ≤ M + 1) :
    (z + M) * ppsF x y z (M + 1) s - ppsc x y z M * ppsF x y z M s =
      ppsG x y z M (s + 1) - ppsG x y z M s := by
  rcases s with _ | u
  · exact pps_tele_zero x y z M
  · rcases Nat.lt_or_ge u M with h | h
    · exact pps_tele_mid x y z M u h
    · obtain rfl : u = M := by omega
      exact pps_tele_last x y z _

/-- Zeilberger recurrence `(z+M) S(M+1) = c(M) S(M)` (every commutative ring). -/
theorem pps_rec (x y z : R) (M : ℕ) :
    (z + M) * ppsS x y z (M + 1) = ppsc x y z M * ppsS x y z M := by
  have hF : ppsF x y z M (M + 1) = 0 := by simp [ppsF, Nat.choose_succ_self]
  have hG : ppsG x y z M (M + 2) = 0 := by simp [ppsG, ppsg, Nat.choose_succ_self]
  have key : ∑ s ∈ range (M + 2),
      ((z + M) * ppsF x y z (M + 1) s - ppsc x y z M * ppsF x y z M s) = 0 := by
    rw [Finset.sum_congr rfl (fun s hs => pps_tele x y z M s (by simp at hs; omega)),
      Finset.sum_range_sub, hG]
    simp [ppsG]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_succ (fun s => ppsF x y z M s) (M + 1), hF, add_zero] at key
  unfold ppsS
  linear_combination key

/-- The right side satisfies the same recurrence. -/
lemma pps_rhs_rec (x y z : R) (M : ℕ) :
    (z + M) * (rpoch (z - x) (M + 1) * rpoch (z - y) (M + 1) *
        rpoch (z + ((M + 1 : ℕ) : R)) (M + 1)) =
      ppsc x y z M * (rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M) := by
  have h1 := rpoch_succ' (z + (M : R)) (M + 1)
  rw [rpoch_succ (z + (M : R)) (M + 1), rpoch_succ (z + (M : R)) M,
    show z + (M : R) + 1 = z + ((M + 1 : ℕ) : R) by push_cast; ring] at h1
  unfold ppsc
  rw [rpoch_succ (z - x) M, rpoch_succ (z - y) M]
  push_cast at h1 ⊢
  linear_combination (rpoch (z - x) M * (z - x + M) * (rpoch (z - y) M * (z - y + M))) * h1.symm

/-- PPS in a domain, for `z` avoiding the non-positive integers. -/
theorem pps_domain [IsDomain R] (x y z : R) (hz : ∀ j : ℕ, z + j ≠ 0) (M : ℕ) :
    ppsS x y z M = rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M := by
  induction M with
  | zero => simp [ppsS, ppsF, rpoch_zero]
  | succ M ih =>
    apply mul_left_cancel₀ (hz M)
    rw [pps_rec, ih, pps_rhs_rec]

/-- **Polynomial Pfaff–Saalschütz**, in any field, for all `x y z` (via `K[X]`, `z := X`). -/
theorem pps_field {K : Type*} [Field K] (x y z : K) (M : ℕ) :
    ppsS x y z M = rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M := by
  have h := pps_domain (R := Polynomial K) (Polynomial.C x) (Polynomial.C y) Polynomial.X
    (fun j => by
      rw [show ((j : ℕ) : Polynomial K) = Polynomial.C (j : K) by simp]
      exact Polynomial.X_add_C_ne_zero _) M
  have h2 := congrArg (Polynomial.evalRingHom z) h
  simp only [ppsS, ppsF, map_sum, map_mul, map_natCast, map_rpoch, map_sub, map_add,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X] at h2
  simpa [ppsS, ppsF] using h2

/-- PPS with factorial denominators (characteristic zero). -/
theorem pps_div {K : Type*} [Field K] [CharZero K] (x y z : K) (M : ℕ) :
    ∑ s ∈ range (M + 1), rpoch x s * rpoch y s * rpoch (z - x - y) (M - s) *
        rpoch (z + s) (2 * M - s) / ((s.factorial : K) * ((M - s).factorial : K)) =
      rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M / (M.factorial : K) := by
  have h := pps_field x y z M
  unfold ppsS ppsF at h
  have hM : (M.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  rw [eq_div_iff hM, Finset.sum_mul, ← h]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s ≤ M := by simp at hs; omega
  rw [Nat.cast_choose K hs']
  have h1 : (s.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  have h2 : ((M - s).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

end PPS

/-! ### 2–3. Bailey pairs at `q = 1`: the unit pair and Bailey's lemma -/

section Bailey

variable {K : Type*} [Field K] [CharZero K]

lemma fact_ne (n : ℕ) : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- Bailey-pair relation (q = 1, polynomial normalisation) relative to `a`, at level `n`. -/
def BP (a : K) (α β : ℕ → K) (n : ℕ) : Prop :=
  rpoch (1 + a) (2 * n) * β n =
    ∑ r ∈ range (n + 1), α r * rpoch (1 + a + n + r) (n - r) / ((n - r).factorial : K)

/-- The unit Bailey pair, `α` side. -/
def unitα (a : K) (r : ℕ) : K := (a + 2 * r) / a * rpoch a r * (-1) ^ r / (r.factorial : K)

/-- The unit Bailey pair, `β` side. -/
def unitβ (n : ℕ) : K := if n = 0 then 1 else 0

/-- Partial sums of the unit-pair sum at level `N = n' + 1` (telescoping). -/
lemma unit_partial (a : K) (ha : a ≠ 0) (n' k : ℕ) (hk : k ≤ n') :
    ∑ r ∈ range (k + 1), unitα a r * rpoch (1 + a + ((n' + 1 : ℕ) : K) + r) (n' + 1 - r) /
        ((n' + 1 - r).factorial : K) =
      (-1) ^ k * rpoch (1 + a) k * rpoch (1 + a + ((n' + 1 : ℕ) : K) + k) (n' + 1 - k) /
        ((k.factorial : K) * ((n' - k).factorial : K) * ((n' + 1 : ℕ) : K)) := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, unitα, Nat.cast_zero, mul_zero, add_zero,
      rpoch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, Nat.sub_zero,
      one_mul, div_self ha]
    rw [Nat.factorial_succ]
    push_cast
    have := fact_ne (K := K) n'
    field_simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, n' = k + 1 + j := ⟨n' - (k + 1), by omega⟩
    rw [show k + 1 + j + 1 - k = (j + 1) + 1 by omega,
      show k + 1 + j + 1 - (k + 1) = j + 1 by omega,
      show k + 1 + j - k = j + 1 by omega, show k + 1 + j - (k + 1) = j by omega]
    rw [rpoch_succ' (1 + a + ((k + 1 + j + 1 : ℕ) : K) + k) (j + 1),
      show 1 + a + ((k + 1 + j + 1 : ℕ) : K) + k + 1 =
        1 + a + ((k + 1 + j + 1 : ℕ) : K) + ((k + 1 : ℕ) : K) by push_cast; ring]
    unfold unitα
    rw [rpoch_succ' a k, rpoch_succ (1 + a) k, show a + 1 = 1 + a by ring,
      Nat.factorial_succ k, Nat.factorial_succ j]
    have h1 := fact_ne (K := K) k
    have h2 := fact_ne (K := K) j
    have h3 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h4 : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have h5 : ((k + 1 + j + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1 + j)
    push_cast at h5 ⊢
    field_simp
    ring

/-- The unit Bailey pair satisfies `BP` at every level. -/
theorem bp_unit (a : K) (ha : a ≠ 0) (n : ℕ) : BP a (unitα a) unitβ n := by
  unfold BP
  rcases n with _ | n'
  · simp [unitα, unitβ, rpoch_zero, ha]
  · have hsplit := Finset.sum_range_succ (fun r => unitα a r *
        rpoch (1 + a + ((n' + 1 : ℕ) : K) + r) (n' + 1 - r) / ((n' + 1 - r).factorial : K))
        (n' + 1)
    rw [hsplit, unit_partial a ha n' n' le_rfl]
    simp only [unitβ, Nat.succ_ne_zero, ite_false, mul_zero, Nat.sub_self, rpoch_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [show n' + 1 - n' = 0 + 1 by omega, rpoch_succ, rpoch_zero]
    unfold unitα
    rw [rpoch_succ' a n', show a + 1 = 1 + a by ring, Nat.factorial_succ n']
    have h1 := fact_ne (K := K) n'
    have h3 : ((n' : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n'
    push_cast
    field_simp
    ring

/-- Bailey-lemma weight `(ρ)_j (σ)_j (1+a-ρ-σ)_{n-j} / ((1+a-ρ)_n (1+a-σ)_n (n-j)!)`. -/
def bw (a ρ σ : K) (n j : ℕ) : K :=
  rpoch ρ j * rpoch σ j * rpoch (1 + a - ρ - σ) (n - j) /
    (rpoch (1 + a - ρ) n * rpoch (1 + a - σ) n * ((n - j).factorial : K))

/-- New `α` after one Bailey step with the pair `(ρ, σ)`. -/
def bα (a ρ σ : K) (α : ℕ → K) (r : ℕ) : K :=
  rpoch ρ r * rpoch σ r / (rpoch (1 + a - ρ) r * rpoch (1 + a - σ) r) * α r

/-- New `β` after one Bailey step with the pair `(ρ, σ)`. -/
def bβ (a ρ σ : K) (β : ℕ → K) (n : ℕ) : K := ∑ j ∈ range (n + 1), bw a ρ σ n j * β j

/-- The inner sum of Bailey's lemma is a polynomial Pfaff–Saalschütz sum. -/
lemma bailey_inner (a ρ σ : K) (r M : ℕ)
    (hρ : rpoch (1 + a - ρ) (r + M) ≠ 0) (hσ : rpoch (1 + a - σ) (r + M) ≠ 0) :
    ∑ s ∈ range (M + 1), bw a ρ σ (r + M) (r + s) *
        rpoch (1 + a + ((2 * (r + s) : ℕ) : K)) (2 * (r + M - (r + s))) *
        (rpoch (1 + a + ((r + s : ℕ) : K) + r) (r + s - r) / ((r + s - r).factorial : K)) =
      rpoch ρ r * rpoch σ r / (rpoch (1 + a - ρ) r * rpoch (1 + a - σ) r) *
        (rpoch (1 + a + ((r + M : ℕ) : K) + r) (r + M - r) / ((r + M - r).factorial : K)) := by
  have hρr : rpoch (1 + a - ρ) r ≠ 0 := rpoch_ne_zero_of_le _ hρ (by omega)
  have hσr : rpoch (1 + a - σ) r ≠ 0 := rpoch_ne_zero_of_le _ hσ (by omega)
  have hρ' := hρ
  have hσ' := hσ
  rw [rpoch_add] at hρ' hσ'
  have hρM : rpoch (1 + a - ρ + r) M ≠ 0 := right_ne_zero_of_mul hρ'
  have hσM : rpoch (1 + a - σ + r) M ≠ 0 := right_ne_zero_of_mul hσ'
  have hP := pps_div (ρ + r) (σ + r) (1 + a + 2 * r) M
  have key : ∀ s ∈ range (M + 1), bw a ρ σ (r + M) (r + s) *
      rpoch (1 + a + ((2 * (r + s) : ℕ) : K)) (2 * (r + M - (r + s))) *
      (rpoch (1 + a + ((r + s : ℕ) : K) + r) (r + s - r) / ((r + s - r).factorial : K)) =
      rpoch ρ r * rpoch σ r / (rpoch (1 + a - ρ) (r + M) * rpoch (1 + a - σ) (r + M)) *
        (rpoch (ρ + r) s * rpoch (σ + r) s * rpoch (1 + a + 2 * r - (ρ + r) - (σ + r)) (M - s) *
          rpoch (1 + a + 2 * r + s) (2 * M - s) /
            ((s.factorial : K) * ((M - s).factorial : K))) := by
    intro s hs
    have hs' : s ≤ M := by simp at hs; omega
    unfold bw
    rw [Nat.add_sub_add_left, Nat.add_sub_cancel_left, rpoch_add ρ r s, rpoch_add σ r s,
      show 1 + a + 2 * (r : K) - (ρ + r) - (σ + r) = 1 + a - ρ - σ by ring]
    have hz : rpoch (1 + a + 2 * (r : K) + s) (2 * M - s) =
        rpoch (1 + a + ((r + s : ℕ) : K) + r) s *
          rpoch (1 + a + ((2 * (r + s) : ℕ) : K)) (2 * (M - s)) := by
      rw [show 2 * M - s = s + 2 * (M - s) by omega, rpoch_add,
        show 1 + a + ((r + s : ℕ) : K) + r = 1 + a + 2 * (r : K) + s by push_cast; ring,
        show 1 + a + ((2 * (r + s) : ℕ) : K) = 1 + a + 2 * (r : K) + s + s by push_cast; ring]
    rw [hz]
    have h1 := fact_ne (K := K) s
    have h2 := fact_ne (K := K) (M - s)
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hP]
  rw [Nat.add_sub_cancel_left, rpoch_add (1 + a - ρ) r M, rpoch_add (1 + a - σ) r M,
    show 1 + a + 2 * (r : K) - (ρ + r) = 1 + a - ρ + r by ring,
    show 1 + a + 2 * (r : K) - (σ + r) = 1 + a - σ + r by ring,
    show 1 + a + 2 * (r : K) + M = 1 + a + ((r + M : ℕ) : K) + r by push_cast; ring]
  have h3 := fact_ne (K := K) M
  field_simp

/-- **Bailey's lemma** (q = 1, polynomial normalisation). -/
theorem bailey_step (a ρ σ : K) (α β : ℕ → K) (n : ℕ)
    (hρ : rpoch (1 + a - ρ) n ≠ 0) (hσ : rpoch (1 + a - σ) n ≠ 0)
    (h : ∀ j ≤ n, BP a α β j) : BP a (bα a ρ σ α) (bβ a ρ σ β) n := by
  unfold BP bβ
  rw [Finset.mul_sum]
  have step1 : ∀ j ∈ range (n + 1), rpoch (1 + a) (2 * n) * (bw a ρ σ n j * β j) =
      ∑ r ∈ range (j + 1), α r * (bw a ρ σ n j *
        rpoch (1 + a + ((2 * j : ℕ) : K)) (2 * (n - j)) *
        (rpoch (1 + a + (j : K) + r) (j - r) / ((j - r).factorial : K))) := by
    intro j hj
    have hjn : j ≤ n := by simp at hj; omega
    have hBP := h j hjn
    unfold BP at hBP
    rw [show 2 * n = 2 * j + 2 * (n - j) by omega, rpoch_add]
    calc rpoch (1 + a) (2 * j) * rpoch (1 + a + ((2 * j : ℕ) : K)) (2 * (n - j)) *
          (bw a ρ σ n j * β j)
        = bw a ρ σ n j * rpoch (1 + a + ((2 * j : ℕ) : K)) (2 * (n - j)) *
            (rpoch (1 + a) (2 * j) * β j) := by ring
      _ = _ := by
        rw [hBP, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => by ring)
  rw [Finset.sum_congr rfl step1]
  have flip := Finset.sum_range_diag_flip (n + 1) (fun r s => α r * (bw a ρ σ n (r + s) *
      rpoch (1 + a + ((2 * (r + s) : ℕ) : K)) (2 * (n - (r + s))) *
      (rpoch (1 + a + ((r + s : ℕ) : K) + r) (r + s - r) / ((r + s - r).factorial : K))))
  have lhs_eq : ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1), α r * (bw a ρ σ n j *
        rpoch (1 + a + ((2 * j : ℕ) : K)) (2 * (n - j)) *
        (rpoch (1 + a + (j : K) + r) (j - r) / ((j - r).factorial : K))) =
      ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1), α r * (bw a ρ σ n (r + (j - r)) *
        rpoch (1 + a + ((2 * (r + (j - r)) : ℕ) : K)) (2 * (n - (r + (j - r)))) *
        (rpoch (1 + a + ((r + (j - r) : ℕ) : K) + r) (r + (j - r) - r) /
          ((r + (j - r) - r).factorial : K))) := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r hr => ?_))
    have hrj : r ≤ j := by simp at hr; omega
    rw [Nat.add_sub_cancel' hrj]
  rw [lhs_eq, flip]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrn : r ≤ n := by simp at hr; omega
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hrn
  rw [show r + M + 1 - r = M + 1 by omega, ← Finset.mul_sum,
    bailey_inner a ρ σ r M hρ hσ]
  unfold bα
  push_cast
  ring

end Bailey

/-! ### 4. Chains: `m + 1` Bailey steps produce Andrews' multiple sum -/

section Chains

lemma snoc_mem_chains {m n j : ℕ} {i' : Fin m → ℕ} (hi' : i' ∈ chains m j) (hj : j ≤ n) :
    (Fin.snoc i' j : Fin (m + 1) → ℕ) ∈ chains (m + 1) n := by
  rw [mem_chains] at hi' ⊢
  obtain ⟨hv, hmono⟩ := hi'
  refine ⟨fun k => ?_, fun a b hab => ?_⟩
  · induction k using Fin.lastCases with
    | last => simp [Fin.snoc_last, hj]
    | cast k => simp only [Fin.snoc_castSucc]; exact (hv k).trans hj
  · induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact le_rfl
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact hv a
    | cast b =>
      induction a using Fin.lastCases with
      | last =>
        exfalso
        have h1 : (Fin.last m : ℕ) ≤ (Fin.castSucc b : ℕ) := hab
        simp at h1
        omega
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact hmono a b (Fin.castSucc_le_castSucc_iff.mp hab)

lemma init_mem_chains {m n : ℕ} {i : Fin (m + 1) → ℕ} (hi : i ∈ chains (m + 1) n) :
    Fin.init i ∈ chains m (i (Fin.last m)) := by
  rw [mem_chains] at hi ⊢
  obtain ⟨_, hmono⟩ := hi
  refine ⟨fun k => hmono _ _ (Fin.castSucc_lt_last k).le, fun a b hab => ?_⟩
  exact hmono _ _ (Fin.castSucc_le_castSucc_iff.mpr hab)

/-- Chains of length `m + 1` in `[0, n]`, sorted by their last entry `j`. -/
lemma sum_chains_succ {M : Type*} [AddCommMonoid M] (m n : ℕ) (f : (Fin (m + 1) → ℕ) → M) :
    ∑ i ∈ chains (m + 1) n, f i = ∑ j ∈ range (n + 1), ∑ i' ∈ chains m j, f (Fin.snoc i' j) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun i => ⟨i (Fin.last m), Fin.init i⟩) (fun p => Fin.snoc p.2 p.1)
    ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_sigma, Finset.mem_range]
    have hi' := hi
    rw [mem_chains] at hi'
    exact ⟨Nat.lt_succ_of_le (hi'.1 _), init_mem_chains hi⟩
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact snoc_mem_chains hp.2 (Nat.le_of_lt_succ hp.1)
  · intro i _
    simp [Fin.snoc_init_self]
  · intro p _
    simp [Fin.init_snoc, Fin.snoc_last]
  · intro i _
    simp [Fin.snoc_init_self]

lemma chainPrev_snoc_castSucc {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) (k : Fin m) :
    chainPrev (Fin.snoc i' j : Fin (m + 1) → ℕ) k.castSucc = chainPrev i' k := by
  unfold chainPrev
  simp only [Fin.val_castSucc]
  split_ifs with h
  · rfl
  · have : (⟨(k : ℕ) - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨(k : ℕ) - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]

lemma chainPrev_snoc_last {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) :
    chainPrev (Fin.snoc i' j : Fin (m + 1) → ℕ) (Fin.last m) = chainLast i' := by
  unfold chainPrev chainLast
  simp only [Fin.val_last]
  split_ifs with h
  · rfl
  · have : (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨m - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]

lemma chainLast_snoc {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) :
    chainLast (Fin.snoc i' j : Fin (m + 1) → ℕ) = j := by
  unfold chainLast
  simp only [Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
  exact Fin.snoc_last (α := fun _ => ℕ) (p := i') (x := j)

lemma chainLast_le {m N : ℕ} {i : Fin m → ℕ} (hi : i ∈ chains m N) : chainLast i ≤ N := by
  unfold chainLast
  split_ifs with h
  · exact Nat.zero_le _
  · exact (mem_chains.1 hi).1 _

variable {K : Type*} [Field K] [CharZero K]

/-- The `k`-th factor of the chain weight in Andrews' right side (verbatim from `Andrews_Stmt`). -/
def chainFactor (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (i : Fin m → ℕ) (k : Fin m) : K :=
  rpoch (1 + a - b k.castSucc - c k.castSucc) (i k - chainPrev i k) *
      rpoch (b k.succ) (i k) * rpoch (c k.succ) (i k) /
    (((i k - chainPrev i k).factorial : K) * rpoch (1 + a - b k.castSucc) (i k) *
      rpoch (1 + a - c k.castSucc) (i k))

/-- `β` after `m + 1` Bailey steps with the pairs `(b k, c k)` (applied in the order `k = 0, 1, …`),
as a chain sum. -/
def Bchain (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (n : ℕ) : K :=
  ∑ i ∈ chains m n, (∏ k : Fin m, chainFactor a b c i k) *
    (rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) (n - chainLast i) /
      (rpoch (1 + a - b (Fin.last m)) n * rpoch (1 + a - c (Fin.last m)) n *
        ((n - chainLast i).factorial : K)))

/-- `α` after `m + 1` Bailey steps. -/
def Achain (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (r : ℕ) : K :=
  (∏ k, rpoch (b k) r * rpoch (c k) r / (rpoch (1 + a - b k) r * rpoch (1 + a - c k) r)) *
    unitα a r

omit [CharZero K] in
lemma Achain_zero (a : K) (b c : Fin 1 → K) :
    Achain a b c = bα a (b 0) (c 0) (unitα a) := by
  funext r
  simp [Achain, bα]

omit [CharZero K] in
lemma Achain_succ (a : K) {m : ℕ} (b c : Fin (m + 2) → K) :
    Achain a b c = bα a (b (Fin.last (m + 1))) (c (Fin.last (m + 1)))
      (Achain a (Fin.init b) (Fin.init c)) := by
  funext r
  simp only [Achain, bα, Fin.prod_univ_castSucc, Fin.init]
  ring

omit [CharZero K] in
lemma Bchain_zero (a : K) (b c : Fin 1 → K) :
    Bchain a b c = bβ a (b 0) (c 0) unitβ := by
  funext n
  have hch : chains 0 n = {Fin.elim0} := by
    ext i
    simp only [Finset.mem_singleton]
    constructor
    · intro _; funext k; exact k.elim0
    · intro _; rw [mem_chains]; exact ⟨fun k => k.elim0, fun a _ _ => a.elim0⟩
  rw [Bchain, hch, Finset.sum_singleton, bβ, Finset.sum_eq_single 0]
  · simp [bw, unitβ, chainLast, rpoch_zero, Fin.last]
  · intro j _ hj
    simp [unitβ, hj]
  · intro h
    simp at h

omit [CharZero K] in
lemma Bchain_succ (a : K) {m : ℕ} (b c : Fin (m + 2) → K) :
    Bchain a b c = bβ a (b (Fin.last (m + 1))) (c (Fin.last (m + 1)))
      (Bchain a (Fin.init b) (Fin.init c)) := by
  funext n
  rw [Bchain, sum_chains_succ, bβ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Bchain, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [Fin.prod_univ_castSucc, chainLast_snoc]
  have hcast : ∀ k : Fin m, chainFactor a b c (Fin.snoc i' j) k.castSucc =
      chainFactor a (Fin.init b) (Fin.init c) i' k := by
    intro k
    simp only [chainFactor, Fin.snoc_castSucc, chainPrev_snoc_castSucc, Fin.init,
      Fin.succ_castSucc]
  simp only [hcast]
  simp only [chainFactor, bw, Fin.snoc_last, chainPrev_snoc_last, Fin.succ_last, Fin.init]
  ring

/-- `m + 1` Bailey steps from the unit pair: `(Achain, Bchain)` satisfies `BP` up to level `N`. -/
theorem bp_chain (a : K) (ha : a ≠ 0) (N : ℕ) : ∀ (m : ℕ) (b c : Fin (m + 1) → K),
    (∀ k, rpoch (1 + a - b k) N ≠ 0) → (∀ k, rpoch (1 + a - c k) N ≠ 0) →
    ∀ n ≤ N, BP a (Achain a b c) (Bchain a b c) n := by
  intro m
  induction m with
  | zero =>
    intro b c hb hc n hn
    rw [Achain_zero, Bchain_zero]
    exact bailey_step a (b 0) (c 0) (unitα a) unitβ n (rpoch_ne_zero_of_le _ (hb 0) hn)
      (rpoch_ne_zero_of_le _ (hc 0) hn) (fun j _ => bp_unit a ha j)
  | succ m ih =>
    intro b c hb hc n hn
    rw [Achain_succ, Bchain_succ]
    exact bailey_step a _ _ _ _ n (rpoch_ne_zero_of_le _ (hb _) hn)
      (rpoch_ne_zero_of_le _ (hc _) hn)
      (fun j hj => ih (Fin.init b) (Fin.init c) (fun k => hb _) (fun k => hc _) j (hj.trans hn))

end Chains

end CitedAndrews

open CitedAndrews in
/-- **Andrews' transformation** (Krattenthaler–Rivoal, Théorème 8; Andrews 1975 Thm 4 at
`q = 1`): proof of the cited hypothesis `Andrews_Stmt`. -/
theorem Andrews_proof : Andrews_Stmt := by
  intro K _ _ m N a b c ha hb hc hN hL
  have hBP := bp_chain a ha N m b c hb hc N le_rfl
  unfold BP at hBP
  have hNf := fact_ne (K := K) N
  -- left side `= N! / (1+a+N)_N · ∑_r α_r (1+a+N+r)_{N-r} / (N-r)!`
  have hLHS : ∑ κ ∈ range (N + 1),
        (a + 2 * κ) / a * (rpoch a κ / (κ.factorial : K)) *
        (∏ k, rpoch (b k) κ * rpoch (c k) κ / (rpoch (1 + a - b k) κ * rpoch (1 + a - c k) κ)) *
        (rpoch (-(N : K)) κ / rpoch (1 + a + N) κ) =
      (N.factorial : K) / rpoch (1 + a + N) N *
        ∑ r ∈ range (N + 1), Achain a b c r * rpoch (1 + a + N + r) (N - r) /
          ((N - r).factorial : K) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun κ hκ => ?_)
    have hκN : κ ≤ N := by simp at hκ; omega
    have hsplit : rpoch (1 + a + N) N = rpoch (1 + a + N) κ * rpoch (1 + a + N + κ) (N - κ) := by
      rw [← rpoch_add, Nat.add_sub_cancel' hκN]
    have hκ0 : rpoch (1 + a + N) κ ≠ 0 := rpoch_ne_zero_of_le _ hN hκN
    have hrest : rpoch (1 + a + N + κ) (N - κ) ≠ 0 := by
      intro h0; apply hN; rw [hsplit, h0, mul_zero]
    have hneg := rpoch_negN_mul (R := K) N κ hκN
    have hf1 := fact_ne (K := K) κ
    have hf2 := fact_ne (K := K) (N - κ)
    have hneg' : rpoch (-(N : K)) κ =
        (-1) ^ κ * (N.factorial : K) / ((N - κ).factorial : K) := by
      rw [eq_div_iff hf2, hneg]
    rw [hsplit, hneg']
    unfold Achain unitα
    field_simp
  -- right side `= N! (1+a)_N β_N`
  have hRHS : rpoch (1 + a) N * rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) N /
        (rpoch (1 + a - b (Fin.last m)) N * rpoch (1 + a - c (Fin.last m)) N) *
      ∑ i ∈ chains m N,
        rpoch (-(N : K)) (chainLast i) /
            rpoch (b (Fin.last m) + c (Fin.last m) - a - N) (chainLast i) *
          ∏ k : Fin m,
            rpoch (1 + a - b k.castSucc - c k.castSucc) (i k - chainPrev i k) *
                rpoch (b k.succ) (i k) * rpoch (c k.succ) (i k) /
              (((i k - chainPrev i k).factorial : K) * rpoch (1 + a - b k.castSucc) (i k) *
                rpoch (1 + a - c k.castSucc) (i k)) =
      (N.factorial : K) * rpoch (1 + a) N * Bchain a b c N := by
    unfold Bchain
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hl : chainLast i ≤ N := chainLast_le hi
    set l := chainLast i
    have hLl : rpoch (b (Fin.last m) + c (Fin.last m) - a - N) l ≠ 0 :=
      rpoch_ne_zero_of_le _ hL hl
    have hrefl := rpoch_reflect (1 + a - b (Fin.last m) - c (Fin.last m)) N l hl
    rw [show 1 - (1 + a - b (Fin.last m) - c (Fin.last m)) - (N : K) =
      b (Fin.last m) + c (Fin.last m) - a - N by ring] at hrefl
    have hneg := rpoch_negN_mul (R := K) N l hl
    have hf2 := fact_ne (K := K) (N - l)
    have hneg' : rpoch (-(N : K)) l = (-1) ^ l * (N.factorial : K) / ((N - l).factorial : K) := by
      rw [eq_div_iff hf2, hneg]
    have hx : rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) (N - l) =
        (-1) ^ l * rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) N /
          rpoch (b (Fin.last m) + c (Fin.last m) - a - N) l := by
      rw [eq_div_iff hLl, hrefl]
    have hbL := hb (Fin.last m)
    have hcL := hc (Fin.last m)
    rw [hneg', hx]
    simp only [chainFactor]
    field_simp
  -- `(1+a)_{2N} = (1+a)_N (1+a+N)_N`
  rw [hLHS, hRHS, ← hBP, show 2 * N = N + N by ring, rpoch_add]
  field_simp

end Zeta2

end
