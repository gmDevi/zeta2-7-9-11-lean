import Zeta2Lean.Cited.Statements

/-!
# Polynomial Pfaff–Saalschütz (Andrews track)

**Statement.** `Stmt_PPS`: for every field `K`, all `x y z : K` and `M : ℕ`,
```
∑_{s=0}^{M} C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} = (z-x)_M (z-y)_M (z+M)_M.
```
No hypotheses.  (It is an identity in `ℤ[x,y,z]`; the field version is all that is needed.)

**Proof (Zeilberger certificate).** Let `F(M,s)` be the summand, `S(M) = ∑_s F(M,s)`,
`R(M)` the right side and `c(M) = (z-x+M)(z-y+M)(z+2M)(z+2M+1)`.  With the certificate
`G(M,0) = 0`, `G(M,s+1) = -(z+2M+1) C(M,s) (x)_{s+1} (y)_{s+1} (z-x-y)_{M-s} (z+s)_{2M+1-s}`:
1. *Telescoping* (`pps_tele`): `(z+M) F(M+1,s) - c(M) F(M,s) = G(M,s+1) - G(M,s)` for
   `s ≤ M+1`.  Cases `s = 0` and `s = M+1` close by `ring` after peeling `rpoch_succ`; the
   middle case `s = u+1`, `M = u+1+t` is `linear_combination λ * hrel` in the atoms
   `X = (x)_{u+1}`, `Y = (y)_{u+1}`, `P = (z-x-y)_t`, `Z = (z+u+1)_{u+2t+1}`, `C1 = C(M,u+1)`,
   `C2 = C(M,u)`, with the binomial relation `hrel : (u+1) C1 = (t+1) C2`
   (`Nat.choose_succ_right_eq`) and `λ = P X Y Z (x+y-z-t) (z+2u+2t+2) (z+2u+2t+3)`.
2. *Recurrence* (`pps_rec`): summing over `s ≤ M+1` (`Finset.sum_range_sub`, `G(M,M+2) = 0`,
   `F(M,M+1) = 0`): `(z+M) S(M+1) = c(M) S(M)` in every commutative ring.  `R` satisfies the
   same recurrence (`pps_rhs_rec`, from `rpoch_succ`, `rpoch_succ'`).
3. *Cancellation* (`pps_domain`, `pps_field`): in the domain `K[X]` with `z := X`, `X + M ≠ 0`
   (`Polynomial.X_add_C_ne_zero`), so induction on `M` with `mul_left_cancel₀` gives `S = R`
   there; evaluate at `z` (`Polynomial.evalRingHom`, `map_rpoch`).

**Provenance.** Copied from the Andrews scout's complete, compiled proof
(`docs/cited/AndrewsScout.lean`, section `PPS`, lines 120–289), with identical bodies.  The
Pochhammer API it uses (`rpoch_zero`, `rpoch_one`, `rpoch_succ`, `rpoch_succ'`, `map_rpoch`) is
the one of `Cited/Defs.lean`.  All helpers live in `namespace Zeta2.Cited.PPS`; only
`Zeta2.Cited.PPS_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_PPS`; the scout's symbolic
check of the certificate is `docs/cited/pps_certificate.py` (needs sympy).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

namespace PPS

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

end PPS

theorem PPS_proof : Stmt_PPS := by
  intro K _ x y z M
  exact PPS.pps_field x y z M

end Zeta2.Cited

end
