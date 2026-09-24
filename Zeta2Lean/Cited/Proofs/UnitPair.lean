import Zeta2Lean.Cited.Statements

/-!
# The unit Bailey pair (Andrews track)

**Task.** Prove `Stmt_UnitPair`: in every field `K` of characteristic zero, for `a ≠ 0` and every
`n`, `BP a (unitα a) unitβ n`, i.e.
```
(1+a)_{2n} [n = 0] = ∑_{r=0}^{n} (a+2r)/a (a)_r (-1)^r / r! · (1+a+n+r)_{n-r} / (n-r)!.
```
No hypotheses.

**Informal proof.** `n = 0`: both sides are `1` (`(a+0)/a = 1`).  `n = n'+1`: the right side
vanishes.  Telescoping: for `k ≤ n'`, the partial sum `∑_{r ≤ k}` equals
```
T(k) = (-1)^k (1+a)_k (1+a+n+k)_{n-k} / (k! (n'-k)! n)          (n = n'+1)
```
(induction on `k`: `T(k) + term(k+1) = T(k+1)`, using `(a)_{k+1} = a (1+a)_k`,
`(1+a+n+k)_{n-k} = (1+a+n+k) (1+a+n+k+1)_{n-k-1}` and `field_simp; ring`).  At `k = n'` the last
term `r = n` cancels `T(n')` exactly.  Only `a ≠ 0` and `r! ≠ 0` are divided by; `(1+a)_k` may
vanish (e.g. `a = -1`), which is harmless since the relation is multiplied out.

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`, lines 328–382
(`unit_partial`, `bp_unit`); `UnitPair_proof := fun K _ _ a ha n => bp_unit a ha n` was checked
to typecheck against `Stmt_UnitPair`.  `BP`, `unitα`, `unitβ`, `fact_ne` and the Pochhammer API
(`rpoch_zero`, `rpoch_succ`, `rpoch_succ'`) are in `Cited/Defs.lean` with the same names and
bodies: do not redeclare them.  Put helpers in `namespace Zeta2.Cited.UnitPair` (or make them
`private`); only `Zeta2.Cited.UnitPair_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_UnitPair` (generic and
degenerate `a`, including `a ∈ {-1, -2, -3, -1/2, -3/2}`, `n ≤ 10`).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

namespace UnitPair

variable {K : Type*} [Field K] [CharZero K]

/-- Partial sums of the unit-pair sum at level `N = n' + 1` (telescoping):
`∑_{r ≤ k} unitα a r (1+a+N+r)_{N-r} / (N-r)! = (-1)^k (1+a)_k (1+a+N+k)_{N-k} / (k! (n'-k)! N)`
for `k ≤ n'`. -/
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

end UnitPair

theorem UnitPair_proof : Stmt_UnitPair := by
  intro K _ _ a ha n
  exact UnitPair.bp_unit a ha n

end Zeta2.Cited

end
