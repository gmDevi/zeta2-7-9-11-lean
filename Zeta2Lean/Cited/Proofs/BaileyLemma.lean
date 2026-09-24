import Zeta2Lean.Cited.Statements

/-!
# Bailey's lemma at `q = 1` (Andrews track)

**Task.** Prove `Stmt_BaileyLemma` from `Stmt_PPS` (hypothesis `hP`): in a field of
characteristic zero, if `BP a α β j` for all `j ≤ n` and `(1+a-ρ)_n, (1+a-σ)_n ≠ 0`, then
`BP a (bα a ρ σ α) (bβ a ρ σ β) n`, where
`bα a ρ σ α r = (ρ)_r (σ)_r / ((1+a-ρ)_r (1+a-σ)_r) · α_r` and
`bβ a ρ σ β n = ∑_{j ≤ n} (ρ)_j (σ)_j (1+a-ρ-σ)_{n-j} / ((1+a-ρ)_n (1+a-σ)_n (n-j)!) · β_j`.

**Informal proof.** Write `w_j = bw a ρ σ n j`.  Split `(1+a)_{2n} = (1+a)_{2j} (1+a+2j)_{2(n-j)}`
(`rpoch_add`) and substitute `BP(j)` for `(1+a)_{2j} β_j`:
```
(1+a)_{2n} β'_n = ∑_{j ≤ n} ∑_{r ≤ j} α_r · w_j (1+a+2j)_{2(n-j)} (1+a+j+r)_{j-r} / (j-r)!.
```
Exchange the sums (`Finset.sum_range_diag_flip`, `j = r + s`), and for fixed `r`, with
`M = n - r`, the inner sum over `s ≤ M` is the factorial form of Pfaff–Saalschütz
```
∑_{s=0}^{M} (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} / (s! (M-s)!) = (z-x)_M (z-y)_M (z+M)_M / M!
```
at `x = ρ+r`, `y = σ+r`, `z = 1+a+2r` (so `z-x-y = 1+a-ρ-σ`), times
`(ρ)_r (σ)_r / ((1+a-ρ)_{r+M} (1+a-σ)_{r+M})`; with `(1+a-ρ)_{r+M} = (1+a-ρ)_r (1+a-ρ+r)_M`
(both factors non-zero, `rpoch_ne_zero_of_le`, `right_ne_zero_of_mul`) it collapses to
`bα a ρ σ α r · (1+a+n+r)_{n-r} / (n-r)!`, which is the `r`-th term of `BP(n)` for the new pair.
The factorial form follows from `hP` by `Nat.cast_choose` and `field_simp` (divide by `M!`).

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`: `pps_div` (lines 291–305,
there proved from `pps_field`; here derive it from `hP K x y z M`, whose left side is the
explicit sum), `bailey_inner` (396–440), `bailey_step` (442–486);
`fun K _ _ a ρ σ α β n hρ hσ h => bailey_step a ρ σ α β n hρ hσ h` was checked to typecheck
against `Stmt_BaileyLemma`.  `BP`, `bw`, `bα`, `bβ`, `fact_ne`, `rpoch_add`,
`rpoch_ne_zero_of_le` are in `Cited/Defs.lean` with the same names and bodies.  Put helpers in
`namespace Zeta2.Cited.Bailey` (or make them `private`); only `Zeta2.Cited.BaileyLemma_proof`
is exported.

**Lean hints.** `Finset.sum_range_diag_flip`, `Finset.mul_sum`, `Finset.sum_congr`,
`Nat.exists_eq_add_of_le`, `Nat.add_sub_cancel_left`, `Nat.add_sub_add_left`, `Nat.cast_choose`,
`eq_div_iff`, `field_simp`, `push_cast`, `ring`.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_BaileyLemma` (random `α`
with `β` solved from `BP`, and degenerate `a` with `α` from the unit/chain pairs).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

namespace Bailey

variable {K : Type} [Field K] [CharZero K]

/-- Pfaff–Saalschütz with factorial denominators (characteristic zero), from the polynomial form
`hP`: divide `hP K x y z M` by `M!` and use `C(M,s) = M! / (s! (M-s)!)`. -/
theorem pps_div (hP : Stmt_PPS) (x y z : K) (M : ℕ) :
    ∑ s ∈ range (M + 1), rpoch x s * rpoch y s * rpoch (z - x - y) (M - s) *
        rpoch (z + s) (2 * M - s) / ((s.factorial : K) * ((M - s).factorial : K)) =
      rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M / (M.factorial : K) := by
  have h := hP K x y z M
  have hM : (M.factorial : K) ≠ 0 := fact_ne M
  rw [eq_div_iff hM, Finset.sum_mul, ← h]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s ≤ M := by simp at hs; omega
  rw [Nat.cast_choose K hs']
  have h1 : (s.factorial : K) ≠ 0 := fact_ne s
  have h2 : ((M - s).factorial : K) ≠ 0 := fact_ne (M - s)
  field_simp

/-- The inner sum of Bailey's lemma is a Pfaff–Saalschütz sum (`x = ρ+r`, `y = σ+r`,
`z = 1+a+2r`, `M = n-r`). -/
lemma bailey_inner (hP : Stmt_PPS) (a ρ σ : K) (r M : ℕ)
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
  have hPd := pps_div hP (ρ + r) (σ + r) (1 + a + 2 * r) M
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
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, hPd]
  rw [Nat.add_sub_cancel_left, rpoch_add (1 + a - ρ) r M, rpoch_add (1 + a - σ) r M,
    show 1 + a + 2 * (r : K) - (ρ + r) = 1 + a - ρ + r by ring,
    show 1 + a + 2 * (r : K) - (σ + r) = 1 + a - σ + r by ring,
    show 1 + a + 2 * (r : K) + M = 1 + a + ((r + M : ℕ) : K) + r by push_cast; ring]
  have h3 := fact_ne (K := K) M
  field_simp

/-- **Bailey's lemma** (`q = 1`, polynomial normalisation), from polynomial Pfaff–Saalschütz. -/
theorem bailey_step (hP : Stmt_PPS) (a ρ σ : K) (α β : ℕ → K) (n : ℕ)
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
    bailey_inner hP a ρ σ r M hρ hσ]
  unfold bα
  push_cast
  ring

end Bailey

theorem BaileyLemma_proof (hP : Stmt_PPS) : Stmt_BaileyLemma := by
  exact fun _ _ _ a ρ σ α β n hρ hσ h => Bailey.bailey_step hP a ρ σ α β n hρ hσ h

end Zeta2.Cited

end
