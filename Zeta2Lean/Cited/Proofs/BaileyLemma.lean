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

theorem BaileyLemma_proof (hP : Stmt_PPS) : Stmt_BaileyLemma := by
  sorry

end Zeta2.Cited

end
