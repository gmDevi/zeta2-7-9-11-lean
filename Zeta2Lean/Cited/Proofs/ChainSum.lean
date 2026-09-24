import Zeta2Lean.Cited.Statements

/-!
# Chains sorted by their last entry (Andrews track)

**Task.** Prove `Stmt_SumChainsSucc`: for every additive commutative monoid `M`, all `m n : ℕ` and
`f : (Fin (m + 1) → ℕ) → M`,
```
∑ i ∈ chains (m + 1) n, f i = ∑ j ∈ range (n + 1), ∑ i' ∈ chains m j, f (Fin.snoc i' j).
```
No hypotheses.

**Informal proof.** The map `i ↦ ⟨i (last m), Fin.init i⟩` is a bijection from `chains (m+1) n`
onto the sigma-set `{⟨j, i'⟩ | j ≤ n, i' ∈ chains m j}`, with inverse `⟨j, i'⟩ ↦ Fin.snoc i' j`:
a monotone `i` with values `≤ n` has `init i` monotone with values `≤ i (last m)`, and
conversely (`init_mem_chains`, `snoc_mem_chains`, both proved in `Cited/Defs.lean`);
`Fin.snoc_init_self`, `Fin.init_snoc`, `Fin.snoc_last` give the two inverse laws.

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`, lines 525–544
(`sum_chains_succ`: `Finset.sum_sigma'` then `Finset.sum_nbij'` with the maps above);
`fun M _ m n f => sum_chains_succ m n f` was checked to typecheck against `Stmt_SumChainsSucc`.
Put helpers in `namespace Zeta2.Cited.ChainSum` (or make them `private`); only
`Zeta2.Cited.SumChainsSucc_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_SumChainsSucc` (exhaustive
bijection check and random weights, `m ≤ 4`, `n ≤ 5`).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

theorem SumChainsSucc_proof : Stmt_SumChainsSucc := by
  sorry

end Zeta2.Cited

end
