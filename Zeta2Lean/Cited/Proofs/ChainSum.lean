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

namespace ChainSum

/-- Chains of length `m + 1` in `[0, n]`, sorted by their last entry `j`: the map
`i ↦ ⟨i (last m), Fin.init i⟩` is a bijection onto the sigma-set `Σ j ≤ n, chains m j`, with
inverse `⟨j, i'⟩ ↦ Fin.snoc i' j` (Andrews scout, `docs/cited/AndrewsScout.lean`). -/
lemma sum_chains_succ {M : Type*} [AddCommMonoid M] (m n : ℕ) (f : (Fin (m + 1) → ℕ) → M) :
    ∑ i ∈ chains (m + 1) n, f i = ∑ j ∈ range (n + 1), ∑ i' ∈ chains m j, f (Fin.snoc i' j) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun i => ⟨i (Fin.last m), Fin.init i⟩) (fun p => Fin.snoc p.2 p.1)
    ?_ ?_ ?_ ?_ ?_
  · -- `i ↦ ⟨i (last m), init i⟩` maps chains into the sigma-set
    intro i hi
    simp only [Finset.mem_sigma, Finset.mem_range]
    have hi' := hi
    rw [mem_chains] at hi'
    exact ⟨Nat.lt_succ_of_le (hi'.1 _), init_mem_chains hi⟩
  · -- `⟨j, i'⟩ ↦ snoc i' j` maps the sigma-set into chains
    intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact snoc_mem_chains hp.2 (Nat.le_of_lt_succ hp.1)
  · -- left inverse: `snoc (init i) (i (last m)) = i`
    intro i _
    simp [Fin.snoc_init_self]
  · -- right inverse: `⟨(snoc i' j) (last m), init (snoc i' j)⟩ = ⟨j, i'⟩`
    intro p _
    simp [Fin.init_snoc, Fin.snoc_last]
  · -- the summands agree
    intro i _
    simp [Fin.snoc_init_self]

end ChainSum

theorem SumChainsSucc_proof : Stmt_SumChainsSucc := by
  exact fun M _ m n f => ChainSum.sum_chains_succ m n f

end Zeta2.Cited

end
