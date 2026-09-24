import Zeta2Lean.Cited.Statements

/-!
# Zeta2Lean.Cited.Assembly — the two cited hypotheses from the sub-lemma statements

Complete, no gaps (like `Zeta2Lean/Assembly.lean`):

* `pnt_of_stmts : Stmt_WienerIkehara → PNT_Stmt` — Wiener–Ikehara applied to the von Mangoldt
  function (the residue class `0 mod 1`), with Mathlib's `LFunctionResidueClassAux`
  (`= -ζ'/ζ - 1/(s-1)` for `q = 1`, continuous on `re s ≥ 1`) and Chebyshev's bound
  `ψ x ≤ (log 4 + 4) x`.  This is `WeakPNT.lean` of mathlib4 PR #43238 (head `78e1b2bbd0`,
  `tendsto_residueClass_sum_div`, `tendsto_residueClass_sum_div_atTop`, `tendsto_psi_div_atTop`)
  with the Wiener–Ikehara theorem taken as the hypothesis `hWI`.
* `bpChain_of_stmts : Stmt_UnitPair → Stmt_BaileyLemma → Stmt_ChainStep → Stmt_BPChain` —
  induction on the number `m + 1` of Bailey steps.
* `andrews_of_bpChain : Stmt_BPChain → Andrews_Stmt` — both sides of `Andrews_Stmt` equal
  `N! (1+a)_N · Bchain_N`: the left side via `(-N)_κ (N-κ)! = (-1)^κ N!` and
  `(1+a+N)_N = (1+a+N)_κ (1+a+N+κ)_{N-κ}`, the right side via the reflection
  `(x)_{N-l} (1-x-N)_l = (-1)^l (x)_N`, and the middle by the Bailey-pair relation at level `N`
  with `(1+a)_{2N} = (1+a)_N (1+a+N)_N`.
* `andrews_of_stmts` — the composition.

Only the hypotheses of `Andrews_Stmt` are used: `a ≠ 0`, `(1+a-b_k)_N, (1+a-c_k)_N ≠ 0`,
`(1+a+N)_N ≠ 0`, `(b_L+c_L-a-N)_N ≠ 0`.  The Andrews part is the final section of the Andrews
scout's compiled proof (`docs/cited/AndrewsScout.lean`, `bp_chain` and `Andrews_proof`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Cited

/-! ## PNT -/

section PNT

open ArithmeticFunction.vonMangoldt Chebyshev Real

/-- Wiener–Ikehara for the von Mangoldt function restricted to the residue class `a` mod `q`:
the average of `residueClass a` over `[0, x]` tends to `(q.totient)⁻¹` (mathlib4 PR #43238,
`tendsto_residueClass_sum_div`, with the Wiener–Ikehara theorem as the hypothesis `hWI`). -/
theorem tendsto_residueClass_sum_div_of_WI (hWI : Stmt_WienerIkehara) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  refine hWI (residueClass a) (log 4 + 4) (q.totient : ℝ)⁻¹ (LFunctionResidueClassAux a)
    (fun N => ?_) (by positivity) (continuousOn_LFunctionResidueClassAux a) (fun s hs => ?_)
    (fun σ hσ => ?_) (residueClass_nonneg a)
  · calc
      _ ≤ ∑ i ∈ range N, Λ i := by
        simp_rw [abs_of_nonneg (residueClass_nonneg _ _)]
        grw [residueClass_le]
      _ ≤ (log 4 + 4) * N := by
        rcases eq_or_ne N 0 with rfl | h
        · simp
        grw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
          ← psi_eq_sum_Icc, psi_le_const_mul_self <| sub_nonneg_of_le <|
          Nat.one_le_cast_iff_ne_zero.mpr h, (by linarith : (N : ℝ) - 1 ≤ N)]
  · rw [eqOn_LFunctionResidueClassAux ha hs]
    push_cast
    ring
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hσ

/-- The weak prime number theorem in arithmetic progressions, from Wiener–Ikehara (mathlib4 PR
#43238, `ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop`). -/
theorem tendsto_residueClass_sum_div_atTop_of_WI (hWI : Stmt_WienerIkehara) {q a : ℕ}
    [NeZero q] (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, if n % q = a then Λ n else 0) / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply (tendsto_residueClass_sum_div_of_WI hWI ((ZMod.isUnit_iff_coprime a q).mpr ha)).congr
  simp [residueClass, Set.indicator_apply, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']

/-- **The prime number theorem** `ψ(x)/x → 1`, from the Wiener–Ikehara theorem (the `q = 1`
case; mathlib4 PR #43238, `Chebyshev.tendsto_psi_div_atTop`). -/
theorem pnt_of_stmts (hWI : Stmt_WienerIkehara) : PNT_Stmt := by
  unfold PNT_Stmt
  simpa [Nat.mod_one, Nat.totient_one, psi_eq_sum_Icc] using
    tendsto_residueClass_sum_div_atTop_of_WI hWI (q := 1) (a := 0) (by simp) one_pos

end PNT

/-! ## Andrews -/

/-- `m + 1` Bailey steps from the unit pair: `(Achain, Bchain)` is a Bailey pair up to level
`N` (induction on `m`; the Bailey lemma needs the relation at all levels `j ≤ n`). -/
theorem bpChain_of_stmts (hU : Stmt_UnitPair) (hB : Stmt_BaileyLemma) (hC : Stmt_ChainStep) :
    Stmt_BPChain := by
  intro K _ _ a ha N m
  induction m with
  | zero =>
    intro b c hb hc n hn
    rw [hC.achain_zero K a b c, hC.bchain_zero K a b c]
    exact hB K a (b 0) (c 0) (unitα a) unitβ n (rpoch_ne_zero_of_le _ (hb 0) hn)
      (rpoch_ne_zero_of_le _ (hc 0) hn) (fun j _ => hU K a ha j)
  | succ m ih =>
    intro b c hb hc n hn
    rw [hC.achain_succ K a m b c, hC.bchain_succ K a m b c]
    exact hB K a _ _ _ _ n (rpoch_ne_zero_of_le _ (hb _) hn) (rpoch_ne_zero_of_le _ (hc _) hn)
      (fun j hj => ih (Fin.init b) (Fin.init c) (fun k => hb _) (fun k => hc _) j (hj.trans hn))

/-- **Andrews' transformation** from the chain Bailey pair at level `N`:
`LHS = N! (1+a)_N · Bchain_N = RHS`. -/
theorem andrews_of_bpChain (hBPC : Stmt_BPChain) : Andrews_Stmt := by
  intro K _ _ m N a b c ha hb hc hN hL
  have hBP := hBPC K a ha N m b c hb hc N le_rfl
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

/-- **Andrews' transformation** from the sub-lemma statements. -/
theorem andrews_of_stmts (hU : Stmt_UnitPair) (hB : Stmt_BaileyLemma) (hC : Stmt_ChainStep) :
    Andrews_Stmt :=
  andrews_of_bpChain (bpChain_of_stmts hU hB hC)

end Zeta2.Cited

end
