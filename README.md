# zeta2-lean

A Lean 4 + Mathlib formalisation of a new (unrefereed) result:

> **Theorem.** At least one of the 2-adic zeta values ζ₂(7), ζ₂(9), ζ₂(11) is irrational.

This sharpens L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235
(arXiv:2304.00816), Thm 1.1 with s = 3, which proves that at least one of ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13)
is irrational. Here ζ₂(13) is removed.

## What exactly is proved in Lean

```lean
theorem Zeta2.zeta2_7_9_11_not_all_rational (hPNT : PNT_Stmt) (hAndrews : Andrews_Stmt) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q))
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `axiom`
declaration and no `native_decide`. `leanchecker` replays the result in the kernel.

**Trusted definitions.** These are the only project definitions that occur in the statement
(`Zeta2Lean/Defs.lean`):
* `volkenbornSum f N = (2^N)⁻¹ * ∑_{x < 2^N} f x`, the Riemann sums of the Volkenborn integral on ℤ₂;
* `HasVolkenborn f I`, meaning `Filter.Tendsto (volkenbornSum f) atTop (𝓝 I)` in `ℚ_[2]`;
* `halfPow s x = (x + 1/2)^(-s)`;
* `J s = limUnder …` (the first conjunct of the theorem proves that this limit exists);
* `zeta2 s = J (s-1) / ((s-1) * 2^s)`.

**Cited hypotheses.** These are explicit theorem parameters, never axioms:
* `PNT_Stmt`: the prime number theorem, ψ(x)/x → 1, stated with Mathlib's `Chebyshev.psi`. It is proved in
  Lean in the PrimeNumberTheoremAnd project but is not in Mathlib. Only the upper bound
  ψ(x) ≤ (1+δ)x is used.
* `Andrews_Stmt`: Andrews' multiple-series transformation of terminating very-well-poised hypergeometric
  series (G. E. Andrews 1975, Thm 4; Krattenthaler–Rivoal, Mém. AMS 186 (2007), Théorème 8). It is stated
  as an identity over any field of characteristic 0. It was checked in exact arithmetic at about 550
  random parameter points, with m ≤ 8.

**One cited identification, not formalised.** `zeta2 s` is defined through the Volkenborn integral. By
Lai–Sprang–Zudilin (arXiv:2505.05005, Lemma 2.8) it equals the Kubota–Leopoldt value
ζ₂(s) = L₂(s, ω^{1−s}), up to the stated normalisation. That relation is a multiplication by a nonzero
rational factor, which does not affect irrationality.

## The mathematics

The informal proof is in `docs/proof.md`. The construction is

R_n(t) = 2^{16n} (2t+n) (t+½)_n^8 / (t)_{n+1}^8,  S_n = −∫_{ℤ₂} R_n'''(t+½) dt = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9) + Z₁₁ ζ₂(11).

It is the (a, j) = (8, 3) member of the Lai–Sprang–Zudilin family. The ingredients are:
* the one-power denominator saving (Andrews' transformation), which gives D_n = d_n^{12}/Φ_n = e^{11n+o(n)};
* coefficients bounded by poly(n)·2^{16n};
* the exact valuation v₂(S_n) = 32n + 14 − 11m along n = 2^m − 1 (Lai's dominant-term method, with one new
  identity);
* Lai's criterion.

The resulting exponent is 11 − 16 log 2 = −0.0904 < 0.

## Status and caveats

* **Unrefereed.** The proof and this formalisation were produced with AI assistance (Claude) and have not been
  reviewed by a human expert. The Lean kernel checks the formal statement as displayed above. Whether that
  statement matches the mathematics is a matter of the trusted definitions and cited hypotheses listed here.
* **Novelty.** As of 2026-09-24 we found no prior statement of the {7, 9, 11} result in refereed work, arXiv,
  Zenodo, zbMATH, OpenAlex, Crossref or public talks and blogs. Unrefereed GitHub drafts by C. D. Long
  (August 2026) claim irrationality of every ζ₂(s) with s odd and s ≤ 29, which would imply this result. We
  have not been able to verify their large-prime step.
* **Scope.** The result cannot give "two of the three": the 2-adic Nesterenko ratio is 22.18/22.09 = 1.004,
  and dimension 3 would need a ratio above 2.

## Layout

* `Zeta2Lean/Defs.lean`, `Zeta2Lean/Statements.lean`: definitions and the 24 lemma statements (`Stmt_*`).
* `Zeta2Lean/Assembly.lean`: the main theorem from the statements.
* `Zeta2Lean/Proofs/*.lean`: one proof obligation per file.
* `Zeta2Lean/Main.lean`: the final theorem and `#print axioms`.
* `BLUEPRINT.md`: statement map and dependency graph. `STATUS.md`: per-file census.
* `python/mirror.py`: an exact-arithmetic mirror of the definitions, with numerical checks of every statement.
* `scripts/`: `check.sh` (elaborate one file), `build.sh`, `audit.sh`.

## Building

```bash
lake exe cache get
lake build
lake env lean Zeta2Lean/Main.lean   # prints the axioms of the main theorem
```
