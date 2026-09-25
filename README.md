# zeta2-lean

A Lean 4 + Mathlib formalisation of an unrefereed result that our literature search did not find stated
before (see *Novelty* below):

> **Theorem.** At least one of the 2-adic zeta values ζ₂(7), ζ₂(9), ζ₂(11) is irrational.

This sharpens L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235
(arXiv:2304.00816), Thm 1.1 with s = 3, which proves that at least one of ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13)
is irrational. Here ζ₂(13) is removed.

## What exactly is proved in Lean

```lean
-- Zeta2Lean/Cited/Main.lean
theorem Zeta2.zeta2_7_9_11_not_all_rational_unconditional : MainStatement

-- MainStatement (Zeta2Lean/Statements.lean):
--   (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
--     ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q))
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`, with no hypotheses. There is no `sorry`,
no `axiom` declaration and no `native_decide`. CI replays every module in the kernel with `leanchecker`.

The development has two layers:
* `Zeta2Lean/Main.lean` proves `zeta2_7_9_11_not_all_rational (hPNT : PNT_Stmt) (hAndrews : Andrews_Stmt)`,
  with the prime number theorem and Andrews' transformation as explicit hypotheses.
* `Zeta2Lean/Cited/` then proves both hypotheses:
  * **PNT** (`PNT_proof : PNT_Stmt`, i.e. ψ(x)/x → 1 with Mathlib's `Chebyshev.psi`) comes from the
    Wiener–Ikehara theorem. It is vendored under `Cited/Vendor/PNT/` from mathlib4 PRs #43046, #43233 and
    #43238 (head 78e1b2bbd0). That code is derived from the PrimeNumberTheoremAnd project, keeps its
    Apache-2.0 headers and authors, and was ported to this Mathlib pin.
  * **Andrews** (`Andrews_proof : Andrews_Stmt`, Krattenthaler–Rivoal Théorème 8 over any field of
    characteristic 0) is proved here, via the q = 1 Bailey chain and a polynomial Pfaff–Saalschütz
    identity with a Zeilberger certificate.

**Trusted definitions.** These are the only project definitions that occur in the statement
(`Zeta2Lean/Defs.lean`):
* `volkenbornSum f N = (2^N)⁻¹ * ∑_{x < 2^N} f x`, the Riemann sums of the Volkenborn integral on ℤ₂;
* `HasVolkenborn f I`, meaning `Filter.Tendsto (volkenbornSum f) atTop (𝓝 I)` in `ℚ_[2]`;
* `halfPow s x = (x + 1/2)^(-s)`;
* `J s = limUnder …` (the first conjunct of the theorem proves that this limit exists);
* `zeta2 s = J (s-1) / ((s-1) * 2^s)`.

**One cited identification, not formalised.** `zeta2 s` is defined through the Volkenborn integral. By
Lai–Sprang–Zudilin (IMRN 2026, rnag180; arXiv:2505.05005, Lemma 2.8), J(s−1) = (s−1)·2^s·ζ₂(s) for every
integer s ≥ 2, where ζ₂(s) = L₂(s, ω^{1−s}) is the Kubota–Leopoldt value; so `zeta2 s` = ζ₂(s). This
identification is cited, not formalised. It only involves the nonzero rational factor (s−1)·2^s, which does
not affect irrationality.

## The mathematics

The informal proof is in `docs/proof.md`. The construction is

R_n(t) = 2^{16n} (2t+n) (t+½)_n^8 / (t)_{n+1}^8,  S_n = −∫_{ℤ₂} R_n'''(t+½) dt = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9) + Z₁₁ ζ₂(11).

It is the case (a, j) = (8, 3) (eighth powers, third derivative) of a family that extends the Lai–Sprang–Zudilin
construction for ζ₂(5), which is the case (a, j) = (4, 1). The ingredients are:
* the one-power denominator saving (Andrews' transformation), which gives D_n = d_n^{12}/Φ_n = e^{11n+o(n)};
* coefficients bounded by poly(n)·2^{16n};
* the exact valuation v₂(S_n) = 32n + 14 − 11m along n = 2^m − 1 (Lai's dominant-term method, with one new
  identity);
* Lai's criterion.

The resulting exponent is 11 − 16 log 2 = −0.0904 < 0.

## Status and caveats

* **Unrefereed, produced by AI agents.** The mathematics (the construction and the informal proof) and this
  formalisation were produced by AI agents (Anthropic Claude models) under the direction of the maintainer,
  and have not been reviewed by a human expert (`formalization.yaml` describes the process). The Lean kernel
  checks the formal statement as displayed above. Whether that statement matches the mathematics is a matter
  of the trusted definitions and the cited identification listed here.
* **Novelty.** As of 2026-09-24 we found no prior statement of the {7, 9, 11} result in refereed work, arXiv,
  Zenodo, zbMATH, OpenAlex, Crossref or public talks and blogs; Google Scholar, MathSciNet and Lai's thesis
  were not searched, so novelty beyond this search is not established. Unrefereed GitHub drafts by
  C. D. Long (August 2026) claim irrationality of every ζ₂(s) with s odd and s ≤ 29, which would imply this
  result. We have not been able to verify their large-prime step.
* **Scope.** This method does not give "two of the three": the 2-adic Nesterenko ratio is
  22.18/22.09 = 1.004, and dimension 3 would need a ratio above 2.

## Layout

* `Zeta2Lean/Defs.lean`, `Zeta2Lean/Statements.lean`: definitions and the 24 lemma statements (`Stmt_*`).
* `Zeta2Lean/Assembly.lean`: the main theorem from the statements.
* `Zeta2Lean/Proofs/*.lean`: one proof obligation per file.
* `Zeta2Lean/Main.lean`: the theorem with the two hypotheses, and `#print axioms`.
* `Zeta2Lean/Cited/`: proofs of the two hypotheses and `Cited/Main.lean`, which contains the unconditional
  theorem. `Cited/Vendor/PNT/` is the vendored Wiener–Ikehara code (Apache-2.0). See `STATUS.md`.
* `BLUEPRINT.md`: statement map and dependency graph. `STATUS.md`: per-file census.
* `python/mirror.py`: an exact-arithmetic mirror of the definitions, with numerical checks of every statement.
* `scripts/`: `check.sh` (elaborate one file), `build.sh`, `audit.sh`.
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the statement, proof and metadata
  for [Comparator](https://github.com/leanprover/comparator) and the Palomar registry (next section).

## Challenge and Solution

`Challenge.lean` imports only Mathlib. It contains verbatim copies of the six trusted definitions of
`Zeta2Lean/Defs.lean` and states the theorem as `Zeta2.zeta2_7_9_11_not_all_rational_palomar`, with `sorry`.
`Solution.lean` proves the same statement from `zeta2_7_9_11_not_all_rational_unconditional`. `comparator.json`
asks Comparator to check that the two statements, and every definition they use, are identical, and that the
proof uses only `propext`, `Quot.sound` and `Classical.choice`. The toolchain (v4.35.0-rc2) ships `lake comparator`;
it needs `bwrap` (bubblewrap) for its sandbox. On 2026-09-25 the toolchain's `lake comparator`, run as Palomar runs
it (with the NanoDa and con-ron kernels besides Lean's), and leanprover/comparator built from source both accepted
`Solution.lean`; both runs were unsandboxed. An independent re-run of the Palomar-style check (also unsandboxed)
accepted it again. Altered copies of `Challenge.lean` were rejected: one with a changed theorem statement, and two
with a changed definition (`halfPow`, `zeta2`). `formalization.yaml` records the sources, the production process and
the review status.

## Building

```bash
lake exe cache get
lake build                                 # also builds Challenge and Solution
lake env lean Zeta2Lean/Cited/Main.lean   # prints the axioms of the unconditional theorem
lake comparator                            # judges Solution against Challenge (needs bwrap)
```

## Licence

Apache-2.0 (`LICENSE`). The vendored files under `Zeta2Lean/Cited/Vendor/PNT/` keep their upstream Apache-2.0
headers and authors.
