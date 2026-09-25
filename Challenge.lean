import Mathlib

/-!
# At least one of the 2-adic zeta values ζ₂(7), ζ₂(9), ζ₂(11) is irrational

This is the statement to audit. It imports only Mathlib. The six definitions below are verbatim
copies of the first six definitions of `Zeta2Lean/Defs.lean` (same namespace, names, bodies,
docstrings, `open`s and `noncomputable section`). Comparator checks that they are identical to
the definitions used by the proof in `Solution.lean`. Two of the copied docstrings refer to the
proof development: `Stmt_JConv` is the first conjunct of the theorem below, and "proof.md" is the
informal proof `docs/proof.md`.

## The objects

* `ℚ_[2]` is Mathlib's field of 2-adic numbers.
* The Volkenborn integral `∫_{ℤ₂} f(t) dt` is the 2-adic limit of the Riemann sums
  `2^{-N} ∑_{x < 2^N} f(x)` (`volkenbornSum`). Only the values of `f` at natural numbers enter,
  so here `f` is a function on `ℕ`. `HasVolkenborn f I` says that these sums converge to `I`.
* `halfPow s x = (x + 1/2)^{-s}` and `J s = ∫_{ℤ₂} (t + 1/2)^{-s} dt`. The integral `volkenborn`
  is Mathlib's `limUnder`, which is an unspecified value when the limit does not exist. For this
  reason the theorem also states that the Riemann sums of `halfPow s` converge to `J s`, for
  every `s`.
* `zeta2 s = J (s - 1) / ((s - 1) 2^s)`.

## Relation to the Kubota–Leopoldt 2-adic zeta function (cited, not formalised)

For an integer `s ≥ 2` let `ζ₂(s) = L₂(s, ω^{1-s})`, where `L₂` is the Kubota–Leopoldt 2-adic
L-function and `ω` is the Teichmüller character. Lemma 2.8 of L. Lai, J. Sprang and W. Zudilin,
*A note on the irrationality of ζ₂(5)*, Int. Math. Res. Not. IMRN 2026, no. 16, rnag180
(arXiv:2505.05005), states that `(s - 1)⁻¹ ∫_{ℤ₂} (t + 1/2)^{1-s} dt = 2^s ζ₂(s)` for every
integer `s ≥ 2`, with the Volkenborn integral defined by the Riemann sums above. Hence
`zeta2 s = ζ₂(s)` for `s ≥ 2`. This identification is cited and is not formalised. Other
normalisations of ζ₂(s) in the literature differ from this one by a non-zero rational factor (for
example the Euler factor `(1 - 2^{-s})⁻¹`), which does not change whether the value is rational.

## The statement

`zeta2_7_9_11_not_all_rational_palomar`: for every `s`, the Riemann sums of `(x + 1/2)^{-s}`
converge in `ℚ_[2]` to `J s`; and `zeta2 7`, `zeta2 9`, `zeta2 11` are not all rational, that is,
they do not all lie in the image of `ℚ → ℚ_[2]`. So at least one of ζ₂(7), ζ₂(9), ζ₂(11) is
irrational.

L. Lai, *On the irrationality of certain 2-adic zeta values*, Int. J. Number Theory 21 (2025),
no. 1, 207–235 (arXiv:2304.00816), Theorem 1.1 with `s = 3`, proves that at least one of
ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13) is irrational. The statement here removes ζ₂(13). The literature
search recorded in `formalization.yaml` found no earlier statement of it, apart from unrefereed
drafts by C. D. Long that claim stronger results. It has not been refereed. `README.md`,
`docs/proof.md` and `formalization.yaml` give the proof, the sources and how the work was
produced.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-- Riemann sum `2^{-N} ∑_{x < 2^N} f x` of the Volkenborn integral. -/
def volkenbornSum (f : ℕ → ℚ_[2]) (N : ℕ) : ℚ_[2] :=
  ((2 : ℚ_[2]) ^ N)⁻¹ * ∑ x ∈ range (2 ^ N), f x

/-- `f` is Volkenborn integrable with integral `I`: the Riemann sums converge 2-adically to `I`. -/
def HasVolkenborn (f : ℕ → ℚ_[2]) (I : ℚ_[2]) : Prop :=
  Tendsto (volkenbornSum f) atTop (𝓝 I)

/-- The Volkenborn integral.  Only ever used together with a `HasVolkenborn` certificate
(`Stmt_JConv` proves convergence for every `J s`). -/
def volkenborn (f : ℕ → ℚ_[2]) : ℚ_[2] :=
  limUnder atTop (volkenbornSum f)

/-- `halfPow s x = (x + 1/2)^{-s}`, an element of `ℚ_[2]` (a 2-adic integer times `2^s`). -/
def halfPow (s x : ℕ) : ℚ_[2] :=
  ((x : ℚ_[2]) + 2⁻¹)⁻¹ ^ s

/-- `J s = ∫_{ℤ₂} (t + 1/2)^{-s} dt` (proof.md P2). -/
def J (s : ℕ) : ℚ_[2] :=
  volkenborn (halfPow s)

/-- The 2-adic zeta value, normalised by LSZ Lemma 2.8: `J_{s-1} = (s-1) 2^s ζ₂(s)` (`s ≥ 2`).
E.g. `zeta2 7 = J 6 / 768`, `zeta2 9 = J 8 / 4096`, `zeta2 11 = J 10 / 20480`. -/
def zeta2 (s : ℕ) : ℚ_[2] :=
  J (s - 1) / (((s : ℚ_[2]) - 1) * 2 ^ s)

/-- **At least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational.** For every `s`, the Riemann sums
`2^{-N} ∑_{x < 2^N} (x + 1/2)^{-s}` converge in `ℚ_[2]` to `J s`; and the 2-adic zeta values
`zeta2 7`, `zeta2 9`, `zeta2 11` are not all equal to rational numbers. -/
theorem zeta2_7_9_11_not_all_rational_palomar :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q)) := by
  sorry

end Zeta2

end
