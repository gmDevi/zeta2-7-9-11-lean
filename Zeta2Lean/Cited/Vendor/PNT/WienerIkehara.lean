/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
import Mathlib
import Zeta2Lean.Cited.Vendor.PNT.SchwartzCompactSupport

/-!
# The Wiener–Ikehara Tauberian theorem (VENDORED — currently a stub)

**Provenance.** `Mathlib/NumberTheory/LSeries/WienerIkehara.lean` of leanprover-community/mathlib4
PR #43233 (Wiener–Ikehara, adapted from the PrimeNumberTheoremAnd project), in the version
contained in PR #43238 at head `78e1b2bbd0d256081c926fccada84fd084653286` (fork
`teorth/mathlib4`; PR base: master `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`, Lean
`v4.34.0-rc2`).  Raw source: `https://raw.githubusercontent.com/leanprover-community/mathlib4/`
followed by `<head>/Mathlib/NumberTheory/LSeries/WienerIkehara.lean`.
Licence: Apache 2.0, see `LICENSE` in this directory (copied from Mathlib).  Upstream's copyright
header above is kept.  (PR #43233's own head is `41648e636503fd0a1e6f865c9774b055eeec2e35`; use
the #43238 version, whose external API uses were checked against our pin by the PNT scout.)

**Exported interface (used by `Cited/Proofs/WienerIkehara.lean`, must not change):** the class
`WienerIkehara` below (fields verbatim from upstream) and
`WienerIkehara.tendsto_sum_div [WienerIkehara] :
  Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A)`.

**Task (porter).** Replace this stub by the upstream file, verbatim except for these header edits:
delete the `module` line; replace all `public import` / `import` lines by `import Mathlib` and
`import Zeta2Lean.Cited.Vendor.PNT.SchwartzCompactSupport` (upstream imports
`Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport`, which is not in our pin); delete
`@[expose] public section` (keep `noncomputable section`).  Keep every declaration name verbatim
(`SchwartzMap.Q`, `WienerIkehara.S`, `lim_S_one_fourier_schwartz`, `tendsto_sum_div_smooth`,
`exists_cutoff`, `tendsto_sum_range_div`, `tendsto_sum_div`, …; `private` ones stay `private`):
none of them exists in our Mathlib pin (`065356127b`, Lean `v4.35.0-rc2`).  Keep
`set_option backward.isDefEq.respectTransparency false in` (still valid on `v4.35.0-rc2`).  The
only use of the other vendored file is `SchwartzMap.dense_hasCompactSupport.inter_open_nonempty`
(in the extension from compactly supported to Schwartz test functions); until
`SchwartzCompactSupport.lean` is ported, its stub provides that theorem with the final statement,
so both files can be ported in parallel.
Fix drift errors locally (expect `simp`/`grind`/`grw`/`field_simp`/`convert` changes from the
Lean `v4.34.0-rc2 → v4.35.0-rc2` bump; all upstream API names were checked to exist in our pin);
record each deviation in a "Porting notes" list in this docstring.  Fallback for a stubborn
lemma: the corresponding lemma of PrimeNumberTheoremAnd `Wiener.lean` (commit `55270df807`:
`limiting_fourier*`, `wiener_ikehara_smooth*`, `WienerIkeharaInterval*`, `WienerIkeharaTheorem'`).
Forbidden: proof placeholders and every construct flagged by `scripts/audit.sh`.

**Informal proof (upstream outline).** For a test function `φ` put
`S σ φ x = ∑' n, f n n^{-σ} φ(log(n/x)/(2π)) - A x^{1-σ} ∫_{-log x}^∞ e^{-u(σ-1)} φ(u/(2π)) du`.
Both halves are Fourier integrals (`sum_term_mul_fourier_eq`, `integral_exp_mul_fourier_eq`); the
pole cancels and `S` is an integral of `G(σ + it) φ̂(t) x^{it}`
(`sum_term_mul_sub_mul_integral_eq`).
Letting `σ → 1⁺` (dominated convergence, `G` continuous on `re s ≥ 1`) and then `x → ∞`
(Riemann–Lebesgue) gives `S 1 φ̂ x → 0`, first for compactly supported `φ`, then for all Schwartz
`φ` by density (`dense_hasCompactSupport`) and a uniform bound from `∑_{i<n} |f i| ≤ C n`.
Surjectivity of the Fourier transform on `𝓢(ℝ, ℂ)` gives the smoothed theorem
`∑ f n ψ(n/x) / x → A ∫_0^∞ ψ` (`tendsto_sum_div_smooth`); non-negativity of `f` and smooth
Urysohn cut-offs `1_{[b,c]} ≤ ψ ≤ 1_{(a,d)}` (`exists_cutoff`) squeeze the sharp cut-off, giving
`∑_{n<N} f n / N → A` (`tendsto_sum_range_div`) and the real-variable form `tendsto_sum_div`.

**Check.** `bash scripts/check.sh Zeta2Lean/Cited/Vendor/PNT/WienerIkehara.lean` (needs the
olean of the other vendored file:
`bash scripts/build.sh Zeta2Lean.Cited.Vendor.PNT.SchwartzCompactSupport`), then
`bash scripts/build.sh Zeta2Lean.Cited.Proofs.WienerIkehara`: the wrapper
`Zeta2.Cited.WienerIkehara_proof : Stmt_WienerIkehara` must still compile unchanged against the
ported class and theorem (it builds the instance with named fields).
-/

noncomputable section

open ArithmeticFunction hiding log
open Complex hiding log
open Real BigOperators MeasureTheory Filter Set FourierTransform LSeries Asymptotics SchwartzMap
  Function
open scoped Topology ContDiff ComplexConjugate

/- Upstream declares this coercion before the class; it is what makes `LSeries f s` (with
`f : ℕ → ℝ`) elaborate to `LSeries (fun n ↦ (f n : ℂ)) s`. -/
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n ↦ f n⟩

/-- The data and hypotheses for the Wiener--Ikehara theorem.  Can be conveniently accessed inside
the `WienerIkehara` namespace by adding a `[WienerIkehara]` instance.

The `hf` hypothesis can be derived from `bound`, and `bound` and `hA` are in fact redundant; but
implementing these simplifications is non-trivial, and the hypotheses can usually be easily
verified from existing API in practice anyway. -/
class WienerIkehara where
  /-- The function being estimated. -/
  f : ℕ → ℝ
  /-- The constant in the Chebyshev-type bound. -/
  C : ℝ
  bound : ∀ n, ∑ i ∈ .range n, |f i| ≤ C * n
  /-- The asymptotic constant. -/
  A : ℝ
  hA : 0 ≤ A
  /-- The continuous extension of `s ↦ LSeries f s - A / (s - 1)` to `re s ≥ 1`. -/
  G : ℂ → ℂ
  hG : ContinuousOn G {s | 1 ≤ s.re}
  hG' : EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}
  hf : ∀ (σ : ℝ), 1 < σ → LSeriesSummable f σ
  hpos : 0 ≤ f

namespace WienerIkehara

variable [WienerIkehara]

/-- The *Wiener-Ikehara Tauberian Theorem* (real cutoff version) -/
theorem tendsto_sum_div : Tendsto (fun x : ℝ ↦ (∑ n ∈ .Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  sorry

end WienerIkehara
