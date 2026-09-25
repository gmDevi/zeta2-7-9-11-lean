# Status: at least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational

Updated 2026-09-24 by the integrator after the first prove round of `Zeta2Lean/Cited/`, which discharges
the two cited hypotheses. The previous state is commit `ba5470c` (the Cited blueprint, with seven stubs).
The main development was completed in commit `e14030c` (prove round 1).

## Headline

* `bash scripts/build.sh Zeta2Lean` is **green** (8960 jobs, exit 0). All 24 proof files compile.
* `bash scripts/build.sh Zeta2Lean.Cited.Main` is **green** (8970 jobs, exit 0). All 12 `Cited/` modules
  compile, with no warnings.
* **0 `sorry`** across the project, `Cited/` included, and `scripts/audit.sh` finds **no forbidden
  construct**.
* The main theorem is proved from the two cited hypotheses, and both hypotheses are now proved as well.
  So the main theorem holds **unconditionally**:

```
'Zeta2.zeta2_7_9_11_not_all_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta2.zeta2_7_9_11_not_all_rational_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```lean
theorem Zeta2.zeta2_7_9_11_not_all_rational (hPNT : PNT_Stmt) (hAndrews : Andrews_Stmt) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q))

theorem Zeta2.zeta2_7_9_11_not_all_rational_unconditional : MainStatement :=
  zeta2_7_9_11_not_all_rational PNT_proof Andrews_proof
```

`MainStatement` (`Zeta2Lean/Statements.lean`) is exactly the conclusion of the first theorem. The
unconditional theorem is in `Zeta2Lean/Cited/Main.lean`, which the root `Zeta2Lean.lean` does not import
yet (see "Remaining integration steps" below).

## Discharging the cited hypotheses

`Zeta2Lean/Cited/` proves `PNT_Stmt` and `Andrews_Stmt` as theorems and applies the frozen
`zeta2_7_9_11_not_all_rational` to them. The blueprint is in `BLUEPRINT.md`, "Discharging the cited
hypotheses". The tree is **complete** after one prove round: all seven stubs are proved, and there is no
`sorry`. `bash scripts/build.sh Zeta2Lean.Cited.Main` prints:

```
'Zeta2.PNT_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta2.Andrews_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta2.zeta2_7_9_11_not_all_rational_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `PNT_Stmt` comes from the Wiener–Ikehara theorem, vendored verbatim from mathlib4 PR #43238 (head
  `78e1b2bbd0`, which contains PRs #43046 and #43233). Neither vendored file needed a drift fix for our
  pin.
* `Andrews_Stmt` comes from the `q = 1` Bailey chain with a polynomial Pfaff–Saalschütz identity. The
  five Andrews files follow the Andrews scout's compiled proof (`docs/cited/AndrewsScout.lean`).

### Per-file census (Cited)

All paths are under `Zeta2Lean/Cited/`.

| file | theorem : Stmt | deps (hypotheses) | sorry | lines | status |
|---|---|---|---|---|---|
| `Vendor/PNT/SchwartzCompactSupport` | `SchwartzMap.dense_hasCompactSupport` | – | 0 | 228 | done (vendored, PR #43046) |
| `Vendor/PNT/WienerIkehara` | `WienerIkehara.tendsto_sum_div` | (import) SchwartzCompactSupport | 0 | 777 | done (vendored, PR #43233) |
| `Proofs/WienerIkehara` | `WienerIkehara_proof : Stmt_WienerIkehara` | (import) vendored WI | 0 | 33 | done (wrapper, unchanged) |
| `Proofs/PfaffSaalschutz` | `PPS_proof : Stmt_PPS` | – | 0 | 221 | done |
| `Proofs/UnitPair` | `UnitPair_proof : Stmt_UnitPair` | – | 0 | 110 | done |
| `Proofs/BaileyLemma` | `BaileyLemma_proof : Stmt_PPS → Stmt_BaileyLemma` | PPS | 0 | 171 | done |
| `Proofs/ChainSum` | `SumChainsSucc_proof : Stmt_SumChainsSucc` | – | 0 | 72 | done |
| `Proofs/ChainStep` | `ChainStep_proof : Stmt_SumChainsSucc → Stmt_ChainStep` | SumChainsSucc | 0 | 115 | done |
| `Assembly` | `pnt_of_stmts`, `bpChain_of_stmts`, `andrews_of_bpChain`, `andrews_of_stmts` | – | 0 | 181 | done (blueprint, unchanged) |
| `Main` | `PNT_proof`, `Andrews_proof`, `zeta2_7_9_11_not_all_rational_unconditional` | all | 0 | 50 | done (wiring, unchanged) |

`Cited/Defs.lean` (259 lines) and `Cited/Statements.lean` (117 lines) are unchanged.

### How the files were proved (one line each; details in each file's docstring)

* **SchwartzCompactSupport** (vendored): the truncations `bumpR R • f` converge to `f` in every Schwartz
  seminorm, because the derivatives of the rescaled bump are `O(R^{-i})` and vanish on `‖x‖ < R`
  (Leibniz). Density follows.
* **WienerIkehara** (vendored): Fourier identities for the smoothed sums, `σ → 1⁺` by dominated
  convergence, then Riemann–Lebesgue. Density extends this from compactly supported to all Schwartz test
  functions, and smooth Urysohn cut-offs squeeze the sharp cut-off.
* **PfaffSaalschutz**: a Zeilberger certificate in any commutative ring (telescoping, with
  `linear_combination` in the middle case) gives the recurrence `(z+M) S(M+1) = c(M) S(M)`. Cancel in
  `K[X]` with `z := X`, then evaluate at `z`.
* **UnitPair**: the partial sums telescope (induction on `k`), and the last term cancels them.
* **BaileyLemma**: expand with the pair relation at each level `j ≤ n` and flip the triangular double
  sum (`Finset.sum_range_diag_flip`). The inner sum is Pfaff–Saalschütz at `x = ρ+r`, `y = σ+r`,
  `z = 1+a+2r`, `M = n-r`.
* **ChainSum**: the bijection `i ↦ ⟨i (last m), Fin.init i⟩`, with inverse `Fin.snoc`, onto a sigma-set
  (`Finset.sum_nbij'`).
* **ChainStep**: `achain_*` split off the last product factor (`Fin.prod_univ_castSucc`); `bchain_zero`
  uses `chains 0 n = {Fin.elim0}`; `bchain_succ` sorts the chains by their last entry (`hS`).

### Integrator checks (Cited round 1)

* **Build.** `bash scripts/build.sh Zeta2Lean` is green (8960 jobs). The twelve `Cited` modules, built
  as explicit targets, are green too (8970 jobs). Lake rebuilt only `Cited/Main` (86 s). Every other
  `Cited` module was already current: the provers built each one after its last source edit. Lake's
  stored build logs contain no warning or error for any `Cited` module. The only messages are the three
  `#print axioms` lines of `Cited/Main`.
* **Types and axioms.** A scratch file (since deleted) set `pp.fullNames` and checked the following:
  * `#check` prints `Zeta2.zeta2_7_9_11_not_all_rational_unconditional : Zeta2.MainStatement`;
  * `example : <deps> → Stmt_X := X_proof` type-checks for all six `Cited/Proofs` files, and so do
    `PNT_proof : PNT_Stmt` and `Andrews_proof : Andrews_Stmt`;
  * `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every one of them, and for
    `SchwartzMap.dense_hasCompactSupport`, `WienerIkehara.tendsto_sum_div`, `pnt_of_stmts` and
    `andrews_of_stmts`.
* **Kernel replay.** `leanchecker` replayed the declarations of each of the twelve `Cited` modules, one
  module at a time. All runs exit 0.
* **Frozen files.** `git diff` touches only the seven stub files, and no file was added or removed.
  * Unchanged since `e14030c`: `Defs`, `Statements`, `Assembly`, `Main`, `Proofs/`, the root
    `Zeta2Lean.lean`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.
  * Unchanged since `ba5470c`: `Cited/Defs`, `Cited/Statements`, `Cited/Assembly`, `Cited/Main` and
    `Cited/Proofs/WienerIkehara`.
* **Headers.** Each of the five Andrews files keeps the stub's `theorem X_proof` header (hypotheses and
  type) and only replaces `sorry`. Their helpers live in the files' own namespaces (`Zeta2.Cited.PPS`,
  `.UnitPair`, `.Bailey`, `.ChainSum`, `.ChainStep`). The vendored files keep the exported interface:
  the class `WienerIkehara`, `WienerIkehara.tendsto_sum_div` and `SchwartzMap.dense_hasCompactSupport`.
* **Meta-level constructs.** A grep of `Cited/` for `set_option`, `attribute`, `macro`, `syntax`,
  `elab`, `notation`, `instance`, `run_cmd`, `#eval`, `initialize`, `axiom`, `opaque`, `unsafe`,
  `implemented_by`, `extern` and `native_decide` finds two hits. Both are verbatim upstream code in the
  vendored `WienerIkehara`:
  * a file-local `Coe (E → ℝ) (E → ℂ)` instance;
  * `set_option backward.isDefEq.respectTransparency false in` on one lemma. It affects only the
    elaborator; the kernel still checks the result.
* **Statement issues.** None was reported (the Wiener–Ikehara prover reported "none" explicitly), and
  none was found. No `Cited` statement changed.
* **Provenance.** The byte-identity of the vendored files with PR #43238 is as recorded in their porting
  notes. The integrator did not download upstream again. Soundness does not depend on it: both files are
  kernel-checked, and only their proved statements are used.

### What the unconditional theorem depends on

1. **Lean kernel + Mathlib** (`v4.35.0-rc2`). Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
2. **Trusted definitions**, the only ones in `MainStatement` (`Defs.lean`): `volkenbornSum`,
   `HasVolkenborn`, `volkenborn`, `halfPow`, `J`, `zeta2`. `PNT_Stmt`, `Andrews_Stmt` and all of
   `Cited/`, the vendored Wiener–Ikehara code included, are now internal to the proof. If one of them
   were unfaithful, the proof would still be valid.
3. **The cited identification, not formalised**: `zeta2 s` is the Kubota–Leopoldt value (LSZ Lemma 2.8).
   See item 4 of the next section.

### Remaining integration steps (for the architect; not done in this round)

`BLUEPRINT.md`, "Workflow for provers (Cited)", lists these steps. They change the verified default
build and the public description, so the integrator left them alone:
* add `import Zeta2Lean.Cited.Main` to the root `Zeta2Lean.lean` and rebuild `Zeta2Lean`;
* drop the `grep -v '^Zeta2Lean/Cited/'` from the CI census, and add the unconditional theorem to the CI
  axiom check (optionally also `leanchecker Zeta2Lean.Cited.Main`);
* update `README.md`, which still calls `Zeta2Lean/Cited/` "work in progress" and lists the two cited
  hypotheses as open inputs.

## What the conditional main theorem (`Main.lean`) depends on

This list is for the frozen `zeta2_7_9_11_not_all_rational`, which takes the two cited hypotheses as
parameters. The unconditional theorem drops item 2, because both hypotheses are now proved (see "What
the unconditional theorem depends on" above).

1. **Lean kernel + Mathlib** (`v4.35.0-rc2`). Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
2. **Two cited hypotheses**, passed as theorem parameters (never as axioms):
   * `PNT_Stmt`: the prime number theorem `ψ(x)/x → 1` (Mathlib's `Chebyshev.psi`). Only `Asymptotic_proof`
     uses it. It is proved in Lean in PrimeNumberTheoremAnd but is not in this Mathlib.
   * `Andrews_Stmt`: Andrews' multiple-series transformation (Krattenthaler–Rivoal, Théorème 8), in full
     generality over any field of characteristic 0. Only `AndrewsApplied_proof` uses it, so it enters only the
     one-power denominator saving L2c.
3. **Trusted definitions**, the only ones that occur in the final statement (`Defs.lean`): `volkenbornSum`,
   `HasVolkenborn`, `volkenborn` (`limUnder`, certified by the first conjunct), `halfPow`, `J`, `zeta2`. The
   hypotheses also use `rpoch`, `chains`, `chainPrev`, `chainLast` and `Chebyshev.psi`.
   All other definitions (`rcoef`, `rho0`, `Z7`…`Z11`, `Dn`, `Tser`, `Fser`, `FJ0`, `leibTerm`, `domTerm`,
   `target`, …) are internal to the proof. If one of them were unfaithful to `proof.md`, the proof would
   still be valid.
4. **One cited identification, not formalised**: `zeta2 s = J(s-1)/((s-1)2^s)` is the Kubota–Leopoldt value
   `ζ₂(s) = L₂(s, ω^{1-s})` (LSZ Lemma 2.8). For odd `s`,
   `ζ₂(s) = (s-1)^{-1} ∫_{ℤ₂^×} x^{1-s} dx`, and the substitution `x = 2t+1` gives
   `2^{-s} J_{s-1}/(s-1)`. The relation is multiplicative, and a non-zero rational factor does not change
   irrationality.

## Per-file census (main development)

All files import only `Zeta2Lean.Statements` and prove exactly the blueprint type: `Zeta2Lean/Scratch/integrator_axioms.lean`
type-checked `example : <deps> → Stmt_X := X_proof` for every file (scratch since deleted). Every `X_proof`
has axioms `[propext, Classical.choice, Quot.sound]`.

| file | theorem : Stmt | deps (hypotheses) | sorry | lines | status |
|---|---|---|---|---|---|
| `JConvergence` | `JConv_proof : Stmt_JConv` | – | 0 | 217 | done |
| `Translation` | `Translation_proof : Stmt_Translation` | – | 0 | 148 | done |
| `Criterion` | `Criterion_proof : Stmt_Criterion` | – | 0 | 148 | done |
| `PartialFractions` | `PF_proof : Stmt_PF` | – | 0 | 408 | done |
| `CoeffVanish` | `CoeffVanish_proof : Stmt_CoeffVanish` | PF | 0 | 193 | done |
| `LinearForm` | `L1_proof : Stmt_L1` | JConv, Translation, CoeffVanish | 0 | 114 | done |
| `BuildingBlock` | `BlockF_proof : Stmt_BlockF` | – | 0 | 320 | done |
| `DenomL2a` | `L2a_proof : Stmt_L2a` | BlockF | 0 | 200 | done |
| `DenomL2b` | `L2b_proof : Stmt_L2b` | PF, L2a | 0 | 316 | done |
| `ResidueForm` | `ResidueForm_proof : Stmt_ResidueForm` | – | 0 | 237 | done |
| `AndrewsApplied` | `AndrewsApplied_proof : Stmt_AndrewsApplied` | **Andrews** (cited) | 0 | 574 | done |
| `ClosedFormFJ` | `FJClosed_proof : Stmt_FJClosed` | – | 0 | 299 | done |
| `KummerFJ` | `FJKummer_proof : Stmt_FJKummer` | – | 0 | 227 | done |
| `DenomL2c` | `L2c_proof : Stmt_L2c` | ResidueForm, AndrewsApplied, FJClosed, FJKummer | 0 | 317 | done |
| `DenomCor` | `L2cor_proof : Stmt_L2cor` | L2a, L2b, L2c | 0 | 147 | done |
| `ArchBound` | `L4_proof : Stmt_L4` | – | 0 | 361 | done (`Cst = 2^50`, `A = 3`) |
| `Asymptotics` | `Asymptotic_proof : Stmt_Asymptotic` | (**PNT** inside the statement) | 0 | 257 | done |
| `DeltaCalculus` | `Delta_proof : Stmt_Delta` | – | 0 | 220 | done |
| `DeltaFunctions` | `DeltaFun_proof : Stmt_DeltaFun` | Delta | 0 | 327 | done |
| `Digits` | `Digit_proof : Stmt_Digit` | – | 0 | 128 | done |
| `Leibniz` | `Leibniz_proof : Stmt_Leibniz` | PF | 0 | 327 | done |
| `LeibnizTermBound` | `LeibTermBound_proof : Stmt_LeibTermBound` | Delta, DeltaFun, Digit | 0 | 391 | done |
| `DominantTerm` | `L5Dom_proof : Stmt_L5Dom` | Delta, DeltaFun, Digit | 0 | 367 | done |
| `Nonvanishing` | `L5_proof : Stmt_L5` | Delta, Leibniz, LeibTermBound, L5Dom | 0 | 280 | done |
| `Assembly.lean` | `main_of_stmts : … → MainStatement` | JConv, L1, L2cor, L4, L5, Asymptotic, Criterion, PNT | 0 | – | done (blueprint) |
| `Main.lean` | `zeta2_7_9_11_not_all_rational` | PNT, Andrews | 0 | – | done |

`Defs.lean`, `Statements.lean`, `Assembly.lean` and `Main.lean` compile with 0 `sorry`. None of them was
changed in this round.

**Remaining helper statements: none.** No file contains a `sorry` or an auxiliary unproved lemma. The only
open inputs are the two cited hypotheses above.

The build has 47 warnings, all from Mathlib's style linters, in 15 of the proof files:
* lines over 100 characters;
* `show` that changes the goal, where `change` is meant;
* "missing space in the source";
* one flexible `simp at h`.

None of them affects correctness.

### How the files were proved (one line each; details in each file's docstring)

* **JConvergence**: `w(x) = (2x+1)^{-1}` is a unit. Odd power sums satisfy `‖∑_{x<2^N} w^k‖ ≤ 2^{-N}` by
  reflecting `x ↦ 2^{N+1}-1-x`, so consecutive Riemann sums differ by `≤ 2^{-N}` (a Cauchy sequence).
* **Translation**: exact difference-quotient algebra (`geom_sum₂_mul`) and continuity. No error bound needed.
* **Criterion**: common denominator `D`. A non-zero integer `z` has `‖z‖₂ |z| ≥ 1`, which gives `B_m‖L_m‖ ≥ 1/E`
  frequently.
* **PartialFractions**: polynomial divisibility at each pole (`ε^8 ∣ subst(-k)(Rnum - PFpoly)`), pairwise
  coprime `(X+k)^8`, and a degree count. The series form multiplies by an inverse.
* **CoeffVanish**: `rescale (-1)` symmetry of `Gser`. `c₁ = 0` from the coefficient of `t^{8n+7}`.
* **LinearForm**: linearity of `HasVolkenborn` with JConv and Translation. The c_even and c₁ terms vanish.
* **BuildingBlock**: Chu–Vandermonde for falling factorials. `4^m (t-1/2)^{\underline m}/m! ∈ ℤ` by Pascal
  induction. The `d`-integral series form a subring.
* **DenomL2a**: the `d_n`-integral subring. `n!/((1-ε)_k(1+ε)_{n-k})` is a binomial times geometric series.
* **DenomL2b**: q-local integrality for every prime `q` (the root identity from `Stmt_PF.series`).
* **ResidueForm**: an explicit series for `(x-ε)^{-5}`, then a reindex and exchange of the double sum.
* **AndrewsApplied**: works in `FractionRing ℚ⟦X⟧` with a locally supplied (proved) `CharZero` instance.
  `Andrews_Stmt` is applied at `m = 8`, `(b₈, c₈) = (1, 1+a+N)`, then pulled back along the injective
  algebra map.
* **ClosedFormFJ**: Pochhammer calculus, the reflection formula, and `(1/2)_m 4^m = C(2m,m) m!`, closed by
  `field_simp; ring`.
* **KummerFJ**: Lucas' theorem (`p ≤ 2(m mod p) ⇒ p ∣ C(2m,m)`), with residue bookkeeping in `ZMod p`.
* **DenomL2c**: the "tame" predicate `v_p([ε^j]F) ≥ v_p(F(0)) - j` is closed under products and inverses,
  and every linear factor of `Fser` is tame.
* **DenomCor**: `Φ_n ∣ d_n^{12}ρ₀` prime by prime (`Finset.prod_primes_dvd`). No valuations of `D_n` needed.
* **ArchBound**: the weighted ℓ¹ norm `∑_{j<8}|[X^j]f| 4^{-j}` is submultiplicative (an algebraic Cauchy
  estimate at radius 1/4).
* **Asymptotics**: `log D_n ≤ 11ψ(n) + C√n + …` (Mathlib's `ψ - θ ≤ C√x`). PNT with `δ = 1/400` gives decay
  `e^{-n/50}` eventually.
* **DeltaCalculus**: halving the Riemann sums, plus ultrametric bounds.
* **DeltaFunctions**: Vandermonde plus `‖C(2^L,i)‖ ≤ 2^{⌊log₂ N⌋-L}`. `h_β` is a polynomial in the odd
  reciprocals.
* **Digits**: `2^{s₂(a)} ≤ a+1` and `s₂(2^m-1) = m`, with `omega` for the rest.
* **Leibniz**: coefficient extraction in `ℚ⟦X⟧` (`coeff_prod`, `finsuppAntidiag`) and the `Y_l` factorisation.
* **LeibnizTermBound**: a `‖·‖ ≤ 2^{-e}` calculus. The exponent comparison is an identity closed by `ring`.
* **DominantTerm**: `v₂(K) = target + m` exactly. Odd central binomials (Lucas) and `‖∑ Φ‖ = 1` by the
  ultrametric equality.
* **Nonvanishing**: separate the dominant term from the rest, then use continuity of the norm along the
  convergent Riemann sums.

## Integrator checks (main development, prove round 1)

* `git diff cc3e1d7` touches only `Zeta2Lean/Proofs/*.lean`. `Defs`, `Statements`, `Assembly`, `Main`,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged, and no file was added or removed.
* Every `theorem X_proof` header (hypotheses and type) is identical to the stub's. Two files only switched to
  `where` structure syntax. `Main.lean` compiles against them.
* Grep of the proof files found none of the following: `set_option`, `elab`, `macro`, `syntax`,
  `run_cmd`, `#eval`, `instance` declarations, `axiom`, `opaque` or `unsafe`. The words "opaque" and
  "instance" appear only in docstrings. The one attribute is `attribute [local instance] charZero_KK` in
  AndrewsApplied, a proved `CharZero (FractionRing ℚ⟦X⟧)`.
* `AndrewsApplied` and `ResidueForm` (up to date, hence not rebuilt by lake) were re-elaborated with
  `scripts/check.sh`: exit 0.
* **Cited `Andrews_Stmt` re-tested** with a fresh literal Python transcription of the Lean text: 416 admissible
  points (m ∈ {0,1,2,3,4,8}, N ≤ 4; generic, integer and half-integer parameters, `b_k = c_k`), 0 failures.
  This matches the two earlier audits.
* No statement issues were reported by provers, so no statement fixes were needed.

## Scope: how far the result generalises (does it give two of the three?)

**No.** The formal conclusion is exactly `¬(ζ₂(7) ∈ ℚ ∧ ζ₂(9) ∈ ℚ ∧ ζ₂(11) ∈ ℚ)`, i.e.
`dim_ℚ span{1, ζ₂(7), ζ₂(9), ζ₂(11)} ≥ 2`.
"Two of the three are irrational" means that each of the pairs {7,9}, {7,11}, {9,11} contains an irrational.
One sequence of linear forms with Lai's criterion (`Stmt_Criterion`) cannot give this: if ζ₂(7) and ζ₂(9)
were rational, the forms would become forms in 1 and ζ₂(11) alone, which is consistent with ζ₂(11) being
irrational.

The ways around this do not work here:
* The margin is only `11 − 16 log 2 ≈ −0.09` per n, so there is no room to lose.
* Eliminating a constant by combining two forms (type II) costs far more than the margin. The
  smaller-sets exploration estimated a sketch cost of about +12 per n for (8,3).
* A symmetry of the half-shift family kills either all live constants or none (parity lemma, same
  exploration), so it cannot turn {7,9,11} into a pair.

For other (a, j), see `BLUEPRINT.md`, "Scope of the result": (6,3) {7,9} has exponent +0.68, and (10,3)
gives Lai's {7,…,13} again. The same exploration found a pair {ζ₂(7), ζ₂(9)} only in a different,
Rhin–Viola-shifted family, and only numerically: the growth rate, denominators and nonvanishing are unproven.
Even that would cover one of the three pairs needed.

Reuse of the Lean development:
* JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions and Digits do not depend on
  (a, j) = (8, 3).
* The DenomL2a argument works for any exponent `a`.
* The KummerFJ and DenomL2c arguments do not use `p ≥ 11`, according to their docstrings; that
  hypothesis only matches `Φ_n`.
* Everything else is hard-wired to (8, 3) and p = 2.

## Possible next steps (not required for the stated theorem)

* Discharge `PNT_Stmt` and `Andrews_Stmt`: **done** in `Zeta2Lean/Cited/` (see "Discharging the cited
  hypotheses" above). What is left is the integration listed there: the root import, CI and README.
* Once Mathlib contains PRs #43046 and #43233 and the project deliberately bumps Mathlib, delete
  `Cited/Vendor/` and import `Mathlib.NumberTheory.LSeries.WienerIkehara` in
  `Cited/Proofs/WienerIkehara.lean`. That file then compiles unchanged.
* Formalise LSZ Lemma 2.8 once a Kubota–Leopoldt ζ_p exists in Mathlib.
* Cosmetic: silence the style linters (long lines, `show` → `change`).
