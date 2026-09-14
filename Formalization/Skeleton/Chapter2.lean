/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Family
import SpatialLine.TransformUniqueness
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The target types of Chapter 2 — preliminaries

**This file carries `sorry`s and is not part of the `SpatialLine` library.** Statement-skeleton
campaign, phase A (2026-09-08): the whole blueprint is typed before any proof is attempted, so
that the design decisions are taken once, visibly, and the remaining work is countable rather
than estimated. The design record is `Formalization/SKELETON.md`.

## What writing this chapter down found

**1. Two of the chapter's four transform interfaces are covered by Mathlib, and one of them is
covered *exactly* where the article spends it.** `prop:fourier-uniqueness` (ledger A5) is
`MeasureTheory.Measure.ext_of_charFun`, verbatim for finite measures on `ℝ`. `prop:levy-continuity`
(ledger A6) has two clauses, and the *first* — the limit is known to be a transform — is
`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`. Reading the article's *uses*
rather than its statement: `thm:main-characterization`(⇐) and `prop:two-members`(1) both invoke
the continuity theorem with the limit already known (`μ̂_{s_n,t_n} → μ̂_{s,t}` by continuity of
`F`), so the first clause is the whole of the article's consumption. The second clause needs
tightness (`isTightMeasureSet_of_tendsto_charFun`, also Mathlib) plus Prokhorov plus an
identification, and is a real but bounded piece of work. Both are recorded here as
**demotable to [T] via Mathlib**; changing the nodes' `\statusA` is a review decision and is not
taken here.

> **Taken 2026-09-09 (proving campaign).** The author's decision on the review's Q2 demotes both
> nodes. `SpatialLine.fourier_uniqueness` and `SpatialLine.levy_continuity` are proved; ledger
> A5 and A6 are retired, kept for the record and grounding no node; the general clause of
> `prop:levy-continuity` had no consumer and became `rem:levy-continuity-general`. Neither
> demotion put a name on `blueprint/trust-boundary.txt`.

**2. Bochner and Schoenberg are not in Mathlib, and neither is positive definiteness of a
function on a group.** A search of `Mathlib/Analysis/Fourier/` and
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/` turns up `charFun`, `charPoly` and the
character machinery, but no positive-definite predicate and no Bochner theorem. So A1–A4 stay
where the ledger puts them, and `IsPositiveDefinite` had to be defined here (`SpatialLine/
Exponent.lean`).

**3. The `ν`-side of the Lévy–Khintchine pair is a measure on `ℝ` carrying `IsFolded`, not a
measure on a subtype.** The folding convention of the chapter — a symmetric Lévy measure on
`ℝ ∖ {0}` written as its image under `x ↦ |x|` — is a statement about pushforwards, and dilation
of a Lévy measure (used throughout Chapter 7) is a pushforward too. A subtype `Ioi 0` would put
a coercion in the way of both.

## Conventions in this file

* `charFun` is Mathlib's `∫ exp (ωx i) ∂μ`, the **opposite sign convention** to the blueprint's
  `(2.1)`. Every use here is either sign-insensitive (uniqueness, the value `1`, continuity) or
  is about a symmetric measure, where the two transforms agree and are real. `fourierCos` is the
  article's own object; `fourierCos_eq_charFun_re` is the bridge.
* Weak convergence is spelled out as convergence of the integrals of bounded continuous
  functions, rather than through `ProbabilityMeasure`'s topology, because that is the form the
  `ε/3` argument in `thm:main-characterization` consumes.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology ComplexOrder

/-! ## The bridge to Mathlib's characteristic function

**PROVED AND MOVED (2026-09-09).** `fourierCos_eq_charFun_re` and
`charFun_eq_fourierCos_of_symmetric` are now `SpatialLine.fourierCos_eq_charFun_re` and
`SpatialLine.charFun_eq_fourierCos_of_symmetric`, in `SpatialLine/TransformBridge.lean`, with
`SpatialLine.integrable_charFun_integrand` beside them. Both were priced **S** and both cost
**S**; the only Lean friction was that `RCLike.re` and `Complex.re` are not syntactically the
same head symbol, so `integral_re` needs `RCLike.re_to_complex` on either side of it.
-/

/-! ## `prop:fourier-toolbox` (draft Proposition 2.3) — ledger A1–A4

Class (b): the four clauses correspond one to one with the causal `prop:bernstein-toolbox`, and
so do the ledger entries, but no declaration can be shared — the theorems are different.

The node is split one declaration per clause, and clause (3) further into existence, converse
and uniqueness, because the three are spent in different places and at different prices: the
blueprint's own annotation says uniqueness is spent in `lem:selfdecomposable-exponents`,
`prop:choquet-cone`, `thm:matern` and `thm:scale-locality`, and the converse in
`thm:increments-levy` and `thm:main-characterization`(⇐).

**Interface.** Each is a ledger interface: it enters `SpatialLine/Interfaces.lean` and the
trust boundary only when a proof consumes it. Never an `axiom` before then.

> **2026-09-09 (proving campaign).** One clause has been admitted: the **converse**, clause (3),
> is now `SpatialLine.fourier_toolbox_levy_converse` — an `axiom` with this file's type verbatim,
> on `blueprint/trust-boundary.txt`, with ledger **A3**'s `**Lean:**` line naming it. Its only
> consumer is `SpatialLine.profile_integrability_mem`. The other eight clauses are admitted
> nowhere; the `sorry`'d declarations below stay as the statement record.
-/

/-- **`prop:fourier-toolbox`(1), Bochner** — interface, ledger **A1**.

Reading: stated for Mathlib's `charFun`, whose sign convention is the opposite of `(2.1)`; the
statement is an equivalence over *all* probability measures and is therefore insensitive to it
(replace `μ` by its reflection).

What A1's citation carries: exactly this equivalence, for probability measures on `ℝ`
(@sato1999levy Prop. 2.5(i), p. 8). It carries nothing about finite non-probability measures and
nothing about the folding convention.

Class (b) — twin `prop:bernstein-toolbox`(1), causal ledger A1 (Bernstein–Widder), no Lean decl.
Cost **L (interface)**: Mathlib has no Bochner theorem and no positive-definite predicate for
functions on a group, so proving it is a Mathlib-scale project, not a node. -/
theorem fourier_toolbox_bochner (φ : ℝ → ℂ) :
    (Continuous φ ∧ IsPositiveDefinite φ ∧ φ 0 = 1)
      ↔ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ charFun μ = φ := by
  sorry

/-- **`prop:fourier-toolbox`(1), the symmetric leg** — interface, ledger **A1**.

Reading: "it is the transform of a *symmetric* probability measure if and only if moreover `φ`
is real, equivalently even" is stated for a real-valued `φ` throughout, and the transform is the
article's `fourierCos`. The "equivalently even" of the blueprint is not a separate clause: for a
transform, real and even are the same condition, and that is the content of
`charFun_eq_fourierCos_of_symmetric` above.

What A1's citation carries: the source gives that a measure is symmetric iff its transform is
real; the ledger entry records that the reduction of "real" to "even" is elementary and ours.

Class (b). Cost **L (interface)**, as above. -/
theorem fourier_toolbox_bochner_symm (φ : ℝ → ℝ) :
    (Continuous φ ∧ IsPositiveDefinite (fun ω => (φ ω : ℂ)) ∧ φ 0 = 1)
      ↔ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ fourierCos μ = φ := by
  sorry

/-- **`prop:fourier-toolbox`(2), Schoenberg** — interface, ledger **A2**.

Reading: the equivalence between the *exponential* form (which `IsSymNegDef` takes as primitive)
and the *kernel* form, under the standing hypotheses the blueprint states — `ψ` continuous, even,
nonnegative, `ψ(0) = 0`. Those hypotheses are repeated on the left of the iff because
`IsSymNegDef` bundles them; on the right they are genuine hypotheses.

What A2's citation carries (@schilling2012bernstein Def. 4.3 and Prop. 4.4, p. 36): exactly this
equivalence. The blueprint's third formulation — "equivalently, by clause (1), `e^{-τψ}` is the
transform of a symmetric probability measure" — is A1 applied to the exponential, not A2, and is
not restated here.

Class (b) — twin: the causal side's "`e^{-τg}` completely monotone for every `τ`", causal ledger
A2. Cost **L (interface)**: needs the kernel-form theory Mathlib does not have. -/
theorem fourier_toolbox_schoenberg (ψ : ℝ → ℝ) (hcont : Continuous ψ)
    (heven : ∀ ω, ψ (-ω) = ψ ω) (hnonneg : ∀ ω, 0 ≤ ψ ω) (hzero : ψ 0 = 0) :
    IsSymNegDef ψ ↔ IsNegDefKernel ψ := by
  sorry

/-- **`prop:fourier-toolbox`(3), existence** — interface, ledger **A3**.

Reading: every member of `NDₛ` *is* a member of `LEₛ`, i.e. is given by some `SymLevyPair`. The
folding to `(0,∞)` is built into `SymLevyPair` and is the part A3 does **not** carry: the source
(@sato1999levy Thm. 8.1(iii), pp. 37–38) states the representation on `ℝ` with a centering term
and a Lévy measure on `ℝ ∖ {0}`, and the reduction — the centering term vanishes by symmetry,
the two halves are added under `x ↦ |x|` — is the blueprint's own, written out under "The
folding convention". That reduction is where the factor 2 of the profile lives.

Class (b). Cost **L (interface)** for the citation; **L** for the reduction if it were ever
formalised separately, which the blueprint's proof of record covers. -/
theorem fourier_toolbox_levy_exists {ψ : ℝ → ℝ} (h : IsSymNegDef ψ) : IsSymLevyExponent ψ := by
  sorry

/-- **`prop:fourier-toolbox`(3), the converse** — interface, ledger **A3**.

Reading: every pair defines a member of `NDₛ`. This is the direction `thm:increments-levy`'s last
step and `thm:main-characterization`(⇐) consume, and it is the direction that has to be spent to
know that a constructed exponent is the exponent of a probability measure at all.

Cost **L (interface)**. -/
theorem fourier_toolbox_levy_converse (P : SymLevyPair) : IsSymNegDef P.exponent := by
  sorry

/-- **`prop:fourier-toolbox`(3), uniqueness of the pair** — interface, ledger **A3**.

Reading: two pairs with the same exponent *function on all of `ℝ`* have the same Gaussian
coefficient and the same Lévy measure — equality of measures on `ℝ`, which is meaningful because
both are `IsFolded` and therefore determined by their restriction to `(0,∞)`.

This is A3's workhorse clause: `lem:selfdecomposable-exponents`((1) ⟹ (3)) spends it once, and
so do `prop:choquet-cone`, `thm:matern` and `thm:scale-locality`.

Cost **L (interface)**. -/
theorem fourier_toolbox_levy_unique (P Q : SymLevyPair)
    (h : ∀ ω, P.exponent ω = Q.exponent ω) : P.a = Q.a ∧ P.ν = Q.ν := by
  sorry

/-- **`prop:fourier-toolbox`(4), the cone** — interface, ledger **A4**.

Reading: `NDₛ` is closed under sums and nonnegative scalar multiples.

Class (b). Cost **M (interface)**; `trust-boundary.txt` records the expectation that A4 never
reaches the boundary, because `thm:increments-levy` extracts the representation directly and the
cone is used only in `lem:admissible-cone`, where it is proved from the *representation* rather
than from the class. -/
theorem fourier_toolbox_cone {ψ₁ ψ₂ : ℝ → ℝ} (h₁ : IsSymNegDef ψ₁) (h₂ : IsSymNegDef ψ₂) :
    IsSymNegDef (fun ω => ψ₁ ω + ψ₂ ω) ∧ ∀ c : ℝ, 0 ≤ c → IsSymNegDef (fun ω => c * ψ₁ ω) := by
  sorry

/-- **`prop:fourier-toolbox`(4), closure of the kernel form** — interface, ledger **A4**.

Reading: in the kernel form the class is closed under pointwise limits **with no proviso**. The
proviso-free statement is exactly what distinguishes this clause from the next one, and it is
why the two are separate declarations.

Cost **M (interface)**. -/
theorem fourier_toolbox_kernel_closed {ψ : ℕ → ℝ → ℝ} {ψ' : ℝ → ℝ}
    (h : ∀ n, IsNegDefKernel (ψ n))
    (hlim : ∀ ω, Tendsto (fun n => ψ n ω) atTop (𝓝 (ψ' ω))) : IsNegDefKernel ψ' := by
  sorry

/-- **`prop:fourier-toolbox`(4), closure with the continuity proviso** — interface, ledger **A4**.

Reading: the limit is asked only to be continuous *at the origin*; that it is then continuous
everywhere, and even, nonnegative and zero at the origin — the other fields of `IsSymNegDef` —
is part of the conclusion, not of the hypothesis. The proviso "is what the line costs against
the half-line, where pointwise limits suffice" (the node's annotation), and it is the same
proviso as in A6.

Cost **M (interface)**. -/
theorem fourier_toolbox_closure {ψ : ℕ → ℝ → ℝ} {ψ' : ℝ → ℝ}
    (h : ∀ n, IsSymNegDef (ψ n)) (hlim : ∀ ω, Tendsto (fun n => ψ n ω) atTop (𝓝 (ψ' ω)))
    (hcont : ContinuousAt ψ' 0) : IsSymNegDef ψ' := by
  sorry

/-! ## `prop:fourier-uniqueness` and `prop:levy-continuity` (additive) — the Q2 demotion

**PROVED AND MOVED (2026-09-09).** Both nodes were `[A]`, on ledger **A5** and **A6**; the
author's decision answering the statement review's Q2 demotes both to `[T]`, and both are now
proved in `SpatialLine/TransformUniqueness.lean`:

* `SpatialLine.fourier_uniqueness` — `MeasureTheory.Measure.ext_of_charFun` plus a `funext`.
  Priced **S**, cost **S** (one line).
* `SpatialLine.levy_continuity` — `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`
  read through `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. Priced **S**/**M**
  depending on whether the `ProbabilityMeasure` packaging fought back; it did not, so **S**:
  the subtype is built from the measure and its instance and both `charFun` coercions are `rfl`.

`levy_continuity_of_continuousAt` — the general clause, in which the limit function is only
assumed continuous at the origin — is **withdrawn, not moved**. Reading the `\uses` edges of the
four consumers of `prop:levy-continuity` (`prop:two-members`(1), `thm:main-characterization`,
`prop:matern-density`, `prop:thorin-machine`) confirms what phase A's finding predicted for two
of them: every one applies the theorem with the limit law already in hand. The clause has no
consumer, so it leaves the statement and becomes `rem:levy-continuity-general` in the blueprint;
ledger A6 is retired with A5. Should a later chapter want it, Mathlib's
`isTightMeasureSet_of_tendsto_charFun` is the tightness half and the rest is a Prokhorov
extraction and a `Measure.ext_of_charFun`, priced **M** then and **M** now.
-/

/-! ## `prop:laplace-uniqueness-locally-finite` (additive) — [T]

**PROVED AND MOVED (2026-09-09)** to `SpatialLine/LaplaceUniqueness.lean`, as
`SpatialLine.laplace_uniqueness_locally_finite`, together with the whole route it needs:
`expNeg` and its measurable-embedding lemmas, `ext_of_moments`,
`laplaceL_injective_of_isFiniteMeasure`, `laplaceL_withDensity_expNeg` and
`laplaceL_injective_of_ne_top`. Lean core alone.

Priced **S** ("port, or zero if the declaration moves to `ScaleSpaceCore` first") and cost
**S**: the port is `Hemigroup/Injectivity.lean` with `IsCausal` replaced by `IsFolded` and one
proof step changed, the step where the causal hypothesis `t < 0` becomes `t ≤ 0`. Two notes for
the abstraction:

* The file is a **core candidate** in the strongest sense: nothing in it mentions symmetry, the
  Fourier transform or a cascade, and the two copies now differ in exactly one predicate. Lifting
  it should take the carrier set as a parameter, not the two predicates.
* Paper I's real-valued `laplace` was **not** ported. `SpatialLine/Transform.lean` carries only
  the `ℝ≥0∞`-valued `laplaceL`, and the one place a Bochner integral is needed — the moment
  identity — is served by the unconditional bridge `integral_exp_neg_eq_toReal_laplaceL`. So this
  chapter adds no vocabulary.
-/

/-! ## `lem:quadratic-growth` (additive, rerouted) — [T]

**PROVED AND MOVED (2026-09-09)** to `SpatialLine/Growth.lean`, as
`SpatialLine.SymLevyPair.quadratic_growth`, `SpatialLine.SymLevyPair.quadratic_growth_isBigO`
and the helper `SpatialLine.SymLevyPair.exponentL_ne_top`, with two auxiliary finiteness lemmas
(`lintegral_sq_div_two_ne_top`, `measure_Ioi_one_ne_top`) that the constant needs. Lean core
alone.

Priced **S** ("three lines of mathematics and perhaps thirty of `ℝ≥0∞` bookkeeping") and cost
**S**: about forty lines, of which the mathematics is `Real.one_sub_sq_div_two_le_cos` and
`Real.neg_one_le_cos`. Two things cost more than expected and are worth recording, because both
recur in every `ℝ≥0∞` statement of this development. First, splitting a `lintegral` against a
folded measure at the truncation needs the *measure* restricted to `(0,∞)` to be recovered
first (`Measure.restrict_eq_self_of_ae_mem` from `ν_folded`) before `lintegral_union` applies;
the split is not `Ioc 0 1 ∪ Ioi 1` of the ambient line. Second, `gcongr` handles the three
`a·x ≤ a·y` steps that `mul_le_mul_left'` would, and is not deprecated.
-/


/-! ## `lem:lattice-zero` (draft Remark 2.4, promoted) — [T]

**PROVED AND MOVED (2026-09-09)**, all seven declarations, to `SpatialLine/LatticeZero.lean`,
together with two helpers: `sin_eq_zero_of_cos_eq_one` and — the one the whole node turns on —
`charFun_eq_one_iff`. A third, `integrable_cos`, was deduplicated at the wave-1 merge against the
same statement in chapters 4 and 5, and is `integrable_cos_mul` in
`SpatialLine/TransformBridge.lean`. Lean core alone.

Priced **S–M** and cost **S–M**, at the low end. What the writing found:

* **The trichotomy was priced "M if Mathlib's classification of closed additive subgroups of `ℝ`
  is directly usable, L if the dense-but-not-all case has to be excluded by hand". It is
  directly usable and the case is one line.** `AddSubgroup.dense_or_cyclic` gives dense-or-cyclic
  for any subgroup of an archimedean linearly ordered group, and a dense *closed* set is `univ`
  by `IsClosed.closure_eq`. The lookup the estimate was waiting on cost ten minutes and removed
  the only **L** risk in the chapter. What did cost something is the *cyclic* branch: the
  generator Mathlib produces is an arbitrary real, and the node's `c > 0` needs `|a|`, so the
  identity `zmultiples a = zmultiples (-a)` has to be supplied by hand (`n ↦ -n`); Mathlib's
  `Subgroup.zpowers_inv` has no additive form under the name one would guess.
* **Two hypotheses of the reviewed statements are not consumed**, and both are deliberate rather
  than defects — see the report. `lattice_zero_exponent` does not use `hψ : IsSymNegDef ψ`: the
  conclusion follows from the transform identity alone, and `hψ` is in the statement because the
  blueprint's sentence is "if `μ` is symmetric with `μ̂ = e^{-ψ}` for some `ψ ∈ NDₛ`".
  `lattice_zero_example_lattice` does not use `hc : 0 < c`: at `ω₀ = 2π` the exponent vanishes
  whatever `c` is, and at `c = 0` the law is `δ₀`, which is carried by `ℤ` too.
* **The `[0,1]`-valued clause needed one fact the blueprint's proof leaves implicit.** The
  example's law is only known through its *cosine* transform, and the zero set is stated for
  `charFun`; for a measure not known to be symmetric those differ. The bridge is that a
  probability measure's transform has modulus at most one, so a real part of `1` forces the value
  `1` — `norm_charFun_le_one` plus one `nlinarith`. The blueprint proof of record is not wrong,
  it simply reads `μ̂` as the article's real transform throughout.
-/


/-! ## `prop:sd-exponents` (draft Proposition 2.6) — ledger A7 -/

/-- **`prop:sd-exponents`** — interface, ledger **A7**.

Reading: the law is quantified over: any symmetric probability measure whose cosine transform is
`e^{-P.exponent}` for a given pair `P`. Self-decomposability is then equivalent to `P.ν` being
the profile measure of some nonincreasing `k` with the two integrability conditions — that is, to
`P` coming from an `SDProfile` with the same Gaussian coefficient.

The blueprint's closing sentence, "self-decomposability imposes no restriction on the Gaussian
coefficient `a`", is a *reading of this equivalence* — whose right-hand side constrains `ν`
alone — and not a further clause; no declaration corresponds to it, and none should.

What A7's citation carries: the whole equivalence, for symmetric infinitely divisible laws on
`ℝ`. What it does **not** carry: anything this development consumes. The profile form is obtained
independently in `lem:selfdecomposable-exponents`, from the dilation identity and a convex-tail
argument, and every later node cites that one. This is the single place where the spatial trust
base is narrower than the causal one, and it should stay so.

Class (b) — **status inversion**: the causal article consumes its twin (causal ledger A18), this
one does not. Cost **L (interface)**, and it lies on no proof path. -/
theorem sd_exponents (P : SymLevyPair) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) (h : ∀ ω, fourierCos μ ω = Real.exp (-P.exponent ω)) :
    IsSelfDecomposable μ ↔ ∃ Q : SDProfile, Q.a = P.a ∧ P.ν = profileMeasure Q.k := by
  sorry

/-! ## `lem:profile-integrability` (additive) — [T] -/

/-! ## `lem:profile-integrability` (additive) — [T]

**PROVED AND MOVED (2026-09-09)** to `SpatialLine/ProfileIntegrability.lean`, as
`SpatialLine.profile_integrability` and `SpatialLine.profile_integrability_mem`, with two
helpers: `isFolded_profileMeasure` and `exponentL_eq_of_profileMeasure`.

Priced **S** and cost **S**; the Lean cost was the `withDensity` rewriting, as predicted, and
the mathematics was one `field_simp`. Three findings:

* The node's "consequently" clause is **split**, into `profile_integrability_pair` (the Lévy
  pair, Lean core) and `profile_integrability_mem` (the bundle, which adds membership of `NDₛ`).
  `profile_integrability_mem` is the **only declaration of chapter 2 that spends a ledger
  interface**: `SpatialLine.fourier_toolbox_levy_converse`, ledger **A3**, admitted as an axiom
  in `SpatialLine/Interfaces.lean` and named on `blueprint/trust-boundary.txt`. The split is
  what makes the two `#print axioms` lines say which half of the node the boundary pays for.
* `SDProfile` carries **no measurability field**, and `profile_integrability` needs one. It is
  not missing: `k_antitone` supplies it, through
  `aemeasurable_restrict_of_antitoneOn measurableSet_Ioi`. This is the one place `k_antitone` is
  consumed in the chapter — and it is consumed for measurability, not for monotonicity, which is
  exactly the distinction the node's own hypothesis archaeology draws.
* The blueprint writes the near-origin condition over `Ioo 0 1` and the Lévy condition splits
  the line at `Ioc 0 1`; the two differ by the Lebesgue-null point `{1}`, which is
  `Ioo_ae_eq_Ioc`. Nothing is lost, but a statement has to pick, and this one picks `Ioo`.
-/

end Skeleton
