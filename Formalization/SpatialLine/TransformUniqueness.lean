/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TransformBridge
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Uniqueness and continuity for the Fourier transform of a measure on the line

Blueprint: `prop:fourier-uniqueness` and `prop:levy-continuity`
(`blueprint/src/parts/02-preliminaries.tex`). Both were graded `[A]` in the statement skeleton,
on ledger entries **A5** and **A6**; both are **proved here from Mathlib**, and the author's
decision of 2026-09-09 (the review's Q2) regrades the consumed statements `[T]`. A5 and A6 are
kept in `blueprint/AXIOMS.md` for the record and ground no node; neither reaches
`blueprint/trust-boundary.txt`.

* `fourier_uniqueness` is `MeasureTheory.Measure.ext_of_charFun`, which holds for finite measures
  on a complete second-countable inner product space, of which `ℝ` is one. The article uses it
  for finite measures on `ℝ` and nothing more; the corresponding statement for a locally finite
  measure on a half-line is `laplace_uniqueness_locally_finite` and is proved separately.
* `levy_continuity` is `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun` together
  with `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. The clause proved
  here is the one the article consumes — the limit is *known in advance* to be the transform of
  a probability measure, which is the case at both call sites, `thm:main-characterization`(⇐)
  and `prop:two-members`(1). The general clause, in which the limit function is only assumed
  continuous at the origin, is not used anywhere in this article and is not stated: Mathlib
  supplies its tightness half (`isTightMeasureSet_of_tendsto_charFun`) and the rest — Prokhorov
  and the identification of the limit — remains open work with no consumer.

Weak convergence is spelled out as convergence of the integrals of bounded continuous functions
rather than as convergence in `ProbabilityMeasure ℝ`, because that is the form the `ε/3`
argument of `thm:main-characterization` consumes.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped Topology

/-- **`prop:fourier-uniqueness`.** A finite Borel measure on `ℝ` is determined by its Fourier
transform.

Stated for Mathlib's `charFun`, whose sign convention is the opposite of the blueprint's (2.1);
the statement is symmetric in the convention, since `ω ↦ -ω` is a bijection of `ℝ`. -/
theorem fourier_uniqueness {μ ρ : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (h : ∀ ω, charFun μ ω = charFun ρ ω) : μ = ρ :=
  Measure.ext_of_charFun (funext h)

/-- **`prop:levy-continuity`, the clause the article consumes.** If the transforms of a sequence
of probability measures converge pointwise to the transform of a probability measure, the
sequence converges weakly.

Sequences, not nets: the article's uses are all along sequences `(sₙ,tₙ) → (s,t)` in a metric
space. -/
theorem levy_continuity {μ : ℕ → Measure ℝ} {μ₀ : Measure ℝ}
    [hμ : ∀ n, IsProbabilityMeasure (μ n)] [hμ₀ : IsProbabilityMeasure μ₀]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 (charFun μ₀ ω))) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(μ n)) atTop (𝓝 (∫ x, g x ∂μ₀)) := by
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ n, hμ n⟩ with hP
  set P₀ : ProbabilityMeasure ℝ := ⟨μ₀, hμ₀⟩ with hP₀
  have hconv : Tendsto P atTop (𝓝 P₀) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun (μ := P) (μ₀ := P₀) h
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv

end SpatialLine
