/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The transform side: symmetry, the cosine transform, the exponent, the Laplace transform

Blueprint: `blueprint/src/parts/02-preliminaries.tex`, equation (2.1) and the paragraph after it,
and `blueprint/src/parts/04-representation.tex`, the definition of `g_{s,t}`. Nothing here is a
blueprint node; these are the objects Chapters 2–7 quantify over.

## The primary object is the *cosine* transform

`(2.1)` writes the Fourier transform `μ̂(ω) = ∫ e^{-iωx} μ(dx)` and immediately observes that for
symmetric `μ` it is real: `μ̂(ω) = ∫ cos(ωx) μ(dx)`. Every kernel in this article is symmetric
(axiom (A3) through `lem:convolution-representation`), and every statement about a kernel's
transform is a statement about a *real* number — its sign, its logarithm, its monotonicity. So
`fourierCos` is the primitive, a Bochner integral of a bounded continuous function against a
finite measure, hence unconditionally defined.

Mathlib's `charFun μ ω = ∫ exp (⟪x,ω⟫ * I) ∂μ` is the complex transform with the *opposite* sign
convention to (2.1). For symmetric measures the two agree and both are real, which is what the
bridge `Skeleton.fourierCos_eq_charFun_re` records; the sign is immaterial everywhere this
article uses uniqueness or continuity, and the one place it would matter — a *signed* measure's
transform in `prop:no-positivity-no-classification` — is also symmetric.

## The exponent

`-log μ̂` is the quantity the cascade makes additive. It is defined for every finite measure and
is junk (`Real.log` of a nonpositive number is `0`) exactly where `lem:nonvanishing` says the
axioms forbid us to be. Defining it unconditionally is what lets `lem:additivity` and everything
downstream be stated without carrying a positivity hypothesis into the *definition*; the
positivity is a hypothesis of the statements that need it.

## The Laplace transform

Present only for `prop:laplace-uniqueness-locally-finite`, and for the Thorin and
Pólya-frequency arguments of Chapters 10 and 13 that recover a Lévy tail from its Laplace
transform. It is `Hemigroup.laplaceL` verbatim: an `ℝ≥0∞`-valued `lintegral`, so no integrability
side condition is needed.

twin: `Hemigroup.laplaceL`. **`ScaleSpaceCore` candidate**, together with the node it serves —
TWINS.md's first proposal, and the only class-(a) node of Chapter 2.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## Symmetry -/

/-- A measure on the line is *symmetric* when it is invariant under `x ↦ -x`. The blueprint's
`R μ = μ`, with `R` extended to measures as the pushforward. -/
def IsSymmetric (μ : Measure ℝ) : Prop := μ.map (fun x => -x) = μ

/-! ## The cosine transform -/

/-- **(2.1) for a symmetric measure**: `μ̂(ω) = ∫ cos(ωx) μ(dx)`.

A Bochner integral of a bounded continuous function; for a finite `μ` it always converges, and
for a symmetric `μ` it is the Fourier transform of (2.1). -/
noncomputable def fourierCos (μ : Measure ℝ) (ω : ℝ) : ℝ := ∫ x, Real.cos (ω * x) ∂μ

lemma fourierCos_apply (μ : Measure ℝ) (ω : ℝ) : fourierCos μ ω = ∫ x, Real.cos (ω * x) ∂μ := rfl

/-- **The exponent `g(ω) = -log μ̂(ω)`** of Chapter 4, the quantity the cascade makes additive.

Unconditional, hence junk where `μ̂ ≤ 0`; `lem:nonvanishing` is the statement that the axioms
exclude that, and every node that reads `exponent` as `-log` of a positive number says so in its
hypotheses. -/
noncomputable def exponent (μ : Measure ℝ) (ω : ℝ) : ℝ := -Real.log (fourierCos μ ω)

lemma exponent_apply (μ : Measure ℝ) (ω : ℝ) :
    exponent μ ω = -Real.log (fourierCos μ ω) := rfl

/-! ## Measures on the half-line, and the Laplace transform -/

/-- A measure on `ℝ` is *folded* when it is carried by `(0,∞)`.

This is the blueprint's "measure on `(0,∞)`" — the folding convention of Chapter 2, under which
a symmetric Lévy measure on `ℝ ∖ {0}` is written as its image under `x ↦ |x|`. Carrying a
predicate keeps the ambient space `ℝ`, so that `Measure.conv` and the dilation pushforward stay
applicable, exactly as `Hemigroup.IsCausal` does on the half-line.

twin: `Hemigroup.IsCausal`, with `Iio 0` replaced by `Iic 0` — the origin carries no weight
here, because `1 - cos 0 = 0` and the blueprint's `ν` lives on the *open* half-line. -/
def IsFolded (m : Measure ℝ) : Prop := m (Iic 0) = 0

/-- The Laplace transform of a measure carried by the half-line, valued in `ℝ≥0∞`.

twin: `Hemigroup.laplaceL`, verbatim. -/
noncomputable def laplaceL (m : Measure ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (Real.exp (-(τ * u))) ∂m

lemma laplaceL_apply (m : Measure ℝ) (τ : ℝ) :
    laplaceL m τ = ∫⁻ u, ENNReal.ofReal (Real.exp (-(τ * u))) ∂m := rfl

end SpatialLine
