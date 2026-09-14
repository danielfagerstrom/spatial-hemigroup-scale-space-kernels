/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The corner definitions the earlier chapters read

Blueprint: `blueprint/src/parts/10-corners.tex`. Nothing here is a blueprint node; these are the
definitions of `SpatialLine/Corners.lean` that modules below Chapter 10 quantify over, held in a
module of their own so that reading one of them does not import the corner propositions. They
are `besselK`; the Matérn exponent, profile and density; the Laplace density;
`IsCompletelyMonotone`; the symmetric Thorin exponent in both its forms; and the symmetric
stable constant and profile. What stays in `Corners.lean` is `erfc`, the Laplace law and the
Student-t and inverse-gamma objects, which nothing below Chapter 10 reads.

`SpatialLine/Interfaces.lean` reads `besselK` and `IsCompletelyMonotone` — ledger **A11** and
**A19** are stated in them — and Chapter 7's stable and Matérn profiles read the rest. An
interface or Chapter 7 file that reached `SpatialLine/Corners.lean` for them would carry
Chapters 8 and 9 into the release export of the characterization theorem (ADR-0005).
`SpatialLine/Corners.lean` imports this file, so its own consumers see everything as before; the
split is of 2026-09-14 and moved no statement and no proof.

## The special function Mathlib does not have

Mathlib (v4.31.0) has no modified Bessel function and no error function. Three nodes are stated
in terms of them — `prop:matern-density`'s closed form, `prop:student-t`(2)'s transform,
`thm:joint-locality`(2)'s transform, and `prop:thorin-subclass`(5)'s image profile — so each is
defined by the integral representation the ledger's own sources use; `erfc` stays beside the
nodes that read it, in `SpatialLine/Corners.lean`.

* `besselK ν z = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` — DLMF (10.32.9), the standard integral
  representation of `K_ν` for `z > 0`, which is the range every use here lies in. For `z ≤ 0`
  the integral diverges and the Bochner integral is junk, in the phase A sense: `exponent` and
  `laplaceL` are total for the same reason. A19 and A16 are statements about *this* function
  under *this* representation, and whether that is the right primitive is an open question for
  the review (Q10).

No property of `besselK` is proved here; it exists so that the nodes can be typed.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The modified Bessel function -/

/-- **`K_ν`**, the modified Bessel function of the second kind, by its integral representation
`K_ν(z) = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` (DLMF 10.32.9), valid for `z > 0`.

Mathlib has no Bessel function; see the module docstring for why this is a definition here and
what the review is asked to decide. -/
noncomputable def besselK (ν z : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)

/-! ## The Matérn corner -/

/-- The Matérn exponent at range `θ`: `F(ω) = γ\log(1 + θ^2ω^2)`. -/
noncomputable def maternExponent (γ θ ω : ℝ) : ℝ := γ * Real.log (1 + θ ^ 2 * ω ^ 2)

/-- The Matérn folded profile at range `θ`: `k(x) = 2γ e^{-x/θ}` on `(0,∞)`, and `0` elsewhere.

The indicator is what makes `k 0 = 0`, `SDProfile`'s normalisation; every value off `(0,∞)` is
outside the profile's domain. -/
noncomputable def maternProfile (γ θ : ℝ) : ℝ → ℝ :=
  Set.indicator (Ioi (0 : ℝ)) fun x => 2 * γ * Real.exp (-(x / θ))

/-- The Matérn kernel at smoothness `γ - 1/2` and range `t`, normalised to unit mass:
the symmetric variance-gamma density of `prop:matern-density`. -/
noncomputable def maternDensity (γ t x : ℝ) : ℝ :=
  (Real.sqrt Real.pi * Real.Gamma γ * t)⁻¹ * (|x| / (2 * t)) ^ (γ - 1 / 2)
    * besselK (γ - 1 / 2) (|x| / t)

/-- The Laplace kernel of range `θ`: `(2θ)^{-1}e^{-|x|/θ}`, the Matérn member at `γ = 1`. -/
noncomputable def laplaceDensity (θ x : ℝ) : ℝ := (2 * θ)⁻¹ * Real.exp (-(|x| / θ))

/-! ## Complete monotonicity -/

/-- **Complete monotonicity on the half-line**: `f` is smooth there and
`(-1)^n f^{(n)}` is nonnegative for every `n`.

Neither Mathlib nor Paper I's development defines this — Paper I's `def:completely-monotone` has
no Lean declaration — so it is defined here, for `prop:thorin-subclass`(1) and
`prop:moments-tails`(2). Smoothness is a conjunct and not left implicit: `iteratedDeriv` returns
`0` where a function is not differentiable, so the sign conditions alone would be satisfied
vacuously by a nowhere-differentiable positive function. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0) ∧
    ∀ (n : ℕ) (x : ℝ), 0 < x → 0 ≤ (-1) ^ n * iteratedDeriv n f x

/-! ## The Thorin subclass -/

/-- **`eq:thorin`**, the symmetric Thorin representation
`F(ω) = aω^2 + \tfrac12∫\log(1 + ω^2/θ^2)\,U(dθ)`, `ℝ≥0∞`-valued.

`ℝ≥0∞` first, as everywhere in this development: the integrand is nonnegative, so the integral
needs no side condition, and finiteness is the node's integrability clause rather than a
definitional assumption. -/
noncomputable def thorinExponentL (a : ℝ) (U : Measure ℝ) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (a * ω ^ 2)
    + ENNReal.ofReal 2⁻¹ * ∫⁻ θ, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2)) ∂U

/-- The real-valued Thorin exponent. -/
noncomputable def thorinExponent (a : ℝ) (U : Measure ℝ) (ω : ℝ) : ℝ :=
  (thorinExponentL a U ω).toReal

/-! ## The symmetric stable corner -/

/-- The normalising constant `C_α = ∫₀^∞ (1 - \cos u)\,u^{-1-α}\,du` of
`cor:semigroup-case`. -/
noncomputable def stableConst (α : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), (1 - Real.cos u) / u ^ (1 + α)

/-- The symmetric stable folded profile `k(x) = C_α^{-1}x^{-α}` on `(0,∞)`. -/
noncomputable def stableProfile (α : ℝ) : ℝ → ℝ :=
  Set.indicator (Ioi (0 : ℝ)) fun x => (stableConst α)⁻¹ * x ^ (-α)

end SpatialLine
