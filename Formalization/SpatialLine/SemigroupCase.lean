/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.AdmissibleCone

/-!
# `cor:semigroup-case`, the boundary `α = 2`: the Gaussian ray

Blueprint: `cor:semigroup-case`, and `rem:boundary` on what sits at the endpoint.

The profile is `0` and the Gaussian coefficient is `1`, so the exponent is `ω²` — the one member
of the stable family that is not given by a jump profile, and the trace of the boundary in the
general class. The declaration exists because `cor:semigroup-case`'s statement exhibits it, and
because it is the cheapest available check that `SDProfile`'s seven fields are satisfiable with
a vanishing profile.

The other two declarations of the node — the Cauchy-equation argument fixing the index and the
profile `C_α^{-1}x^{-α}` for `0 < α < 2` — are not proved: both need the convergence of
`C_α = ∫₀^∞ (1 - \cos u)u^{-1-α}du`, an improper integral with no Mathlib support at either
endpoint, and the second needs the substitution `u = ωx` inside it.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-- **The Gaussian datum**: the `SDProfile` with Gaussian coefficient `a` and no jump
catalogue.

Chapter 10's `prop:stable-family` needs the same object for the `α = 2` endpoint of the stable
family, and wrote it independently; wave 2's merge (2026-09-09) kept this copy, the one in the
file of the node it belongs to, and `SpatialLine/StableCorner.lean` imports it. -/
noncomputable def gaussianDatum (a : ℝ) (ha : 0 ≤ a) : SDProfile where
  a := a
  k := 0
  a_nonneg := ha
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  k_zero := rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

@[simp]
theorem gaussianDatum_a (a : ℝ) (ha : 0 ≤ a) : (gaussianDatum a ha).a = a := rfl

@[simp]
theorem gaussianDatum_k (a : ℝ) (ha : 0 ≤ a) : (gaussianDatum a ha).k = 0 := rfl

/-- The exponent of the Gaussian datum is `aω²`. -/
theorem gaussianDatum_exponent (a : ℝ) (ha : 0 ≤ a) (ω : ℝ) :
    (gaussianDatum a ha).exponent ω = a * ω ^ 2 := by
  rw [SDProfile.exponent, SDProfile.exponentL]
  have hzero : (fun x : ℝ =>
      ENNReal.ofReal ((1 - Real.cos (ω * x)) * (gaussianDatum a ha).k x / x))
      = fun _ : ℝ => (0 : ℝ≥0∞) := by
    funext x
    show ENNReal.ofReal ((1 - Real.cos (ω * x)) * (0 : ℝ) / x) = 0
    simp
  rw [hzero]
  simp only [lintegral_zero, add_zero]
  show (ENNReal.ofReal (a * ω ^ 2)).toReal = a * ω ^ 2
  exact ENNReal.toReal_ofReal (by positivity)

/-- **`cor:semigroup-case`, the boundary `α = 2`: the Gaussian.** -/
theorem semigroup_case_gaussian :
    ∃ Q : SDProfile, Q.a = 1 ∧ (∀ x : ℝ, Q.k x = 0) ∧ ∀ ω : ℝ, Q.exponent ω = ω ^ 2 :=
  ⟨gaussianDatum 1 zero_le_one, rfl, fun _ => rfl, fun ω => by
    rw [gaussianDatum_exponent, one_mul]⟩

end SpatialLine
