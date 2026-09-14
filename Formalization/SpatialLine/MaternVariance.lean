/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.VarianceFormula
import SpatialLine.MaternCorner

/-!
# The Matérn corner's variance

Blueprint: the variance sentence of `prop:two-members`(2) and of `prop:matern-exponent`(3),
both of which are `prop:moments-tails`(1)'s variance formula evaluated on the Matérn profile
`k(x) = 2γ e^{-x}`.

**The file was called `SpatialLine.MaternMoments` until 2026-09-14** and reached the variance
formula through `SpatialLine.Moments`, the moment criterion. It reads `VarianceFormula` and
`MaternCorner` directly now; nothing here spends ledger A13 or A14, and the rename says so
(ADR-0005).

## What proving this found

**The catalogue's first moment is a Gamma value and nothing more.** The variance formula asks
for `∫₀^∞ x k(x) dx` with `k = 2γ e^{-x}`, which is `2γ Γ(2) = 2γ` — Mathlib's
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at shape `2` and rate `1`. So the variance clause of
the Matérn corner is one Gamma evaluation on top of `moments_tails_variance`, and in
particular it does *not* go through `prop:bridge-families`(2)'s Gamma mixture, which is the
route the printed proof takes and which is chapter 9's unproved material.

**The transform hypothesis of `prop:two-members` is the Matérn exponent at `s = 0`.** The node
states the family by its transfer function `((1+s²ω²)/(1+t²ω²))^γ`; the profile-side
declarations want `exp(-F(tω))`. At `s = 0` these are the same function, which is
`maternTransform_zero`, and that identification is all that stands between the chapter-3 node
and the chapter-10 machinery.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The transfer function at the lower endpoint -/

/-- **The Matérn transfer function from the origin is the Matérn transform.**
`((1 + 0)/(1 + t²ω²))^γ = e^{-γ log(1 + t²ω²)}`. -/
theorem maternTransform_zero (γ t ω : ℝ) :
    ((1 + (0 : ℝ) ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ
      = Real.exp (-maternExponent γ 1 (t * ω)) := by
  have hA : (0 : ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
  have hbase : (1 + (0 : ℝ) ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2) = (1 + t ^ 2 * ω ^ 2)⁻¹ := by
    rw [show (1 : ℝ) + (0 : ℝ) ^ 2 * ω ^ 2 = 1 by ring, one_div]
  rw [hbase, Real.rpow_def_of_pos (inv_pos.mpr hA), Real.log_inv, maternExponent]
  congr 1
  rw [show (1 : ℝ) ^ 2 * (t * ω) ^ 2 = t ^ 2 * ω ^ 2 by ring]
  ring

/-! ## The catalogue's first moment -/

/-- `∫₀^∞ x · 2γ e^{-x} dx` converges. -/
theorem integrableOn_id_mul_maternProfile_Ioi (γ : ℝ) :
    IntegrableOn (fun x : ℝ => x * maternProfile γ 1 x) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun x : ℝ => 2 * γ * (x ^ ((2 : ℝ) - 1) * Real.exp (-1 * x ^ (1 : ℝ))))
      (Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 : ℝ) - 1) (p := 1) (b := 1)
      (by norm_num) le_rfl one_pos).const_mul _
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  show 2 * γ * (x ^ ((2 : ℝ) - 1) * Real.exp (-1 * x ^ (1 : ℝ))) = x * maternProfile γ 1 x
  rw [maternProfile_eq_exp one_pos hx0, show ((2 : ℝ) - 1) = 1 by norm_num]
  simp only [Real.rpow_one]
  field_simp

/-- **The catalogue's first moment is `2γ`.** `∫₀^∞ x · 2γ e^{-x} dx = 2γ Γ(2) = 2γ`. -/
theorem integral_id_mul_maternProfile (γ : ℝ) :
    (∫ x in Ioi (0 : ℝ), x * maternProfile γ 1 x) = 2 * γ := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := 1)
    (by norm_num) one_pos
  have hstep : (∫ x in Ioi (0 : ℝ), x * maternProfile γ 1 x)
      = 2 * γ * ∫ x in Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(1 * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [maternProfile_eq_exp one_pos hx0, show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one]
    field_simp
  have h2 : Real.Gamma 2 = 1 := by simp
  rw [hstep, hgamma, h2]
  norm_num

/-- The `ℝ≥0∞` form, which is the shape `moments_tails_variance`'s hypothesis and conclusion
both use. -/
theorem lintegral_id_mul_maternProfile {γ : ℝ} (hγ : 0 < γ) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * maternProfile γ 1 x)) = ENNReal.ofReal (2 * γ) := by
  rw [← integral_id_mul_maternProfile γ]
  refine (ofReal_integral_eq_lintegral_ofReal (integrableOn_id_mul_maternProfile_Ioi γ) ?_).symm
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (.of_forall fun x hx => mul_nonneg (le_of_lt hx) (maternProfile_nonneg hγ 1 x))

/-! ## The variance of the Matérn kernel -/

/-- **The Matérn corner's mean and variance.** For the family whose transform at canonical
scale `t` is `(1 + t²ω²)^{-γ}`, the mean displacement is `0` and the variance is `2γt²`.

This is `moments_tails_variance` at the witness `maternDatum γ 1`, whose catalogue has first
moment `2γ`. Lean core. -/
theorem matern_mean_variance (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hsym : ∀ t : ℝ, 0 < t → IsSymmetric (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-maternExponent γ 1 (t * ω)))
    {t : ℝ} (ht : 0 < t) :
    (∫ x, x ∂(μ t)) = 0 ∧ (∫ x, x ^ 2 ∂(μ t)) = 2 * γ * t ^ 2 := by
  have hcos' : ∀ s ω : ℝ, 0 < s →
      fourierCos (μ s) ω = Real.exp (-(maternDatum γ 1 hγ one_pos).exponent (s * ω)) := by
    intro s ω hs
    rw [maternDatum_exponent]
    exact hcos s ω hs
  have hk : (maternDatum γ 1 hγ one_pos).k = maternProfile γ 1 := rfl
  have hfin : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (x * (maternDatum γ 1 hγ one_pos).k x)) ≠ ⊤ := by
    rw [hk, lintegral_id_mul_maternProfile hγ]
    exact ENNReal.ofReal_ne_top
  obtain ⟨hmean, hvar⟩ :=
    moments_tails_variance (maternDatum γ 1 hγ one_pos) μ hprob hsym hcos' ht hfin
  refine ⟨hmean, ?_⟩
  rw [hvar, hk, lintegral_id_mul_maternProfile hγ, maternDatum_a,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-! ## `prop:two-members`(2), the moment sentence

**Moved (2026-09-14, R156) to `SpatialLine/MaternMixture.lean`.** `two_members_matern_moments`
stood here and took its integrability conjunct from `matern_moments_integrable`, the moment
criterion, hence ledger **A13**. The same conjunct is inside `matern_moments`, which gets it
from the even moments of the Gamma mixture by `|x|^n ≤ 1 + x^{2n}` and prints Lean core; the
re-route is what takes the node to Lean core, and it has to live beside `matern_moments`
because `MaternMixture.lean` imports this file. `matern_mean_variance` above is unchanged and
is still where the mean and the variance come from. -/

end SpatialLine
