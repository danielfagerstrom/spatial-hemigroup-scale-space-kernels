/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transform
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The bridge between the cosine transform and Mathlib's characteristic function

Nothing here is a blueprint node. These are the two identities that let the article's real
cosine transform `fourierCos` (the primitive of `blueprint/src/parts/02-preliminaries.tex`,
equation (2.1) read on a symmetric measure) and Mathlib's complex `charFun` be used in the same
proof.

`charFun μ ω = ∫ exp (ω x i) ∂μ` carries the **opposite** sign convention to (2.1). Every use in
this development is either sign-insensitive — uniqueness, the value `1`, continuity — or is
about a symmetric measure, where the two transforms agree and are real. That is what the second
lemma below records.

Proving campaign, chapter 2 (2026-09-09): moved here from `Skeleton/Chapter2.lean`, where the
two were stated as `Skeleton.fourierCos_eq_charFun_re` and
`Skeleton.charFun_eq_fourierCos_of_symmetric`.
-/

namespace SpatialLine

open MeasureTheory Set

/-- The cosine transform's integrand is integrable against a finite measure: it is continuous
and bounded by `1`.

Wave 1 of the proving campaign (2026-09-09) moved this here. It was proved three times
independently — as `integrable_cos` in `SpatialLine/LatticeZero.lean`, and as
`integrable_cos_mul` in `SpatialLine/Nonvanishing.lean` and `SpatialLine/Pairing.lean`. This
file is the chapter-2 home of the elementary facts about (2.1), and it sits low enough in the
import graph for every chapter to reach it. -/
theorem integrable_cos_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Real.cos (ω * x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)

/-- The transform of `δ₀` is `1` at every frequency.

Moved here by the wave-1 merge (2026-09-09) from the three files that proved it independently:
chapters 3, 4 and 5 each need it, and this is the file they all import. -/
@[simp] theorem fourierCos_dirac_zero (ω : ℝ) :
    fourierCos (Measure.dirac (0 : ℝ)) ω = 1 := by
  rw [fourierCos_apply, integral_dirac]
  simp

/-- The integrand of `charFun` is integrable against a finite measure: it is continuous of
constant modulus `1`. -/
theorem integrable_charFun_integrand (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) μ := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  have hbound : ∀ x : ℝ, ‖Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)‖ ≤ ‖(1 : ℝ)‖ := by
    intro x
    have : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
    simp
  exact (hasFiniteIntegral_const (1 : ℝ)).mono (Filter.Eventually.of_forall hbound)

/-- The characteristic function of a sum of finite measures is the sum of the characteristic
functions.

Lifted here by the wave-6 merge (2026-09-10): chapters 3 and 8 wrote it independently, in
`SpatialLine/SignedUniqueness.lean` and `SpatialLine/CinDelayForm.lean`, with the same name in
the same namespace and the same proof to the letter. It belongs beside the integrability that
proves it. -/
theorem charFun_add_measure (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ω : ℝ) :
    charFun (μ + ν) ω = charFun μ ω + charFun ν ω := by
  rw [charFun_apply_real, charFun_apply_real, charFun_apply_real]
  exact integral_add_measure (integrable_charFun_integrand μ ω)
    (integrable_charFun_integrand ν ω)

/-- The sine transform's integrand is integrable against a finite measure: it is continuous and
bounded by `1`, the twin of `integrable_cos_mul` above.

Lifted here by the wave-6 merge (2026-09-10) from `SpatialLine/Pairing.lean` (chapter 4), which
had carried it since the sine half of the characteristic function was written, and from
`SpatialLine/GeneratorSignal.lean` (chapter 11), which wrote it again. This is the wave-1 remedy
applied to the other half of the pair: `integrable_cos_mul` was moved out of `Pairing.lean` for
the same reason and by the same argument. -/
theorem integrable_sin_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Real.sin (ω * x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)

/-- **The cosine transform is the real part of the characteristic function.**

`fourierCos μ ω = ∫ cos(ωx) ∂μ` and `charFun μ ω = ∫ exp(ωx i) ∂μ`, and `re` commutes with the
Bochner integral of an integrable function. -/
theorem fourierCos_eq_charFun_re (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    fourierCos μ ω = (charFun μ ω).re := by
  rw [charFun_apply_real, ← RCLike.re_to_complex,
    ← integral_re (integrable_charFun_integrand μ ω), fourierCos_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
  simp only [RCLike.re_to_complex, hx, Complex.exp_ofReal_mul_I_re]

/-- **For a symmetric finite measure the characteristic function is real**, and equal to the
cosine transform; so the sign convention of (2.1) is immaterial wherever this development reads
a symmetric measure's transform.

The imaginary part is `∫ sin(ωx) ∂μ`, which vanishes because `μ` is invariant under `x ↦ -x`
and `sin` is odd. -/
theorem charFun_eq_fourierCos_of_symmetric {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsym : IsSymmetric μ) (ω : ℝ) :
    charFun μ ω = (fourierCos μ ω : ℂ) := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  -- The imaginary part is the integral of an odd function against a symmetric measure.
  have him : (charFun μ ω).im = 0 := by
    have hint := integrable_charFun_integrand μ ω
    have h1 : (charFun μ ω).im = ∫ x, Real.sin (ω * x) ∂μ := by
      rw [charFun_apply_real, ← RCLike.im_to_complex, ← integral_im hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
      simp only [RCLike.im_to_complex, hx, Complex.exp_ofReal_mul_I_im]
    -- Substituting `x ↦ -x` fixes `μ` and negates the integral.
    have h2 : ∫ x, Real.sin (ω * x) ∂μ = ∫ x, Real.sin (ω * (-x)) ∂μ := by
      conv_lhs => rw [← hsym]
      rw [integral_map hneg.aemeasurable (by fun_prop)]
    have h3 : ∫ x, Real.sin (ω * (-x)) ∂μ = -∫ x, Real.sin (ω * x) ∂μ := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_neg, Real.sin_neg]
    have h4 : ∫ x, Real.sin (ω * x) ∂μ = -∫ x, Real.sin (ω * x) ∂μ := h2.trans h3
    rw [h1]
    linarith
  have hre : (charFun μ ω).re = fourierCos μ ω := (fourierCos_eq_charFun_re μ ω).symm
  exact Complex.ext (by simpa using hre) (by simpa using him)

/-! ## Elementary facts about the cosine transform

Moved here by wave 2's merge (2026-09-09) from `SpatialLine/Nonvanishing.lean`, on wave 1's
rule: these are elementary facts about (2.1), not about `lem:nonvanishing`, so they belong in
the chapter-2 file every chapter can reach. `SpatialLine/Interfaces.lean` needs two of them for
the reverse direction of ledger A1 and must not import chapter 4. -/

@[simp] theorem fourierCos_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    fourierCos μ 0 = 1 := by
  simp [fourierCos_apply]

theorem fourierCos_neg (μ : Measure ℝ) (ω : ℝ) : fourierCos μ (-ω) = fourierCos μ ω := by
  simp only [fourierCos_apply, neg_mul, Real.cos_neg]

theorem fourierCos_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (ω : ℝ) :
    fourierCos μ ω ≤ 1 := by
  have h := integral_mono (integrable_cos_mul μ ω) (integrable_const (1 : ℝ))
    (fun x => Real.cos_le_one (ω * x))
  simpa [fourierCos_apply] using h

theorem continuous_fourierCos (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (fourierCos μ) := by
  refine continuous_of_dominated (F := fun ω x => Real.cos (ω * x)) (bound := fun _ => (1 : ℝ))
    (fun ω => (integrable_cos_mul μ ω).aestronglyMeasurable) ?_ (integrable_const 1) ?_
  · intro ω
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
  · filter_upwards with x
    exact (Real.continuous_cos.comp (continuous_id.mul continuous_const))

/-- **The transform of a dilated measure** is the transform at the dilated frequency.

Moved here by wave 2's merge (2026-09-09) from `MaternData.charFun_map_const_mul`, where it
was stranded in a concrete namespace: it mentions no Matérn datum, and
`SpatialLine/MainConstruction.lean` already called it across the namespace boundary. -/
theorem charFun_map_const_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (c ω : ℝ) :
    charFun (μ.map (fun x => c * x)) ω = charFun μ (c * ω) := by
  have hmeas : ∀ ν : Measure ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (↑ω * ↑x * Complex.I)) ν := fun ν =>
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  calc charFun (μ.map (fun x => c * x)) ω
      = ∫ x, Complex.exp (↑ω * ↑x * Complex.I) ∂(μ.map (fun x => c * x)) := charFun_apply_real ω
    _ = ∫ x, Complex.exp (↑ω * ↑(c * x) * Complex.I) ∂μ :=
        integral_map (measurable_const_mul c).aemeasurable (hmeas _)
    _ = ∫ x, Complex.exp (↑(c * ω) * ↑x * Complex.I) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        push_cast
        ring_nf
    _ = charFun μ (c * ω) := (charFun_apply_real (c * ω)).symm

/-- **The cosine transform of a centred Gaussian law of variance `v`**, `e^{-vω²/2}`.

Collected here by wave 2's merge (2026-09-09). Chapter 5's `Pairing.lean` proved the case
`v = 1` for the test function, and chapter 3's Gaussian member needs the general `v` for the
continuity of its transform in the pair of scales; this is the general fact, in the chapter-2
file both can reach. -/
theorem fourierCos_gaussianReal (v : NNReal) (ω : ℝ) :
    fourierCos (ProbabilityTheory.gaussianReal 0 v) ω = Real.exp (-((v : ℝ) * ω ^ 2 / 2)) := by
  rw [fourierCos_eq_charFun_re, ProbabilityTheory.charFun_gaussianReal]
  have harg : (ω : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2
      = (((-((v : ℝ) * ω ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp, Complex.ofReal_re]

end SpatialLine
