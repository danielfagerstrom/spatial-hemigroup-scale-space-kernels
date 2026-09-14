/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TransformUniqueness

/-!
# Uniqueness for the cosine transform of an integrable function

Blueprint: `prop:no-positivity-no-classification` (`blueprint/src/parts/03-axioms.tex`), the last
step of `no_positivity_example`.

An even integrable function whose cosine transform vanishes at every frequency is null. This is
step (D) of the route wave 2 surveyed for that node, and the survey called it cheap; writing it
is what turns that into a measurement. It is **S-M**, and the two things that make it more than
one line are worth naming, because both are the reason Mathlib's own Fourier inversion does not
apply.

* **Inversion is unavailable.** `MeasureTheory.Integrable.fourierInv_fourier_eq` recovers `f`
  from its transform only at *continuity points* of `f`, and the node's `q` is a combination of
  indicators. So the argument has to go through uniqueness for *measures*, which asks nothing of
  regularity, and that is `Measure.ext_of_charFun`, wrapped here as
  `prop:fourier-uniqueness`.
* **The function is signed, and that uniqueness is about positive measures.** The cure is the
  Jordan split: `q` is the difference of its positive and negative parts, both integrable and
  nonnegative, so both are densities of finite measures, and the hypothesis says exactly that
  those two measures have the same *cosine* transform. The missing half of the characteristic
  function -- the sine part -- is where evenness of `q` is spent, and it is spent nowhere else:
  an odd integrable function on the line has vanishing integral, so the two measures'
  characteristic functions agree in full.

Both remarks are about the shape of the obligation and not about this article, so the lemmas are
stated for an arbitrary integrable function.

Proving campaign, wave 3, chapter 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## Two elementary steps -/

/-- **The integral of an odd integrable function on the line vanishes.** -/
theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hf : Integrable f)
    (hodd : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have hmap : (volume : Measure ℝ).map (fun x => -x) = volume :=
    Measure.map_neg_eq_self (volume : Measure ℝ)
  have h1 : ∫ x, f x = ∫ x, f (-x) := by
    conv_lhs => rw [← hmap]
    exact integral_map measurable_neg.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable)
  have h2 : ∫ x, f (-x) = -∫ x, f x := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  linarith [h1.trans h2]

/-- The positive part of an integrable function is integrable. -/
theorem integrable_toNNReal {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x : ℝ => ((f x).toNNReal : ℝ)) := by
  refine hf.abs.mono' (hf.aemeasurable.real_toNNReal.coe_nnreal_real.aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, Real.coe_toNNReal']
  rcases le_or_gt (f x) 0 with hle | hgt
  · rw [max_eq_right hle]
    simp [abs_nonneg]
  · rw [max_eq_left hgt.le, abs_of_pos hgt]

/-- The positive part of an integrable function is the density of a finite measure. -/
theorem isFiniteMeasure_withDensity_toNNReal {f : ℝ → ℝ} (hf : Integrable f) :
    IsFiniteMeasure (volume.withDensity fun x => (((f x).toNNReal : ℝ≥0) : ℝ≥0∞)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf.hasFiniteIntegral
  calc (((f x).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (f x) := rfl
    _ ≤ ENNReal.ofReal ‖f x‖ := ENNReal.ofReal_le_ofReal (le_abs_self (f x))
    _ = ‖f x‖ₑ := ofReal_norm (f x)

/-- Integration against a measure with a real density. Unconditional in `g`, both sides being
junk where the integrand is not integrable.

Lifted here by the wave-6 merge (2026-09-10). Chapters 3 and 8 wrote this name in this namespace
independently — `SpatialLine/NoPositivityClassification.lean` at Lebesgue measure with a
nonnegative density, `SpatialLine/CinDelayForm.lean` at an arbitrary measure and unconditionally
— and this is the general one, stated where the rest of the "a real density is a finite measure"
vocabulary already lives. The nonnegative reading is two lines over it and keeps its own name
there. -/
theorem integral_withDensity_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} (hf : AEMeasurable f μ)
    (g : ℝ → ℝ) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (f x))
      = ∫ x, ((f x).toNNReal : ℝ) * g x ∂μ := by
  have hcast : (fun x : ℝ => ENNReal.ofReal (f x))
      = fun x : ℝ => (((f x).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hcast, integral_withDensity_eq_integral_smul₀ hf.real_toNNReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])

/-- The characteristic function of a measure with an integrable real density, split into its
cosine and sine parts.

Stated for an arbitrary measure: chapter 8's delay equation needs it against the increment
measure, and the ambient-Lebesgue reading every consumer in this file wants is the same
statement with `μ` unified to `volume`. -/
theorem integral_smul_exp_eq {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g μ) (ω : ℝ) :
    ∫ x, g x • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) ∂μ
      = ((∫ x, Real.cos (ω * x) * g x ∂μ : ℝ) : ℂ)
        + ((∫ x, Real.sin (ω * x) * g x ∂μ : ℝ) : ℂ) * Complex.I := by
  have hcosI : Integrable (fun x : ℝ => Real.cos (ω * x) * g x) μ := by
    refine hg.bdd_mul (c := 1)
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
  have hsinI : Integrable (fun x : ℝ => Real.sin (ω * x) * g x) μ := by
    refine hg.bdd_mul (c := 1)
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)
  have hE : ∀ x : ℝ, g x • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)
      = ((Real.cos (ω * x) * g x : ℝ) : ℂ)
        + ((Real.sin (ω * x) * g x : ℝ) : ℂ) * Complex.I := by
    intro x
    have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
    rw [hx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.real_smul]
    push_cast
    ring
  calc ∫ x, g x • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) ∂μ
      = ∫ x, (((Real.cos (ω * x) * g x : ℝ) : ℂ)
          + ((Real.sin (ω * x) * g x : ℝ) : ℂ) * Complex.I) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hE)
    _ = (∫ x, ((Real.cos (ω * x) * g x : ℝ) : ℂ) ∂μ)
          + ∫ x, ((Real.sin (ω * x) * g x : ℝ) : ℂ) * Complex.I ∂μ :=
        integral_add hcosI.ofReal (hsinI.ofReal.mul_const Complex.I)
    _ = ((∫ x, Real.cos (ω * x) * g x ∂μ : ℝ) : ℂ)
          + ((∫ x, Real.sin (ω * x) * g x ∂μ : ℝ) : ℂ) * Complex.I := by
        rw [integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-! ## The uniqueness statement -/

/-- **An even integrable function whose cosine transform vanishes identically is null.**

The Jordan parts of `q` are the densities of two finite measures; the hypothesis says their
cosine transforms agree, evenness says their sine transforms both vanish, so their
characteristic functions agree and `prop:fourier-uniqueness` identifies the measures, hence the
densities almost everywhere. -/
theorem ae_eq_zero_of_even_of_integral_cos_eq_zero {q : ℝ → ℝ} (hq : Integrable q)
    (hqeven : ∀ x, q (-x) = q x)
    (h : ∀ ω : ℝ, ∫ x, Real.cos (ω * x) * q x = 0) :
    q =ᵐ[volume] 0 := by
  classical
  have hqpI : Integrable (fun x : ℝ => ((q x).toNNReal : ℝ)) := integrable_toNNReal hq
  have hqmI : Integrable (fun x : ℝ => (((-q x)).toNNReal : ℝ)) := integrable_toNNReal hq.neg
  haveI hfp : IsFiniteMeasure
      (volume.withDensity fun x => (((q x).toNNReal : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_toNNReal hq
  haveI hfm : IsFiniteMeasure
      (volume.withDensity fun x => ((((-q x)).toNNReal : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_toNNReal hq.neg
  -- the sine transform of `q` vanishes by evenness
  have hsin : ∀ ω : ℝ, ∫ x, Real.sin (ω * x) * q x = 0 := by
    intro ω
    have hint : Integrable (fun x : ℝ => Real.sin (ω * x) * q x) := by
      refine hq.bdd_mul' (c := 1)
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)
    refine integral_eq_zero_of_odd hint fun x => ?_
    rw [mul_neg, Real.sin_neg, hqeven x]
    ring
  -- the Jordan parts split `q`
  have hsplit : ∀ x : ℝ, ((q x).toNNReal : ℝ) - (((-q x)).toNNReal : ℝ) = q x := by
    intro x
    simp only [Real.coe_toNNReal']
    rcases le_or_gt (q x) 0 with hle | hgt
    · rw [max_eq_right hle, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith)]
      ring
  -- their characteristic functions agree
  have hcf : ∀ ω : ℝ,
      charFun (volume.withDensity fun x => (((q x).toNNReal : ℝ≥0) : ℝ≥0∞)) ω
        = charFun (volume.withDensity fun x => ((((-q x)).toNNReal : ℝ≥0) : ℝ≥0∞)) ω := by
    intro ω
    have hconv : ∀ f : ℝ → ℝ, AEMeasurable (fun x => (f x).toNNReal) volume →
        charFun (volume.withDensity fun x => (((f x).toNNReal : ℝ≥0) : ℝ≥0∞)) ω
          = ∫ x, ((f x).toNNReal : ℝ) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) := by
      intro f hf
      rw [charFun_apply_real, integral_withDensity_eq_integral_smul₀ hf]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])
    rw [hconv q hq.aemeasurable.real_toNNReal, hconv (fun x => -q x) hq.neg.aemeasurable.real_toNNReal,
      integral_smul_exp_eq hqpI, integral_smul_exp_eq hqmI]
    have hc : (∫ x, Real.cos (ω * x) * ((q x).toNNReal : ℝ))
        = ∫ x, Real.cos (ω * x) * (((-q x)).toNNReal : ℝ) := by
      have hcosp : Integrable (fun x : ℝ => Real.cos (ω * x) * ((q x).toNNReal : ℝ)) := by
        refine hqpI.bdd_mul' (c := 1)
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
      have hcosm : Integrable (fun x : ℝ => Real.cos (ω * x) * (((-q x)).toNNReal : ℝ)) := by
        refine hqmI.bdd_mul' (c := 1)
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
      rw [← sub_eq_zero, ← integral_sub hcosp hcosm, ← h ω]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [← mul_sub, hsplit x]
    have hs : (∫ x, Real.sin (ω * x) * ((q x).toNNReal : ℝ))
        = ∫ x, Real.sin (ω * x) * (((-q x)).toNNReal : ℝ) := by
      have hsinp : Integrable (fun x : ℝ => Real.sin (ω * x) * ((q x).toNNReal : ℝ)) := by
        refine hqpI.bdd_mul' (c := 1)
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)
      have hsinm : Integrable (fun x : ℝ => Real.sin (ω * x) * (((-q x)).toNNReal : ℝ)) := by
        refine hqmI.bdd_mul' (c := 1)
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)
      rw [← sub_eq_zero, ← integral_sub hsinp hsinm, ← hsin ω]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [← mul_sub, hsplit x]
    rw [hc, hs]
  have hμ := fourier_uniqueness hcf
  have hae : (fun x => (((q x).toNNReal : ℝ≥0) : ℝ≥0∞))
      =ᵐ[volume] fun x => ((((-q x)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (withDensity_eq_iff_of_sigmaFinite
      hq.aemeasurable.real_toNNReal.coe_nnreal_ennreal
      hq.neg.aemeasurable.real_toNNReal.coe_nnreal_ennreal).mp hμ
  filter_upwards [hae] with x hx
  have hxn : ((q x).toNNReal : ℝ) = (((-q x)).toNNReal : ℝ) := by
    have : (q x).toNNReal = ((-q x)).toNNReal := by exact_mod_cast hx
    exact congrArg _ this
  have := hsplit x
  rw [hxn, sub_self] at this
  exact this.symm

end SpatialLine
