/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CosineUniqueness

/-!
# A signed integrable function with the cosine transform of a measure

Blueprint: `prop:no-positivity-no-classification`, the split half
`no_positivity_classification`, in its `⇐` direction.

An even integrable `k` whose cosine transform is that of a symmetric finite measure `ν` is
**nonnegative almost everywhere**, and `ν` is the measure with density `k`. This is the
generalisation the wave-5 re-price named: `ae_eq_zero_of_even_of_integral_cos_eq_zero`
(`SpatialLine/CosineUniqueness.lean`) is the case `ν = 0`, and the argument is the same Jordan
split run against `ν + k⁻\,dx` instead of against `k⁻\,dx`.

## What proving this found

**The nonnegativity is not a second argument.** It was expected to need a separate step —
"the resulting `k⁻dx ≤ k⁺dx` between mutually singular measures forces `k⁻ = 0`". It does not
need mutual singularity, and it does not need a measurable representative of `k` either: the
identity of measures is tested on the *set where a measurable version of `k` is negative*,
where the left side has zero mass by construction, so the right side's `k⁻` integral vanishes
there and Lebesgue's `lintegral_eq_zero_iff` closes it. One set, one application.

**`ENNReal.ofReal (k x)` and `((k x).toNNReal : ℝ≥0∞)` are definitionally equal**, so the
statement can be given in the `ofReal` form the consumers want while the proof runs in the
`toNNReal` form `CosineUniqueness.lean` already supports. Stating it in the `ofReal` form
matters: `volume.withDensity (ENNReal.ofReal ∘ k)` is the measure a kernel family is built from,
and it is *automatically* the positive part, so the conclusion `ν = k\,dx` needs no `k ≥ 0`
rider to be meaningful.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-- The characteristic function of a measure with an integrable density, split into its cosine
and sine parts. -/
theorem charFun_withDensity_toNNReal {f : ℝ → ℝ} (hf : Integrable f) (ω : ℝ) :
    charFun (volume.withDensity fun x => (((f x).toNNReal : ℝ≥0) : ℝ≥0∞)) ω
      = ((∫ x, Real.cos (ω * x) * ((f x).toNNReal : ℝ) : ℝ) : ℂ)
        + ((∫ x, Real.sin (ω * x) * ((f x).toNNReal : ℝ) : ℝ) : ℂ) * Complex.I := by
  rw [charFun_apply_real,
    integral_withDensity_eq_integral_smul₀ hf.aemeasurable.real_toNNReal]
  rw [show (∫ x, ((f x).toNNReal : ℝ≥0) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I))
      = ∫ x, ((f x).toNNReal : ℝ) • Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])]
  exact integral_smul_exp_eq (integrable_toNNReal hf) ω

/-- A bounded continuous weight against an integrable function is integrable. -/
theorem integrable_bdd_mul {g : ℝ → ℝ} (hg : Integrable g) {w : ℝ → ℝ} (hw : Continuous w)
    (hb : ∀ x, |w x| ≤ 1) : Integrable (fun x => w x * g x) :=
  hg.bdd_mul' (c := 1) hw.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- **The Jordan identity.** With the hypotheses below, `k⁺dx = ν + k⁻dx`. -/
theorem withDensity_pos_eq_of_fourierCos_eq {k : ℝ → ℝ} (hk : Integrable k)
    (hkeven : ∀ x, k (-x) = k x) {ν : Measure ℝ} [IsFiniteMeasure ν] (hsym : IsSymmetric ν)
    (h : ∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = fourierCos ν ω) :
    (volume.withDensity fun x => (((k x).toNNReal : ℝ≥0) : ℝ≥0∞))
      = ν + volume.withDensity fun x => ((((-k x)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hkpI : Integrable (fun x : ℝ => ((k x).toNNReal : ℝ)) := integrable_toNNReal hk
  have hkmI : Integrable (fun x : ℝ => (((-k x)).toNNReal : ℝ)) := integrable_toNNReal hk.neg
  haveI hfp : IsFiniteMeasure (volume.withDensity fun x => (((k x).toNNReal : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_toNNReal hk
  haveI hfm : IsFiniteMeasure
      (volume.withDensity fun x => ((((-k x)).toNNReal : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_toNNReal hk.neg
  have hsplit : ∀ x : ℝ, ((k x).toNNReal : ℝ) - (((-k x)).toNNReal : ℝ) = k x := by
    intro x
    simp only [Real.coe_toNNReal']
    rcases le_or_gt (k x) 0 with hle | hgt
    · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hgt.le, max_eq_right (by linarith)]; ring
  -- the sine transform of `k` vanishes by evenness
  have hsin : ∀ ω : ℝ, ∫ x, Real.sin (ω * x) * k x = 0 := by
    intro ω
    refine integral_eq_zero_of_odd
      (integrable_bdd_mul hk (by fun_prop) fun x => Real.abs_sin_le_one (ω * x)) fun x => ?_
    rw [mul_neg, Real.sin_neg, hkeven x]
    ring
  refine fourier_uniqueness fun ω => ?_
  rw [charFun_add_measure, charFun_withDensity_toNNReal hk,
    charFun_withDensity_toNNReal (f := fun x => -k x) hk.neg,
    charFun_eq_fourierCos_of_symmetric hsym]
  have hcosint : ∀ g : ℝ → ℝ, Integrable g →
      Integrable (fun x => Real.cos (ω * x) * g x) := fun g hg =>
    integrable_bdd_mul hg (by fun_prop) fun x => Real.abs_cos_le_one (ω * x)
  have hsinint : ∀ g : ℝ → ℝ, Integrable g →
      Integrable (fun x => Real.sin (ω * x) * g x) := fun g hg =>
    integrable_bdd_mul hg (by fun_prop) fun x => Real.abs_sin_le_one (ω * x)
  have hcdiff : (∫ x, Real.cos (ω * x) * ((k x).toNNReal : ℝ))
        - ∫ x, Real.cos (ω * x) * (((-k x)).toNNReal : ℝ)
      = ∫ x, Real.cos (ω * x) * k x := by
    rw [← integral_sub (hcosint _ hkpI) (hcosint _ hkmI)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← mul_sub, hsplit x]
  have hsdiff : (∫ x, Real.sin (ω * x) * ((k x).toNNReal : ℝ))
        - ∫ x, Real.sin (ω * x) * (((-k x)).toNNReal : ℝ)
      = ∫ x, Real.sin (ω * x) * k x := by
    rw [← integral_sub (hsinint _ hkpI) (hsinint _ hkmI)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← mul_sub, hsplit x]
  have hc : (∫ x, Real.cos (ω * x) * ((k x).toNNReal : ℝ))
      = fourierCos ν ω + ∫ x, Real.cos (ω * x) * (((-k x)).toNNReal : ℝ) := by
    rw [← h ω]; linarith [hcdiff]
  have hs : (∫ x, Real.sin (ω * x) * ((k x).toNNReal : ℝ))
      = ∫ x, Real.sin (ω * x) * (((-k x)).toNNReal : ℝ) := by
    have := hsin ω
    linarith [hsdiff]
  rw [hc, hs]
  push_cast
  ring

/-- **The signed uniqueness step of `no_positivity_classification`.**

An even integrable `k` whose cosine transform is that of a symmetric finite measure `ν` is
nonnegative almost everywhere, and `ν` is the measure with density `k`.

`ae_eq_zero_of_even_of_integral_cos_eq_zero` is the case `ν = 0` and this is the strict
generalisation the wave-5 annotation named; the extra content is the nonnegativity, and it is
one test of the Jordan identity on the set where `k` is negative. -/
theorem ae_nonneg_of_fourierCos_eq {k : ℝ → ℝ} (hk : Integrable k)
    (hkeven : ∀ x, k (-x) = k x) {ν : Measure ℝ} [IsFiniteMeasure ν] (hsym : IsSymmetric ν)
    (h : ∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = fourierCos ν ω) :
    (∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x) ∧
      ν = volume.withDensity fun x => ENNReal.ofReal (k x) := by
  classical
  have hJ := withDensity_pos_eq_of_fourierCos_eq hk hkeven hsym h
  -- a measurable version of `k`
  set k' : ℝ → ℝ := hk.aemeasurable.mk k with hk'def
  have hk'meas : Measurable k' := hk.aemeasurable.measurable_mk
  have hk'ae : k =ᵐ[volume] k' := hk.aemeasurable.ae_eq_mk
  have hdp : (volume.withDensity fun x => (((k x).toNNReal : ℝ≥0) : ℝ≥0∞))
      = volume.withDensity fun x => ENNReal.ofReal (k' x) := by
    refine withDensity_congr_ae ?_
    filter_upwards [hk'ae] with x hx
    rw [show ((((k x).toNNReal : ℝ≥0) : ℝ≥0∞)) = ENNReal.ofReal (k x) from rfl, hx]
  have hdm : (volume.withDensity fun x => ((((-k x)).toNNReal : ℝ≥0) : ℝ≥0∞))
      = volume.withDensity fun x => ENNReal.ofReal (-k' x) := by
    refine withDensity_congr_ae ?_
    filter_upwards [hk'ae] with x hx
    rw [show (((((-k x)).toNNReal : ℝ≥0) : ℝ≥0∞)) = ENNReal.ofReal (-k x) from rfl, hx]
  rw [hdp, hdm] at hJ
  -- the negative set carries no mass
  set S : Set ℝ := {x | k' x < 0} with hSdef
  have hSm : MeasurableSet S := hk'meas measurableSet_Iio
  have hleft : (volume.withDensity fun x => ENNReal.ofReal (k' x)) S = 0 := by
    rw [withDensity_apply _ hSm]
    refine (lintegral_eq_zero_iff (by fun_prop)).mpr ?_
    filter_upwards [self_mem_ae_restrict hSm] with x hx
    have : k' x < 0 := hx
    simp [ENNReal.ofReal_eq_zero, this.le]
  have hright : (volume.withDensity fun x => ENNReal.ofReal (k' x)) S
      = ν S + (volume.withDensity fun x => ENNReal.ofReal (-k' x)) S := by
    rw [hJ, Measure.add_apply]
  rw [hleft] at hright
  have hmzero : (volume.withDensity fun x => ENNReal.ofReal (-k' x)) S = 0 :=
    (add_eq_zero.mp hright.symm).2
  have hnull : volume S = 0 := by
    rw [withDensity_apply _ hSm] at hmzero
    have hae := (lintegral_eq_zero_iff
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (-k' x))).mp hmzero
    have hbad : ∀ᵐ _x ∂(volume.restrict S), False := by
      filter_upwards [hae, self_mem_ae_restrict hSm] with x hx hxS
      have h1 : k' x < 0 := hxS
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hbad
    exact hbad
  have hknn : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x := by
    have hS : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ S := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [hk'ae, hS] with x hx hxS
    rw [hx]
    exact not_lt.mp hxS
  refine ⟨hknn, ?_⟩
  have hmz : (volume.withDensity fun x => ENNReal.ofReal (-k' x)) = 0 := by
    have hzero : (fun x => ENNReal.ofReal (-k' x)) =ᵐ[volume] 0 := by
      filter_upwards [hknn, hk'ae] with x hx hxe
      have hx' : 0 ≤ k' x := by rw [← hxe]; exact hx
      show ENNReal.ofReal (-k' x) = 0
      simp [ENNReal.ofReal_eq_zero, neg_nonpos.mpr hx']
    rw [withDensity_congr_ae hzero, withDensity_zero]
  rw [hmz, add_zero] at hJ
  rw [← hJ, ← hdp]
  rfl

end SpatialLine
