/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Nonvanishing
import SpatialLine.TransformBridge
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Pairing a test function against `mconv`, and the measure it determines

Vocabulary, not a blueprint node. What is proved here is the block finding **F9** of
`SKELETON.md` calls the natural second `ScaleSpaceCore` candidate: the transport lemmas that
turn an identity between convolution *operators* into an identity between *measures*, and the
transform identities that turn one between measures into one between real numbers.

## Why this file exists, and what it duplicates

`lem:convolution-representation` asserts existence **and** uniqueness, and Chapters 5 and 6 take
the whole conclusion as the hypothesis `IsKernelFamily`. What those chapters then need, over and
over, is not the representation but its **uniqueness clause** read the other way round: two
finite measures that convolve one test function alike are equal. That is a statement about
measures with no axiom in it, and Paper I keeps it in `Nondegeneracy.lean`, apart from the
existence proof in `Representation.lean`, for exactly this reason.

`integral_mul_mconv` is Paper I's `Hemigroup.integral_mul_mconv` verbatim — its hypotheses are
already in `SpatialLine/Basic.lean`, `integrable_uncurry_sub` doing the work Fubini needs. What
is new is the test pair. The causal argument pairs the box `1_{(0,1)}` against a clamped
exponential and reads off a Laplace transform; on the line the box is the wrong function,
its cosine transform `2 sin ω / ω` vanishing at every `ω ∈ πℤ`, and a measure is not determined
by a transform that is allowed to vanish. The **standard Gaussian density** is the test
function instead: even, integrable, and with cosine transform `e^{-ω²/2}`, which is positive at
every frequency. Pairing it against `cos(ω ·)` and `sin(ω ·)` returns both halves of the
characteristic function, so `Measure.ext_of_charFun` finishes.

The evenness of the test function is what makes the two pairings separate cleanly: for even `f`
the sine moment `∫ sin(ωu) f(u) du` vanishes, so the cosine pairing sees only `∫ cos(ωr) μ(dr)`
and the sine pairing only `∫ sin(ωr) μ(dr)`. With a general `f` the two would mix and neither
would be recoverable from one test function.

## What the wave-1 merge removed from this file

Eight declarations proved here in parallel with chapters 2, 3 and 4 were deleted at the merge of
2026-09-09 and their consumers rewired to the surviving copy: the transform bridge
(`fourierCos_eq_charFun_re`, `charFun_eq_fourierCos_of_symmetric`) and `integrable_cos_mul` to
chapter 2's `SpatialLine/TransformBridge.lean`; the transport lemmas `mconv_conv` and
`mconv_dirac_zero` to chapter 4's `SpatialLine/ConvolutionOperator.lean`; `gaussL1` and its
coercion lemma to `SpatialLine/BochnerConvolution.lean`; and `eq_of_mconv_ae`, which had no
consumer, to `eq_mconvL1_of_ae` and `mconvL1_injective` in `SpatialLine/Representation.lean`.
`fourierSin`, `charFun_eq` and the Gaussian test pair are this file's own and stay.

The import of `SpatialLine.Nonvanishing` that pays for the transport lemmas is not incidental:
chapters 5 and 6 consume `lem:nonvanishing` and the uniqueness clause of
`lem:convolution-representation` throughout, so the dependence belongs in the import graph. It
corrects the independence `SKELETON.md` F4 claimed for these chapters.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The odd half of the transform, and the decomposition of `charFun` -/

/-- `∫ sin(ωx) μ(dx)`, the odd half of the transform. It is not part of the article's
vocabulary — every kernel is symmetric and this vanishes — but the *proof* that the kernels are
symmetric has to talk about it. -/
noncomputable def fourierSin (μ : Measure ℝ) (ω : ℝ) : ℝ := ∫ x, Real.sin (ω * x) ∂μ

lemma fourierSin_apply (μ : Measure ℝ) (ω : ℝ) :
    fourierSin μ ω = ∫ x, Real.sin (ω * x) ∂μ := rfl

/-- **The characteristic function in its two real halves**: `μ̂ = fourierCos + i fourierSin`.

Mathlib's `charFun` uses the sign convention opposite to `(2.1)`; the two agree on the cosine
half and differ by a sign on the sine half, which is immaterial everywhere below because the
sine half is only ever compared with itself or shown to vanish. -/
theorem charFun_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    charFun μ ω = ((fourierCos μ ω : ℝ) : ℂ) + Complex.I * ((fourierSin μ ω : ℝ) : ℂ) := by
  rw [charFun_apply_real]
  have hpt : ∀ x : ℝ, Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)
      = ((Real.cos (ω * x) : ℂ)) + Complex.I * ((Real.sin (ω * x) : ℂ)) := by
    intro x
    have hcast : (ω : ℂ) * (x : ℂ) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  simp only [hpt]
  rw [integral_add, integral_complex_ofReal, integral_const_mul, integral_complex_ofReal]
  · rfl
  · exact (integrable_cos_mul μ ω).ofReal
  · exact ((integrable_sin_mul μ ω).ofReal).const_mul _

/-- **A symmetric measure has vanishing sine transform.** -/
theorem fourierSin_eq_zero_of_symmetric {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsym : IsSymmetric μ) (ω : ℝ) : fourierSin μ ω = 0 := by
  have hmap : ∫ x, Real.sin (ω * x) ∂μ = ∫ x, Real.sin (ω * -x) ∂μ := by
    conv_lhs => rw [← hsym]
    exact integral_map (by fun_prop) (by fun_prop)
  simp only [mul_neg, Real.sin_neg, integral_neg] at hmap
  rw [fourierSin_apply]
  linarith

/-- **The cosine transform of a convolution of symmetric measures** is the product. This is what
turns the cascade law into additivity of the exponents. -/
theorem fourierCos_conv {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : IsSymmetric μ) (hν : IsSymmetric ν) (ω : ℝ) :
    fourierCos (μ ∗ ν) ω = fourierCos μ ω * fourierCos ν ω := by
  have h := charFun_conv (μ := μ) (ν := ν) ω
  rw [charFun_eq_fourierCos_of_symmetric hμ, charFun_eq_fourierCos_of_symmetric hν] at h
  rw [fourierCos_eq_charFun_re, h]
  simp

/-! ## Pairing a bounded test function against `mconv` -/

/-- **Pairing against a bounded function.** `∫ g · (μ * f) = ∫∫ g(t) f(t - r)`.

twin: `Hemigroup.integral_mul_mconv`, verbatim — the integrability Fubini needs is
`integrable_uncurry_sub`, dominated by `C`, which is why `g` is asked to be bounded rather than
integrable. -/
theorem integral_mul_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : Measurable g) {C : ℝ} (hgb : ∀ t, |g t| ≤ C) :
    ∫ t, g t * mconv μ f t = ∫ r, (∫ t, g t * f (t - r)) ∂μ := by
  have hFm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 * f (p.1 - p.2)) (volume.prod μ) :=
    ((hg.comp measurable_fst).aestronglyMeasurable).mul
      (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ))
  have hdom : Integrable (fun p : ℝ × ℝ => C * ‖f (p.1 - p.2)‖) (volume.prod μ) :=
    ((integrable_uncurry_sub μ hf hfi).norm).const_mul C
  have hFi : Integrable (fun p : ℝ × ℝ => g p.1 * f (p.1 - p.2)) (volume.prod μ) := by
    refine hdom.mono' hFm (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hgb p.1) (norm_nonneg _)
  calc ∫ t, g t * mconv μ f t
      = ∫ t, (∫ r, g t * f (t - r) ∂μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change g t * mconv μ f t = ∫ r, g t * f (t - r) ∂μ
        rw [mconv_apply, integral_const_mul]
    _ = ∫ r, (∫ t, g t * f (t - r)) ∂μ := integral_integral_swap hFi

/-! ## The even test function, translated -/

lemma integral_odd_eq_zero {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h1 : ∫ x, g (-x) = ∫ x, g x := integral_neg_eq_self g volume
  simp only [hodd, integral_neg] at h1
  linarith

variable {f : ℝ → ℝ}

lemma integrable_cos_mul_self (hfi : Integrable f) (ω : ℝ) :
    Integrable (fun u => Real.cos (ω * u) * f u) := by
  refine hfi.bdd_mul (c := 1)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  exact ae_of_all _ fun u => by simpa using Real.abs_cos_le_one (ω * u)

lemma integrable_sin_mul_self (hfi : Integrable f) (ω : ℝ) :
    Integrable (fun u => Real.sin (ω * u) * f u) := by
  refine hfi.bdd_mul (c := 1)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  exact ae_of_all _ fun u => by simpa using Real.abs_sin_le_one (ω * u)

/-- For an even `f` the sine moment vanishes — the fact that separates the two pairings. -/
lemma integral_sin_mul_eq_zero (heven : ∀ x, f (-x) = f x) (ω : ℝ) :
    ∫ u, Real.sin (ω * u) * f u = 0 := by
  refine integral_odd_eq_zero fun x => ?_
  rw [heven, mul_neg, Real.sin_neg, neg_mul]

/-- Translating the cosine test function against an even `f`. -/
lemma integral_cos_mul_translate (hfi : Integrable f) (heven : ∀ x, f (-x) = f x) (ω r : ℝ) :
    ∫ t, Real.cos (ω * t) * f (t - r) = Real.cos (ω * r) * ∫ u, Real.cos (ω * u) * f u := by
  have hshift : ∫ t, Real.cos (ω * t) * f (t - r)
      = ∫ u, Real.cos (ω * (u + r)) * f u := by
    rw [← integral_add_right_eq_self (fun t => Real.cos (ω * t) * f (t - r)) r]
    simp
  rw [hshift]
  have hpt : ∀ u : ℝ, Real.cos (ω * (u + r)) * f u
      = Real.cos (ω * r) * (Real.cos (ω * u) * f u)
        - Real.sin (ω * r) * (Real.sin (ω * u) * f u) := by
    intro u
    rw [mul_add, Real.cos_add]
    ring
  simp only [hpt]
  rw [integral_sub ((integrable_cos_mul_self hfi ω).const_mul _)
      ((integrable_sin_mul_self hfi ω).const_mul _),
    integral_const_mul, integral_const_mul, integral_sin_mul_eq_zero heven, mul_zero, sub_zero]

/-- Translating the sine test function against an even `f`. -/
lemma integral_sin_mul_translate (hfi : Integrable f) (heven : ∀ x, f (-x) = f x) (ω r : ℝ) :
    ∫ t, Real.sin (ω * t) * f (t - r) = Real.sin (ω * r) * ∫ u, Real.cos (ω * u) * f u := by
  have hshift : ∫ t, Real.sin (ω * t) * f (t - r)
      = ∫ u, Real.sin (ω * (u + r)) * f u := by
    rw [← integral_add_right_eq_self (fun t => Real.sin (ω * t) * f (t - r)) r]
    simp
  rw [hshift]
  have hpt : ∀ u : ℝ, Real.sin (ω * (u + r)) * f u
      = Real.sin (ω * r) * (Real.cos (ω * u) * f u)
        + Real.cos (ω * r) * (Real.sin (ω * u) * f u) := by
    intro u
    rw [mul_add, Real.sin_add]
    ring
  simp only [hpt]
  rw [integral_add ((integrable_cos_mul_self hfi ω).const_mul _)
      ((integrable_sin_mul_self hfi ω).const_mul _),
    integral_const_mul, integral_const_mul, integral_sin_mul_eq_zero heven, mul_zero, add_zero]

/-- **The cosine pairing factorises.** -/
theorem integral_cos_mul_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] (hfi : Integrable f)
    (hfm : Measurable f) (heven : ∀ x, f (-x) = f x) (ω : ℝ) :
    ∫ t, Real.cos (ω * t) * mconv μ f t = (∫ u, Real.cos (ω * u) * f u) * fourierCos μ ω := by
  rw [integral_mul_mconv (f := f) (g := fun t => Real.cos (ω * t)) μ
    hfm.aestronglyMeasurable hfi (by fun_prop) (C := 1) (fun t => Real.abs_cos_le_one _)]
  simp only [integral_cos_mul_translate hfi heven ω]
  rw [integral_mul_const, fourierCos_apply]
  ring

/-- **The sine pairing factorises**, against the same cosine moment of the test function. -/
theorem integral_sin_mul_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] (hfi : Integrable f)
    (hfm : Measurable f) (heven : ∀ x, f (-x) = f x) (ω : ℝ) :
    ∫ t, Real.sin (ω * t) * mconv μ f t = (∫ u, Real.cos (ω * u) * f u) * fourierSin μ ω := by
  rw [integral_mul_mconv (f := f) (g := fun t => Real.sin (ω * t)) μ
    hfm.aestronglyMeasurable hfi (by fun_prop) (C := 1) (fun t => Real.abs_sin_le_one _)]
  simp only [integral_sin_mul_translate hfi heven ω]
  rw [integral_mul_const, fourierSin_apply]
  ring

/-! ## The Gaussian test function -/

/-- The standard Gaussian density, the test function of every argument below. Even, integrable,
and with a cosine transform that vanishes nowhere — which the box, the causal test function, is
not. -/
noncomputable def gaussTest : ℝ → ℝ := gaussianPDFReal 0 1

lemma measurable_gaussTest : Measurable gaussTest := measurable_gaussianPDFReal 0 1

lemma integrable_gaussTest : Integrable gaussTest := integrable_gaussianPDFReal 0 1

lemma gaussTest_even (x : ℝ) : gaussTest (-x) = gaussTest x := by
  simp [gaussTest, gaussianPDFReal]

lemma gaussTest_nonneg (x : ℝ) : 0 ≤ gaussTest x := gaussianPDFReal_nonneg 0 1 x

/-- **The cosine moment of the test function**, `e^{-ω²/2}` — positive at every frequency, which
is the whole reason the Gaussian is the test function. -/
theorem integral_cos_mul_gaussTest (ω : ℝ) :
    ∫ u, Real.cos (ω * u) * gaussTest u = Real.exp (-(ω ^ 2) / 2) := by
  have h1 : ∫ u, Real.cos (ω * u) * gaussTest u
      = ∫ u, Real.cos (ω * u) ∂(gaussianReal 0 1) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
    simp [gaussTest, smul_eq_mul, mul_comm]
  rw [h1, ← fourierCos_apply, fourierCos_gaussianReal]
  norm_num
  ring

theorem integral_cos_mul_gaussTest_pos (ω : ℝ) : 0 < ∫ u, Real.cos (ω * u) * gaussTest u := by
  rw [integral_cos_mul_gaussTest]
  exact Real.exp_pos _

/-! ## The measure is determined by its convolution operator -/

/-- **A finite measure is determined by how it convolves the Gaussian** — the uniqueness clause
of `lem:convolution-representation`, read as a statement about measures.

twin: `Hemigroup.eq_of_mconv_box_ae`, with the box and the clamped exponential replaced by the
Gaussian and the two trigonometric test functions; see the module docstring for why the box
cannot be used on the line. -/
theorem eq_of_mconv_gaussTest_ae {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : mconv μ gaussTest =ᵐ[volume] mconv ν gaussTest) : μ = ν := by
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have hcosint : ∫ t, Real.cos (ω * t) * mconv μ gaussTest t
      = ∫ t, Real.cos (ω * t) * mconv ν gaussTest t := by
    refine integral_congr_ae ?_
    filter_upwards [h] with t ht
    rw [ht]
  have hsinint : ∫ t, Real.sin (ω * t) * mconv μ gaussTest t
      = ∫ t, Real.sin (ω * t) * mconv ν gaussTest t := by
    refine integral_congr_ae ?_
    filter_upwards [h] with t ht
    rw [ht]
  rw [integral_cos_mul_mconv μ integrable_gaussTest measurable_gaussTest gaussTest_even ω,
    integral_cos_mul_mconv ν integrable_gaussTest measurable_gaussTest gaussTest_even ω] at hcosint
  rw [integral_sin_mul_mconv μ integrable_gaussTest measurable_gaussTest gaussTest_even ω,
    integral_sin_mul_mconv ν integrable_gaussTest measurable_gaussTest gaussTest_even ω] at hsinint
  have hC := (integral_cos_mul_gaussTest_pos ω).ne'
  rw [charFun_eq, charFun_eq, mul_left_cancel₀ hC hcosint, mul_left_cancel₀ hC hsinint]

/-- `gaussL1` read at the test function's own name.

Wave 1 of the merge (2026-09-09): `gaussL1` and its coercion lemma were proved twice, here and in
`SpatialLine/BochnerConvolution.lean`, where `lem:convolution-representation` needs them. That
copy survives; `gaussTest` is `gaussianPDFReal 0 1` by definition, so this adapter is the same
statement read at the name chapters 5 and 6 use. -/
lemma coeFn_gaussL1_gaussTest : ((gaussL1 : X) : ℝ → ℝ) =ᵐ[volume] gaussTest := coeFn_gaussL1

end SpatialLine
