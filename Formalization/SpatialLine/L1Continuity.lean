/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transport
import SpatialLine.TransformUniqueness
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The modulus of continuity of translation, and what it buys for (A7)

Blueprint: `def:cascade-family` (A7), and the continuity paragraph in the proof of
`thm:main-characterization`. Nothing here is a blueprint node.

(A7) asks for continuity of `(s,t) ↦ Φ_{s,t} f` **into `L¹`**, which is strictly more than
convergence of the kernels. Paper I bridges the two with an `ε/3` argument on a compact carrying
most of the kernel's mass, and pays for a tail estimate to make the compact work. On the line
there is a cheaper route, and it is the one this file takes, because the estimate it rests on is
an identity rather than an approximation:

  `‖μ * f - f‖₁ ≤ ∫ ‖T_y f - f‖₁ μ(dy)`,                                            (★)

for a probability measure `μ`. Everything on the right is a *bounded continuous* function of
`y` vanishing at `y = 0`, so (★) converts "the kernel concentrates at the origin" into "the
operator converges strongly", with no compact, no density argument and no tail estimate. What
makes it work on the line and not on the half-line is that `Θ_f(y) = ‖T_y f - f‖₁` is continuous
in `y` — strong continuity of the translation group on `L¹`, which Mathlib carries as the
`ContinuousVAdd ℝᵈᵃᵃ (Lp E p volume)` instance.

The review (2026-09-09, R30) priced (A7) at a concrete family as `main_construction`'s own `ε/3`
argument written again, and recommended extracting a reusable continuity lemma first. (★) is
that lemma, and it turned out *cheaper* than the estimate the review had in mind: the `ε/3`
argument is not needed at all once the kernels form a convolution semigroup in one parameter,
because then the difference of two operators factors through a single increment — see
`SpatialLine/Gaussian.lean`.

## Two consequences the two-parameter case needs

A *hemigroup* has no single increment parameter, so a difference `Φ_{s,t} - Φ_{s',t'}` factors
only after the two endpoints are moved one at a time. Moving the left endpoint leaves an
increment applied *first*, which the contraction bound absorbs; moving the right endpoint leaves
one applied *last*, and (★) then has to be read at the moved element rather than at `f`. That
costs nothing, because `Θ` is *decreasing under convolution*: translation commutes with
convolution and convolution is a contraction, so `Θ_{μ*f} ≤ Θ_f` pointwise. This is
`transDiff_mconvL1_le`, and it is what makes the estimate uniform over the family.

The other consequence is the bridge to Lévy's continuity theorem: a sequence of kernels whose
characteristic functions tend to `1` concentrates at the origin, hence gives operators tending
strongly to the identity (`tendsto_norm_mconvL1_sub_of_tendsto_charFun`). This is the form
`prop:levy-continuity`'s first clause is consumed in, and it is Mathlib's
`ProbabilityMeasure.tendsto_of_tendsto_charFun` with (★) on top.
-/

namespace SpatialLine

open MeasureTheory Set Filter DomAddAct
open scoped ENNReal Topology

/-! ## The modulus of continuity -/

/-- `Θ_f(y) = ‖T_y f - f‖₁`, the modulus of continuity of translation at `f`. -/
noncomputable def transDiff (f : X) (y : ℝ) : ℝ := ‖transL1 y f - f‖

theorem continuous_transDiff (f : X) : Continuous (transDiff f) :=
  ((continuous_transL1 f).sub continuous_const).norm

theorem transDiff_nonneg (f : X) (y : ℝ) : 0 ≤ transDiff f y := norm_nonneg _

@[simp]
theorem transDiff_zero (f : X) : transDiff f 0 = 0 := by
  simp only [transDiff]
  rw [norm_eq_zero, sub_eq_zero]
  refine Lp.ext ?_
  refine (coeFn_transL1 0 f).trans ?_
  filter_upwards with x
  simp

/-- `Θ_f ≤ 2‖f‖`: the bound that makes `Θ_f` dominated-convergence-ready against any probability
measure. -/
theorem transDiff_le (f : X) (y : ℝ) : transDiff f y ≤ 2 * ‖f‖ := by
  have h1 : ‖transL1 y f‖ ≤ ‖f‖ := by
    calc ‖transL1 y f‖ ≤ ‖transL1 y‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ := by
          have hop : ‖transL1 y‖ ≤ 1 := by
            rw [transL1]
            exact LinearMap.mkContinuous_norm_le _ zero_le_one _
          nlinarith [norm_nonneg f]
      _ = ‖f‖ := one_mul _
  calc transDiff f y ≤ ‖transL1 y f‖ + ‖f‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith

theorem integrable_transDiff (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Integrable (transDiff f) μ :=
  (integrable_const (2 * ‖f‖)).mono' (continuous_transDiff f).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiff_nonneg f y)]
      exact transDiff_le f y)

/-- `Θ_f(y)` as a lower integral, the register the estimate (★) is proved in. -/
theorem lintegral_enorm_sub_eq (f : X) (y : ℝ) :
    ∫⁻ x, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ = ENNReal.ofReal (transDiff f y) := by
  have hint : Integrable (fun x => (f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x) volume :=
    (integrable_translate (L1.integrable_coeFn f) y).sub (L1.integrable_coeFn f)
  have hlt : ∫⁻ x, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ ≠ ⊤ := by
    have h := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    exact h.ne
  have heq : ∫⁻ x, ‖((transL1 y f : X) : ℝ → ℝ) x - (f : ℝ → ℝ) x‖ₑ
      = ∫⁻ x, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ := by
    refine lintegral_congr_ae ?_
    filter_upwards [coeFn_transL1 y f] with x hx
    rw [hx]
  rw [transDiff, norm_sub_eq_lintegral, heq, ENNReal.ofReal_toReal hlt]

/-! ## The estimate (★) -/

/-- **(★) in `ℝ≥0∞`.** For a probability measure, `μ * f - f` is the `μ`-average of the
translates `T_y f - f`, so its `L¹` norm is at most the average of theirs. Both steps are
Tonelli: the pointwise bound is `‖∫ ·‖ ≤ ∫ ‖·‖`, and the swap needs no integrability side
condition because everything is `ℝ≥0∞`-valued. -/
theorem lintegral_enorm_mconv_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : X) :
    ∫⁻ x, ‖mconv μ (f : ℝ → ℝ) x - (f : ℝ → ℝ) x‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (transDiff f y) ∂μ := by
  have hf := Lp.aestronglyMeasurable f
  have hfi := L1.integrable_coeFn f
  have hstep : ∀ᵐ x ∂volume, ‖mconv μ (f : ℝ → ℝ) x - (f : ℝ → ℝ) x‖ₑ
      ≤ ∫⁻ y, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ ∂μ := by
    filter_upwards [(integrable_uncurry_sub μ hf hfi).prod_right_ae] with x hx
    simp only [Function.uncurry] at hx
    have hsplit : mconv μ (f : ℝ → ℝ) x - (f : ℝ → ℝ) x
        = ∫ y, ((f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x) ∂μ := by
      rw [integral_sub hx (integrable_const _), integral_const, mconv_apply]
      simp
    rw [hsplit]
    exact enorm_integral_le_lintegral_enorm _
  calc ∫⁻ x, ‖mconv μ (f : ℝ → ℝ) x - (f : ℝ → ℝ) x‖ₑ
      ≤ ∫⁻ x, (∫⁻ y, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ ∂μ) := lintegral_mono_ae hstep
    _ = ∫⁻ y, (∫⁻ x, ‖(f : ℝ → ℝ) (x - y) - (f : ℝ → ℝ) x‖ₑ) ∂μ := by
        refine lintegral_lintegral_swap ?_
        have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (f : ℝ → ℝ) (p.1 - p.2))
            (volume.prod μ) :=
          hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
        have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (f : ℝ → ℝ) p.1) (volume.prod μ) :=
          hf.comp_fst
        exact (h1.sub h2).enorm
    _ = ∫⁻ y, ENNReal.ofReal (transDiff f y) ∂μ := by
        simp only [lintegral_enorm_sub_eq]

/-- **(★).** `‖μ * f - f‖₁ ≤ ∫ Θ_f dμ` for a probability measure `μ`.

This is the whole of the (A7) machinery: it reduces strong convergence of the operators to
concentration of the kernels at the origin, tested against a fixed bounded continuous function
that vanishes there. -/
theorem norm_mconvL1_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : X) :
    ‖mconvL1 μ f - f‖ ≤ ∫ y, transDiff f y ∂μ := by
  have hofReal : ∫⁻ y, ENNReal.ofReal (transDiff f y) ∂μ
      = ENNReal.ofReal (∫ y, transDiff f y ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_transDiff μ f)
      (Eventually.of_forall (transDiff_nonneg f))).symm
  have hcoe : ∫⁻ x, ‖((mconvL1 μ f - f : X) : ℝ → ℝ) x‖ₑ
      = ∫⁻ x, ‖mconv μ (f : ℝ → ℝ) x - (f : ℝ → ℝ) x‖ₑ := by
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (mconvL1 μ f) f, coeFn_mconvL1 μ f] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hbound : ∫⁻ x, ‖((mconvL1 μ f - f : X) : ℝ → ℝ) x‖ₑ
      ≤ ENNReal.ofReal (∫ y, transDiff f y ∂μ) := by
    rw [hcoe, ← hofReal]
    exact lintegral_enorm_mconv_sub_le μ f
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
  calc (∫⁻ x, ‖((mconvL1 μ f - f : X) : ℝ → ℝ) x‖ₑ).toReal
      ≤ (ENNReal.ofReal (∫ y, transDiff f y ∂μ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ∫ y, transDiff f y ∂μ :=
        ENNReal.toReal_ofReal (integral_nonneg (transDiff_nonneg f))

/-- **The modulus of continuity decreases under convolution.** Translation commutes with
convolution and convolution by a probability measure is a contraction, so `Θ_{ν*f} ≤ Θ_f`. -/
theorem transDiff_mconvL1_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : X) (y : ℝ) :
    transDiff (mconvL1 ν f) y ≤ transDiff f y := by
  have hcomm : transL1 y (mconvL1 ν f) - mconvL1 ν f = mconvL1 ν (transL1 y f - f) := by
    rw [ContinuousLinearMap.map_sub, mconvL1_transL1]
  rw [transDiff, transDiff, hcomm]
  exact norm_mconvL1_le ν _

/-- **(★) after an operator.** The estimate read at `ν * f` rather than at `f`, with the bound
still expressed at `f`. This is the form the two-parameter case needs: moving the right endpoint
of `Φ_{s,t}` leaves an increment applied last, to an element that varies with the parameters. -/
theorem norm_mconvL1_comp_sub_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : X) :
    ‖mconvL1 μ (mconvL1 ν f) - mconvL1 ν f‖ ≤ ∫ y, transDiff f y ∂μ :=
  (norm_mconvL1_sub_le μ (mconvL1 ν f)).trans
    (integral_mono (integrable_transDiff μ _) (integrable_transDiff μ f)
      (transDiff_mconvL1_le ν f))

/-! ## Lévy's continuity theorem, in the form (A7) consumes -/

/-- The modulus of continuity as a bounded continuous function, so that weak convergence of the
kernels can be tested against it. -/
noncomputable def transDiffBCF (f : X) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (transDiff f) (continuous_transDiff f)
    (2 * ‖f‖) fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiff_nonneg f y)]
      exact transDiff_le f y

@[simp]
theorem transDiffBCF_apply (f : X) (y : ℝ) : transDiffBCF f y = transDiff f y := rfl

/-- **Kernels whose transforms tend to `1` concentrate at the origin**, measured by the modulus
of continuity: the transform of `δ₀` is `1`, so the hypothesis is weak convergence to `δ₀` by
Lévy's theorem, and `Θ_f` is bounded, continuous and vanishes there. -/
theorem tendsto_integral_transDiff_of_tendsto_charFun {μ : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : X) :
    Tendsto (fun n => ∫ y, transDiff f y ∂(μ n)) atTop (𝓝 0) := by
  have hdirac : ∀ ω : ℝ, charFun (Measure.dirac (0 : ℝ)) ω = 1 := by
    intro ω
    rw [charFun_dirac]
    simp
  have := levy_continuity (μ := μ) (μ₀ := Measure.dirac (0 : ℝ))
    (by simpa [hdirac] using h) (transDiffBCF f)
  simpa using this

/-- **Kernels whose transforms tend to `1` give operators tending strongly to the identity.**
(★) transfers the concentration above to the operators. -/
theorem tendsto_norm_mconvL1_sub_of_tendsto_charFun {μ : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : X) :
    Tendsto (fun n => ‖mconvL1 (μ n) f - f‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_mconvL1_sub_le (μ n) f)
    (tendsto_integral_transDiff_of_tendsto_charFun h f)

end SpatialLine
