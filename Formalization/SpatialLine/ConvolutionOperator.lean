/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Family

/-!
# Convolution by a measure as an operator on `L¹`, and the axioms it satisfies

Blueprint: `blueprint/src/parts/04-representation.tex`, the converse clause of
`lem:convolution-representation`.

`SpatialLine/Basic.lean` builds `mconv` and packages it as the bounded operator `mconvL1`. This
file proves what that operator *does*: (A2) translation covariance, (A3) commutation with
reflection for a symmetric measure, (A4) positivity, (A5) unit mass, the composition law behind
(A6), and that `δ₀` acts as the identity. Each is the corresponding pointwise fact read through
`coeFn_mconvL1`, with the pointwise hypotheses supplied a.e. by `ae_ae_sub_of_ae`.

-- core candidate: this whole block is Paper I's `Operator.lean` / `OperatorL1.lean` /
-- `Family.lean` transport section with causality replaced by reflection symmetry. Nothing in it
-- mentions the axioms of the article; every statement is about convolution operators on `L¹(ℝ)`.
-- SKELETON.md F9 lists it as the second `ScaleSpaceCore` candidate after `laplaceL`, and it is
-- consumed four times in this article alone (`representation_converse`, `two_members_gaussian`,
-- `two_members_matern`, `main_construction`).

## Provenance

twin: `Hemigroup.mconv_comp_sub`, `Hemigroup.mconv_nonneg`, `Hemigroup.integral_mconv`,
`Hemigroup.mconv_conv`, `Hemigroup.mconv_dirac_zero`, `Hemigroup.mconvL1_congr`,
`Hemigroup.norm_mconvL1_le`, `Hemigroup.mconvL1_transL1`, `Hemigroup.isNonneg_mconvL1`,
`Hemigroup.integral_mconvL1`, `Hemigroup.mconvL1_satisfies_axioms`.

The one declaration with no causal twin is `mconvL1_reflL1`. Where the causal development
transports causality of the measure into causality of the image, the line transports symmetry of
the measure into commutation with `R`, and the proof is the change of variables `y ↦ -y` that
`IsSymmetric` licenses. The pointwise form is stated for a *strongly measurable* representative
rather than an a.e. one: `mconv μ f` sees `f` through a `μ`-integral of translates, and a
`volume`-null modification of `f` need not be `μ`-null, so the `L¹` statement picks a
representative first (`AEStronglyMeasurable.mk`) and transports back with `mconv_congr_ae`. This
is the same phenomenon Paper I's `OperatorL1.lean` records for `mconv_congr_ae`.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

variable {μ : Measure ℝ}

/-! ## The pointwise facts -/

/-- **(A2)** at the level of functions: convolution commutes with translation. -/
theorem mconv_comp_sub (μ : Measure ℝ) (f : ℝ → ℝ) (a : ℝ) :
    mconv μ (fun x => f (x - a)) = fun x => mconv μ f (x - a) := by
  funext x
  simp only [mconv_apply, sub_right_comm]

/-- **(A4)** at the level of functions: convolution preserves the positive cone. -/
theorem mconv_nonneg (μ : Measure ℝ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ mconv μ f x := integral_nonneg fun _ => hf _

/-- **(A3)** at the level of functions: for a symmetric measure, convolution commutes with
reflection. The change of variables is `y ↦ -y`, which `IsSymmetric` says leaves `μ` alone. -/
theorem mconv_reflect (hμ : IsSymmetric μ) {f : ℝ → ℝ} (hf : StronglyMeasurable f) (x : ℝ) :
    mconv μ (fun u => f (-u)) x = mconv μ f (-x) := by
  simp only [mconv_apply]
  have hmap : ∫ y, f (y - x) ∂μ = ∫ y, f (-y - x) ∂μ := by
    conv_lhs => rw [← hμ]
    exact integral_map measurable_neg.aemeasurable
      ((hf.comp_measurable (measurable_id.sub_const x)).aestronglyMeasurable)
  have hl : (fun y : ℝ => f (-(x - y))) = fun y : ℝ => f (y - x) := by
    funext y; rw [neg_sub]
  rw [hl, hmap]
  simp only [show ∀ y : ℝ, -y - x = -x - y from fun y => by ring]

/-- **(A5)** at the level of functions: `∫ (μ * f) = ‖μ‖ ∫ f`. -/
theorem integral_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    ∫ x, mconv μ f x = (μ univ).toReal * ∫ x, f x := by
  simp only [mconv_apply]
  rw [integral_integral_swap (integrable_uncurry_sub μ hf hfi)]
  simp_rw [integral_sub_right_eq_self]
  rw [integral_const, smul_eq_mul, measureReal_def]

/-- **(A6)** at the level of functions: `ν * (μ * f) = (μ ∗ ν) * f`, a.e. -/
theorem mconv_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    mconv ν (mconv μ f) =ᵐ[volume] mconv (μ ∗ ν) f := by
  filter_upwards [(integrable_uncurry_sub (μ ∗ ν) hf hfi).prod_right_ae] with x hx
  simp only [Function.uncurry] at hx
  have hadd : AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) :=
    (measurable_fst.add measurable_snd).aemeasurable
  have hprod : Integrable (fun p : ℝ × ℝ => f (x - (p.1 + p.2))) (μ.prod ν) := by
    rw [Measure.conv] at hx
    exact (integrable_map_measure hx.aestronglyMeasurable hadd).mp hx
  have hmap : ∫ u, f (x - u) ∂(μ ∗ ν) = ∫ p : ℝ × ℝ, f (x - (p.1 + p.2)) ∂(μ.prod ν) := by
    rw [Measure.conv]
    exact integral_map hadd (by rw [← Measure.conv]; exact hx.aestronglyMeasurable)
  simp only [mconv_apply]
  rw [hmap, integral_prod_symm _ hprod]
  simp only [sub_add_eq_sub_sub, sub_right_comm]

/-- `δ₀ * f = f`: the diagonal clause of (A6). -/
theorem mconv_dirac_zero (f : ℝ → ℝ) : mconv (Measure.dirac 0) f = f := by
  funext x
  rw [mconv_apply, integral_dirac, sub_zero]

/-! ## The operator on `L¹` -/

/-- Equal measures give equal operators. Needed because `mconvL1` carries an `IsFiniteMeasure`
instance argument, so `rw` on the measure produces an ill-typed motive. -/
theorem mconvL1_congr {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) :
    mconvL1 μ = mconvL1 ν := by
  subst h
  congr 1

/-- **(A1)** with the constant made explicit: `Φ` is a contraction for a probability measure. -/
theorem norm_mconvL1_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : X) :
    ‖mconvL1 μ f‖ ≤ ‖f‖ := by
  have hop : ‖mconvL1 μ‖ ≤ 1 := by
    rw [mconvL1]
    refine le_trans (LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _) ?_
    rw [measure_univ, ENNReal.toReal_one]
  calc ‖mconvL1 μ f‖ ≤ ‖mconvL1 μ‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by nlinarith [norm_nonneg f]
    _ = ‖f‖ := one_mul _

/-- **(A2)** for `mconvL1`. -/
theorem mconvL1_transL1 [IsFiniteMeasure μ] (a : ℝ) (f : X) :
    mconvL1 μ (transL1 a f) = transL1 a (mconvL1 μ f) := by
  refine Lp.ext ?_
  refine (coeFn_mconvL1 μ (transL1 a f)).trans ?_
  refine (mconv_congr_ae μ (coeFn_transL1 a f)).trans ?_
  rw [mconv_comp_sub]
  refine Filter.EventuallyEq.symm ?_
  refine (coeFn_transL1 a (mconvL1 μ f)).trans ?_
  exact translate_congr_ae a (coeFn_mconvL1 μ f)

/-- **(A3)** for `mconvL1`: a symmetric measure gives an operator commuting with reflection. -/
theorem mconvL1_reflL1 [IsFiniteMeasure μ] (hμ : IsSymmetric μ) (f : X) :
    mconvL1 μ (reflL1 f) = reflL1 (mconvL1 μ f) := by
  set f₀ := (Lp.aestronglyMeasurable f).mk (f : ℝ → ℝ) with hf₀
  have hfm : StronglyMeasurable f₀ := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hfae : (f : ℝ → ℝ) =ᵐ[volume] f₀ := (Lp.aestronglyMeasurable f).ae_eq_mk
  refine Lp.ext ?_
  have hlhs : ((mconvL1 μ (reflL1 f) : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (fun u => f₀ (-u)) :=
    (coeFn_mconvL1 μ (reflL1 f)).trans
      (mconv_congr_ae μ ((coeFn_reflL1 f).trans (reflect_congr_ae hfae)))
  have hrhs : ((reflL1 (mconvL1 μ f) : X) : ℝ → ℝ) =ᵐ[volume] fun x => mconv μ f₀ (-x) :=
    (coeFn_reflL1 (mconvL1 μ f)).trans
      (reflect_congr_ae ((coeFn_mconvL1 μ f).trans (mconv_congr_ae μ hfae)))
  refine hlhs.trans (Filter.EventuallyEq.symm (hrhs.trans ?_))
  exact Filter.Eventually.of_forall fun x => (mconv_reflect hμ hfm x).symm

/-- **(A4)** for `mconvL1`. -/
theorem isNonneg_mconvL1 [IsFiniteMeasure μ] (f : X) (hf : IsNonneg f) :
    IsNonneg (mconvL1 μ f) := by
  filter_upwards [coeFn_mconvL1 μ f, ae_ae_sub_of_ae μ hf] with x hcoe hx
  rw [Pi.zero_apply, hcoe, mconv_apply]
  exact integral_nonneg_of_ae hx

/-- **(A5)** for `mconvL1`, stated for every `f`: the Tonelli identity does not see the sign. -/
theorem integral_mconvL1 [IsProbabilityMeasure μ] (f : X) :
    ∫ x, ((mconvL1 μ f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x := by
  rw [integral_congr_ae (coeFn_mconvL1 μ f),
    integral_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f),
    measure_univ, ENNReal.toReal_one, one_mul]

/-- **(A6)** for `mconvL1`: composing the operators convolves the measures. -/
theorem mconvL1_comp (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (mconvL1 ν).comp (mconvL1 μ) = mconvL1 (μ ∗ ν) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine ((coeFn_mconvL1 ν (mconvL1 μ f)).trans
    (mconv_congr_ae ν (coeFn_mconvL1 μ f))).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1 (μ ∗ ν) f).symm
  exact mconv_conv μ ν (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)

/-- `δ₀` acts as the identity on `L¹`. -/
theorem mconvL1_dirac_zero : mconvL1 (Measure.dirac (0 : ℝ)) = ContinuousLinearMap.id ℝ X := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_mconvL1 _ f).trans ?_
  rw [mconv_dirac_zero]
  rfl

/-! ## `lem:convolution-representation`, the converse clause -/

/-- **`lem:convolution-representation`, the converse.**

Reading: "every symmetric probability measure defines an operator satisfying (A1)–(A5)". (A1) is
the type of `mconvL1 μ`, so the conclusion lists (A2)–(A5); the symmetry hypothesis is consumed
by (A3) alone.

twin: `Hemigroup.mconvL1_satisfies_axioms`, which bundles its four clauses for the same reason:
the blueprint node wants one Lean name, not four. -/
theorem representation_converse (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ) :
    (∀ (a : ℝ) (f : X), mconvL1 μ (transL1 a f) = transL1 a (mconvL1 μ f)) ∧
      (∀ f : X, mconvL1 μ (reflL1 f) = reflL1 (mconvL1 μ f)) ∧
      (∀ f : X, IsNonneg f → IsNonneg (mconvL1 μ f)) ∧
      (∀ f : X, IsNonneg f →
        ∫ x, ((mconvL1 μ f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x) :=
  ⟨fun a f => mconvL1_transL1 a f, fun f => mconvL1_reflL1 hsym f,
    fun f hf => isNonneg_mconvL1 f hf, fun f _ => integral_mconvL1 f⟩

end SpatialLine
