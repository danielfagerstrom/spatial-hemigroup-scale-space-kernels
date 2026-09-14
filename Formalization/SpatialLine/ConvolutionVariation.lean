/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ConvolutionOperator
import SpatialLine.VariationDefs
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# What a convolution inherits: absolute continuity, symmetry, variation diminution

Blueprint: `blueprint/src/parts/13-noncreation.tex`, `thm:scale-monotone-noncreation`, step 1.

Step 1 smooths an increment by a Laplace kernel because ledger **A22**'s necessity leg is stated
for a *density* and an increment need not have one. The smoothed law `ν_ε = μ_{s,t} ∗ L` then has
to meet every hypothesis of `isPolyaExponent_of_variationDiminishing`, and three of those are
properties a convolution *inherits* rather than properties of either factor. Neither Mathlib nor
this library had them in the form needed, and this file is the three.

* **Absolute continuity**, `conv_absolutelyContinuous`: one factor absolutely continuous is
  enough, because the inner slice of a null set is a translate of it.
* **Symmetry**, `isSymmetric_conv`: negation is a group homomorphism, so it passes through the
  product and the addition.
* **Variation diminution**, `isVariationDiminishing_conv`: the convolution operator of `μ ∗ ν` is
  the composition of the two operators. `mconv_conv` proves that for an **integrable** test
  function, and `IsVariationDiminishing` quantifies over integrable **or bounded** ones, so the
  bounded leg is proved here (`mconv_conv_bounded`) — pointwise rather than almost everywhere,
  the integrand being bounded against a finite measure. Two smaller gaps sit in the way and are
  filled beside it: `mconv μ f` has to be known measurable (`measurable_mconv`, through
  `StronglyMeasurable.integral_prod_right'`) and bounded (`mconv_bounded`) before it can be fed
  to the second law, and the bound the definition supplies is only *almost everywhere* once a
  representative has been chosen, so `exists_good_representative` truncates it to a pointwise
  one. That truncation is the only unobvious step in the file.

Nothing here is specific to chapter 13; `isVariationDiminishing_conv` is the statement that the
Pólya frequency laws are closed under convolution, read at the operators.

Proving campaign, chapter 13, wave 5 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Absolute continuity and symmetry -/

/-- **A convolution with an absolutely continuous factor is absolutely continuous.** -/

theorem conv_absolutelyContinuous {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hν : ν ≪ volume) : (μ ∗ ν) ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  have hmA : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) :=
    (measurable_fst.add measurable_snd) hA
  rw [Measure.conv, Measure.map_apply (by fun_prop) hA, Measure.prod_apply hmA]
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hmA)).mpr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hset : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) = (fun y : ℝ => y + x) ⁻¹' A := by
    ext y; simp [add_comm]
  simp only [Pi.zero_apply, hset]
  refine hν ?_
  rw [show (fun y : ℝ => y + x) ⁻¹' A = (fun y : ℝ => y + x) ⁻¹' A from rfl]
  simpa [hA0] using measure_preimage_add_right volume x A

/-- **A convolution of symmetric laws is symmetric.** -/
theorem isSymmetric_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hμ : IsSymmetric μ) (hν : IsSymmetric ν) : IsSymmetric (μ ∗ ν) := by
  rw [IsSymmetric, Measure.conv, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun x : ℝ => -x) ∘ (fun p : ℝ × ℝ => p.1 + p.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [IsSymmetric] at hμ hν
  rw [hμ, hν, ← Measure.conv]

/-- **(A6) at the level of functions, for a bounded test function**: the pointwise companion of
`mconv_conv`, which asks for an integrable one. -/
theorem mconv_conv_bounded (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : ℝ) :
    mconv ν (mconv μ f) x = mconv (μ ∗ ν) f x := by
  have hbound : ∀ y : ℝ, ‖f y‖ ≤ C := fun y => by simpa [Real.norm_eq_abs] using hC y
  have hprodint : Integrable (fun p : ℝ × ℝ => f (x - (p.1 + p.2))) (μ.prod ν) := by
    refine ⟨((hf.comp (measurable_const.sub (measurable_fst.add measurable_snd)))
      ).aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded (C := C) (.of_forall fun p => hbound _)
  have hmap : ∫ u, f (x - u) ∂(μ ∗ ν) = ∫ p : ℝ × ℝ, f (x - (p.1 + p.2)) ∂(μ.prod ν) := by
    rw [Measure.conv]
    exact integral_map (measurable_fst.add measurable_snd).aemeasurable
      (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  simp only [mconv_apply]
  rw [hmap, integral_prod_symm _ hprodint]
  simp only [sub_add_eq_sub_sub, sub_right_comm]

/-! ## Variation diminution composes -/

/-- `signChangesAE` sees a function only through its almost-everywhere class. -/
theorem signChangesAE_congr {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    signChangesAE f = signChangesAE g := by
  have hset : {u : ℝ → ℝ | u =ᵐ[volume] f} = {u : ℝ → ℝ | u =ᵐ[volume] g} := by
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hu; exact hu.trans h
    · intro hu; exact hu.trans h.symm
  rw [signChangesAE, signChangesAE, hset]

/-- `mconv μ f` is measurable when `f` is. -/
theorem measurable_mconv (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (mconv μ f) := by
  have h : StronglyMeasurable (Function.uncurry fun x y : ℝ => f (x - y)) :=
    (hf.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have h2 := (h.integral_prod_right' (ν := μ)).measurable
  simp only [Function.uncurry] at h2
  exact h2

/-- `mconv μ f` inherits a bound from `f` when `μ` is a probability law. -/
theorem mconv_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : ℝ) : |mconv μ f x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (C := C) (μ := μ)
    (f := fun y => f (x - y)) (.of_forall fun y => by simpa [Real.norm_eq_abs] using hC (x - y))
  simpa [mconv_apply, Real.norm_eq_abs, measure_univ] using h

/-- A good representative: measurable, almost everywhere equal, and carrying the same
integrability or the same bound *everywhere*. The truncation is what turns an almost-everywhere
bound into a pointwise one. -/
theorem exists_good_representative {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hgb : Integrable g volume ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C) :
    ∃ g₀ : ℝ → ℝ, Measurable g₀ ∧ g =ᵐ[volume] g₀ ∧
      (Integrable g₀ volume ∨ ∃ C : ℝ, ∀ x, |g₀ x| ≤ C) := by
  rcases hgb with hint | ⟨C, hC⟩
  · exact ⟨hg.mk g, hg.stronglyMeasurable_mk.measurable, hg.ae_eq_mk,
      Or.inl (hint.congr hg.ae_eq_mk)⟩
  · have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
    set g' : ℝ → ℝ := hg.mk g with hg'def
    have hg'meas : Measurable g' := hg.stronglyMeasurable_mk.measurable
    set g₀ : ℝ → ℝ := fun x => if |g' x| ≤ C then g' x else 0 with hg₀def
    have hmeasset : MeasurableSet {x : ℝ | |g' x| ≤ C} :=
      measurableSet_le (hg'meas.abs) measurable_const
    refine ⟨g₀, Measurable.ite hmeasset hg'meas measurable_const, ?_, Or.inr ⟨C, fun x => ?_⟩⟩
    · refine hg.ae_eq_mk.trans ?_
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), |g' x| ≤ C := by
        filter_upwards [hg.ae_eq_mk] with x hx
        have : g' x = g x := by rw [hg'def, ← hx]
        rw [this]; exact hC x
      filter_upwards [hae] with x hx
      show g' x = g₀ x
      rw [hg₀def]
      simp [hx]
    · rw [hg₀def]
      by_cases h : |g' x| ≤ C
      · simpa [h] using h
      · simpa [h] using hC0

/-- **Variation diminution composes.** The convolution operator of `μ ∗ ν` is the composition of
the two operators, so a convolution of variation-diminishing probability laws is
variation-diminishing.

This is the step that makes the `ε`-smoothing of `thm:scale-monotone-noncreation` step 1 legal:
the smoothed increment's operator is the composition of two variation-diminishing ones. Both legs
of `IsVariationDiminishing` have to be carried, which is why `mconv_conv_bounded` exists beside
`mconv_conv`, and the bound has to be made pointwise, which is `exists_good_representative`. -/
theorem isVariationDiminishing_conv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsVariationDiminishing μ) (hν : IsVariationDiminishing ν) :
    IsVariationDiminishing (μ ∗ ν) := by
  intro g hg hgb
  obtain ⟨g₀, hg₀meas, hg₀ae, hg₀b⟩ := exists_good_representative hg hgb
  have hcomp : mconv (μ ∗ ν) g₀ =ᵐ[volume] mconv ν (mconv μ g₀) := by
    rcases hg₀b with hint | ⟨C, hC⟩
    · exact (mconv_conv μ ν hg₀meas.aestronglyMeasurable hint).symm
    · exact Filter.Eventually.of_forall fun x =>
        (mconv_conv_bounded μ ν hg₀meas hC x).symm
  have hinner : Integrable (mconv μ g₀) volume ∨ ∃ C : ℝ, ∀ x, |mconv μ g₀ x| ≤ C := by
    rcases hg₀b with hint | ⟨C, hC⟩
    · exact Or.inl (integrable_mconv μ hg₀meas.aestronglyMeasurable hint)
    · exact Or.inr ⟨C, mconv_bounded μ hC⟩
  calc signChangesAE (mconv (μ ∗ ν) g)
      = signChangesAE (mconv ν (mconv μ g₀)) := by
        rw [signChangesAE_congr (mconv_congr_ae (μ ∗ ν) hg₀ae), signChangesAE_congr hcomp]
    _ ≤ signChangesAE (mconv μ g₀) :=
        hν _ (measurable_mconv μ hg₀meas).aestronglyMeasurable hinner
    _ ≤ signChangesAE g₀ := hμ _ hg₀meas.aestronglyMeasurable hg₀b
    _ = signChangesAE g := (signChangesAE_congr hg₀ae).symm

end SpatialLine
