/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The ambient space and its operators: `L¹(ℝ)`, translation, reflection, dilation, convolution

Blueprint: `blueprint/src/parts/02-preliminaries.tex`, the notation preamble, and
`def:cascade-family` in Chapter 3. Nothing in this file is a blueprint node: it supplies the
*objects* the axioms quantify over, so that (A2), (A3) and (A8) can be *stated* at all.

## Provenance

Everything except `reflL1` is Paper I's, copied rather than imported — there is deliberately no
lake dependency on `hemigroup-causal-scale-space-kernels`, and the two developments are meant to
be lifted into `ScaleSpaceCore` together rather than one depending on the other. Each copied
declaration carries a `twin:` line naming its original. The one new operator is `reflL1`, which
is what (A3) reads here where the causal (A3) read support in a half-line.

## Design, unchanged from Paper I

* The ambient space is `X = ℝ →₁[volume] ℝ`, real, and the operators are `X →L[ℝ] X`, so (A1) is
  carried by the type.
* Kernels are measures on `ℝ` carrying a *predicate* (symmetry, here) rather than living on a
  bespoke type, because axiom (A6) is a convolution identity and `Measure.conv` lives on a group.
* `dilate lam f = lam⁻¹ f (lam⁻¹ ·)` — the mass-preserving normalisation, which is what makes
  `dilL1` an isometry of `L¹` and matches the measure-side dilation, pushforward along
  `x ↦ lam * x`.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-- `X = L¹(ℝ)`, the space `def:cascade-family` acts on.

twin: `Hemigroup.X`. -/
noncomputable abbrev X := ℝ →₁[volume] ℝ

/-- The positive cone `L¹₊` of the blueprint's notation preamble, the object (A4) and (A5) speak
about.

twin: `Hemigroup.IsNonneg`. -/
def IsNonneg (f : X) : Prop := 0 ≤ᵐ[volume] (f : ℝ → ℝ)

/-! ## Translation

twin: `Hemigroup.transL1` and its supporting lemmas, verbatim.
-/

/-- `x ↦ x - a` preserves Lebesgue measure. -/
theorem measurePreserving_sub_const (a : ℝ) :
    MeasurePreserving (fun x : ℝ => x - a) volume volume := by
  simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-a)

theorem translate_congr_ae (a : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (x - a)) =ᵐ[volume] fun x => g (x - a) :=
  (measurePreserving_sub_const a).quasiMeasurePreserving.ae h

theorem integrable_translate {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun x => f (x - a)) :=
  ((measurePreserving_sub_const a).integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `T_a f = f(· - a)` as a linear map on `L¹`. -/
noncomputable def transₗ (a : ℝ) : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_translate (L1.integrable_coeFn f) a).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_smul c f))

/-- **Translation is an isometry of `L¹`** — Lebesgue measure is translation invariant. -/
noncomputable def transL1 (a : ℝ) : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (transₗ a).mkContinuous 1 fun f => by
    rw [transₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    exact le_of_eq (congrArg ENNReal.toReal
      (lintegral_sub_right_eq_self (fun x => ‖(f : ℝ → ℝ) x‖ₑ) a))

lemma coeFn_transL1 (a : ℝ) (f : ℝ →₁[volume] ℝ) :
    transL1 a f =ᵐ[volume] fun x => (f : ℝ → ℝ) (x - a) :=
  Integrable.coeFn_toL1 (integrable_translate (L1.integrable_coeFn f) a)

/-! ## Reflection

The one operator with no causal counterpart. `(R f)(x) = f(-x)`, an isometric involution of
`L¹`, because Lebesgue measure on the line is invariant under `x ↦ -x`. Axiom (A3) is
`Φ ∘ R = R ∘ Φ`.
-/

/-- `x ↦ -x` preserves Lebesgue measure. -/
theorem measurePreserving_neg' : MeasurePreserving (fun x : ℝ => -x) volume volume :=
  Measure.measurePreserving_neg (volume : Measure ℝ)

theorem reflect_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (-x)) =ᵐ[volume] fun x => g (-x) :=
  measurePreserving_neg'.quasiMeasurePreserving.ae h

theorem integrable_reflect {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (-x)) :=
  (measurePreserving_neg'.integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `R f = f(-·)` as a linear map on `L¹`. -/
noncomputable def reflₗ : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_reflect (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_ae (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_ae (Lp.coeFn_smul c f))

/-- **Reflection is an isometry of `L¹`.** The change of variables is `x ↦ -x`, a measurable
equivalence preserving Lebesgue measure, so the constant is `1`. -/
noncomputable def reflL1 : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  reflₗ.mkContinuous 1 fun f => by
    rw [reflₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    exact measurePreserving_neg'.lintegral_comp_emb
      (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding fun x => ‖(f : ℝ → ℝ) x‖ₑ

lemma coeFn_reflL1 (f : ℝ →₁[volume] ℝ) :
    reflL1 f =ᵐ[volume] fun x => (f : ℝ → ℝ) (-x) :=
  Integrable.coeFn_toL1 (integrable_reflect (L1.integrable_coeFn f))

/-! ## Dilation

twin: `Hemigroup.dilL1` and its supporting lemmas, verbatim.
-/

/-- Multiplication by a nonzero constant is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_const_mul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => c * x) volume volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous

/-- `D_lam f = lam⁻¹ f(lam⁻¹ ·)`, the mass-preserving normalisation. -/
noncomputable def dilate (lam : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => lam⁻¹ * f (lam⁻¹ * x)

theorem dilate_congr_ae {lam : ℝ} (hlam : lam ≠ 0) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    dilate lam f =ᵐ[volume] dilate lam g := by
  filter_upwards [(quasiMeasurePreserving_const_mul (inv_ne_zero hlam)).ae h] with x hx
  simp only [dilate, hx]

theorem integrable_dilate {f : ℝ → ℝ} (hf : Integrable f) {lam : ℝ} (hlam : lam ≠ 0) :
    Integrable (dilate lam f) :=
  (Integrable.comp_mul_left' hf (inv_ne_zero hlam)).const_mul lam⁻¹

/-- The change of variables the isometry rests on: `∫⁻ g(c x) dx = |c⁻¹| ∫⁻ g`. -/
theorem lintegral_comp_const_mul {c : ℝ} (hc : c ≠ 0) {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ x, g (c * x) = ENNReal.ofReal |c⁻¹| * ∫⁻ x, g x := by
  have hmap := Real.map_volume_mul_left hc
  calc ∫⁻ x, g (c * x)
      = ∫⁻ y, g y ∂(Measure.map (fun x : ℝ => c * x) volume) := by
        rw [lintegral_map' (hg.mono_ac (by rw [hmap]; exact Measure.smul_absolutelyContinuous))
          (measurable_const_mul c).aemeasurable]
    _ = ENNReal.ofReal |c⁻¹| * ∫⁻ x, g x := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- `D_lam` as a linear map on `L¹`. -/
noncomputable def dilₗ {lam : ℝ} (hlam : lam ≠ 0) :
    (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_dilate (L1.integrable_coeFn f) hlam).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hlam (Lp.coeFn_add f g)).trans ?_
    filter_upwards with x
    simp only [dilate, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hlam (Lp.coeFn_smul c f)).trans ?_
    filter_upwards with x
    simp only [dilate, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Dilation is an isometry of `L¹`** for `lam > 0`. -/
noncomputable def dilL1 {lam : ℝ} (hlam : 0 < lam) :
    (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (dilₗ hlam.ne').mkContinuous 1 fun f => by
    rw [dilₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    have henorm : ∀ x : ℝ, ‖dilate lam (f : ℝ → ℝ) x‖ₑ
        = ENNReal.ofReal lam⁻¹ * ‖(f : ℝ → ℝ) (lam⁻¹ * x)‖ₑ := by
      intro x
      simp only [dilate, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hlam.le)]
    simp only [henorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_comp_const_mul (inv_ne_zero hlam.ne') (Lp.aestronglyMeasurable f).enorm,
      ← mul_assoc, inv_inv, abs_of_pos hlam, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hlam)),
      inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one, one_mul]

lemma coeFn_dilL1 {lam : ℝ} (hlam : 0 < lam) (f : ℝ →₁[volume] ℝ) :
    dilL1 hlam f =ᵐ[volume] dilate lam (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_dilate (L1.integrable_coeFn f) hlam.ne')

/-! ## Convolution by a measure

twin: `Hemigroup.mconv` / `Hemigroup.mconvL1` and their supporting lemmas, verbatim. The
representation lemma `lem:convolution-representation` is a statement *about* this operation, so
it has to exist before the node can be typed.
-/

/-- `(μ * f)(x) = ∫ f(x - y) μ(dy)`. -/
noncomputable def mconv (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ y, f (x - y) ∂μ

lemma mconv_apply (μ : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mconv μ f x = ∫ y, f (x - y) ∂μ := rfl

/-- The Tonelli identity behind (A1) and (A5). -/
theorem lintegral_lintegral_sub_eq (μ : Measure ℝ) [SFinite μ] {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g) :
    ∫⁻ x, (∫⁻ y, g (x - y) ∂μ) = μ univ * ∫⁻ x, g x := by
  have huncurry : AEMeasurable (Function.uncurry fun x y : ℝ => g (x - y)) (volume.prod μ) :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  calc ∫⁻ x, (∫⁻ y, g (x - y) ∂μ)
      = ∫⁻ y, (∫⁻ x, g (x - y) ∂volume) ∂μ := lintegral_lintegral_swap huncurry
    _ = ∫⁻ _, (∫⁻ x, g x) ∂μ := lintegral_congr fun y => lintegral_sub_right_eq_self _ y
    _ = μ univ * ∫⁻ x, g x := by rw [lintegral_const, mul_comm]

/-- **(A1)** as an `L¹` bound. -/
theorem lintegral_enorm_mconv_le (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) :
    ∫⁻ x, ‖mconv μ f x‖ₑ ≤ μ univ * ∫⁻ x, ‖f x‖ₑ := by
  calc ∫⁻ x, ‖mconv μ f x‖ₑ ≤ ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = μ univ * ∫⁻ x, ‖f x‖ₑ := lintegral_lintegral_sub_eq μ hf.enorm

theorem integrable_uncurry_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    Integrable (Function.uncurry fun x y : ℝ => f (x - y)) (volume.prod μ) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun x y : ℝ => f (x - y)) (volume.prod μ) :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  refine ⟨hm, ?_⟩
  have hprod : ∫⁻ p, ‖Function.uncurry (fun x y : ℝ => f (x - y)) p‖ₑ ∂(volume.prod μ)
      = ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) := lintegral_prod _ hm.enorm
  rw [hasFiniteIntegral_iff_enorm, hprod, lintegral_lintegral_sub_eq μ hf.enorm]
  exact ENNReal.mul_lt_top (measure_lt_top μ univ) hfi.2

/-- `μ * f` is integrable: `Φ` maps `L¹` into `L¹`. -/
theorem integrable_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) : Integrable (mconv μ f) :=
  (integrable_uncurry_sub μ hf hfi).integral_prod_left

/-- The null-set transfer: `mconv` respects a.e. equality, so it descends to `L¹`. -/
theorem ae_ae_sub_of_ae (μ : Measure ℝ) [SFinite μ] {p : ℝ → Prop} (h : ∀ᵐ u ∂volume, p u) :
    ∀ᵐ x ∂volume, ∀ᵐ y ∂μ, p (x - y) :=
  Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_sub volume μ).ae h)

theorem mconv_congr_ae (μ : Measure ℝ) [SFinite μ] {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    mconv μ f =ᵐ[volume] mconv μ g := by
  filter_upwards [ae_ae_sub_of_ae μ h] with x hx
  exact integral_congr_ae hx

theorem mconv_add_ae (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : AEStronglyMeasurable g) (hgi : Integrable g) :
    mconv μ (f + g) =ᵐ[volume] mconv μ f + mconv μ g := by
  filter_upwards [(integrable_uncurry_sub μ hf hfi).prod_right_ae,
    (integrable_uncurry_sub μ hg hgi).prod_right_ae] with x h1 h2
  simp only [Function.uncurry] at h1 h2
  simp only [mconv_apply, Pi.add_apply]
  exact integral_add h1 h2

theorem mconv_smul (μ : Measure ℝ) (c : ℝ) (f : ℝ → ℝ) :
    mconv μ (c • f) = c • mconv μ f := by
  funext x
  simp only [mconv_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul]

/-- `Φ f = μ * f` as a linear map on `L¹`. -/
noncomputable def mconvₗ (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_add f g)).trans ?_
    exact mconv_add_ae μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)
      (Lp.aestronglyMeasurable g) (L1.integrable_coeFn g)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_smul c f)).trans ?_
    rw [mconv_smul]

private lemma norm_L1_eq (f : ℝ →₁[volume] ℝ) : ‖f‖ = (∫⁻ x, ‖(f : ℝ → ℝ) x‖ₑ).toReal := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]

/-- **(A1)** in the form `def:cascade-family` states it: `Φ` is a bounded operator on `L¹`. -/
noncomputable def mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (mconvₗ μ).mkContinuous (μ univ).toReal fun f => by
    rw [mconvₗ, LinearMap.coe_mk, AddHom.coe_mk,
      Integrable.norm_toL1_eq_lintegral_enorm, norm_L1_eq, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono ?_ (lintegral_enorm_mconv_le μ (Lp.aestronglyMeasurable f))
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) (L1.integrable_coeFn f).2.ne

lemma coeFn_mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →₁[volume] ℝ) :
    mconvL1 μ f =ᵐ[volume] mconv μ (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f))

end SpatialLine
