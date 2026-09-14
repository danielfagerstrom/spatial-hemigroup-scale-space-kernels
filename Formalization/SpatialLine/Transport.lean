/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.BochnerConvolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The transport block, chapter 3's part: dilation and the kernel of the identity

Blueprint: `def:cascade-family`, and the converse clause of `lem:convolution-representation`.
Nothing here is a blueprint node.

**Wave 1 of the proving campaign (2026-09-09) reduced this file.** The transport block proper —
(A1)-(A6) for `mconv` and `mconvL1`, the clauses that turn a *kernel* into an operator family —
was proved twice, once here for chapter 3 and once in `SpatialLine/ConvolutionOperator.lean` for
`lem:convolution-representation`'s converse. The copy in `ConvolutionOperator.lean` survives,
because that is the file which proves the node the block belongs to; the reflection clause is
`mconvL1_reflL1` there, stated exactly as `reflL1_mconvL1` was here. What is left in this file
is the two things chapter 3 needed and chapter 4 did not: the dilation clause **(A8)**, and the
identification of the kernel of the identity.

## Identifying the kernel of the identity

`eq_dirac_of_mconvL1_eq_id` is the converse direction the *nondegeneracy* clause (ND) of every
concrete family reads: if convolution by a probability measure fixes every element of `L¹`, the
measure is `δ₀`. It is proved by testing at the bump `k(y) = e^{-y²}`: `μ * k` is continuous, so
the almost-everywhere identity `μ * k = k` may be read at the origin, where it says
`∫ k dμ = k(0) = 1`; since `k ≤ 1` with equality only at `0`, that forces `μ` to sit at the
origin, and `Measure.ext_of_charFun` finishes.

This is not the full uniqueness clause of `lem:convolution-representation` — it identifies the
kernel of the *identity*, not of an arbitrary operator — but it is what (ND) needs, and it needs
no Fourier inversion. Recording what writing it down found: **(ND) is a statement about the
operator, not about the kernel**, and this lemma is the bridge between the two readings.

## The measurable representative

`dilL1_comp_mconvL1` passes to a measurable representative before applying `dilate_mconv`,
because the pointwise clause needs a genuinely measurable `f` while an `L¹` coercion supplies
only `AEStronglyMeasurable` against `volume`. `mconvL1_reflL1` in `ConvolutionOperator.lean`
makes the same move for the same reason.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The pointwise clauses -/

/-- **(A8)** at the level of functions: dilating intertwines with dilating the measure.

twin: `Hemigroup.dilate_mconv`, verbatim. -/
theorem dilate_mconv {lam : ℝ} (hlam : 0 < lam) (μ : Measure ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    dilate lam (mconv μ f) = mconv (μ.map (fun x => lam * x)) (dilate lam f) := by
  have hmeas : Measurable (dilate lam f) := (hf.comp (measurable_const_mul lam⁻¹)).const_mul lam⁻¹
  funext x
  have hcomp : AEStronglyMeasurable (fun y : ℝ => dilate lam f (x - y))
      (μ.map (fun x => lam * x)) :=
    (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  rw [mconv_apply, integral_map (measurable_const_mul lam).aemeasurable hcomp]
  have harg : ∀ y : ℝ, lam⁻¹ * (x - lam * y) = lam⁻¹ * x - y := fun y => by
    field_simp
  simp only [dilate, harg]
  rw [integral_const_mul]
  rfl

/-- **The kernel of the identity is `δ₀`.**

If convolution by a probability measure is the identity on `L¹`, the measure is `δ₀`. This is
what the nondegeneracy clause (ND) of a concrete family is checked through: the contrapositive
says that a kernel whose transform is not identically `1` gives an operator different from the
identity.

The test function is the bump `k(y) = e^{-y²}`, which is bounded, continuous, integrable, and
takes its maximum `1` at the origin and nowhere else. `μ * k` is continuous by dominated
convergence, so the almost-everywhere identity `μ * k = k` holds at every point, and at the
origin it reads `∫ k dμ = 1`. Since `1 - k ≥ 0` with equality only at `0`, `μ` sits at the
origin, and `Measure.ext_of_charFun` turns that into `μ = δ₀`. -/
theorem eq_dirac_of_mconvL1_eq_id {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : mconvL1 μ = ContinuousLinearMap.id ℝ X) : μ = Measure.dirac 0 := by
  set k : ℝ → ℝ := fun y => Real.exp (-1 * y ^ 2) with hk
  have hkc : Continuous k := Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))
  have hk0 : k 0 = 1 := by simp [hk]
  have hkb : ∀ y, k y ≤ 1 := fun y => Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
  have hklt : ∀ y : ℝ, y ≠ 0 → k y < 1 := fun y hy =>
    Real.exp_lt_one_iff.mpr (by nlinarith [pow_two_pos_of_ne_zero hy])
  have hki : Integrable k := integrable_exp_neg_mul_sq one_pos
  have hkiμ : Integrable k μ :=
    (integrable_const (1 : ℝ)).mono' hkc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact hkb y)
  have hae : mconv μ k =ᵐ[volume] k := by
    have h1 : ((mconvL1 μ (hki.toL1 k) : X) : ℝ → ℝ) =ᵐ[volume] mconv μ k :=
      (coeFn_mconvL1 μ _).trans (mconv_congr_ae μ (Integrable.coeFn_toL1 hki))
    have h2 : ((mconvL1 μ (hki.toL1 k) : X) : ℝ → ℝ) =ᵐ[volume] k := by
      rw [h]; simpa using Integrable.coeFn_toL1 hki
    exact h1.symm.trans h2
  have hcont : Continuous (mconv μ k) := by
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
    · exact fun x => (hkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact fun x => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact hkb _
    · exact Filter.Eventually.of_forall fun y => hkc.comp (continuous_id.sub continuous_const)
  have heq : mconv μ k = k := (hcont.ae_eq_iff_eq volume hkc).mp hae
  have hint : ∫ y, k y ∂μ = 1 := by
    have h0 : mconv μ k 0 = k 0 := by rw [heq]
    rw [mconv_apply, hk0] at h0
    have hsimp : ∫ y, k (0 - y) ∂μ = ∫ y, k y ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [hk]
    rw [hsimp] at h0
    exact h0
  have hzero : ∀ᵐ y ∂μ, (1 : ℝ) - k y = 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun y => sub_nonneg.mpr (hkb y))
      ((integrable_const (1 : ℝ)).sub hkiμ)).mp ?_
    rw [integral_sub (integrable_const _) hkiμ, integral_const, hint]
    simp
  have hae0 : ∀ᵐ y ∂μ, y = 0 := by
    filter_upwards [hzero] with y hy
    by_contra hne
    have hlt := hklt y hne
    have hone : k y = 1 := by linarith [sub_eq_zero.mp hy]
    linarith
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_apply_real, charFun_dirac]
  simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [integral_congr_ae (g := fun _ : ℝ => (1 : ℂ)) ?_]
  · simp
  · filter_upwards [hae0] with y hy
    simp [hy]

/-! ## The clauses on `L¹`

Each is the corresponding pointwise result read through `coeFn_mconvL1`, with the pointwise
hypotheses supplied almost everywhere by `ae_ae_sub_of_ae`.
-/

/-- The `L¹` norm of a difference as a lower integral — the form every estimate below speaks in.

twin: `Hemigroup.norm_sub_eq_lintegral`, verbatim. -/
theorem norm_sub_eq_lintegral (a b : X) :
    ‖a - b‖ = (∫⁻ x, ‖(a : ℝ → ℝ) x - (b : ℝ → ℝ) x‖ₑ).toReal := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub a b] with x hx
  rw [hx]
  rfl

variable {μ : Measure ℝ}

/-- **(A8)** for `mconvL1`: dilating intertwines with dilating the measure.

twin: `Hemigroup.dilL1_comp_mconvL1`, verbatim. -/
theorem dilL1_comp_mconvL1 {lam : ℝ} (hlam : 0 < lam) (μ : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure (μ.map (fun x => lam * x))] :
    (dilL1 hlam).comp (mconvL1 μ) = (mconvL1 (μ.map (fun x => lam * x))).comp (dilL1 hlam) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  set g := (Lp.aestronglyMeasurable f).mk (f : ℝ → ℝ) with hg_def
  have hgm : Measurable g := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  have hfg : (f : ℝ → ℝ) =ᵐ[volume] g := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hpt : dilate lam (mconv μ g)
      =ᵐ[volume] mconv (μ.map (fun x => lam * x)) (dilate lam g) := by
    rw [dilate_mconv hlam μ hgm]
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : ((dilL1 hlam (mconvL1 μ f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv (μ.map (fun x => lam * x)) (dilate lam (f : ℝ → ℝ)) :=
    (coeFn_dilL1 hlam (mconvL1 μ f)).trans
      ((dilate_congr_ae hlam.ne' (coeFn_mconvL1 μ f)).trans
        ((dilate_congr_ae hlam.ne' (mconv_congr_ae μ hfg)).trans
          (hpt.trans (mconv_congr_ae _ (dilate_congr_ae hlam.ne' hfg.symm)))))
  have h2 : ((mconvL1 (μ.map (fun x => lam * x)) (dilL1 hlam f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv (μ.map (fun x => lam * x)) (dilate lam (f : ℝ → ℝ)) :=
    (coeFn_mconvL1 _ (dilL1 hlam f)).trans (mconv_congr_ae _ (coeFn_dilL1 hlam f))
  exact h1.trans h2.symm

end SpatialLine
