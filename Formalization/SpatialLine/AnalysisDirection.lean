/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.AntitoneDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The analysis direction of `lem:selfdecomposable-exponents`

Blueprint: `lem:selfdecomposable-exponents`(1) implies (3), the direction
`thm:main-characterization`'s analysis half consumes.

The direction has three parts and this file is the third, which glues the other two:

* `SpatialLine/DilationDecrease.lean` -- from "every dilation increment is a symmetric Levy
  exponent" to `D_c nu <= nu`, where the uniqueness clause of `prop:fourier-toolbox`(3)
  (ledger **A3**) is spent, once;
* `SpatialLine/AntitoneDensity.lean` -- a measure on the line decreasing under every right
  translation has a nonincreasing density, proved through the dyadic difference quotients rather
  than through convexity;
* here -- the passage between the multiplicative coordinate `x`, where the Levy measure lives,
  and the additive coordinate `theta = log x`, where the translation statement lives.

## The passage, and the one place it is delicate

Pushing `nu` forward under `log` loses nothing (`nu` is folded, so what `log` does to the
nonpositive axis is invisible), the finiteness of the rays is the Levy condition
(`SymLevyPair.measure_Ioi_ne_top`), and the translation hypothesis is the dilation hypothesis at
`c = e^{-h}`. Coming back is Mathlib's one-dimensional change of variables at `exp`
(`lintegral_image_eq_lintegral_abs_deriv_mul`), which turns `Lebesgue.withDensity f` into the
measure of density `f(log x)/x` on `(0,infty)` -- and that is `profileMeasure` of
`k(x) = f(log x)`.

The delicate step is that `k` has to be a **real** function, so `f` must be finite, and finite at
**every** point rather than almost every point: `(top : ENNReal).toReal` is `0`, so a single
infinite value of the antitone `f` would make `k` vanish exactly where the profile is largest and
destroy `SDProfile.k_antitone`. It is finite everywhere, and not by assumption: `f` is antitone,
so `f(theta) = infinity` would force `f = infinity` on `(theta - 1, theta]` and hence
`m((theta-1,theta]) = infinity`, which the finiteness of the rays forbids
(`dyadicDensity_ne_top`).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The tails of a Lévy measure -/

/-- **Every positive tail of a Lévy measure is finite**, `Growth.lean`'s
`measure_Ioi_one_ne_top` at a general threshold: on `(r,∞)` the truncation `1 ∧ x²` is at
least `1 ∧ r² > 0`. -/
theorem SymLevyPair.measure_Ioi_ne_top (P : SymLevyPair) {r : ℝ} (hr : 0 < r) :
    P.ν (Ioi r) ≠ ⊤ := by
  set c : ℝ := min 1 (r ^ 2) with hc
  have hc0 : 0 < c := lt_min zero_lt_one (by positivity)
  refine ne_top_of_le_ne_top
    (ENNReal.div_ne_top P.ν_integrable (ENNReal.ofReal_pos.mpr hc0).ne') ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hc0).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  calc ENNReal.ofReal c * P.ν (Ioi r)
      = ∫⁻ _ in Ioi r, ENNReal.ofReal c ∂P.ν := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in Ioi r, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hx' : r < x := hx
        refine le_min (min_le_left _ _) ?_
        rw [hc]
        exact le_trans (min_le_right 1 (r ^ 2)) (by nlinarith)
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := setLIntegral_le_lintegral _ _


variable {ν : Measure ℝ}

/-! ## The log coordinate -/

/-- A folded measure sees only the positive half-line, so two sets with the same positive part
have the same measure. -/
theorem measure_eq_of_inter_Ioi (hfold : IsFolded ν) {s t : Set ℝ}
    (h : s ∩ Ioi 0 = t ∩ Ioi 0) : ν s = ν t := by
  have key : ∀ u : Set ℝ, ν u = ν (u ∩ Ioi 0) := by
    intro u
    have h1 := measure_inter_add_diff₀ (μ := ν) (t := Ioi (0:ℝ)) u
      measurableSet_Ioi.nullMeasurableSet
    have h2 : ν (u \ Ioi 0) = 0 :=
      measure_mono_null (fun x hx => mem_Iic.mpr (not_lt.mp hx.2)) hfold
    rw [h2, add_zero] at h1
    exact h1.symm
  rw [key s, key t, h]

/-- The rays of the image measure are the rays of the original: `(log_* ν)((θ,∞)) =
ν((e^θ,∞))`. What `log` does off `(0,∞)` is invisible because `ν` is folded. -/
theorem map_log_Ioi (hfold : IsFolded ν) (θ : ℝ) :
    (Measure.map Real.log ν) (Ioi θ) = ν (Ioi (Real.exp θ)) := by
  rw [Measure.map_apply Real.measurable_log measurableSet_Ioi]
  refine measure_eq_of_inter_Ioi hfold ?_
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [← Real.exp_lt_exp, Real.exp_log h2] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← Real.log_exp θ]
    exact Real.log_lt_log (Real.exp_pos θ) h1

/-- **Dilation becomes translation.** `D_c ν ≤ ν` at `c = e^{-h}` is the statement that the
image of `ν` under `log` decreases under the right shift by `h`. -/
theorem map_log_shift (hfold : IsFolded ν)
    (hdil : ∀ c : ℝ, 0 < c → c ≤ 1 → Measure.map (fun x : ℝ => c * x) ν ≤ ν)
    {h : ℝ} (hh : 0 < h) :
    Measure.map (fun θ : ℝ => θ - h) (Measure.map Real.log ν) ≤ Measure.map Real.log ν := by
  set c : ℝ := Real.exp (-h) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := by
    rw [hc, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcomp : Measure.map (fun θ : ℝ => θ - h) (Measure.map Real.log ν)
      = Measure.map (fun x : ℝ => Real.log x - h) ν := by
    rw [show (fun x : ℝ => Real.log x - h) = (fun θ : ℝ => θ - h) ∘ Real.log from rfl,
      ← Measure.map_map (by fun_prop : Measurable fun θ : ℝ => θ - h) Real.measurable_log]
  have hae : (fun x : ℝ => Real.log x - h) =ᵐ[ν] (fun x : ℝ => Real.log (c * x)) := by
    have hnull : ν (Iic 0) = 0 := hfold
    have : ∀ᵐ x ∂ν, x ∈ Ioi (0 : ℝ) := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hnull
      simp only [mem_Ioi, not_lt, mem_setOf_eq] at hx
      exact mem_Iic.mpr hx
    filter_upwards [this] with x hx
    rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt hx), hc, Real.log_exp]
    ring
  rw [hcomp, Measure.map_congr hae,
    show (fun x : ℝ => Real.log (c * x)) = Real.log ∘ (fun x : ℝ => c * x) from rfl,
    ← Measure.map_map Real.measurable_log (by fun_prop)]
  exact Measure.map_mono (hdil c hc0 hc1) Real.measurable_log


/-! ## Back to the multiplicative coordinate -/

/-- **The change of variables `x = e^θ`**: the image of `Lebesgue.withDensity f` under `exp` is
the measure of density `f(\log x)/x` on `(0,∞)`. One application of Mathlib's one-dimensional
Jacobian formula, the derivative of `exp` cancelling the `1/x`. -/
theorem map_exp_withDensity (f : ℝ → ℝ≥0∞) :
    Measure.map Real.exp (volume.withDensity f)
      = (volume.restrict (Ioi 0)).withDensity (fun x => f (Real.log x) / ENNReal.ofReal x) := by
  ext A hA
  rw [Measure.map_apply Real.measurable_exp hA,
    withDensity_apply _ (Real.measurable_exp hA),
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  set G : ℝ → ℝ≥0∞ := A.indicator (fun x => f (Real.log x) / ENNReal.ofReal x) with hG
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp)
    (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) G
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at hjac
  have hLHS : (∫⁻ x in Ioi (0 : ℝ), G x) = ∫⁻ x in A ∩ Ioi 0, f (Real.log x) / ENNReal.ofReal x := by
    rw [hG, lintegral_indicator hA, Measure.restrict_restrict hA, Set.inter_comm]
  have hRHS : (∫⁻ θ, ENNReal.ofReal |Real.exp θ| * G (Real.exp θ))
      = ∫⁻ θ in Real.exp ⁻¹' A, f θ := by
    rw [← lintegral_indicator (Real.measurable_exp hA)]
    refine lintegral_congr fun θ => ?_
    by_cases hθ : Real.exp θ ∈ A
    · rw [hG, Set.indicator_of_mem hθ, Set.indicator_of_mem (by exact hθ : θ ∈ Real.exp ⁻¹' A),
        Real.log_exp, abs_of_pos (Real.exp_pos θ),
        ENNReal.mul_div_cancel (ENNReal.ofReal_pos.mpr (Real.exp_pos θ)).ne'
          ENNReal.ofReal_ne_top]
    · rw [hG, Set.indicator_of_notMem hθ,
        Set.indicator_of_notMem (by exact hθ : θ ∉ Real.exp ⁻¹' A), mul_zero]
  rw [← hLHS, ← hRHS]
  exact hjac.symm


/-! ## The density is finite everywhere -/

/-- **`f` is finite at every point**, not merely almost every point --- which is what lets the
profile be a real antitone function rather than an a.e. class. An infinite value at `θ` would,
by antitonicity, be infinite on all of `(θ-1,θ]` and make `m((θ-1,θ])` infinite. -/
theorem dyadicDensity_ne_top {m : Measure ℝ} (hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤)
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) (θ : ℝ) :
    dyadicDensity m θ ≠ ⊤ := by
  intro htop
  have hbig : (∫⁻ x in Ioc (θ - 1) θ, dyadicDensity m x) = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = ⊤ * volume (Ioc (θ - 1) θ) := by
          rw [Real.volume_Ioc, show θ - (θ - 1) = 1 by ring, ENNReal.ofReal_one, mul_one]
      _ = ∫⁻ _ in Ioc (θ - 1) θ, (⊤ : ℝ≥0∞) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Ioc (θ - 1) θ, dyadicDensity m x := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          rw [← htop]
          exact antitone_dyadicDensity hshift hx.2
  rw [setLIntegral_dyadicDensity hfin hshift] at hbig
  exact (ne_top_of_le_ne_top (hfin (θ - 1)) (measure_mono Ioc_subset_Ioi_self)) hbig


/-- **The profile of a Lévy measure that decreases under dilation.** -/
theorem exists_profile_of_dilate_le (P : SymLevyPair)
    (hdil : ∀ c : ℝ, 0 < c → c ≤ 1 → Measure.map (fun x : ℝ => c * x) P.ν ≤ P.ν) :
    ∃ Q : SDProfile, Q.a = P.a ∧ P.ν = profileMeasure Q.k := by
  set m : Measure ℝ := Measure.map Real.log P.ν with hm
  have hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤ := fun θ => by
    rw [hm, map_log_Ioi P.ν_folded θ]
    exact P.measure_Ioi_ne_top (Real.exp_pos θ)
  have hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m := fun h hh =>
    map_log_shift P.ν_folded hdil hh
  set f : ℝ → ℝ≥0∞ := dyadicDensity m with hf
  have hfanti : Antitone f := antitone_dyadicDensity hshift
  have hftop : ∀ θ : ℝ, f θ ≠ ⊤ := dyadicDensity_ne_top hfin hshift
  have hmf : m = volume.withDensity f := eq_withDensity_dyadicDensity hfin hshift
  -- the profile
  set k : ℝ → ℝ := fun x => if 0 < x then (f (Real.log x)).toReal else 0 with hk
  have hk0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x := by
    intro x hx
    rw [hk]
    simp only [if_pos (mem_Ioi.mp hx)]
    exact ENNReal.toReal_nonneg
  have hkanti : AntitoneOn k (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    rw [hk]
    simp only [if_pos hx0, if_pos hy0]
    exact (ENNReal.toReal_le_toReal (hftop _) (hftop _)).mpr
      (hfanti (Real.log_le_log hx0 hxy))
  -- the change of variables
  have hpos : ∀ᵐ x ∂P.ν, 0 < x := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) P.ν_folded
    simp only [mem_Ioi, not_lt, mem_setOf_eq] at hx
    exact mem_Iic.mpr hx
  have hexplog : Measure.map Real.exp m = P.ν := by
    rw [hm, Measure.map_map Real.measurable_exp Real.measurable_log]
    have hae : (Real.exp ∘ Real.log) =ᵐ[P.ν] id := by
      filter_upwards [hpos] with x hx
      simp [Function.comp_apply, Real.exp_log hx]
    rw [Measure.map_congr hae, Measure.map_id]
  have hνeq : P.ν = profileMeasure k := by
    rw [← hexplog, hmf, map_exp_withDensity, profileMeasure]
    refine withDensity_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [hk]
    simp only [if_pos hx0]
    rw [ENNReal.ofReal_div_of_pos hx0, ENNReal.ofReal_toReal (hftop _)]
  refine ⟨⟨P.a, k, P.a_nonneg, hk0, hkanti, by simp [hk], ?_, ?_⟩, rfl, hνeq⟩ <;>
    · have hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ))) :=
        aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hkanti
      have := (profile_integrability hk0 hkm).mp (by rw [← hνeq]; exact P.ν_integrable)
      first
        | exact this.1
        | exact this.2


/-! ## The node's declaration -/

/-- **`lem:selfdecomposable-exponents`, (1) ⟹ (3).** The analysis direction: the dilation
identity read backwards, and the profile of the Lévy measure.

`SpatialLine.dilate_le_of_increments` turns the hypothesis into `D_c ν ≤ ν` (spending A3's
uniqueness clause), and `exists_profile_of_dilate_le` turns that into the profile. -/
theorem sd_exponents_one_implies_three (P : SymLevyPair) (F : ℝ → ℝ)
    (hF : ∀ ω, F ω = P.exponent ω)
    (h : ∀ s t : ℝ, 0 < s → s ≤ t → IsSymLevyExponent fun ω => F (t * ω) - F (s * ω)) :
    ∃ Q : SDProfile, Q.a = P.a ∧ P.ν = profileMeasure Q.k :=
  exists_profile_of_dilate_le P fun _ hc hc1 => dilate_le_of_increments P F hF h hc hc1

end SpatialLine
