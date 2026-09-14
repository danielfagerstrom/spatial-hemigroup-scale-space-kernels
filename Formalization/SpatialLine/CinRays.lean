/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Cin
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# `lem:cin-rays`: the `Cin` rays and the superposition

Blueprint: `blueprint/src/parts/08-cone.tex`, `lem:cin-rays` -- the ray clause and the
superposition clause. The elementary properties of `Cin` are `SpatialLine/Cin.lean`.

twin: `Hemigroup.DickmanSuperposition` (`dickman_superposition`), with `Ein` in place of `Cin`
and the one-sided profile in place of the folded one. The layer-cake exchange is the same and
carries over verbatim: only the antiderivative changes, `Ein(omega u)` there and `Cin(omega u)`
here.

## The ray

`cinSDProfile tau` is the unit-step profile `1_{(0,tau)}` packaged as an `SDProfile`. It is
defined for every real `tau` -- for `tau <= 0` it is the zero profile -- because none of the
structure's fields needs `tau > 0`; positivity of the step enters only where the exponent is
identified, `cinSDProfile_exponentL`, which is where the split of `(0,infty)` at `tau` is made.

## The Choquet measure exists

`cin_superposition_exists` is the second half of `lem:cin-rays`(2), "such a `varpi` exists". It
is the quantile construction of Paper I's `Subordinator.lean` ported: push Lebesgue measure on
`(0,infty)` forward under the generalised inverse `tailInv k`, which needs no
`StieltjesFunction` and so tolerates a profile unbounded at the origin, and restrict to
`(0,infty)` to remove the atom the transform leaves at the origin whenever `k` is bounded -- the
`Cin` ray being the extreme case, its `k` bounded by `1`.

What the construction delivers is a sandwich, `k(x+) <= varpi(x,infty) <= k(x)`, whose two sides
agree off the countably many discontinuities of `k`; that is why `HasProfileTail` reads the tail
identity almost everywhere and not everywhere (SKELETON.md, finding F11).

The construction consumes `SDProfile.tendsto_k_atTop`, and that is forced rather than assumed:
`k` is nonincreasing and nonnegative with `int_1^infty k(x) x^{-1} dx < infty`, so a positive
limit at infinity would make the integral diverge like the harmonic one. The `SDProfile` field
`integrable_at_top` is stated in `ENNReal` and is turned into the `Integrable` packaging the
divergence argument needs by `SDProfile.integrableOn_k_div`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `lem:cin-rays`(1): the ray -/

theorem cinProfile_nonneg (τ : ℝ) (x : ℝ) : 0 ≤ cinProfile τ x := by
  rw [cinProfile]
  by_cases hx : x ∈ Ioo (0 : ℝ) τ <;> simp [hx]

theorem cinProfile_le_one (τ : ℝ) (x : ℝ) : cinProfile τ x ≤ 1 := by
  rw [cinProfile]
  by_cases hx : x ∈ Ioo (0 : ℝ) τ <;> simp [hx]

theorem cinProfile_eq_zero {τ x : ℝ} (hx : x ∉ Ioo (0 : ℝ) τ) : cinProfile τ x = 0 := by
  simp [cinProfile, hx]

theorem cinProfile_eq_one {τ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) τ) : cinProfile τ x = 1 := by
  simp [cinProfile, hx]

theorem antitoneOn_cinProfile (τ : ℝ) : AntitoneOn (cinProfile τ) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  by_cases hb' : b ∈ Ioo (0 : ℝ) τ
  · rw [cinProfile_eq_one hb', cinProfile_eq_one ⟨ha, lt_of_le_of_lt hab hb'.2⟩]
  · rw [cinProfile_eq_zero hb']
    exact cinProfile_nonneg τ a

theorem measurable_cinProfile (τ : ℝ) : Measurable (cinProfile τ) :=
  (measurable_const.indicator measurableSet_Ioo)

/-- The `Cin` ray of step `τ` as an `SDProfile`: Gaussian coefficient `0`, profile `1_{(0,τ)}`. -/
noncomputable def cinSDProfile (τ : ℝ) : SDProfile where
  a := 0
  k := cinProfile τ
  a_nonneg := le_rfl
  k_nonneg := fun x _ => cinProfile_nonneg τ x
  k_antitone := antitoneOn_cinProfile τ
  k_zero := cinProfile_eq_zero (by simp)
  integrable_near_zero := by
    have hle : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * cinProfile τ x))
        ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, 1 := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      refine (ENNReal.ofReal_le_one).mpr ?_
      nlinarith [cinProfile_le_one τ x, cinProfile_nonneg τ x, hx.1.le, hx.2.le]
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_one, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  integrable_at_top := by
    have hle : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (cinProfile τ x / x))
        ≤ ∫⁻ x in Ioi (1 : ℝ), (Ioo (0 : ℝ) τ).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1 : ℝ) < x := hx
      by_cases hxm : x ∈ Ioo (0 : ℝ) τ
      · rw [Set.indicator_of_mem hxm]
        refine (ENNReal.ofReal_le_one).mpr ?_
        rw [div_le_one (by linarith)]
        exact le_trans (cinProfile_le_one τ x) hx1.le
      · rw [cinProfile_eq_zero hxm, zero_div, ENNReal.ofReal_zero]
        exact _root_.zero_le
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator measurableSet_Ioo, setLIntegral_one]
    refine ne_top_of_le_ne_top ?_ (Measure.restrict_apply_le _ _)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top

theorem cinSDProfile_exponentL {τ : ℝ} (hτ : 0 < τ) (ω : ℝ) :
    (cinSDProfile τ).exponentL ω = ENNReal.ofReal (cin (τ * ω)) := by
  have hzero : (∫⁻ x in Ici τ,
      ENNReal.ofReal ((1 - Real.cos (ω * x)) * cinProfile τ x / x)) = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ici fun x hx => ?_
    rw [cinProfile_eq_zero (by simp only [mem_Ioo, not_and, not_lt]; exact fun _ => hx),
      mul_zero, zero_div, ENNReal.ofReal_zero]
    rfl
  have hdisj : Disjoint (Ioo (0 : ℝ) τ) (Ici τ) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd (mem_Ici.mp hx3) (not_le.mpr hx2)
  have hsplit : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * cinProfile τ x / x))
      = ∫⁻ x in Ioo (0 : ℝ) τ, ENNReal.ofReal ((1 - Real.cos (ω * x)) / x) := by
    rw [← Ioo_union_Ici_eq_Ioi hτ, lintegral_union measurableSet_Ici hdisj, hzero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [cinProfile_eq_one hx, mul_one]
  have hint : IntegrableOn (fun x : ℝ => (1 - Real.cos (ω * x)) / x) (Ioo (0 : ℝ) τ) := by
    have h := intervalIntegrable_dilate_cinIntegrand ω hτ.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le] at h
    exact h.mono_set Ioo_subset_Ioc_self
  rw [SDProfile.exponentL, show (cinSDProfile τ).a = 0 from rfl,
    show (cinSDProfile τ).k = cinProfile τ from rfl, zero_mul, ENNReal.ofReal_zero, zero_add,
    hsplit, ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioo).mpr
        (.of_forall fun x hx => dilate_cinIntegrand_nonneg ω hx.1.le))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hτ.le,
    intervalIntegral_dilate_cinIntegrand, mul_comm]

/-- **`lem:cin-rays`(1), the ray.** The unit-step profile `1_{(0,τ)}` is admissible, with Gaussian
coefficient `0`, and its exponent is `Cin(τ·)`. -/
theorem cin_ray {τ : ℝ} (hτ : 0 < τ) :
    ∃ Q : SDProfile, Q.a = 0 ∧ Q.k = cinProfile τ ∧ ∀ ω : ℝ, Q.exponent ω = cin (τ * ω) :=
  ⟨cinSDProfile τ, rfl, rfl, fun ω => by
    rw [SDProfile.exponent, cinSDProfile_exponentL hτ ω,
      ENNReal.toReal_ofReal (cin_nonneg' _)]⟩

theorem SDProfile.integrableOn_k_div (P : SDProfile) :
    IntegrableOn (fun x => P.k x / x) (Ioi 1) := by
  have hmeas : AEMeasurable P.k (volume.restrict (Ioi (1 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
      (P.k_antitone.mono (Ioi_subset_Ioi zero_le_one))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x => P.k x / x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (P.k_nonneg x (mem_Ioi.mpr (lt_trans zero_lt_one hx)))
      (le_of_lt (lt_trans zero_lt_one hx))
  refine ⟨(hmeas.div aemeasurable_id).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  exact lt_top_iff_ne_top.mpr P.integrable_at_top

/-- **The profile vanishes at infinity.** Forced, not assumed: `k` is nonincreasing and
nonnegative and `∫₁^∞ k(x)/x\,dx < ∞`, so a positive limit would make that integral diverge
like the harmonic one.

twin: `Hemigroup.SelfDecomposableExponent.tendsto_k_atTop_nhds_zero`. -/
theorem SDProfile.tendsto_k_atTop (P : SDProfile) : Tendsto P.k atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact lt_of_lt_of_le ha (P.k_nonneg x (mem_Ioi.mpr hx))
  · by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hall : ∀ u : ℝ, 0 < u → a ≤ P.k u := by
      intro u hu
      obtain ⟨x, hxk, hxu⟩ := (hcon.and_eventually (eventually_ge_atTop u)).exists
      exact le_trans (not_lt.mp hxk)
        (P.k_antitone (mem_Ioi.mpr hu) (mem_Ioi.mpr (lt_of_lt_of_le hu hxu)) hxu)
    refine not_integrableOn_Ioi_inv (a := 1) ?_
    refine (P.integrableOn_k_div.const_mul a⁻¹).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := mem_Ioi.mp hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    have hk : a ≤ P.k x := hall x hx0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x⁻¹), inv_eq_one_div,
      div_le_iff₀ hx0, show a⁻¹ * (P.k x / x) * x = a⁻¹ * P.k x from by field_simp]
    calc (1 : ℝ) = a⁻¹ * a := by field_simp
      _ ≤ a⁻¹ * P.k x := by
          exact mul_le_mul_of_nonneg_left hk (by positivity)

/-! ## The tail measure -/

section TailMeasure

/-- The generalised inverse of a nonincreasing `h`: `tailInv h y = sup {u > 0 : h u > y}`.

twin: `Hemigroup.tailInv`, verbatim. -/
noncomputable def tailInv (h : ℝ → ℝ) (y : ℝ) : ℝ := sSup {u : ℝ | 0 < u ∧ y < h u}

variable {h : ℝ → ℝ}

theorem tailInv_nonneg (y : ℝ) : 0 ≤ tailInv h y := by
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | ⟨u, hu⟩
  · rw [tailInv, he, Real.sSup_empty]
  · by_cases hbd : BddAbove {u : ℝ | 0 < u ∧ y < h u}
    · exact le_trans hu.1.le (le_csSup hbd hu)
    · rw [tailInv, Real.sSup_of_not_bddAbove hbd]

theorem bddAbove_tailSet (htend : Tendsto h atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    BddAbove {u : ℝ | 0 < u ∧ y < h u} := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (htend.eventually_lt_const hy)
  refine ⟨M, fun u hu => ?_⟩
  by_contra hc
  exact absurd (hM u (le_of_lt (not_le.mp hc))) (not_lt.mpr hu.2.le)

theorem lt_of_lt_tailInv (hmono : AntitoneOn h (Ioi 0))
    {y r : ℝ} (hr : 0 < r) (hlt : r < tailInv h y) : y < h r := by
  have hne : {u : ℝ | 0 < u ∧ y < h u}.Nonempty := by
    rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | hne
    · rw [tailInv, he, Real.sSup_empty] at hlt; linarith
    · exact hne
  obtain ⟨u, hu, hru⟩ := exists_lt_of_lt_csSup hne hlt
  exact lt_of_lt_of_le hu.2 (hmono (mem_Ioi.mpr hr) (mem_Ioi.mpr hu.1) hru.le)

theorem lt_tailInv_of_lt (htend : Tendsto h atTop (𝓝 0)) {y u r : ℝ} (hy : 0 < y) (hu : 0 < u)
    (hru : r < u) (hlt : y < h u) : r < tailInv h y :=
  lt_of_lt_of_le hru (le_csSup (bddAbove_tailSet htend hy) ⟨hu, hlt⟩)

theorem antitoneOn_tailInv (htend : Tendsto h atTop (𝓝 0)) :
    AntitoneOn (tailInv h) (Ioi 0) := by
  intro y₁ h₁ y₂ h₂ h12
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y₂ < h u} with he | hne
  · rw [tailInv, he, Real.sSup_empty]; exact tailInv_nonneg _
  · exact csSup_le_csSup (bddAbove_tailSet htend (mem_Ioi.mp h₁)) hne
      (fun u hu => ⟨hu.1, lt_of_le_of_lt h12 hu.2⟩)

/-- **The tail measure.** The pushforward of Lebesgue measure on `(0,∞)` under the generalised
inverse of `h` has `ϖ(x,∞) = h(x)` at every continuity point of `h`, hence almost everywhere.

twin: `Hemigroup.exists_tailMeasure`, verbatim. -/
theorem exists_tailMeasure (hmono : AntitoneOn h (Ioi 0)) (htend : Tendsto h atTop (𝓝 0)) :
    ∃ ϖ : Measure ℝ, ϖ (Iio 0) = 0 ∧
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ϖ (Ioi r) = ENNReal.ofReal (h r) := by
  have hmeas : AEMeasurable (tailInv h) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (antitoneOn_tailInv htend)
  refine ⟨(volume.restrict (Ioi (0 : ℝ))).map (tailInv h), ?_, ?_⟩
  · rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Iio]
    convert measure_empty (μ := volume.restrict (Ioi (0 : ℝ)))
    ext y
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact tailInv_nonneg y
  · have hup : ∀ r : ℝ, 0 < r →
        ((volume.restrict (Ioi (0 : ℝ))).map (tailInv h)) (Ioi r) ≤ ENNReal.ofReal (h r) := by
      intro r hr
      rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi,
        Measure.restrict_apply' measurableSet_Ioi]
      refine le_trans (measure_mono (fun y hy => ?_)) (le_of_eq (by
        rw [Real.volume_Ioo, sub_zero]))
      exact ⟨mem_Ioi.mp hy.2, lt_of_lt_tailInv hmono hr hy.1⟩
    have hlow : ∀ r u : ℝ, 0 < r → r < u →
        ENNReal.ofReal (h u) ≤ ((volume.restrict (Ioi (0 : ℝ))).map (tailInv h)) (Ioi r) := by
      intro r u hr hru
      rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi,
        Measure.restrict_apply' measurableSet_Ioi]
      have hvol : volume (Ioo (0 : ℝ) (h u)) = ENNReal.ofReal (h u) := by
        rw [Real.volume_Ioo, sub_zero]
      rw [← hvol]
      refine measure_mono ?_
      rintro y ⟨hy0, hyu⟩
      exact ⟨lt_tailInv_of_lt htend hy0 (lt_trans hr hru) hru hyu, hy0⟩
    have hcount : {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r}.Countable := by
      have hH : Monotone (fun t : ℝ => -h (Real.exp t)) := by
        intro a b hab
        exact neg_le_neg (hmono (mem_Ioi.mpr (Real.exp_pos a)) (mem_Ioi.mpr (Real.exp_pos b))
          (Real.exp_le_exp.mpr hab))
      refine Countable.mono ?_ (hH.countable_not_continuousAt.image Real.exp)
      rintro r ⟨hr, hnc⟩
      refine ⟨Real.log r, fun hc => hnc ?_, Real.exp_log hr⟩
      have hc' : ContinuousAt (fun t : ℝ => h (Real.exp t)) (Real.log r) := by
        simpa using hc.neg
      have hlog : ContinuousAt Real.log r := Real.continuousAt_log (ne_of_gt hr)
      refine (ContinuousAt.congr (hc'.comp hlog) ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hr] with y hy
      simp [Real.exp_log (mem_Ioi.mp hy)]
    have h0 : volume {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} = 0 :=
      hcount.measure_zero volume
    have hnull : (volume.restrict (Ioi (0 : ℝ)))
        {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} = 0 := by
      rw [Measure.restrict_apply₀' measurableSet_Ioi.nullMeasurableSet]
      exact measure_mono_null inter_subset_left h0
    have hae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
        r ∉ {r : ℝ | 0 < r ∧ ¬ ContinuousWithinAt h (Ioi r) r} := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hae] with r hr hcont
    have hrp : (0 : ℝ) < r := mem_Ioi.mp hr
    have hcr : ContinuousWithinAt h (Ioi r) r := by
      by_contra hc
      exact hcont ⟨hrp, hc⟩
    refine le_antisymm (hup r hrp) ?_
    have hlim : Tendsto (fun u => ENNReal.ofReal (h u)) (𝓝[>] r) (𝓝 (ENNReal.ofReal (h r))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hcr
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hlow r u hrp (mem_Ioi.mp hu)

end TailMeasure

/-- **`lem:cin-rays`(2), "such a `ϖ` exists".** Every admissible profile has a Choquet measure:
a measure carried by `(0,∞)` whose tails are the profile at almost every positive point. -/
theorem cin_superposition_exists (P : SDProfile) : ∃ ϖ : Measure ℝ, HasProfileTail P.k ϖ := by
  obtain ⟨ν, -, htail⟩ := exists_tailMeasure P.k_antitone P.tendsto_k_atTop
  refine ⟨ν.restrict (Ioi 0), ?_, ?_⟩
  · rw [IsFolded, Measure.restrict_apply measurableSet_Iic]
    convert measure_empty (μ := ν)
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h
  · filter_upwards [htail, self_mem_ae_restrict measurableSet_Ioi] with r hr hr0
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_left (mem_Ioi.mp hr0).le, hr]

/-- **`lem:cin-rays`(2), the superposition** `eq:cone-superposition`. -/
theorem cin_superposition (P : SDProfile) (ϖ : Measure ℝ) (hϖ : HasProfileTail P.k ϖ) (ω : ℝ) :
    P.exponentL ω = cinSuperpositionL P.a ϖ ω := by
  obtain ⟨hfold, htail⟩ := hϖ
  have hnn : 0 ≤ᵐ[ϖ] (id : ℝ → ℝ) := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [Pi.zero_apply, id_eq, not_le, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht.le
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ϖ) (f := (id : ℝ → ℝ))
    (g := fun t : ℝ => (1 - Real.cos (ω * t)) / t) hnn aemeasurable_id
    (fun t ht => intervalIntegrable_dilate_cinIntegrand ω ht.le)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun t ht => dilate_cinIntegrand_nonneg ω (le_of_lt ht)))
  have hL : (∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ)
      = ∫⁻ τ, ENNReal.ofReal (∫ t in (0 : ℝ)..(id τ), (1 - Real.cos (ω * t)) / t) ∂ϖ :=
    lintegral_congr fun τ => by
      simp only [id_eq]
      rw [intervalIntegral_dilate_cinIntegrand, mul_comm]
  rw [SDProfile.exponentL, cinSuperpositionL, hL, hlayer]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [htail, self_mem_ae_restrict measurableSet_Ioi] with t ht ht0
  have ht0' : (0 : ℝ) < t := ht0
  rw [show {a : ℝ | t < id a} = Ioi t from rfl, ht,
    ← ENNReal.ofReal_mul (P.k_nonneg t (mem_Ioi.mpr ht0'))]
  congr 1
  field_simp

/-! ## `prop:cin-origin-singularity`, the `[T]` half

The node itself is an `[A]` interface on ledger A10 and nothing here consumes it, so no axiom is
admitted. Its fourth declaration is a different matter: read at the statement it is a fact about
`cinProfile` alone and needs neither A10 nor the threshold clause the skeleton's annotation
priced it "given". The profile is constantly `1` on `(0,tau)`, so it has right limit `1` at the
origin and its `K`-integrand vanishes identically on every `(y,tau)`.
-/

/-- **`prop:cin-origin-singularity`, the `Cin` rays sit at the threshold** -- the `[T]` half.

The ray's profile has right limit `1` at the origin, and the inner integral of the node's
threshold function `L` vanishes on `(y,tau)` for every `0 < y < tau`, so the comparison function
is a constant multiple of `log(1/|x|)` near the origin: the kernel is logarithmically singular
there. What is *not* stated is the propagation to the multiples of `tau`, which is
`rem:cin-propagation` and whose induction is written down nowhere.

Priced **S given the threshold clause** and paid **S needing nothing**: the declaration
quantifies over no law and mentions no density, so ledger A10 is an upper bound on what the
node's proof cites, not on what this clause needs. -/
theorem cin_origin_singularity_cin_ray {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (cinProfile τ) (𝓝[>] 0) (𝓝 1) ∧
      ∀ y : ℝ, 0 < y → y < τ → (∫ u in Ioo y τ, (1 - cinProfile τ u) / u) = 0 := by
  constructor
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hτ] with u hu
    exact (cinProfile_eq_one hu).symm
  · intro y hy hyτ
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ : ℝ => (0 : ℝ)) ?_]
    · simp
    · intro u hu
      simp only []
      rw [cinProfile_eq_one ⟨lt_trans hy hu.1, hu.2⟩]
      simp

end SpatialLine
