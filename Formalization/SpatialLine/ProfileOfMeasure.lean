/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ConeDefs
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The profile of a folded measure, and the domain condition that makes it one

Blueprint: `blueprint/src/parts/08-cone.tex`, `prop:choquet-cone` — the half of that node's
material which is a construction rather than a statement about the superposition map, and which
Chapter 7 also consumes. Given a folded measure `ϖ` satisfying the node's domain condition
`∫(τ² ∧ (1 + log₊τ))ϖ(dτ) < ∞`, `choquetSDProfile` is the `SDProfile` whose profile is the tail
`k(x) = ϖ((x,∞))` and whose Gaussian coefficient is prescribed, and
`hasProfileTail_choquetSDProfile` says its tail is `ϖ` again.

`lem:selfdecomposable-exponents`, (2) implies (3), is what makes the file separate: that proof
(`SpatialLine/SymbolInverse.lean`) builds its profile out of a measure exactly this way, so a
Chapter 7 module would otherwise import the whole of `SpatialLine/ChoquetCone.lean` and with it
Chapter 8's superposition map, its surjectivity, its domain and its linearity. Those four stay
there and import this file. Split out of `ChoquetCone.lean` on 2026-09-14 for the release export
(ADR-0005); no statement and no proof changed.

## The two Tonelli exchanges

`lintegral_min_sq_eq` and `lintegral_log_max_eq` are the node's own analysis, and they are the
same layer cake `lem:cin-rays` runs, with the weight changed:

* at the origin, weight `t` cut off at `1`, whose primitive is `(min tau 1)^2/2`, giving
  `int (min tau 1)^2/2 dvarpi = int_0^1 x varpi((x,infty)) dx`;
* at infinity, weight `1/t` cut off below `1`, whose primitive is `log_+ tau`, giving
  `int log_+ tau dvarpi = int_1^infty varpi((x,infty)) x^{-1} dx`.

Together with `domain_sandwich` -- `A + B <= tau^2 wedge (1 + log_+ tau) <= 2(A + B)` for the two
weights `A` and `B` -- they say that the node's domain condition on `varpi` is *exactly* the two
integrability conditions of `lem:profile-integrability` on the tail profile. That equivalence is
what makes `choquet_cone_forward` and `choquet_cone_surjective` two readings of one computation,
and the review's remark that the blueprint's domain condition is "exactly right" is now checked
rather than believed.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The layer-cake weight for the condition at the origin. -/
noncomputable def nearZeroWeight (t : ℝ) : ℝ := if t < 1 then t else 0

/-- The layer-cake weight for the condition at infinity. -/
noncomputable def atTopWeight (t : ℝ) : ℝ := if 1 < t then t⁻¹ else 0

theorem measurable_nearZeroWeight : Measurable nearZeroWeight := by
  unfold nearZeroWeight
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id
    measurable_const

theorem measurable_atTopWeight : Measurable atTopWeight := by
  unfold atTopWeight
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_inv
    measurable_const

theorem nearZeroWeight_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ nearZeroWeight t := by
  unfold nearZeroWeight; split <;> simp [ht]

theorem atTopWeight_nonneg (t : ℝ) : 0 ≤ atTopWeight t := by
  unfold atTopWeight; split
  · positivity
  · exact le_refl 0

theorem intervalIntegrable_nearZeroWeight {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable nearZeroWeight volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const (hs := hfin))
    measurable_nearZeroWeight.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (nearZeroWeight_nonneg ht.1.le)]
  unfold nearZeroWeight
  split <;> linarith

theorem intervalIntegrable_atTopWeight {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable atTopWeight volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const (hs := hfin))
    measurable_atTopWeight.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (atTopWeight_nonneg t)]
  unfold atTopWeight
  split
  · rename_i h; rw [inv_le_one_iff₀]; right; linarith
  · norm_num

/-- Almost every real is different from `1`, in the form the two evaluations below consume. -/
theorem ae_ne_one : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := volume) (1 : ℝ))] with t ht
  simpa using ht

/-- `∫₀^τ nearZeroWeight = (min τ 1)²/2`. -/
theorem integral_nearZeroWeight {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ t in (0 : ℝ)..τ, nearZeroWeight t) = min τ 1 ^ 2 / 2 := by
  have hone : (∫ t in (0 : ℝ)..1, nearZeroWeight t) = 1 / 2 := by
    rw [intervalIntegral.integral_congr_ae (g := fun t : ℝ => t) ?_, integral_id]
    · norm_num
    · filter_upwards [ae_ne_one] with t htne ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      simp only [nearZeroWeight]
      rw [if_pos (lt_of_le_of_ne ht.2 htne)]
  rcases le_or_gt τ 1 with h | h
  · rw [min_eq_left h]
    rw [intervalIntegral.integral_congr_ae (g := fun t : ℝ => t) ?_, integral_id]
    · ring
    · filter_upwards [ae_ne_one] with t htne ht
      rw [Set.uIoc_of_le hτ] at ht
      simp only [nearZeroWeight]
      rw [if_pos (lt_of_le_of_ne (le_trans ht.2 h) htne)]
  · rw [min_eq_right h.le]
    have hsplit : (∫ t in (0 : ℝ)..1, nearZeroWeight t) + (∫ t in (1 : ℝ)..τ, nearZeroWeight t)
        = ∫ t in (0 : ℝ)..τ, nearZeroWeight t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_nearZeroWeight zero_le_one)
        ((intervalIntegrable_nearZeroWeight hτ).mono_set (by
          rw [Set.uIcc_of_le h.le, Set.uIcc_of_le hτ]
          exact Icc_subset_Icc zero_le_one le_rfl))
    have h2 : (∫ t in (1 : ℝ)..τ, nearZeroWeight t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le h.le] at ht
        simp only [nearZeroWeight]
        rw [if_neg (by linarith [ht.1])]
    rw [← hsplit, hone, h2]
    norm_num

/-- `∫₀^τ atTopWeight = log (max τ 1)`. -/
theorem integral_atTopWeight {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ t in (0 : ℝ)..τ, atTopWeight t) = Real.log (max τ 1) := by
  have hzero : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (∫ t in (0 : ℝ)..z, atTopWeight t) = 0 := by
    intro z hz hz1
    rw [intervalIntegral.integral_congr_ae (g := fun _ : ℝ => (0 : ℝ)) ?_]
    · simp
    · filter_upwards [ae_ne_one] with t htne ht
      rw [Set.uIoc_of_le hz] at ht
      simp only [atTopWeight]
      rw [if_neg (by
        have : t ≤ 1 := le_trans ht.2 hz1
        exact not_lt.mpr this)]
  rcases le_or_gt τ 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    exact hzero τ hτ h
  · rw [max_eq_left h.le]
    have hsplit : (∫ t in (0 : ℝ)..1, atTopWeight t) + (∫ t in (1 : ℝ)..τ, atTopWeight t)
        = ∫ t in (0 : ℝ)..τ, atTopWeight t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_atTopWeight zero_le_one)
        ((intervalIntegrable_atTopWeight hτ).mono_set (by
          rw [Set.uIcc_of_le h.le, Set.uIcc_of_le hτ]
          exact Icc_subset_Icc zero_le_one le_rfl))
    have h2 : (∫ t in (1 : ℝ)..τ, atTopWeight t) = Real.log τ := by
      rw [intervalIntegral.integral_congr_ae (g := fun t : ℝ => t⁻¹) ?_,
        integral_inv_of_pos zero_lt_one (lt_trans zero_lt_one h), div_one]
      filter_upwards [ae_ne_one] with t htne ht
      rw [Set.uIoc_of_le h.le] at ht
      simp only [atTopWeight]
      rw [if_pos (lt_of_le_of_ne ht.1.le (Ne.symm htne))]
    rw [← hsplit, hzero 1 zero_le_one le_rfl, h2, zero_add]

/-! ## The two layer-cake exchanges -/

theorem ae_nonneg_of_isFolded {ϖ : Measure ℝ} (hfold : IsFolded ϖ) : 0 ≤ᵐ[ϖ] (id : ℝ → ℝ) := by
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun t ht => ?_) hfold
  simp only [Pi.zero_apply, id_eq, not_le, mem_setOf_eq] at ht
  exact mem_Iic.mpr ht.le

/-- **Tonelli at the origin**: `∫ (min τ 1)²/2 ϖ(dτ) = ∫₀¹ x ϖ((x,∞)) dx`. -/
theorem lintegral_min_sq_eq (ϖ : Measure ℝ) (hfold : IsFolded ϖ) :
    (∫⁻ τ, ENNReal.ofReal (min τ 1 ^ 2 / 2) ∂ϖ)
      = ∫⁻ x in Ioo (0 : ℝ) 1, ϖ (Ioi x) * ENNReal.ofReal x := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ϖ) (f := (id : ℝ → ℝ))
    (g := nearZeroWeight) (ae_nonneg_of_isFolded hfold) aemeasurable_id
    (fun t ht => intervalIntegrable_nearZeroWeight ht.le)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun t ht => nearZeroWeight_nonneg (le_of_lt ht)))
  have hL : (∫⁻ τ, ENNReal.ofReal (min τ 1 ^ 2 / 2) ∂ϖ)
      = ∫⁻ τ, ENNReal.ofReal (∫ t in (0 : ℝ)..(id τ), nearZeroWeight t) ∂ϖ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_isFolded hfold] with τ hτ
    rw [id_eq] at hτ ⊢
    rw [integral_nearZeroWeight hτ]
  rw [hL, hlayer]
  have hsets : {a : ℝ | (0 : ℝ) < a} = Ioi (0 : ℝ) := rfl
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd (mem_Ici.mp hx3) (not_le.mpr hx2)
  rw [← Ioo_union_Ici_eq_Ioi (zero_lt_one (α := ℝ)),
    lintegral_union measurableSet_Ici hdisj]
  have hzero : (∫⁻ t in Ici (1 : ℝ), ϖ {a : ℝ | t < id a} * ENNReal.ofReal (nearZeroWeight t))
      = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ici fun t ht => ?_
    simp only [nearZeroWeight, if_neg (not_lt.mpr (mem_Ici.mp ht)), ENNReal.ofReal_zero, mul_zero]
    rfl
  rw [hzero, add_zero]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [nearZeroWeight, if_pos ht.2, id_eq]
  rfl

/-- **Tonelli at infinity**: `∫ log₊τ ϖ(dτ) = ∫₁^∞ ϖ((x,∞)) x⁻¹ dx`. -/
theorem lintegral_log_max_eq (ϖ : Measure ℝ) (hfold : IsFolded ϖ) :
    (∫⁻ τ, ENNReal.ofReal (Real.log (max τ 1)) ∂ϖ)
      = ∫⁻ x in Ioi (1 : ℝ), ϖ (Ioi x) * ENNReal.ofReal x⁻¹ := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ϖ) (f := (id : ℝ → ℝ))
    (g := atTopWeight) (ae_nonneg_of_isFolded hfold) aemeasurable_id
    (fun t ht => intervalIntegrable_atTopWeight ht.le)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t _ => atTopWeight_nonneg t))
  have hL : (∫⁻ τ, ENNReal.ofReal (Real.log (max τ 1)) ∂ϖ)
      = ∫⁻ τ, ENNReal.ofReal (∫ t in (0 : ℝ)..(id τ), atTopWeight t) ∂ϖ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_isFolded hfold] with τ hτ
    rw [id_eq] at hτ ⊢
    rw [integral_atTopWeight hτ]
  rw [hL, hlayer]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := Ioc_disjoint_Ioi le_rfl
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one (α := ℝ)),
    lintegral_union measurableSet_Ioi hdisj]
  have hzero : (∫⁻ t in Ioc (0 : ℝ) 1, ϖ {a : ℝ | t < id a} * ENNReal.ofReal (atTopWeight t))
      = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ioc fun t ht => ?_
    simp only [atTopWeight, if_neg (not_lt.mpr ht.2), ENNReal.ofReal_zero, mul_zero]
    rfl
  rw [hzero, zero_add]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [atTopWeight, if_pos (mem_Ioi.mp ht), id_eq]
  rfl

/-! ## The domain condition -/

/-- The integrand of `prop:choquet-cone`'s domain condition, `τ² ∧ (1 + log₊τ)`. -/
noncomputable def domainIntegrand (τ : ℝ) : ℝ := min (τ ^ 2) (1 + Real.log (max 1 τ))

theorem log_max_one_nonneg (τ : ℝ) : 0 ≤ Real.log (max 1 τ) :=
  Real.log_nonneg (le_max_left _ _)

theorem domainIntegrand_nonneg {τ : ℝ} (_hτ : 0 ≤ τ) : 0 ≤ domainIntegrand τ :=
  le_min (by positivity) (by linarith [log_max_one_nonneg τ])

theorem one_add_log_le_sq {τ : ℝ} (hτ : 1 ≤ τ) : 1 + Real.log τ ≤ τ ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hτ)
  nlinarith

/-- The two layer-cake integrands add up to the domain integrand, up to a factor of two. -/
theorem domain_sandwich {τ : ℝ} (hτ : 0 < τ) :
    min τ 1 ^ 2 / 2 + Real.log (max τ 1) ≤ domainIntegrand τ ∧
      domainIntegrand τ ≤ 2 * (min τ 1 ^ 2 / 2 + Real.log (max τ 1)) := by
  rcases le_or_gt τ 1 with h | h
  · rw [min_eq_left h, max_eq_right h, Real.log_one, domainIntegrand, max_eq_left h,
      Real.log_one]
    constructor
    · rw [add_zero]
      refine le_min (by nlinarith) (by nlinarith)
    · rw [min_eq_left (by nlinarith : τ ^ 2 ≤ 1 + 0)]
      ring_nf
      linarith
  · rw [min_eq_right h.le, max_eq_left h.le, domainIntegrand, max_eq_right h.le,
      min_eq_right (one_add_log_le_sq h.le)]
    have hlog : 0 ≤ Real.log τ := Real.log_nonneg h.le
    constructor <;> [linarith; (ring_nf; linarith)]

theorem domain_iff (ϖ : Measure ℝ) (hfold : IsFolded ϖ) :
    (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤ ↔
      ((∫⁻ τ, ENNReal.ofReal (min τ 1 ^ 2 / 2) ∂ϖ) ≠ ⊤ ∧
        (∫⁻ τ, ENNReal.ofReal (Real.log (max τ 1)) ∂ϖ) ≠ ⊤) := by
  have hpos : ∀ᵐ τ ∂ϖ, 0 < τ := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  constructor
  · intro hdom
    constructor
    · refine ne_top_of_le_ne_top hdom (lintegral_mono_ae ?_)
      filter_upwards [hpos] with τ hτ
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [(domain_sandwich hτ).1, log_max_one_nonneg τ,
        Real.log_nonneg (le_max_right τ 1)]
    · refine ne_top_of_le_ne_top hdom (lintegral_mono_ae ?_)
      filter_upwards [hpos] with τ hτ
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := (domain_sandwich hτ).1
      have h2 : 0 ≤ min τ 1 ^ 2 / 2 := by positivity
      linarith
  · rintro ⟨h1, h2⟩
    have hle : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ)
        ≤ 2 * ((∫⁻ τ, ENNReal.ofReal (min τ 1 ^ 2 / 2) ∂ϖ)
          + ∫⁻ τ, ENNReal.ofReal (Real.log (max τ 1)) ∂ϖ) := by
      rw [← lintegral_add_left' (Measurable.aemeasurable (by fun_prop)) _, ← lintegral_const_mul']
      · refine lintegral_mono_ae ?_
        filter_upwards [hpos] with τ hτ
        have h := (domain_sandwich hτ).2
        have hA : 0 ≤ min τ 1 ^ 2 / 2 := by positivity
        have hB : 0 ≤ Real.log (max τ 1) := Real.log_nonneg (le_max_right τ 1)
        calc ENNReal.ofReal (domainIntegrand τ)
            ≤ ENNReal.ofReal (2 * (min τ 1 ^ 2 / 2 + Real.log (max τ 1))) :=
              ENNReal.ofReal_le_ofReal h
          _ = 2 * (ENNReal.ofReal (min τ 1 ^ 2 / 2) + ENNReal.ofReal (Real.log (max τ 1))) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hA hB]
              norm_num
      · exact (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    exact ne_top_of_le_ne_top (by finiteness) hle

/-! ## The map into the cone -/

/-- The tail of `ϖ`, as a profile: `k(x) = ϖ((x,∞))` for `x > 0`, and `0` at `x ≤ 0`.

The guard at the origin is `SDProfile.k_zero`'s normalisation, and it is load-bearing here in a
way it is not for a general profile: `ϖ((0,∞))` is the total mass and is typically infinite. -/
noncomputable def tailProfile (ϖ : Measure ℝ) : ℝ → ℝ :=
  fun x => if 0 < x then (ϖ (Ioi x)).toReal else 0

theorem measure_Ioi_ne_top_of_domain {ϖ : Measure ℝ}
    (hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤) {x : ℝ} (hx : 0 < x) :
    ϖ (Ioi x) ≠ ⊤ := by
  have hcpos : 0 < min (x ^ 2) 1 := lt_min (by positivity) zero_lt_one
  have hle : ENNReal.ofReal (min (x ^ 2) 1) * ϖ (Ioi x)
      ≤ ∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ := by
    calc ENNReal.ofReal (min (x ^ 2) 1) * ϖ (Ioi x)
        = ∫⁻ _ in Ioi x, ENNReal.ofReal (min (x ^ 2) 1) ∂ϖ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ τ in Ioi x, ENNReal.ofReal (domainIntegrand τ) ∂ϖ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
          have hτx : x < τ := hτ
          refine ENNReal.ofReal_le_ofReal ?_
          refine le_min (le_trans (min_le_left _ _) (by nlinarith)) ?_
          exact le_trans (min_le_right _ _) (by linarith [log_max_one_nonneg τ])
      _ ≤ _ := setLIntegral_le_lintegral _ _
  intro hcon
  have hne0 : ENNReal.ofReal (min (x ^ 2) 1) ≠ 0 := fun h =>
    absurd (ENNReal.ofReal_eq_zero.mp h) (not_le.mpr hcpos)
  rw [hcon, ENNReal.mul_top hne0] at hle
  exact hdom (top_le_iff.mp hle)

/-- The tail profile is an `SDProfile` with the prescribed Gaussian coefficient, as soon as `ϖ`
lies in `prop:choquet-cone`'s domain. -/
noncomputable def choquetSDProfile {a : ℝ} (ha : 0 ≤ a) (ϖ : Measure ℝ) (hfold : IsFolded ϖ)
    (hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤) : SDProfile where
  a := a
  k := tailProfile ϖ
  a_nonneg := ha
  k_nonneg := fun x _ => by
    simp only [tailProfile]; split
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  k_antitone := by
    intro u hu v hv huv
    have hu' : (0 : ℝ) < u := hu
    have hv' : (0 : ℝ) < v := hv
    simp only [tailProfile, if_pos hu', if_pos hv']
    exact ENNReal.toReal_mono (measure_Ioi_ne_top_of_domain hdom hu')
      (measure_mono (Ioi_subset_Ioi huv))
  k_zero := by simp [tailProfile]
  integrable_near_zero := by
    have heq : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * tailProfile ϖ x))
        = ∫⁻ x in Ioo (0 : ℝ) 1, ϖ (Ioi x) * ENNReal.ofReal x := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      simp only [tailProfile, if_pos hx0]
      rw [ENNReal.ofReal_mul hx0.le,
        ENNReal.ofReal_toReal (measure_Ioi_ne_top_of_domain hdom hx0), mul_comm]
    rw [heq, ← lintegral_min_sq_eq ϖ hfold]
    exact ((domain_iff ϖ hfold).mp hdom).1
  integrable_at_top := by
    have heq : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (tailProfile ϖ x / x))
        = ∫⁻ x in Ioi (1 : ℝ), ϖ (Ioi x) * ENNReal.ofReal x⁻¹ := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      simp only [tailProfile, if_pos hx0]
      rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_Ioi_ne_top_of_domain hdom hx0)]
    rw [heq, ← lintegral_log_max_eq ϖ hfold]
    exact ((domain_iff ϖ hfold).mp hdom).2

theorem hasProfileTail_choquetSDProfile {a : ℝ} (ha : 0 ≤ a) (ϖ : Measure ℝ)
    (hfold : IsFolded ϖ)
    (hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂ϖ) ≠ ⊤) :
    HasProfileTail (choquetSDProfile ha ϖ hfold hdom).k ϖ := by
  refine ⟨hfold, ?_⟩
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  show ϖ (Ioi x) = ENNReal.ofReal (tailProfile ϖ x)
  simp only [tailProfile, if_pos hx0]
  rw [ENNReal.ofReal_toReal (measure_Ioi_ne_top_of_domain hdom hx0)]

end SpatialLine
