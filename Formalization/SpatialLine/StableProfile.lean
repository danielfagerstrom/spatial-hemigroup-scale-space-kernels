/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import SpatialLine.SemigroupCase
import SpatialLine.Frullani
import SpatialLine.StrictPositivityStrict
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `cor:semigroup-case`, the pure-power profile

Blueprint: `cor:semigroup-case`, the clause `k(x) = C_α^{-1}x^{-α}` with
`C_α = ∫₀^∞ (1 - cos u)u^{-1-α}du ∈ (0,∞)`.

## What the constant costs, and what it does not

The normalising constant is an improper integral at both endpoints and Mathlib carries neither
value; but the node does not ask for the value, only for convergence, positivity and the
scaling identity, and each of those is a comparison. Convergence is the two regimes of the
truncation read against `Real.rpow`: near the origin `1 - cos u ≤ u²/2` makes the integrand at
most `u^{1-α}/2`, integrable exactly when `α < 2`; beyond `1` the numerator is at most `2` and
the integrand at most `2u^{-1-α}`, integrable exactly when `α > 0`. Positivity is that the
integrand is nonnegative and does not vanish on `(0,1)`.

The scaling identity `∫₀^∞ (1 - cos ωx)x^{-1-α}dx = C_α|ω|^α` is the change of variables
`u = |ω|x`, and it is done in `ℝ≥0∞` — `setLIntegral_Ioi_comp_mul`, which needs no
integrability — so the only place the Bochner integral appears is the one identification
`∫⁻ ofReal = ofReal ∫` at frequency `1`.

**The estimate.** The skeleton priced this **M** and named the constant as the obstacle. The
constant is not the obstacle: it never has to be evaluated, and its two convergence conditions
are exactly the two integrability fields of `SDProfile`, so the same two comparisons discharge
both. What the estimate did not name is that the dilation identity has to be run in `ℝ≥0∞` to
avoid a second integrability argument at every frequency.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The normalising constant -/

/-- The integrand of `C_α`. -/
noncomputable def stableIntegrand (α u : ℝ) : ℝ := (1 - Real.cos u) / u ^ (1 + α)

theorem measurable_stableIntegrand (α : ℝ) : Measurable (stableIntegrand α) := by
  unfold stableIntegrand
  fun_prop

theorem stableIntegrand_nonneg (α : ℝ) {u : ℝ} (hu : 0 < u) : 0 ≤ stableIntegrand α u := by
  have hcos : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  exact div_nonneg hcos (Real.rpow_nonneg hu.le _)

/-- **`C_α` converges for `0 < α < 2`.** The two regimes of the truncation, compared against a
power. -/
theorem integrableOn_stableIntegrand {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    IntegrableOn (stableIntegrand α) (Ioi (0 : ℝ)) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  refine IntegrableOn.union ?_ ?_
  · -- near the origin: `1 - cos u ≤ u²/2`
    have hb : IntegrableOn (fun u : ℝ => u ^ (1 - α) / 2) (Ioc (0 : ℝ) 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (by linarith : (-1 : ℝ) < 1 - α)).1).div_const 2
    refine Integrable.mono' hb (measurable_stableIntegrand α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hpow : (0 : ℝ) < u ^ (1 + α) := Real.rpow_pos_of_pos hu0 _
    have hkey : u ^ (2 : ℝ) / u ^ (1 + α) = u ^ (1 - α) := by
      rw [← Real.rpow_sub hu0]
      congr 1
      ring
    have hsq : u ^ (2 : ℝ) = u ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (stableIntegrand_nonneg α hu0), stableIntegrand,
      div_le_iff₀ hpow]
    have hcos : 1 - Real.cos u ≤ u ^ 2 / 2 := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := u)]
    have hrw : u ^ (1 - α) / 2 * u ^ (1 + α) = u ^ 2 / 2 := by
      rw [← hkey, hsq]
      field_simp
    rw [hrw]
    exact hcos
  · -- beyond `1`: the numerator is bounded
    have hb : IntegrableOn (fun u : ℝ => 2 * u ^ (-(1 + α))) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) zero_lt_one).const_mul 2
    refine Integrable.mono' hb (measurable_stableIntegrand α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hpow : (0 : ℝ) < u ^ (1 + α) := Real.rpow_pos_of_pos hu0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (stableIntegrand_nonneg α hu0), stableIntegrand,
      div_le_iff₀ hpow, Real.rpow_neg hu0.le]
    have hinv : 2 * (u ^ (1 + α))⁻¹ * u ^ (1 + α) = 2 := by
      field_simp
    rw [hinv]
    linarith [Real.neg_one_le_cos u]

/-- **`C_α > 0`.** The integrand is nonnegative and strictly positive on `(0,1)`. -/
theorem stableConst_pos {α : ℝ} (hα : 0 < α) (hα2 : α < 2) : 0 < stableConst α := by
  show (0 : ℝ) < ∫ u in Ioi (0 : ℝ), stableIntegrand α u
  have hint := integrableOn_stableIntegrand hα hα2
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] stableIntegrand α :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun u hu => stableIntegrand_nonneg α hu)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (stableIntegrand α) ∩ Ioi 0 := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hu1 : u < 1 := hu.2
    refine ⟨?_, hu0⟩
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hcos : Real.cos u < 1 := by
      rcases lt_or_eq_of_le (Real.cos_le_one u) with h | h
      · exact h
      · exfalso
        obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff u).mp h
        have hn0 : (0 : ℤ) < n := by
          by_contra hcon
          have hle : n ≤ 0 := le_of_not_gt hcon
          have hle' : (n : ℝ) ≤ 0 := by exact_mod_cast hle
          nlinarith
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
        nlinarith
    have hpow : (0 : ℝ) < u ^ (1 + α) := Real.rpow_pos_of_pos hu0 _
    simp only [Function.mem_support, ne_eq, stableIntegrand]
    intro hcon
    rw [div_eq_zero_iff] at hcon
    rcases hcon with h | h
    · linarith
    · linarith
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp [Real.volume_Ioo]

/-! ## The profile

`stableConst` and `stableProfile` are chapter 10's vocabulary (`SpatialLine/Corners.lean`), and
they are what `prop:stable-family`'s remaining clauses quantify over, so this node's witness is
built on them rather than on a second copy.
-/

theorem stableConst_eq (α : ℝ) : stableConst α = ∫ u in Ioi (0 : ℝ), stableIntegrand α u := rfl

theorem stableConst_pos' {α : ℝ} (hα : 0 < α) (hα2 : α < 2) : 0 < stableConst α :=
  stableConst_pos hα hα2

theorem stableProfile_of_pos {α : ℝ} {x : ℝ} (hx : 0 < x) :
    stableProfile α x = (stableConst α)⁻¹ * x ^ (-α) :=
  Set.indicator_of_mem hx _

theorem stableProfile_nonneg {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (x : ℝ) :
    0 ≤ stableProfile α x := by
  unfold stableProfile
  rw [Set.indicator_apply]
  split_ifs with h
  · exact mul_nonneg (inv_nonneg.mpr (stableConst_pos hα hα2).le)
      (Real.rpow_nonneg (le_of_lt h) _)
  · exact le_rfl

theorem stableProfile_zero (α : ℝ) : stableProfile α 0 = 0 := by
  simp [stableProfile]

theorem stableProfile_antitoneOn {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    AntitoneOn (stableProfile α) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  rw [stableProfile_of_pos hx0, stableProfile_of_pos hy0]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith : -α ≤ 0))
    (inv_nonneg.mpr (stableConst_pos hα hα2).le)

theorem measurable_stableProfile (α : ℝ) : Measurable (stableProfile α) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

/-! ## The two integrability conditions -/

theorem integrableOn_id_mul_stableProfile {α : ℝ} (hα2 : α < 2) :
    IntegrableOn (fun x : ℝ => x * stableProfile α x) (Ioo (0 : ℝ) 1) := by
  have hbase : IntegrableOn (fun x : ℝ => (stableConst α)⁻¹ * x ^ (1 - α)) (Ioo (0 : ℝ) 1) :=
    IntegrableOn.mono_set
      (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (by linarith : (-1 : ℝ) < 1 - α)).1).const_mul (stableConst α)⁻¹) Ioo_subset_Ioc_self
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioo
  have hx0 : (0 : ℝ) < x := hx.1
  show (stableConst α)⁻¹ * x ^ (1 - α) = x * stableProfile α x
  rw [stableProfile_of_pos hx0, show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hx0,
    Real.rpow_one]
  ring

theorem integrableOn_stableProfile_div {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun x : ℝ => stableProfile α x / x) (Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => (stableConst α)⁻¹ * x ^ (-α + -1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -α + -1 < -1) zero_lt_one).const_mul
      (stableConst α)⁻¹
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  show (stableConst α)⁻¹ * x ^ (-α + -1) = stableProfile α x / x
  rw [stableProfile_of_pos hx0, Real.rpow_add hx0, Real.rpow_neg_one]
  field_simp

/-! ## The witness -/

/-- The `SDProfile` of `cor:semigroup-case` for `0 < α < 2`: Gaussian coefficient `0` and the
pure-power profile `C_α⁻¹x^{-α}` of `SpatialLine/Corners.lean`. -/
noncomputable def stableDatum (α : ℝ) (hα : 0 < α) (hα2 : α < 2) : SDProfile where
  a := 0
  k := stableProfile α
  a_nonneg := le_rfl
  k_nonneg := fun x _ => stableProfile_nonneg hα hα2 x
  k_antitone := stableProfile_antitoneOn hα hα2
  k_zero := stableProfile_zero α
  integrable_near_zero :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_id_mul_stableProfile hα2)
      ((ae_restrict_iff' measurableSet_Ioo).mpr
        (.of_forall fun x hx => mul_nonneg hx.1.le (stableProfile_nonneg hα hα2 x)))
  integrable_at_top :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_stableProfile_div hα)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (.of_forall fun x hx =>
          div_nonneg (stableProfile_nonneg hα hα2 x) (lt_trans zero_lt_one hx).le))

@[simp] theorem stableDatum_a (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
    (stableDatum α hα hα2).a = 0 := rfl

@[simp] theorem stableDatum_k (α : ℝ) (hα : 0 < α) (hα2 : α < 2) :
    (stableDatum α hα hα2).k = stableProfile α := rfl

/-! ## The exponent -/

/-- The jump integral of the pure-power profile is `|ω|^α`.

The change of variables `u = |ω|x` is run in `ℝ≥0∞`, where it needs no integrability; the
Bochner integral appears once, to identify the integral of the integrand with `C_α`. -/
theorem lintegral_stableProfile {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (ω : ℝ) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * stableProfile α x / x))
      = ENNReal.ofReal (|ω| ^ α) := by
  have hCpos : 0 < stableConst α := stableConst_pos hα hα2
  have hCne : stableConst α ≠ 0 := hCpos.ne'
  rcases eq_or_ne ω 0 with hω0 | hω
  · subst hω0
    simp [Real.zero_rpow hα.ne']
  set c : ℝ := |ω| with hcdef
  have hc : 0 < c := abs_pos.mpr hω
  have hcos : ∀ x : ℝ, Real.cos (ω * x) = Real.cos (c * x) := by
    intro x
    rcases abs_cases ω with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hcdef, h]
    · rw [hcdef, h, neg_mul, Real.cos_neg]
  set K : ℝ := c ^ (1 + α) * (stableConst α)⁻¹ with hK
  have hKnn : 0 ≤ K := by positivity
  set G : ℝ → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (K * ((1 - Real.cos u) * u ^ (-(1 + α)))) with hG
  have hchange := setLIntegral_Ioi_comp_mul hc G
  have hright : (∫⁻ x in Ioi (0 : ℝ), G (c * x))
      = ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * stableProfile α x / x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hsplit : (c * x) ^ (-(1 + α)) = c ^ (-(1 + α)) * x ^ (-(1 + α)) :=
      Real.mul_rpow hc.le hx0.le
    have hcancel : c ^ (1 + α) * c ^ (-(1 + α)) = 1 := by
      rw [Real.rpow_neg hc.le]
      exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hc _).ne'
    have hxpow : x ^ (-α) / x = x ^ (-(1 + α)) := by
      rw [show -(1 + α) = -α + -1 by ring, Real.rpow_add hx0, Real.rpow_neg_one]
      field_simp
    show ENNReal.ofReal (K * ((1 - Real.cos (c * x)) * (c * x) ^ (-(1 + α)))) = _
    rw [hsplit, hcos x, stableProfile_of_pos hx0]
    congr 1
    have hL : K * ((1 - Real.cos (c * x)) * (c ^ (-(1 + α)) * x ^ (-(1 + α))))
        = c ^ (1 + α) * c ^ (-(1 + α))
          * ((1 - Real.cos (c * x)) * (stableConst α)⁻¹ * x ^ (-(1 + α))) := by
      rw [hK]; ring
    have hR : (1 - Real.cos (c * x)) * ((stableConst α)⁻¹ * x ^ (-α)) / x
        = (1 - Real.cos (c * x)) * (stableConst α)⁻¹ * (x ^ (-α) / x) := by ring
    rw [hL, hcancel, one_mul, hR, hxpow]
  have hleft : (∫⁻ u in Ioi (0 : ℝ), G u) = ENNReal.ofReal (c ^ (1 + α)) := by
    have hpt : ∀ u ∈ Ioi (0 : ℝ),
        G u = ENNReal.ofReal K * ENNReal.ofReal (stableIntegrand α u) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      show ENNReal.ofReal (K * ((1 - Real.cos u) * u ^ (-(1 + α)))) = _
      rw [← ENNReal.ofReal_mul hKnn]
      congr 1
      simp only [stableIntegrand]
      rw [Real.rpow_neg hu0.le]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_stableIntegrand hα hα2)
        ((ae_restrict_iff' measurableSet_Ioi).mpr
          (.of_forall fun u hu => stableIntegrand_nonneg α hu)),
      ← stableConst_eq, ← ENNReal.ofReal_mul hKnn, hK]
    congr 1
    field_simp
  rw [hright, hleft] at hchange
  have hmul : ENNReal.ofReal c * ENNReal.ofReal (c ^ α) = ENNReal.ofReal (c ^ (1 + α)) := by
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    rw [Real.rpow_add hc, Real.rpow_one]
  rw [← hmul] at hchange
  exact ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top).mp hchange).symm

/-- The exponent of the pure-power profile is `|ω|^α`. -/
theorem stableDatum_exponent {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (ω : ℝ) :
    (stableDatum α hα hα2).exponent ω = |ω| ^ α := by
  rw [SDProfile.exponent, SDProfile.exponentL, stableDatum_a, stableDatum_k,
    lintegral_stableProfile hα hα2 ω]
  simp [ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg ω) α)]

/-! ## The node -/

/-- **`cor:semigroup-case`, the profile for `0 < α < 2`.** The normalising constant converges and
is positive, and the pure-power profile with Gaussian coefficient `0` has exponent `|ω|^α`. -/
theorem semigroup_case_profile (α : ℝ) (hα : 0 < α) (hα2 : α < 2) (C : ℝ)
    (hC : C = ∫ u in Ioi (0 : ℝ), (1 - Real.cos u) / u ^ (1 + α)) :
    0 < C ∧ ∃ Q : SDProfile, Q.a = 0 ∧ (∀ x : ℝ, 0 < x → Q.k x = C⁻¹ * x ^ (-α)) ∧
      ∀ ω : ℝ, Q.exponent ω = |ω| ^ α := by
  have hCeq : C = stableConst α := hC
  subst hCeq
  exact ⟨stableConst_pos hα hα2, stableDatum α hα hα2, rfl,
    fun _ hx => stableProfile_of_pos hx, stableDatum_exponent hα hα2⟩

end SpatialLine
