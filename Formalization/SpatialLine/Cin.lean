/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ConeDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The elementary properties of `Cin`

Blueprint: `blueprint/src/parts/08-cone.tex`, the function clauses of `lem:cin-rays`(1) --
evenness, monotonicity, the bound `z^2/4`, and the two expansions. The node's remaining clauses,
the ray and the superposition, are `SpatialLine/CinRays.lean`.

The `## The calculus of Cin` section below -- `Cin' = cinIntegrand` everywhere, the origin
included -- was written by chapter 7 in `SpatialLine/Symbol.lean` and moved here by the wave-6
merge, chapter 8's delay equation having come to read its ODE off `hasDerivAt_cin`. It is a fact
about `Cin`, and this is `Cin`'s file.

twin: `Hemigroup.Ein`, with `1 - e^{-u}` replaced by `1 - cos u`. The two differ in the way this
file is longer than its twin: `einIntegrand` is bounded by `1`, so `Ein` grows at most linearly
and its behaviour at infinity needs no argument, while `cinIntegrand` is only conditionally
integrable at infinity and the constant `C` of the expansion `Cin(z) = log z + C + O(1/z)` is
reached through one integration by parts.

## The expansion at infinity, and the constant

`cinConst` is the constant, written out as `Cin(1) + sin 1 - int_{(1,infty)} sin v / v^2 dv`, the
last integral absolutely convergent. The node asserts only that *some* finite constant works
(`cin_expansion_top` is existential in `C`), which is its own deliberate narrowing: the value
`gamma_E` is `rem:cin-constant` and is used nowhere. `cinConst` is nevertheless named, because the
error bound `|Cin(z) - log z - C| <= 2/z` for `z >= 1` is what the existential is proved from and
is sharper than the node needs.

The route is the blueprint's own and is machine-checked at every step: split the integral at
`v = 1`, write `(1 - cos v)/v = 1/v - cos v/v` on `[1,z]`, and integrate `cos v / v` by parts
against the primitive `sin v / v`, whose remainder past `z` is dominated by `int_z^infty v^{-2} dv
= 1/z`.

## The expansion at the origin

`cin_expansion_zero` is `Cin(z) - z^2/4 = O(z^4)` at the origin. What is proved is the explicit
bound `|Cin(z) - z^2/4| <= 5 z^4 / 96` for `|z| <= 1`, from Mathlib's `Real.cos_bound`; the
blueprint's route through the term-by-term Taylor series is the same computation with the tail
estimate supplied by a series rather than by a single inequality.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The integrand -/

theorem cinIntegrand_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ cinIntegrand v :=
  div_nonneg (by linarith [Real.cos_le_one v]) hv

theorem cinIntegrand_neg (v : ℝ) : cinIntegrand (-v) = -cinIntegrand v := by
  rw [cinIntegrand, cinIntegrand, Real.cos_neg, div_neg]

theorem cinIntegrand_le_half {v : ℝ} (hv : 0 ≤ v) : cinIntegrand v ≤ v / 2 := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp [cinIntegrand]
  · rw [cinIntegrand, div_le_iff₀ hv']
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]

theorem measurable_cinIntegrand : Measurable cinIntegrand := by
  unfold cinIntegrand; fun_prop

theorem intervalIntegrable_cinIntegrand {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable cinIntegrand volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => z / 2) (integrableOn_const (hs := hfin))
    measurable_cinIntegrand.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun v hv => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cinIntegrand_nonneg hv.1.le)]
  exact le_trans (cinIntegrand_le_half hv.1.le) (by linarith [hv.2])

/-! ## The calculus of `Cin` -/

/-- `|Cin'(v)| ≤ |v|/2`, the bound that makes the integrand continuous at the origin. -/
theorem abs_cinIntegrand_le (v : ℝ) : |cinIntegrand v| ≤ |v| / 2 := by
  rcases le_or_gt 0 v with hv | hv
  · rw [abs_of_nonneg (cinIntegrand_nonneg hv), abs_of_nonneg hv]
    exact cinIntegrand_le_half hv
  · have h := cinIntegrand_le_half (v := -v) (by linarith)
    have h0 := cinIntegrand_nonneg (v := -v) (by linarith)
    have hneg := cinIntegrand_neg v
    rw [abs_of_nonpos (by linarith), abs_of_neg hv]
    linarith

/-- **`Cin'` is continuous**, the origin included: `(1 - cos v)/v` is `0` at `v = 0` by Lean's
division convention and tends to `0` there, the two agreeing because the quotient is squeezed by
`|v|/2`. -/
theorem continuous_cinIntegrand : Continuous cinIntegrand := by
  rw [continuous_iff_continuousAt]
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · rw [ContinuousAt, show cinIntegrand 0 = 0 by simp [cinIntegrand]]
    refine squeeze_zero_norm (a := fun w : ℝ => |w| / 2) (fun w => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact abs_cinIntegrand_le w
    · have hc : Continuous fun w : ℝ => |w| / 2 := by fun_prop
      simpa using (hc.tendsto 0)
  · unfold cinIntegrand
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hv

/-- **`Cin' = cinIntegrand` everywhere**, by the fundamental theorem of calculus. -/
theorem hasDerivAt_cin (z : ℝ) : HasDerivAt cin (cinIntegrand z) z :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_cinIntegrand.intervalIntegrable 0 z)
    (continuous_cinIntegrand.stronglyMeasurableAtFilter _ _)
    continuous_cinIntegrand.continuousAt

theorem continuous_cin : Continuous cin :=
  continuous_iff_continuousAt.mpr fun z => ((hasDerivAt_cin z).differentiableAt).continuousAt

/-! ## `Cin` itself -/

theorem cin_zero : cin 0 = 0 := by simp [cin]

theorem cin_neg (z : ℝ) : cin (-z) = cin z := by
  have h : (∫ x in (0 : ℝ)..z, cinIntegrand (-x)) = ∫ x in (-z)..(-0:ℝ), cinIntegrand x :=
    intervalIntegral.integral_comp_neg cinIntegrand
  have hl : (∫ x in (0 : ℝ)..z, cinIntegrand (-x)) = -cin z := by
    simp only [cinIntegrand_neg, intervalIntegral.integral_neg, cin_apply]
  have hr : (∫ x in (-z)..(-0:ℝ), cinIntegrand x) = -cin (-z) := by
    rw [neg_zero, intervalIntegral.integral_symm, cin_apply]
  rw [hl, hr] at h
  exact (neg_injective h).symm

theorem cin_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ cin z := by
  rw [cin_apply]
  refine intervalIntegral.integral_nonneg hz fun v hv => cinIntegrand_nonneg hv.1

theorem cin_le_sq_of_nonneg {z : ℝ} (hz : 0 ≤ z) : cin z ≤ z ^ 2 / 4 := by
  have hmono : (∫ v in (0 : ℝ)..z, cinIntegrand v) ≤ ∫ v in (0 : ℝ)..z, v / 2 :=
    intervalIntegral.integral_mono_on hz (intervalIntegrable_cinIntegrand hz)
        ((by fun_prop : Continuous fun v : ℝ => v / 2).intervalIntegrable 0 z)
      fun v hv => cinIntegrand_le_half hv.1
  have hval : (∫ v in (0 : ℝ)..z, v / 2) = z ^ 2 / 4 := by
    rw [intervalIntegral.integral_div, integral_id]; ring
  rw [cin_apply, ← hval]
  exact hmono

theorem cin_le_sq (z : ℝ) : cin z ≤ z ^ 2 / 4 := by
  rcases le_or_gt 0 z with hz | hz
  · exact cin_le_sq_of_nonneg hz
  · rw [← cin_neg]
    simpa using cin_le_sq_of_nonneg (by linarith : (0 : ℝ) ≤ -z)

theorem monotoneOn_cin : MonotoneOn cin (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  have hsplit : cin a + (∫ v in a..b, cinIntegrand v) = cin b := by
    rw [cin_apply, cin_apply]
    exact intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_cinIntegrand hb').mono_set (by
        rw [Set.uIcc_of_le ha', Set.uIcc_of_le hb']; exact Icc_subset_Icc le_rfl hab))
      ((intervalIntegrable_cinIntegrand hb').mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb']; exact Icc_subset_Icc ha' le_rfl))
  have hnn : 0 ≤ ∫ v in a..b, cinIntegrand v :=
    intervalIntegral.integral_nonneg hab fun v hv => cinIntegrand_nonneg (le_trans ha' hv.1)
  linarith

/-- **`lem:cin-rays`(1), the elementary clauses**: `Cin` is even, nondecreasing on `[0,infty)`,
and bounded by `z^2/4`.

Evenness is a lemma about the definition rather than a stipulation: the integrand is odd, so the
interval integral from `0` is already even, and the blueprint's "extended evenly to R" describes
what the formula does. -/
theorem cin_elementary :
    (∀ z : ℝ, cin (-z) = cin z) ∧ MonotoneOn cin (Ici 0) ∧ ∀ z : ℝ, cin z ≤ z ^ 2 / 4 :=
  ⟨cin_neg, monotoneOn_cin, cin_le_sq⟩

/-! ## The expansion at the origin -/

theorem cin_sub_sq_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    |cin z - z ^ 2 / 4| ≤ 5 / 96 * z ^ 4 := by
  have hval : (∫ v in (0 : ℝ)..z, v / 2) = z ^ 2 / 4 := by
    rw [intervalIntegral.integral_div, integral_id]; ring
  have hsub : cin z - z ^ 2 / 4 = ∫ v in (0 : ℝ)..z, (cinIntegrand v - v / 2) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_cinIntegrand hz)
      ((by fun_prop : Continuous fun v : ℝ => v / 2).intervalIntegrable 0 z), cin_apply, hval]
  have hbound : ∀ v ∈ Set.uIoc (0 : ℝ) z, ‖cinIntegrand v - v / 2‖ ≤ 5 / 96 * z ^ 3 := by
    intro v hv
    rw [Set.uIoc_of_le hz] at hv
    obtain ⟨hv0, hvz⟩ := hv
    have hv1 : |v| ≤ 1 := by rw [abs_of_pos hv0]; linarith
    have hcb := Real.cos_bound hv1
    rw [abs_of_pos hv0] at hcb
    have hkey : cinIntegrand v - v / 2 = -((Real.cos v - (1 - v ^ 2 / 2)) / v) := by
      rw [cinIntegrand]; field_simp; ring
    rw [Real.norm_eq_abs, hkey, abs_neg, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
    calc |Real.cos v - (1 - v ^ 2 / 2)| ≤ v ^ 4 * (5 / 96) := hcb
      _ ≤ 5 / 96 * z ^ 3 * v := by nlinarith [pow_le_pow_left₀ hv0.le hvz 3, sq_nonneg v, hv0.le]
  have hres := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [← hsub, Real.norm_eq_abs] at hres
  calc |cin z - z ^ 2 / 4| ≤ 5 / 96 * z ^ 3 * |z - 0| := hres
    _ = 5 / 96 * z ^ 4 := by rw [sub_zero, abs_of_nonneg hz]; ring

theorem cin_expansion_zero_bound {z : ℝ} (hz1 : |z| ≤ 1) :
    |cin z - z ^ 2 / 4| ≤ 5 / 96 * z ^ 4 := by
  rcases le_or_gt 0 z with hz | hz
  · exact cin_sub_sq_bound hz (by rwa [abs_of_nonneg hz] at hz1)
  · have h := cin_sub_sq_bound (by linarith : (0 : ℝ) ≤ -z)
      (by rw [abs_of_neg hz] at hz1; exact hz1)
    rw [cin_neg] at h
    calc |cin z - z ^ 2 / 4| = |cin z - (-z) ^ 2 / 4| := by ring_nf
      _ ≤ 5 / 96 * (-z) ^ 4 := h
      _ = 5 / 96 * z ^ 4 := by ring

theorem cin_expansion_zero :
    (fun z : ℝ => cin z - z ^ 2 / 4) =O[𝓝 0] fun z : ℝ => z ^ 4 := by
  refine Asymptotics.isBigO_iff.mpr ⟨5 / 96, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with z hz
  have hz1 : |z| ≤ 1 := by simpa [Real.dist_eq] using hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 4)]
  exact cin_expansion_zero_bound hz1

/-! ## The expansion at infinity -/

theorem rpow_neg_two {v : ℝ} (hv : 0 < v) : v ^ (-2 : ℝ) = (v ^ 2)⁻¹ := by
  rw [← Real.rpow_natCast v 2, ← Real.rpow_neg hv.le]
  norm_num

theorem integrableOn_sin_div_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => Real.sin v / v ^ 2) (Ioi c) := by
  have hg : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  refine Integrable.mono' hg
    ((Real.measurable_sin.div (measurable_id.pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := lt_trans hc hv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2), rpow_neg_two hv0,
    div_le_iff₀ (by positivity : (0 : ℝ) < v ^ 2)]
  have := Real.abs_sin_le_one v
  rw [inv_mul_cancel₀ (by positivity : (v:ℝ) ^ 2 ≠ 0)]
  exact this

theorem norm_integral_Ioi_sin_div_sq {c : ℝ} (hc : 0 < c) :
    ‖∫ v in Ioi c, Real.sin v / v ^ 2‖ ≤ c⁻¹ := by
  have hg : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  have hval : (∫ v in Ioi c, v ^ (-2 : ℝ)) = c⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hc]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, show (-1 : ℝ) = -(1 : ℝ) by norm_num,
      Real.rpow_neg hc.le, Real.rpow_one]
    ring
  calc ‖∫ v in Ioi c, Real.sin v / v ^ 2‖
      ≤ ∫ v in Ioi c, ‖Real.sin v / v ^ 2‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi c, v ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (integrableOn_sin_div_sq hc).norm hg measurableSet_Ioi ?_
        intro v hv
        have hv0 : 0 < v := lt_trans hc hv
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2),
          rpow_neg_two hv0, div_le_iff₀ (by positivity : (0 : ℝ) < v ^ 2),
          inv_mul_cancel₀ (by positivity : (v:ℝ) ^ 2 ≠ 0)]
        exact Real.abs_sin_le_one v
    _ = c⁻¹ := hval

theorem hasDerivAt_sin_div {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.sin u / u) (Real.cos v / v - Real.sin v / v ^ 2) v := by
  have h : HasDerivAt (fun u : ℝ => Real.sin u / u)
      ((Real.cos v * v - Real.sin v * 1) / v ^ 2) v :=
    (Real.hasDerivAt_sin v).div (hasDerivAt_id' (x := v)) hv
  have heq : (Real.cos v * v - Real.sin v * 1) / v ^ 2
      = Real.cos v / v - Real.sin v / v ^ 2 := by field_simp
  rwa [heq] at h

theorem integral_cos_div {z : ℝ} (hz : 1 ≤ z) :
    (∫ v in (1 : ℝ)..z, Real.cos v / v)
      = Real.sin z / z - Real.sin 1 + ∫ v in (1 : ℝ)..z, Real.sin v / v ^ 2 := by
  have hne : ∀ x ∈ uIcc (1 : ℝ) z, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hz] at hx
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
  have hi1 : IntervalIntegrable (fun x : ℝ => Real.cos x / x) volume 1 z :=
    (ContinuousOn.div Real.continuous_cos.continuousOn continuousOn_id hne).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x : ℝ => Real.sin x / x ^ 2) volume 1 z :=
    (ContinuousOn.div Real.continuous_sin.continuousOn
      (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hne x hx)).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => Real.sin u / u)
    (f' := fun x : ℝ => Real.cos x / x - Real.sin x / x ^ 2)
    (fun x hx => hasDerivAt_sin_div (hne x hx)) (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at hftc
  linarith [hftc]

theorem cin_eq_log_sub {z : ℝ} (hz : 1 ≤ z) :
    cin z = cin 1 + Real.log z - ∫ v in (1 : ℝ)..z, Real.cos v / v := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  have hne : ∀ x ∈ uIcc (1 : ℝ) z, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hz] at hx
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
  have hi0 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 1 z :=
    (continuousOn_id.inv₀ hne).intervalIntegrable
  have hi1 : IntervalIntegrable (fun x : ℝ => Real.cos x / x) volume 1 z :=
    (ContinuousOn.div Real.continuous_cos.continuousOn continuousOn_id hne).intervalIntegrable
  have hcongr : (∫ v in (1 : ℝ)..z, cinIntegrand v) = ∫ v in (1 : ℝ)..z, (v⁻¹ - Real.cos v / v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have : v ≠ 0 := hne v hv
    rw [cinIntegrand]
    field_simp
  have hsplit : (∫ v in (1 : ℝ)..z, cinIntegrand v) = Real.log z - ∫ v in (1 : ℝ)..z, Real.cos v / v := by
    rw [hcongr, intervalIntegral.integral_sub hi0 hi1, integral_inv_of_pos zero_lt_one hz0,
      div_one]
  have hadd : cin 1 + (∫ v in (1 : ℝ)..z, cinIntegrand v) = cin z := by
    rw [cin_apply, cin_apply]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cinIntegrand zero_le_one)
      ((intervalIntegrable_cinIntegrand hz0.le).mono_set (by
        rw [Set.uIcc_of_le hz, Set.uIcc_of_le hz0.le]
        exact Icc_subset_Icc zero_le_one le_rfl))
  rw [← hadd, hsplit]
  ring

/-- The constant `C` of `lem:cin-rays`(1)'s expansion at infinity. -/
noncomputable def cinConst : ℝ := cin 1 + Real.sin 1 - ∫ v in Ioi (1 : ℝ), Real.sin v / v ^ 2

theorem cin_sub_log_eq {z : ℝ} (hz : 1 ≤ z) :
    cin z - Real.log z - cinConst
      = -(Real.sin z / z) + ∫ v in Ioi z, Real.sin v / v ^ 2 := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  have hsplit : (∫ v in Ioi (1 : ℝ), Real.sin v / v ^ 2)
      = (∫ v in (1 : ℝ)..z, Real.sin v / v ^ 2) + ∫ v in Ioi z, Real.sin v / v ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hz,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_sin_div_sq zero_lt_one).mono_set Ioc_subset_Ioi_self)
        (integrableOn_sin_div_sq hz0),
      intervalIntegral.integral_of_le hz]
  rw [cin_eq_log_sub hz, integral_cos_div hz, cinConst, hsplit]
  ring

theorem cin_expansion_top_bound {z : ℝ} (hz : 1 ≤ z) :
    |cin z - Real.log z - cinConst| ≤ 2 * z⁻¹ := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  rw [cin_sub_log_eq hz]
  have h1 : |Real.sin z / z| ≤ z⁻¹ := by
    rw [abs_div, abs_of_pos hz0, div_le_iff₀ hz0, inv_mul_cancel₀ hz0.ne']
    exact Real.abs_sin_le_one z
  have h2 : |∫ v in Ioi z, Real.sin v / v ^ 2| ≤ z⁻¹ := by
    simpa [Real.norm_eq_abs] using norm_integral_Ioi_sin_div_sq hz0
  calc |-(Real.sin z / z) + ∫ v in Ioi z, Real.sin v / v ^ 2|
      ≤ |-(Real.sin z / z)| + |∫ v in Ioi z, Real.sin v / v ^ 2| := abs_add_le _ _
    _ ≤ z⁻¹ + z⁻¹ := by rw [abs_neg]; linarith
    _ = 2 * z⁻¹ := by ring

theorem cin_expansion_top :
    ∃ C : ℝ, (fun z : ℝ => cin z - Real.log z - C) =O[atTop] fun z : ℝ => z⁻¹ := by
  refine ⟨cinConst, Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < z⁻¹)]
  exact cin_expansion_top_bound hz

/-! ## The dilated integrand, and the ray -/

theorem cin_nonneg' (z : ℝ) : 0 ≤ cin z := by
  rcases le_or_gt 0 z with hz | hz
  · exact cin_nonneg hz
  · rw [← cin_neg]; exact cin_nonneg (by linarith)

/-- `(1 - cos(ωx))/x = ω · cinIntegrand(ωx)`, at every real `ω` and `x`. -/
theorem dilate_cinIntegrand (ω x : ℝ) :
    (1 - Real.cos (ω * x)) / x = ω * cinIntegrand (ω * x) := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simp [cinIntegrand]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [cinIntegrand]
  · rw [cinIntegrand]; field_simp

/-- **The substitution**: `∫₀^z (1 - cos(ωx))\,dx/x = Cin(ωz)`. -/
theorem intervalIntegral_dilate_cinIntegrand (ω z : ℝ) :
    (∫ x in (0 : ℝ)..z, (1 - Real.cos (ω * x)) / x) = cin (ω * z) := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simp [cin, cinIntegrand]
  · simp only [dilate_cinIntegrand]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hω,
      mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hω, one_mul, cin]

theorem dilate_cinIntegrand_nonneg (ω : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (1 - Real.cos (ω * x)) / x :=
  div_nonneg (by linarith [Real.cos_le_one (ω * x)]) hx

theorem dilate_cinIntegrand_le (ω : ℝ) {x z : ℝ} (hx : 0 ≤ x) (hxz : x ≤ z) :
    (1 - Real.cos (ω * x)) / x ≤ ω ^ 2 * z / 2 := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp; positivity
  · rw [div_le_iff₀ hx']
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ω * x), sq_nonneg (ω * x), hx'.le, sq_nonneg ω]

theorem intervalIntegrable_dilate_cinIntegrand (ω : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    IntervalIntegrable (fun x : ℝ => (1 - Real.cos (ω * x)) / x) volume 0 z := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
  have hfin : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => ω ^ 2 * z / 2) (integrableOn_const (hs := hfin))
    (((measurable_const.sub (Real.measurable_cos.comp (measurable_const.mul measurable_id))).div
      measurable_id).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dilate_cinIntegrand_nonneg ω hx.1.le)]
  exact dilate_cinIntegrand_le ω hx.1.le hx.2

end SpatialLine
