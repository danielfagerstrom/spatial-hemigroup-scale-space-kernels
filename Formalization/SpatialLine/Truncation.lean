/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Additivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The two elementary inequalities of `thm:increments-levy`

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`.

The null-array proof of the increments theorem rests on two pointwise inequalities and nothing
else that is not measure theory. They are proved here, ahead of the theorem, because they are
the part of that proof that is *ours* — the causal argument compactifies the half-line instead —
and because both differ from the constants the blueprint writes.

* `sub_one_sub_exp_neg_le` — `0 ≤ u - (1 - e^{-u}) ≤ u²` for `u ≥ 0`. The blueprint writes
  `u²/2`, which is sharp; the sharper constant needs a derivative argument, `u²` follows from
  `e^v ≥ 1 + v` alone through `e^{-u} ≤ (1+u)⁻¹ ≤ 1 - u + u²`, and the factor multiplies a
  quantity that is going to zero. Paper I records the same substitution at the same step.

* `one_sub_sinc_ge` — `1 - sin u / u ≥ c (1 ∧ u²)` with `c = 2/(3π²)`. **This is a genuine
  correction of the route, not of the statement.** The blueprint justifies the constant `2/15`
  from `sin u ≤ u - u³/6 + u⁵/120`, an alternating-series bound Mathlib does not carry; and the
  Taylor machinery to get it is out of proportion to what the step needs, since the constant is
  multiplied by a quantity that only has to be finite. What Mathlib does carry is
  `Real.cos_le_one_sub_mul_cos_sq`: `1 - cos x ≥ (2/π²)x²` for `|x| ≤ π`. Integrating it over
  `[0,u]` — the identity `u - sin u = ∫₀^u (1 - cos v) dv` — gives `1 - sinc u ≥ (2/(3π²))u²`
  for `0 < u ≤ π`, and beyond `π` the crude bound `sin u / u ≤ 1/u < 1/π` finishes, because
  `2/(3π²) < 2/27 < 2/3 < 1 - 1/π`. The blueprint's proof of record is amended to this route.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The exponential inequality of the null-array step -/

/-- `0 ≤ u - (1 - e^{-u})` for `u ≥ 0`. -/
theorem one_sub_exp_neg_le (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  have h := Real.add_one_le_exp (-u)
  linarith

/-- `u - (1 - e^{-u}) ≤ u²` for `u ≥ 0`. The blueprint's `u²/2` is sharp and needs a derivative
argument; this constant follows from `e^v ≥ 1 + v` alone and is all the step uses. -/
theorem sub_one_sub_exp_neg_le (u : ℝ) (hu : 0 ≤ u) :
    u - (1 - Real.exp (-u)) ≤ u ^ 2 := by
  have h1 : (0:ℝ) < 1 + u := by linarith
  have h2 : Real.exp u ≥ 1 + u := by
    have := Real.add_one_le_exp u
    linarith
  have h3 : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ h1 h2
  have h4 : (1 + u)⁻¹ ≤ 1 - u + u ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith [pow_nonneg hu 3]
  linarith

/-! ## The truncation inequality -/

/-- `u - sin u = ∫₀^u (1 - cos v) dv`. -/
lemma sub_sin_eq_intervalIntegral (u : ℝ) :
    u - Real.sin u = ∫ v in (0:ℝ)..u, (1 - Real.cos v) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_cos)]
  simp

/-- The bound below `π`: `1 - sin u / u ≥ (2/(3π²)) u²` for `0 < u ≤ π`. -/
lemma one_sub_sinc_ge_of_le_pi {u : ℝ} (hu : 0 < u) (hπ : u ≤ Real.pi) :
    2 / (3 * Real.pi ^ 2) * u ^ 2 ≤ 1 - Real.sinc u := by
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hlow : (2 / Real.pi ^ 2) * (u ^ 3 / 3) ≤ u - Real.sin u := by
    rw [sub_sin_eq_intervalIntegral u]
    have hmono : ∫ v in (0:ℝ)..u, (2 / Real.pi ^ 2) * v ^ 2
        ≤ ∫ v in (0:ℝ)..u, (1 - Real.cos v) := by
      refine intervalIntegral.integral_mono_on hu.le
        ((intervalIntegral.intervalIntegrable_pow 2).const_mul _)
        (IntervalIntegrable.sub intervalIntegrable_const
          intervalIntegral.intervalIntegrable_cos) fun v hv => ?_
      have habs : |v| ≤ Real.pi := by
        rw [abs_of_nonneg hv.1]
        exact le_trans hv.2 hπ
      have := Real.cos_le_one_sub_mul_cos_sq habs
      linarith
    refine le_trans (le_of_eq ?_) hmono
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  have hsinc : Real.sinc u = Real.sin u / u := Real.sinc_of_ne_zero hu.ne'
  have hpine : Real.pi ≠ 0 := hπ0.ne'
  have hstep : 1 - Real.sin u / u = (u - Real.sin u) / u := by field_simp
  rw [hsinc, hstep, le_div_iff₀ hu]
  have hcalc : 2 / (3 * Real.pi ^ 2) * u ^ 2 * u = 2 / Real.pi ^ 2 * (u ^ 3 / 3) := by
    field_simp
  rw [hcalc]
  exact hlow

/-- **The truncation inequality**, pointwise: `1 - sin u / u ≥ (2/(3π²)) (1 ∧ u²)`.

This is the inequality that makes the weighted partition measures `(1 ∧ x²) Π̃ₙ` have uniformly
bounded mass in `thm:increments-levy`; the tail half of the same step is Mathlib's
`measureReal_abs_gt_le_integral_charFun`. -/
theorem one_sub_sinc_ge (u : ℝ) :
    2 / (3 * Real.pi ^ 2) * min 1 (u ^ 2) ≤ 1 - Real.sinc u := by
  have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hc : (0:ℝ) < 2 / (3 * Real.pi ^ 2) := by positivity
  -- it suffices to treat `u ≥ 0`
  have key : ∀ v : ℝ, 0 ≤ v → 2 / (3 * Real.pi ^ 2) * min 1 (v ^ 2) ≤ 1 - Real.sinc v := by
    intro v hv
    rcases eq_or_lt_of_le hv with h | hv0
    · rw [← h]
      simp
    rcases le_or_gt v Real.pi with hle | hgt
    · refine le_trans ?_ (one_sub_sinc_ge_of_le_pi hv0 hle)
      have : min 1 (v ^ 2) ≤ v ^ 2 := min_le_right _ _
      nlinarith
    · -- beyond `π` the crude bound suffices
      have hA : 2 / (3 * Real.pi ^ 2) * min 1 (v ^ 2) ≤ 2 / (3 * Real.pi ^ 2) := by
        nlinarith [min_le_left (1:ℝ) (v ^ 2), hc.le]
      have h27 : (3:ℝ) < 3 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
      have hB : 2 / (3 * Real.pi ^ 2) < 2 / 3 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) h27
      have hC : (2:ℝ) / 3 ≤ 1 - Real.sinc v := by
        have h1 : Real.sinc v ≤ v⁻¹ := by
          have h := Real.sinc_le_inv_abs hv0.ne'
          rwa [abs_of_pos hv0] at h
        have h3 : v⁻¹ ≤ (3:ℝ)⁻¹ := by
          refine inv_anti₀ (by norm_num) ?_
          linarith [Real.pi_gt_three]
        norm_num at h3 ⊢
        linarith
      linarith
  rcases le_or_gt 0 u with h | h
  · exact key u h
  · have hneg : (0:ℝ) ≤ -u := by linarith
    simpa using key (-u) hneg

end SpatialLine
