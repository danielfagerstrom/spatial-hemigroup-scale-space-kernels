/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.NullArray
import Mathlib.MeasureTheory.Measure.IntegralCharFun

/-!
# `thm:increments-levy`, part two: the truncation inequality

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, the second step of the
proof ("two bounds, uniform in `n`"), `eq:truncation`.

The masses of the partition measures `Π_n` diverge — `Π_n(ℝ) = n` — so a limit can only be taken
after weighting, and the weight `1 ∧ x²` is what makes the weighted masses bounded. Both the
bound on those masses and the tightness that keeps mass from escaping to infinity come from a
single inequality, and this file proves it.

## The inequality, and where the Fubini step comes from

For a symmetric probability measure `ρ` with positive transform, and `r > 0`,

  `∫ (1 - sinc(r x)) dρ(x) = (2r)⁻¹ ∫_{-r}^{r} (1 - ρ̂(ω)) dω ≤ (2r)⁻¹ ∫_{-r}^{r} g_ρ(ω) dω`,

where `g_ρ = -log ρ̂`. The first equality is the blueprint's Tonelli step, and it is **not**
proved here: Mathlib carries it as `MeasureTheory.integral_charFun_Icc`, which states
`∫_{-r}^{r} charFun ρ = 2r ∫ sinc(r x) dρ` for a finite measure and does the swap internally.
The inequality is `1 - u ≤ -log u` for `u > 0`, that is `Real.log_le_sub_one_of_pos`.

Summing over the partition, and using additivity for `Σ_i g_i = g_{s,t}`, gives `eq:truncation`
for `Π_n` with a right-hand side independent of `n`:

  `∫ (1 - sinc(r x)) dΠ_n(x) ≤ meanExponent r`, where
  `meanExponent r = (2r)⁻¹ ∫_{-r}^{r} g_{s,t}(ω) dω`.

Combined with `one_sub_sinc_ge` (`SpatialLine/Truncation.lean`) this bounds `∫ (1 ∧ x²) dΠ_n`
at `r = 1` and `Π_n{|x| > R}` at `r = 1/R`; and `meanExponent r → 0` as `r ↓ 0` because
`g_{s,t}` is continuous at the origin and vanishes there, which is where the continuity of the
transform does quantitative work.
-/

namespace SpatialLine

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology

/-! ## The truncation inequality for one kernel -/

/-- `sinc (r x)` is integrable against a finite measure: it is continuous and bounded by `1`. -/
lemma integrable_sinc_mul (ρ : Measure ℝ) [IsFiniteMeasure ρ] (r : ℝ) :
    Integrable (fun x : ℝ => Real.sinc (r * x)) ρ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_sinc_le_one (r * x)

/-- The transform of a symmetric measure, integrated over a symmetric interval, is what
`integral_charFun_Icc` computes: `∫_{-r}^{r} ρ̂ = 2r ∫ sinc(r x) dρ`, read on the real line. -/
lemma intervalIntegral_fourierCos_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hsym : IsSymmetric ρ)
    {r : ℝ} (hr : 0 < r) :
    ∫ ω in (-r)..r, fourierCos ρ ω = 2 * r * ∫ x, Real.sinc (r * x) ∂ρ := by
  have h := integral_charFun_Icc (μ := ρ) hr
  rw [show (fun ω : ℝ => charFun ρ ω) = fun ω : ℝ => ((fourierCos ρ ω : ℝ) : ℂ) from
    funext fun ω => charFun_eq_fourierCos_of_symmetric hsym ω] at h
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- **The truncation inequality**, for a single symmetric kernel: the sinc defect is bounded by
the mean of the exponent over `[-r,r]`.

This is `eq:truncation` before the sum over the partition. The Fubini step is Mathlib's
`integral_charFun_Icc`; what is added here is the passage from `1 - ρ̂` to `g_ρ`, which is
`log u ≤ u - 1`. -/
theorem integral_one_sub_sinc_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hsym : IsSymmetric ρ)
    (hpos : ∀ ω, 0 < fourierCos ρ ω) {r : ℝ} (hr : 0 < r) :
    ∫ x, (1 - Real.sinc (r * x)) ∂ρ ≤ (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent ρ ω := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hsinc := integrable_sinc_mul ρ r
  have hval : ∫ x, (1 - Real.sinc (r * x)) ∂ρ
      = (2 * r)⁻¹ * ∫ ω in (-r)..r, (1 - fourierCos ρ ω) := by
    rw [integral_sub (integrable_const (1 : ℝ)) hsinc, integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one,
      intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
        ((continuous_fourierCos ρ).intervalIntegrable _ _),
      intervalIntegral_fourierCos_eq ρ hsym hr]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    field_simp
    ring
  rw [hval]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_on (by linarith)
    (((continuous_const.sub (continuous_fourierCos ρ)).intervalIntegrable _ _))
    (((continuous_fourierCos ρ).log fun ω => (hpos ω).ne').neg.intervalIntegrable _ _)
    fun ω _ => ?_
  have := Real.log_le_sub_one_of_pos (hpos ω)
  rw [exponent_apply]
  linarith

/-! ## The truncation inequality along the partition -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

/-- `meanExponent`: the mean of `g_{s,t}` over `[-r,r]`, the blueprint's `ḡ(r)`. -/
noncomputable def meanExponent (μ : ℝ → ℝ → Measure ℝ) (s t r : ℝ) : ℝ :=
  (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent (μ s t) ω

lemma continuous_exponent_pair (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Continuous (exponent (μ s t)) := by
  haveI := hker.isProbability s t hs hst
  exact ((continuous_fourierCos (μ s t)).log
    fun ω => (kernel_transform_pos hker hs hst ω).ne').neg

lemma meanExponent_nonneg (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) {r : ℝ}
    (hr : 0 < r) : 0 ≤ meanExponent μ s t r := by
  refine mul_nonneg (by positivity) ?_
  refine intervalIntegral.integral_nonneg (by linarith) fun ω _ => exponent_nonneg hker hs hst ω

/-- **`eq:truncation`.** The sinc defect of `Π_n` is bounded by `ḡ(r)`, uniformly in `n`. -/
theorem integral_one_sub_sinc_partitionMeasure_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x, (1 - Real.sinc (r * x)) ∂(partitionMeasure μ s t n)
      ≤ meanExponent μ s t r := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [partitionMeasure, Finset.range_zero, Finset.sum_empty, integral_zero_measure]
    exact meanExponent_nonneg hker hs hst hr
  have hn0 : n ≠ 0 := hn.ne'
  have hint : ∀ i ∈ range n, Integrable (fun x : ℝ => 1 - Real.sinc (r * x))
      (μ (part s t n i) (part s t n (i + 1))) := by
    intro i _
    haveI := isProbabilityMeasure_part hker hs hst n i
    exact (integrable_const (1 : ℝ)).sub (integrable_sinc_mul _ r)
  rw [integral_partitionMeasure_eq_sum μ s t n hint]
  -- each increment obeys the one-kernel inequality
  have hstep : ∀ i ∈ range n,
      ∫ x, (1 - Real.sinc (r * x)) ∂(μ (part s t n i) (part s t n (i + 1)))
        ≤ (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent (μ (part s t n i) (part s t n (i + 1))) ω := by
    intro i _
    haveI := isProbabilityMeasure_part hker hs hst n i
    exact integral_one_sub_sinc_le _
      (kernel_symmetric hker (part_nonneg hs hst n i) (part_le_succ hst n i))
      (fun ω => kernel_transform_pos hker (part_nonneg hs hst n i) (part_le_succ hst n i) ω) hr
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, meanExponent]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [← intervalIntegral.integral_finset_sum]
  · exact intervalIntegral.integral_congr fun ω _ => sum_exponent_part hker hs hst hn0 ω
  · intro i _
    exact ((continuous_exponent_pair hker (part_nonneg hs hst n i)
      (part_le_succ hst n i)).intervalIntegrable _ _)

/-! ## The mean exponent vanishes at the origin

This is where the continuity of `g_{s,t}` at `ω = 0`, with `g_{s,t}(0) = 0`, does quantitative
work: it is what forbids escape of mass in the limit.
-/

lemma exponent_pair_atZero (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) :
    exponent (μ s t) 0 = 0 := by
  rw [exponent_eq_sub hker hs hst 0, exponent_atZero hker (hs.trans hst), exponent_atZero hker hs,
    sub_self]

/-- For every `ε > 0` the mean of `g_{s,t}` over a short enough symmetric interval is at most
`ε`. -/
theorem exists_meanExponent_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → meanExponent μ s t r ≤ ε := by
  have hcont := continuous_exponent_pair hker hs hst
  have h0 := exponent_pair_atZero hker hs hst
  obtain ⟨δ, hδ, hδb⟩ :=
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := (0 : ℝ))) ε hε
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hbnd : ∀ ω ∈ Icc (-r) r, exponent (μ s t) ω ≤ ε := by
    intro ω hω
    have hd : dist ω 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      exact lt_of_le_of_lt (abs_le.mpr ⟨hω.1, hω.2⟩) hrδ
    have hlt := hδb hd
    rw [Real.dist_eq, h0, sub_zero] at hlt
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hlt)
  have hle : ∫ ω in (-r)..r, exponent (μ s t) ω ≤ ∫ _ω in (-r)..r, ε :=
    intervalIntegral.integral_mono_on (by linarith)
      (hcont.intervalIntegrable _ _) intervalIntegral.intervalIntegrable_const hbnd
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  have hle' : ∫ ω in (-r)..r, exponent (μ s t) ω ≤ ε * (2 * r) := by
    calc ∫ ω in (-r)..r, exponent (μ s t) ω ≤ (r - -r) * ε := hle
      _ = ε * (2 * r) := by ring
  rw [meanExponent]
  calc (2 * r)⁻¹ * ∫ ω in (-r)..r, exponent (μ s t) ω
      ≤ (2 * r)⁻¹ * (ε * (2 * r)) := mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = ε := by field_simp

/-- The mean exponent tends to `0` along `r = 1/(n+1)`. -/
theorem tendsto_meanExponent (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => meanExponent μ s t (1 / (n + 1))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδb⟩ := exists_meanExponent_le hker hs hst (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hrδ : 1 / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hn1]
    have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    have : 1 / δ < (n : ℝ) + 1 := by linarith [hN]
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hb := hδb _ hr hrδ
  have hnn := meanExponent_nonneg hker hs hst hr
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end SpatialLine
