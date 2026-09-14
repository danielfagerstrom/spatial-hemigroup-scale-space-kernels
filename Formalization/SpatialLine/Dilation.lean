/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transform
import Mathlib.MeasureTheory.Measure.IntegralCharFun

/-!
# `lem:dilation-invariance` and `lem:dilation-atom`: the two elementary dilation facts

Blueprint: `blueprint/src/parts/06-covariance.tex`. Two nodes of Chapter 6 that depend on
nothing else in the development — neither mentions the axioms, a kernel family or an exponent —
and they are therefore the leaves the proving campaign of Chapters 5 and 6 starts from.

* `dilation_invariance` is the iteration the draft performs three times
  (`lem:action-rigidity`(4), the injectivity of the orbit coordinate in
  `prop:canonical-gauge`, and the uniqueness clause of `thm:main-characterization`), stated
  once. Three lines of real analysis: `h ω = h (c^n ω)` for a contracting `c`, and continuity
  at the origin.
* `dilation_atom` is the Fourier form of "a law whose dilates converge weakly to a point mass is
  a point mass", proved so as to need no weak convergence at all.

## What proving `dilation_atom` found

The blueprint proof runs through the Gaussian density: Fubini turns `∫ μ̂(λₙω) ρ(ω) dω` into
`∫ e^{-λₙ²x²/2} μ(dx)`, and two applications of dominated convergence give `μ({0}) = 1`. The
Lean proof below takes a different route to the same conclusion, because Mathlib supplies the
harder half ready-made: `measureReal_abs_gt_le_integral_charFun` is exactly the truncation
inequality

  `μ.real {x | r < |x|} ≤ 2⁻¹ r ‖∫ t in (-2/r)..(2/r), 1 - charFun μ t‖`,

so applying it to the dilate of `μ` by `λₙ` at the *fixed* radius `1` leaves a single dominated
convergence over a fixed interval, with the constant bound `2` of
`norm_one_sub_charFun_le_two`. No Gaussian, no Fubini. The mathematics of record is unchanged —
the blueprint proof is correct and is the one a reader should read — but the note is worth
keeping, because the same Mathlib inequality is the tightness half of the truncation step of
`thm:increments-levy`, and it was found here.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `lem:dilation-invariance` -/

/-- **`lem:dilation-invariance`.** A function fixed by one dilation and continuous at the
origin, where it vanishes, vanishes identically.

Continuity is asked **at `0` only**, which is all the iteration needs and all three uses supply.

Class (c) — an elementary fact with no causal counterpart, factored out because the draft
performs the iteration three times. -/
theorem dilation_invariance (h : ℝ → ℝ) (hcont : ContinuousAt h 0) (hzero : h 0 = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≠ 1) (hinv : ∀ ω : ℝ, h ω = h (κ * ω)) :
    ∀ ω : ℝ, h ω = 0 := by
  -- The contracting case; the expanding case is reduced to it by inverting `κ`.
  have key : ∀ c : ℝ, 0 < c → c < 1 → (∀ ω : ℝ, h ω = h (c * ω)) → ∀ ω, h ω = 0 := by
    intro c hc hc1 hcinv ω
    have hiter : ∀ n : ℕ, h (c ^ n * ω) = h ω := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have := hcinv (c ^ n * ω)
          rw [← ih, this]
          ring_nf
    have hlim : Tendsto (fun n : ℕ => c ^ n * ω) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1
      simpa using this.mul_const ω
    have h1 : Tendsto (fun n : ℕ => h (c ^ n * ω)) atTop (𝓝 (h 0)) := hcont.tendsto.comp hlim
    have h2 : Tendsto (fun n : ℕ => h (c ^ n * ω)) atTop (𝓝 (h ω)) := by
      simp only [hiter]
      exact tendsto_const_nhds
    have huniq := tendsto_nhds_unique h1 h2
    rw [← huniq, hzero]
  rcases lt_or_gt_of_ne hκ1 with hlt | hgt
  · exact key κ hκ hlt hinv
  · refine key κ⁻¹ (by positivity) (by rw [inv_lt_one_iff₀]; right; exact hgt) ?_
    intro ω
    have hstep := hinv (κ⁻¹ * ω)
    rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at hstep
    exact hstep.symm

/-! ## `lem:dilation-atom` -/

/-- **`lem:dilation-atom`.** A law whose dilates' transforms tend to `1` is a point mass at the
origin.

Stated for `charFun`, i.e. for the blueprint's `μ̂`, and for an arbitrary probability measure, as
the blueprint states it. The proof needs no weak convergence, which is why the statement mentions
none.

Class (c) — the replacement for the causal orientation argument, which used monotonicity of
Bernstein functions; that monotonicity is unavailable here before the classification and is
recovered from it in `prop:strict-positivity`(1). -/
theorem dilation_atom (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop)
    (h : ∀ ω : ℝ, Tendsto (fun n => charFun μ (lam n * ω)) atTop (𝓝 1)) :
    μ = Measure.dirac 0 := by
  -- Dominated convergence on the fixed interval `[-2,2]`, with the constant bound `2`.
  have hint : Tendsto (fun n => ∫ t in (-2:ℝ)..2, (1 - charFun μ (lam n * t))) atTop (𝓝 0) := by
    have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ)) (a := (-2:ℝ)) (b := 2) (l := atTop)
      (F := fun n t => 1 - charFun μ (lam n * t)) (f := fun _ => (0:ℂ))
      (bound := fun _ => (2:ℝ))
      (.of_forall fun n => ((measurable_const.sub
        (measurable_charFun.comp (by fun_prop))).aestronglyMeasurable))
      (.of_forall fun n => ae_of_all _ fun t _ => norm_one_sub_charFun_le_two)
      intervalIntegrable_const
      (ae_of_all _ fun t _ => by simpa using (h t).const_sub 1)
    simpa using hdct
  have hbnd : Tendsto (fun n => 2⁻¹ * ‖∫ t in (-2:ℝ)..2, (1 - charFun μ (lam n * t))‖)
      atTop (𝓝 0) := by simpa using (hint.norm).const_mul (2⁻¹ : ℝ)
  -- Every set `{|x| > r}` is null, by the truncation inequality applied to the dilate.
  have key : ∀ r : ℝ, 0 < r → μ.real {x : ℝ | r < |x|} = 0 := by
    intro r hr
    refine le_antisymm ?_ measureReal_nonneg
    refine ge_of_tendsto hbnd ?_
    filter_upwards [hlam.eventually_ge_atTop (max 1 r⁻¹)] with n hn
    have hc1 : (1:ℝ) ≤ lam n := le_trans (le_max_left _ _) hn
    have hcr : r⁻¹ ≤ lam n := le_trans (le_max_right _ _) hn
    have hc0 : (0:ℝ) < lam n := lt_of_lt_of_le one_pos hc1
    set c := lam n with hcdef
    haveI : IsProbabilityMeasure (μ.map (fun x => c * x)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hmap : (μ.map (fun x => c * x)).real {x : ℝ | 1 < |x|}
        = μ.real {x : ℝ | 1 < |c * x|} := by
      rw [Measure.real, Measure.real, Measure.map_apply (by fun_prop)
        (measurableSet_lt measurable_const (by fun_prop))]
      rfl
    have hsub : {x : ℝ | r < |x|} ⊆ {x : ℝ | 1 < |c * x|} := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      have habs : |c * x| = c * |x| := by rw [abs_mul, abs_of_pos hc0]
      rw [habs]
      calc (1:ℝ) = r⁻¹ * r := by field_simp
        _ ≤ c * r := by gcongr
        _ < c * |x| := by gcongr
    have hle := measureReal_mono (μ := μ) hsub
    have hbase := measureReal_abs_gt_le_integral_charFun
      (μ := μ.map (fun x => c * x)) (r := 1) one_pos
    rw [hmap] at hbase
    have hchar : ∀ t : ℝ, charFun (μ.map (fun x => c * x)) t = charFun μ (c * t) :=
      fun t => charFun_map_mul c t
    simp only [hchar, inv_one, mul_one] at hbase
    exact hle.trans (by norm_num at hbase ⊢; linarith [hbase])
  -- Hence the complement of the origin is null, and a probability measure with that property
  -- is the Dirac mass.
  have hcompl : μ ({(0:ℝ)}ᶜ) = 0 := by
    have hset : ({(0:ℝ)}ᶜ : Set ℝ) = ⋃ n : ℕ, {x : ℝ | (1/(n+1) : ℝ) < |x|} := by
      ext x
      simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, mem_setOf_eq]
      constructor
      · intro hx
        exact exists_nat_one_div_lt (abs_pos.mpr hx)
      · rintro ⟨n, hn⟩ rfl
        simp only [abs_zero] at hn
        have hpos : (0:ℝ) < 1/(n+1) := by positivity
        linarith
    rw [hset]
    refine measure_iUnion_null fun n => ?_
    have h0 := key (1/(n+1)) (by positivity)
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 (measure_ne_top _ _)
  refine Measure.ext fun s hs => ?_
  by_cases h0 : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_mem h0]
    have hc : μ sᶜ = 0 := measure_mono_null (compl_subset_compl.mpr (by simpa using h0)) hcompl
    have hsum := measure_add_measure_compl (μ := μ) hs
    rw [hc, add_zero] at hsum
    simpa [measure_univ] using hsum
  · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h0]
    exact measure_mono_null (by simpa using h0) hcompl

end SpatialLine
