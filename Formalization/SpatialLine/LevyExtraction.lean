/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Tightness
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# `thm:increments-levy`, part three: the test function and the limiting pair

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, third step of the proof
("the limit").

`SpatialLine/NullArray.lean` produced `∫ (1 - cos ωx) dΠ_n → g_{s,t}(ω)` with each `Π_n` finite,
and `SpatialLine/Tightness.lean` produced the two bounds that hold uniformly in `n`. What
remains is to extract a limiting pair `(a, ν)` from `(Π_n)`, and the obstruction is that the
masses `Π_n(ℝ) = n` diverge: mass piles up at the origin, and that pile is exactly the Gaussian
coefficient `a` the pair is allowed to have.

## The weighting and the test function

`ϱ_n := (1 ∧ x²)\,\widetilde\Pi_n` on `[0,∞)`, where `\widetilde\Pi_n` is the image of `Π_n`
under `x ↦ |x|`. The weight vanishes at the origin at the rate that turns piled-up mass into a
Gaussian coefficient, and `Tightness.lean` bounds the masses of the `ϱ_n` and their tails
uniformly.

Under the weighting the observable `1 - cos ωx` becomes

  `k_ω(x) = (1 - cos ωx)/(1 ∧ x²)`,   `k_ω(0) = ω²/2`,

with a removable singularity at the origin whose filled-in value is what turns mass at `0` into
`a ω²`. It is written here in the closed form

  `levyTest ω x = (ω²/2)\,\mathrm{sinc}(ωx/2)^2\,(1 ∨ x²)`,

which needs no `if`: the half-angle identity `1 - \cos u = 2\sin^2(u/2)` makes it equal to
`k_ω` off the origin, `\mathrm{sinc}` is continuous everywhere, and the removable singularity
is filled in by `\mathrm{sinc}(0) = 1` rather than by a case split. **This is a divergence from
the blueprint's route and it is a simplification, not a change of the mathematics**: the
blueprint fills the singularity by hand and appeals to `1 - \cos u = u²/2 + O(u^4)`, and the
closed form makes both the continuity and the boundedness one-liners.

## The extraction

Mathlib's Prokhorov theorem for finite measures,
`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`, is applied with the *monotone*
compacts `K_n = [0, n+1]` and the tolerances `u_n` supplied by the tightness bound. It returns a
cluster point rather than a limit, since `FiniteMeasure ℝ` carries no metrizability instance;
nothing is lost, because every observable used is a continuous real function of the measure that
already converges along the full sequence, and a convergent sequence has one cluster value
(`eq_of_mapClusterPt`, Paper I's). The same constraint that gives tightness also gives that the
cluster point charges no negative half-line, so no portmanteau argument is needed for the
folding.

twin: `Hemigroup.CascadeCore.exists_limit_measure` (`Hemigroup/LevyLimit.lean`) and
`Hemigroup.CascadeCore.exponent_hasLevyRep` (`Hemigroup/LevyTriple.lean`). The causal
development compactifies `[0,∞]` by `1 - e^{-x}` and needs no tightness at all; here the test
function oscillates at infinity and does not extend to a compactification, so tightness replaces
the change of variable. That is the one new idea of the node.
-/

namespace SpatialLine

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology NNReal

/-! ## The test function -/

/-- `k_ω(x) = (1 - \cos ωx)/(1 ∧ x²)`, with the removable singularity at the origin filled in
by its limit `ω²/2`, written in a closed form that makes the filling automatic. -/
noncomputable def levyTest (ω x : ℝ) : ℝ :=
  ω ^ 2 / 2 * Real.sinc (ω * x / 2) ^ 2 * max 1 (x ^ 2)

lemma continuous_levyTest (ω : ℝ) : Continuous (levyTest ω) := by
  unfold levyTest
  exact ((continuous_const.mul ((Real.continuous_sinc.comp (by fun_prop)).pow 2)).mul
    (continuous_const.max (continuous_pow 2)))

@[simp] lemma levyTest_zero (ω : ℝ) : levyTest ω 0 = ω ^ 2 / 2 := by
  simp [levyTest]

/-- **The defining identity**: `k_ω(x)\,(1 ∧ x²) = 1 - \cos ωx`, at *every* `x`, the origin
included (where both sides vanish). -/
theorem levyTest_mul_min (ω x : ℝ) :
    levyTest ω x * min 1 (x ^ 2) = 1 - Real.cos (ω * x) := by
  have hmaxmin : max 1 (x ^ 2) * min 1 (x ^ 2) = x ^ 2 := by
    rcases le_total (1 : ℝ) (x ^ 2) with h | h
    · rw [max_eq_right h, min_eq_left h, mul_one]
    · rw [max_eq_left h, min_eq_right h, one_mul]
  have hhalf : 1 - Real.cos (ω * x) = 2 * Real.sin (ω * x / 2) ^ 2 := by
    have := Real.sin_sq_eq_half_sub (ω * x / 2)
    have hdouble : 2 * (ω * x / 2) = ω * x := by ring
    rw [hdouble] at this
    linarith
  rw [levyTest, mul_assoc, hmaxmin, hhalf]
  rcases eq_or_ne (ω * x / 2) 0 with h | h
  · have hzero : ω * x = 0 := by linarith
    have hsq : ω ^ 2 * x ^ 2 = 0 := by nlinarith [hzero]
    rw [h, Real.sinc_zero, Real.sin_zero]
    linear_combination hsq / 2
  · have hω : ω ≠ 0 := by
      intro h0
      exact h (by rw [h0]; ring)
    have hx : x ≠ 0 := by
      intro h0
      exact h (by rw [h0]; ring)
    rw [Real.sinc_of_ne_zero h]
    field_simp

lemma levyTest_nonneg (ω x : ℝ) : 0 ≤ levyTest ω x := by
  refine mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ?_
  exact le_trans zero_le_one (le_max_left _ _)

/-- The test function is bounded by `\max(ω²/2, 2)`: below `1` the weight is `x²` and the sinc
factor is at most `1`; above it the identity reads `k_ω = 1 - \cos ωx`. -/
theorem levyTest_le (ω x : ℝ) : levyTest ω x ≤ max (ω ^ 2 / 2) 2 := by
  rcases le_total (1 : ℝ) (x ^ 2) with h | h
  · have hmin : min 1 (x ^ 2) = 1 := min_eq_left h
    have := levyTest_mul_min ω x
    rw [hmin, mul_one] at this
    refine le_trans (le_of_eq this) (le_trans ?_ (le_max_right _ _))
    linarith [Real.neg_one_le_cos (ω * x)]
  · have hmax : max 1 (x ^ 2) = 1 := max_eq_left h
    have hsinc : Real.sinc (ω * x / 2) ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one (ω * x / 2)
      nlinarith [abs_nonneg (Real.sinc (ω * x / 2)), sq_abs (Real.sinc (ω * x / 2))]
    refine le_trans ?_ (le_max_left _ _)
    rw [levyTest, hmax, mul_one]
    nlinarith [sq_nonneg ω, hsinc]

/-- The test function as a bounded continuous function, the shape weak convergence needs. -/
noncomputable def levyTestBdd (ω : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (levyTest ω) (continuous_levyTest ω)
    (max (ω ^ 2 / 2) 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (levyTest_nonneg ω x)]
      exact levyTest_le ω x)

@[simp] lemma levyTestBdd_apply (ω x : ℝ) : levyTestBdd ω x = levyTest ω x := rfl

/-! ## A cluster point is pinned by what already converges

twin: `Hemigroup.eq_of_mapClusterPt`, verbatim. The extraction below produces a *cluster* point
rather than a limit, because the space of finite measures on `ℝ` carries no metrizability
instance in Mathlib; nothing is lost, since every observable used converges along the full
sequence.
-/

/-- If `Φ ∘ P` converges and `a` is a cluster point of `P`, then `Φ a` is the limit. -/
theorem eq_of_mapClusterPt {α : Type*} [TopologicalSpace α] {P : ℕ → α} {a : α} {Φ : α → ℝ}
    {L : ℝ} (hcl : MapClusterPt a atTop P) (hΦ : Continuous Φ)
    (hlim : Tendsto (fun n => Φ (P n)) atTop (𝓝 L)) : Φ a = L :=
  eq_of_nhds_neBot ((hcl.continuousAt_comp hΦ.continuousAt).clusterPt.mono hlim)

/-! ## The weighted partition measures -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

/-- `\widetilde\Pi_n`, the image of `Π_n` under `x ↦ |x|`. -/
noncomputable def foldedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  (partitionMeasure μ s t n).map (fun x => |x|)

/-- `ϱ_n = (1 ∧ x²)\,\widetilde\Pi_n`, the weighted approximant. -/
noncomputable def weightedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  (foldedPartition μ s t n).withDensity fun x => ENNReal.ofReal (min 1 (x ^ 2))

lemma isFiniteMeasure_foldedPartition (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    (n : ℕ) : IsFiniteMeasure (foldedPartition μ s t n) := by
  haveI := isFiniteMeasure_partitionMeasure hker hs hst n
  constructor
  rw [foldedPartition, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact measure_lt_top (partitionMeasure μ s t n) univ

lemma isFiniteMeasure_weightedPartition (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) (n : ℕ) : IsFiniteMeasure (weightedPartition μ s t n) := by
  haveI := isFiniteMeasure_foldedPartition hker hs hst n
  constructor
  rw [weightedPartition, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(foldedPartition μ s t n)
      ≤ ∫⁻ _, 1 ∂(foldedPartition μ s t n) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ < ⊤ := by rw [lintegral_one]; exact measure_lt_top _ _

/-- The weighted measure is dominated by the folded one: the density is at most `1`. -/
lemma weightedPartition_le_foldedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    weightedPartition μ s t n A ≤ foldedPartition μ s t n A := by
  rw [weightedPartition, withDensity_apply _ hA]
  calc ∫⁻ x in A, ENNReal.ofReal (min 1 (x ^ 2)) ∂(foldedPartition μ s t n)
      ≤ ∫⁻ _ in A, 1 ∂(foldedPartition μ s t n) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = foldedPartition μ s t n A := by rw [lintegral_one, Measure.restrict_apply_univ]

/-- The folded measure charges no negative half-line. -/
lemma foldedPartition_Iio (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) :
    foldedPartition μ s t n (Iio 0) = 0 := by
  rw [foldedPartition, Measure.map_apply (by fun_prop) measurableSet_Iio]
  convert measure_empty (μ := partitionMeasure μ s t n)
  ext x
  simp [not_lt.mpr (abs_nonneg x)]

/-- **The change of variable, at the level of integrals.** Pairing the test function against
`ϱ_n` is pairing `1 - \cos ωx` against `Π_n` — which is what `NullArray.lean` computes. -/
theorem integral_levyTest_weightedPartition (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) (ω : ℝ) :
    ∫ x, levyTest ω x ∂(weightedPartition μ s t n)
      = ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n) := by
  rw [weightedPartition, integral_withDensity_eq_integral_toReal_smul₀
    (Measurable.aemeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hstep : ∫ x, (ENNReal.ofReal (min 1 (x ^ 2))).toReal • levyTest ω x
        ∂(foldedPartition μ s t n)
      = ∫ x, (1 - Real.cos (ω * x)) ∂(foldedPartition μ s t n) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (ENNReal.ofReal (min 1 (x ^ 2))).toReal • levyTest ω x = 1 - Real.cos (ω * x)
    rw [smul_eq_mul, ENNReal.toReal_ofReal (le_min zero_le_one (sq_nonneg x)), mul_comm]
    exact levyTest_mul_min ω x
  have hmapint : ∫ x, (1 - Real.cos (ω * x))
        ∂(Measure.map (fun x : ℝ => |x|) (partitionMeasure μ s t n))
      = ∫ x, (1 - Real.cos (ω * |x|)) ∂(partitionMeasure μ s t n) :=
    integral_map (by fun_prop) (by fun_prop)
  rw [hstep, foldedPartition, hmapint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show 1 - Real.cos (ω * |x|) = 1 - Real.cos (ω * x)
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, mul_neg, Real.cos_neg]

/-! ## The two uniform bounds, in the shape Prokhorov asks for -/

/-- **The masses are uniformly bounded**, by the truncation inequality at `r = 1`. -/
theorem measureReal_weightedPartition_univ_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) (n : ℕ) :
    (weightedPartition μ s t n).real univ
      ≤ 3 * Real.pi ^ 2 / 2 * meanExponent μ s t 1 := by
  haveI := isFiniteMeasure_partitionMeasure hker hs hst n
  haveI := isFiniteMeasure_foldedPartition hker hs hst n
  haveI := isFiniteMeasure_weightedPartition hker hs hst n
  have hπ : (0 : ℝ) < 2 / (3 * Real.pi ^ 2) := by positivity
  -- the mass is the integral of the weight
  have hwint : Integrable (fun x : ℝ => min 1 (x ^ 2)) (foldedPartition μ s t n) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (sq_nonneg x))]
    exact min_le_left _ _
  have hwnn : 0 ≤ᵐ[foldedPartition μ s t n] fun x : ℝ => min 1 (x ^ 2) :=
    Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x)
  have hmass : (weightedPartition μ s t n).real univ
      = ∫ x, min 1 (x ^ 2) ∂(foldedPartition μ s t n) := by
    rw [measureReal_def, weightedPartition, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hwint hwnn,
      ENNReal.toReal_ofReal (integral_nonneg fun x => le_min zero_le_one (sq_nonneg x))]
  have hint : ∫ x, min 1 (x ^ 2) ∂(foldedPartition μ s t n)
      = ∫ x, min 1 (x ^ 2) ∂(partitionMeasure μ s t n) := by
    rw [foldedPartition, integral_map (by fun_prop : AEMeasurable (fun x : ℝ => |x|) _)
      (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show min 1 (|x| ^ 2) = min 1 (x ^ 2)
    rw [sq_abs]
  -- and the truncation inequality bounds it
  have hpoint : ∀ x : ℝ, 2 / (3 * Real.pi ^ 2) * min 1 (x ^ 2) ≤ 1 - Real.sinc (1 * x) := by
    intro x
    rw [one_mul]
    exact one_sub_sinc_ge x
  have hIleft : Integrable (fun x : ℝ => 2 / (3 * Real.pi ^ 2) * min 1 (x ^ 2))
      (partitionMeasure μ s t n) := by
    refine ((integrable_const (2 / (3 * Real.pi ^ 2))).mono' (by fun_prop) ?_)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [min_le_left (1 : ℝ) (x ^ 2), le_min zero_le_one (sq_nonneg x), hπ]
  have hIright : Integrable (fun x : ℝ => 1 - Real.sinc (1 * x)) (partitionMeasure μ s t n) :=
    (integrable_const (1 : ℝ)).sub (integrable_sinc_mul _ 1)
  have hmono := integral_mono hIleft hIright hpoint
  rw [integral_const_mul] at hmono
  have htrunc := integral_one_sub_sinc_partitionMeasure_le hker hs hst n (r := 1) one_pos
  have hchain : 2 / (3 * Real.pi ^ 2) * ∫ x, min 1 (x ^ 2) ∂(partitionMeasure μ s t n)
      ≤ meanExponent μ s t 1 := le_trans hmono htrunc
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hmass, hint]
  calc ∫ x, min 1 (x ^ 2) ∂(partitionMeasure μ s t n)
      = 3 * Real.pi ^ 2 / 2 * (2 / (3 * Real.pi ^ 2) *
          ∫ x, min 1 (x ^ 2) ∂(partitionMeasure μ s t n)) := by field_simp
    _ ≤ 3 * Real.pi ^ 2 / 2 * meanExponent μ s t 1 :=
        mul_le_mul_of_nonneg_left hchain (by positivity)

/-- **The tails are uniformly small.** For `R ≥ 1` the mass of `ϱ_n` outside `[0,R]` is at most
`(3π²/2)\,ḡ(1/R)`, uniformly in `n`; this is the truncation inequality at `r = 1/R`. -/
theorem measureReal_weightedPartition_compl_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (weightedPartition μ s t n).real ((Icc 0 R)ᶜ)
      ≤ 3 * Real.pi ^ 2 / 2 * meanExponent μ s t (1 / R) := by
  haveI := isFiniteMeasure_partitionMeasure hker hs hst n
  haveI := isFiniteMeasure_foldedPartition hker hs hst n
  haveI := isFiniteMeasure_weightedPartition hker hs hst n
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hr0 : (0 : ℝ) < 1 / R := by positivity
  have hπ : (0 : ℝ) < 2 / (3 * Real.pi ^ 2) := by positivity
  -- outside `[0,R]` the folded measure sees only `{R < |x|}`
  have hfold : foldedPartition μ s t n ((Icc 0 R)ᶜ)
      = partitionMeasure μ s t n {x : ℝ | R < |x|} := by
    rw [foldedPartition, Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_compl_iff, not_and, not_le, Set.mem_setOf_eq]
    constructor
    · intro h; exact h (abs_nonneg x)
    · intro h _; exact h
  -- the truncation inequality at `r = 1/R`
  have hset : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hbig : ∀ x ∈ {x : ℝ | R < |x|},
      2 / (3 * Real.pi ^ 2) ≤ 1 - Real.sinc (1 / R * x) := by
    intro x hx
    have hx' : R < |x| := hx
    have h1 : (1 : ℝ) ≤ (1 / R * x) ^ 2 := by
      have : R ^ 2 < x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x, hR0]
      rw [div_mul_eq_mul_div, one_mul, div_pow]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have := one_sub_sinc_ge (1 / R * x)
    rw [min_eq_left h1] at this
    linarith
  have hIright : Integrable (fun x : ℝ => 1 - Real.sinc (1 / R * x))
      (partitionMeasure μ s t n) :=
    (integrable_const (1 : ℝ)).sub (integrable_sinc_mul _ _)
  have hsetle : 2 / (3 * Real.pi ^ 2) * (partitionMeasure μ s t n).real {x : ℝ | R < |x|}
      ≤ ∫ x in {x : ℝ | R < |x|}, (1 - Real.sinc (1 / R * x)) ∂(partitionMeasure μ s t n) := by
    have := setIntegral_mono_on (μ := partitionMeasure μ s t n)
      (f := fun _ : ℝ => 2 / (3 * Real.pi ^ 2)) (g := fun x => 1 - Real.sinc (1 / R * x))
      (integrable_const _).integrableOn hIright.integrableOn hset hbig
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
  have hall : ∫ x in {x : ℝ | R < |x|}, (1 - Real.sinc (1 / R * x)) ∂(partitionMeasure μ s t n)
      ≤ ∫ x, (1 - Real.sinc (1 / R * x)) ∂(partitionMeasure μ s t n) := by
    refine setIntegral_le_integral hIright (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.zero_apply, sub_nonneg]
    exact Real.sinc_le_one _
  have htrunc := integral_one_sub_sinc_partitionMeasure_le hker hs hst n hr0
  -- assemble
  have hkey : 2 / (3 * Real.pi ^ 2) * (partitionMeasure μ s t n).real {x : ℝ | R < |x|}
      ≤ meanExponent μ s t (1 / R) := le_trans hsetle (le_trans hall htrunc)
  have hdom : (weightedPartition μ s t n).real ((Icc 0 R)ᶜ)
      ≤ (partitionMeasure μ s t n).real {x : ℝ | R < |x|} := by
    rw [measureReal_def, measureReal_def, ← hfold]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (weightedPartition_le_foldedPartition μ s t n _ measurableSet_Icc.compl)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc (weightedPartition μ s t n).real ((Icc 0 R)ᶜ)
      ≤ (partitionMeasure μ s t n).real {x : ℝ | R < |x|} := hdom
    _ = 3 * Real.pi ^ 2 / 2 * (2 / (3 * Real.pi ^ 2) *
          (partitionMeasure μ s t n).real {x : ℝ | R < |x|}) := by field_simp
    _ ≤ 3 * Real.pi ^ 2 / 2 * meanExponent μ s t (1 / R) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)



/-! ## The limiting measure

Mathlib's Prokhorov theorem for finite measures is applied with the monotone compacts
`K_n = [0, n+1]` and the tolerances the tightness bound supplies. It returns a cluster point,
and the same membership condition that gives tightness also gives that the cluster point charges
no negative half-line — so the folding survives the limit without a portmanteau argument.
-/

/-- The value of a `FiniteMeasure` on a set, as a real number. -/
lemma finiteMeasure_apply_coe (ν : FiniteMeasure ℝ) (A : Set ℝ) :
    ((ν A : ℝ≥0) : ℝ) = (ν : Measure ℝ).real A := by
  rw [measureReal_def, ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]

/-- **The weak limit of the weighted approximants.** A single finite measure on `[0,∞)` whose
pairing with the test function is `g_{s,t}(ω)`, for every `ω` at once.

This is the analytic heart of `thm:increments-levy`: what follows it is the change of variable
read backwards, splitting the limit at the origin. -/
theorem exists_limit_measure (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ ϱ : Measure ℝ, IsFiniteMeasure ϱ ∧ ϱ (Iio 0) = 0 ∧
      ∀ ω : ℝ, ∫ x, levyTest ω x ∂ϱ = exponent (μ s t) ω := by
  classical
  set C : ℝ≥0 := (3 * Real.pi ^ 2 / 2 * meanExponent μ s t 1).toNNReal with hCdef
  set u : ℕ → ℝ≥0 :=
    fun n => (3 * Real.pi ^ 2 / 2 * meanExponent μ s t (1 / ((n : ℝ) + 1))).toNNReal with hudef
  set K : ℕ → Set ℝ := fun n => Icc (0 : ℝ) ((n : ℝ) + 1) with hKdef
  set P : ℕ → FiniteMeasure ℝ :=
    fun n => ⟨weightedPartition μ s t n, isFiniteMeasure_weightedPartition hker hs hst n⟩
    with hPdef
  have hPcoe : ∀ n, ((P n : FiniteMeasure ℝ) : Measure ℝ) = weightedPartition μ s t n :=
    fun _ => rfl
  -- the mass bound
  have hmass : ∀ n, (P n).mass ≤ C := by
    intro n
    rw [← NNReal.coe_le_coe]
    refine le_trans (le_of_eq ?_)
      (le_trans (measureReal_weightedPartition_univ_le hker hs hst n) (Real.le_coe_toNNReal _))
    have h := finiteMeasure_apply_coe (P n) univ
    rw [hPcoe] at h
    rw [FiniteMeasure.mass, h]
  -- the tightness bound
  have hcar : ∀ m n : ℕ, (P m) (K n)ᶜ ≤ u n := by
    intro m n
    rw [← NNReal.coe_le_coe]
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h := finiteMeasure_apply_coe (P m) (K n)ᶜ
    rw [hPcoe] at h
    rw [h]
    exact le_trans (measureReal_weightedPartition_compl_le hker hs hst m hR)
      (Real.le_coe_toNNReal _)
  -- the tolerances vanish
  have hu : Tendsto u atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ => 3 * Real.pi ^ 2 / 2 * meanExponent μ s t (1 / ((n : ℝ) + 1))) atTop
        (𝓝 0) := by
      have := (tendsto_meanExponent hker hs hst).const_mul (3 * Real.pi ^ 2 / 2)
      simpa using this
    have := (continuous_real_toNNReal.tendsto (0 : ℝ)).comp hreal
    simpa [hudef, Function.comp_def] using this
  -- Prokhorov
  have hKmono : Monotone K := by
    intro a b hab
    refine Icc_subset_Icc le_rfl ?_
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    linarith
  have hcpt := isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le (E := ℝ)
    (u := u) (K := K) C hu (fun _ => isCompact_Icc) (Or.inr hKmono)
  obtain ⟨a, haS, hcl⟩ := hcpt.exists_mapClusterPt (f := atTop) (u := P)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall
      fun n => ⟨hmass n, fun k => hcar n k⟩))
  refine ⟨(a : Measure ℝ), inferInstance, ?_, fun ω => ?_⟩
  · -- the limit charges no negative half-line
    refine (FiniteMeasure.null_iff_toMeasure_null a (Iio 0)).mp ?_
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hu (Filter.Eventually.of_forall fun n => ?_)
    refine le_trans ?_ (haS.2 n)
    refine FiniteMeasure.apply_mono a ?_
    intro x hx hmem
    exact absurd hmem.1 (not_le.mpr hx)
  · -- the observable
    have hobs : Tendsto (fun n => ∫ x, levyTestBdd ω x ∂((P n : FiniteMeasure ℝ) : Measure ℝ))
        atTop (𝓝 (exponent (μ s t) ω)) := by
      have hEq : ∀ n, ∫ x, levyTestBdd ω x ∂((P n : FiniteMeasure ℝ) : Measure ℝ)
          = ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n) := by
        intro n
        rw [hPcoe]
        exact integral_levyTest_weightedPartition μ s t n ω
      simpa only [hEq] using tendsto_integral_partitionMeasure hker hs hst ω
    have hfix := eq_of_mapClusterPt
      (Φ := fun ν : FiniteMeasure ℝ => ∫ x, levyTestBdd ω x ∂(ν : Measure ℝ)) hcl
      (FiniteMeasure.continuous_integral_boundedContinuousFunction (levyTestBdd ω)) hobs
    simpa using hfix

end SpatialLine
