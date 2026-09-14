/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Truncation

/-!
# `thm:increments-levy`, part one: the null-array estimate

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, the first step of the
proof ("the null array").

In the semigroup case every kernel is a convolution power and infinite divisibility is
immediate. In the hemigroup case there is no such power, and what replaces it is a null-array
limit: for the uniform partition `s = s_0 < ... < s_n = t` and `Π_n := Σ_i μ_{s_i,s_{i+1}}`,

  `∫ (1 - cos ω x) dΠ_n(x) → g_{s,t}(ω)` for every `ω`.

Each `Π_n` is a *finite* measure, of mass `n`; the divergence of the masses is what the
weighting of `SpatialLine/LevyExtraction.lean` cures.

## Why this step is elementary

Three ingredients, and no limit theorem for triangular arrays:

* additivity (`sum_exponent_part`), which makes `g_{s,t}(ω)` the sum of the increments;
* uniform continuity of `G(·,ω)` on the compact `[s,t]`, which makes the increments uniformly
  small;
* the inequality `0 ≤ u - (1 - e^{-u}) ≤ u²` (`sub_one_sub_exp_neg_le`, in
  `SpatialLine/Truncation.lean`), which converts a sum of exponents into a sum of
  `1 - μ̂_i(ω)`, that is into an integral against `Π_n`.

twin: `Hemigroup.CascadeCore.tendsto_integral_partitionMeasure` (`Hemigroup/NullArray.lean`),
which this file follows step for step with `1 - e^{-sx}` replaced by `1 - cos ωx`. The
partition points and their six elementary lemmas are Paper I's verbatim; they are a candidate
for `ScaleSpaceCore`, being about `ℝ` alone.
-/

namespace SpatialLine

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology

/-! ## The uniform partition -/

/-- The `i`-th point of the uniform `n`-partition of `[s,t]`. Total in `n`: at `n = 0` the Lean
convention `i / 0 = 0` makes every point `s`, which no statement below uses.

twin: `Hemigroup.part`, verbatim. -/
noncomputable def part (s t : ℝ) (n i : ℕ) : ℝ := s + (i / n : ℝ) * (t - s)

@[simp] lemma part_zero (s t : ℝ) (n : ℕ) : part s t n 0 = s := by simp [part]

lemma part_self {n : ℕ} (hn : n ≠ 0) (s t : ℝ) : part s t n n = t := by
  rw [part, div_self (Nat.cast_ne_zero.mpr hn)]
  ring

variable {s t : ℝ}

lemma part_le_succ (hst : s ≤ t) (n i : ℕ) : part s t n i ≤ part s t n (i + 1) := by
  have hfrac : (i / n : ℝ) ≤ ((i + 1 : ℕ) / n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      gcongr
      exact_mod_cast Nat.le_succ i
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  rw [part, part]
  nlinarith

lemma part_mem_Icc (hst : s ≤ t) {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ n) :
    part s t n i ∈ Icc s t := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h0 : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have h1 : (i / n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hi
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  constructor
  · rw [part]; nlinarith
  · rw [part]; nlinarith

lemma part_nonneg (hs : 0 ≤ s) (hst : s ≤ t) (n i : ℕ) : 0 ≤ part s t n i := by
  have hfrac : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  rw [part]
  nlinarith

/-- The mesh: consecutive partition points are `(t - s)/n` apart. -/
lemma part_succ_sub {n : ℕ} (hn : n ≠ 0) (s t : ℝ) (i : ℕ) :
    part s t n (i + 1) - part s t n i = (t - s) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [part, part]
  push_cast
  field_simp
  ring

/-! ## Additivity along the partition -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- Each partition increment is a probability measure. -/
lemma isProbabilityMeasure_part (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    (n i : ℕ) : IsProbabilityMeasure (μ (part s t n i) (part s t n (i + 1))) :=
  hker.isProbability _ _ (part_nonneg hs hst n i) (part_le_succ hst n i)

/-- **Additivity along the partition** — `lem:additivity`, telescoped. -/
theorem sum_exponent_part (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t) {n : ℕ}
    (hn : n ≠ 0) (ω : ℝ) :
    ∑ i ∈ range n, exponent (μ (part s t n i) (part s t n (i + 1))) ω
      = exponent (μ s t) ω := by
  have hstep : ∀ i : ℕ, exponent (μ (part s t n i) (part s t n (i + 1))) ω
      = exponent (μ 0 (part s t n (i + 1))) ω - exponent (μ 0 (part s t n i)) ω := fun i =>
    exponent_eq_sub hker (part_nonneg hs hst n i) (part_le_succ hst n i) ω
  simp only [hstep]
  rw [Finset.sum_range_sub (fun i => exponent (μ 0 (part s t n i)) ω), part_self hn, part_zero]
  exact (exponent_eq_sub hker hs hst ω).symm

/-! ## `Π_n`, the partition measures -/

/-- `Π_n = Σ_i μ_{s_i,s_{i+1}}`: a finite measure of total mass `n`. -/
noncomputable def partitionMeasure (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  ∑ i ∈ range n, μ (part s t n i) (part s t n (i + 1))

lemma isFiniteMeasure_partitionMeasure (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    (n : ℕ) : IsFiniteMeasure (partitionMeasure μ s t n) := by
  constructor
  rw [partitionMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.mpr fun i _ => ?_
  haveI := isProbabilityMeasure_part hker hs hst n i
  exact measure_lt_top _ _

/-- An integral against `Π_n` is the sum of the integrals against the increments. -/
lemma integral_partitionMeasure_eq_sum (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) {f : ℝ → ℝ}
    (hf : ∀ i ∈ range n, Integrable f (μ (part s t n i) (part s t n (i + 1)))) :
    ∫ x, f x ∂(partitionMeasure μ s t n)
      = ∑ i ∈ range n, ∫ x, f x ∂(μ (part s t n i) (part s t n (i + 1))) := by
  rw [partitionMeasure, integral_finsetSum_measure hf]

/-- **The `n`-th approximant, computed.** Pairing `1 - cos ωx` against `Π_n` is exactly the sum
of `1 - μ̂_i(ω)` over the partition. -/
theorem integral_partitionMeasure (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    (n : ℕ) (ω : ℝ) :
    ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n)
      = ∑ i ∈ range n,
          (1 - Real.exp (-(exponent (μ (part s t n i) (part s t n (i + 1))) ω))) := by
  have hint : ∀ i ∈ range n, Integrable (fun x : ℝ => 1 - Real.cos (ω * x))
      (μ (part s t n i) (part s t n (i + 1))) := by
    intro i _
    haveI := isProbabilityMeasure_part hker hs hst n i
    exact (integrable_const (1 : ℝ)).sub (integrable_cos_mul _ ω)
  rw [integral_partitionMeasure_eq_sum μ s t n hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := isProbabilityMeasure_part hker hs hst n i
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_cos_mul _ ω), integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  congr 1
  rw [← fourierCos_apply, exponent_apply, neg_neg,
    Real.exp_log (kernel_transform_pos hker (part_nonneg hs hst n i) (part_le_succ hst n i) ω)]

/-! ## The estimate

The whole of the null-array argument, in one inequality. The caller supplies the bound `m` on
the partition increments; where `m` comes from — uniform continuity — is separated out below,
so that this step has no analysis in it at all.
-/

/-- **The null-array estimate.** If every partition increment is at most `m` at the frequency
`ω`, the `n`-th approximant is within `m · g_{s,t}(ω)` of `g_{s,t}(ω)`.

The constant is that of `sub_one_sub_exp_neg_le`, which is the proof of record's. -/
theorem abs_sub_integral_partitionMeasure_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) {n : ℕ} (hn : n ≠ 0) (ω : ℝ) {m : ℝ}
    (hm : ∀ i ∈ range n, exponent (μ (part s t n i) (part s t n (i + 1))) ω ≤ m) :
    |exponent (μ s t) ω - ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n)|
      ≤ m * exponent (μ s t) ω := by
  set g : ℕ → ℝ := fun i => exponent (μ (part s t n i) (part s t n (i + 1))) ω with hg
  have hgnn : ∀ i, 0 ≤ g i := fun i =>
    exponent_nonneg hker (part_nonneg hs hst n i) (part_le_succ hst n i) ω
  have hsum : ∑ i ∈ range n, g i = exponent (μ s t) ω := sum_exponent_part hker hs hst hn ω
  have hdiff : exponent (μ s t) ω
      - ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n)
      = ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) := by
    rw [integral_partitionMeasure hker hs hst n ω, ← hsum, ← Finset.sum_sub_distrib]
  rw [hdiff]
  have hlow : 0 ≤ ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) :=
    Finset.sum_nonneg fun i _ => by linarith [one_sub_exp_neg_le (g i)]
  have hhigh : ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) ≤ ∑ i ∈ range n, m * g i := by
    refine Finset.sum_le_sum fun i hi => ?_
    calc g i - (1 - Real.exp (-(g i))) ≤ g i ^ 2 := sub_one_sub_exp_neg_le (g i) (hgnn i)
      _ = g i * g i := by ring
      _ ≤ m * g i := mul_le_mul_of_nonneg_right (hm i hi) (hgnn i)
  rw [abs_of_nonneg hlow]
  calc ∑ i ∈ range n, (g i - (1 - Real.exp (-(g i)))) ≤ ∑ i ∈ range n, m * g i := hhigh
    _ = m * exponent (μ s t) ω := by rw [← Finset.mul_sum, hsum]

/-! ## The mesh vanishes

The only analysis in the file: `G(·,ω)` is continuous on the compact `[s,t]`, hence uniformly
continuous there, so the partition increments — differences of `G` across a gap of `(t-s)/n` —
are eventually uniformly small.
-/

/-- For every `m > 0`, all increments of a fine enough partition are at most `m`. -/
theorem exists_partition_increment_le (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ℝ) {m : ℝ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ range n, exponent (μ (part s t n i) (part s t n (i + 1))) ω ≤ m := by
  have hsub : Icc s t ⊆ Ici 0 := fun u hu => le_trans hs hu.1
  have hcont : ContinuousOn (fun u => exponent (μ 0 u) ω) (Icc s t) :=
    (continuousOn_exponent hker ω).mono hsub
  have huc : UniformContinuousOn (fun u => exponent (μ 0 u) ω) (Icc s t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδb⟩ := huc m hm
  obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / δ)
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn i hi => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr (le_trans (le_max_left N 1) hn)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hi' : i < n := Finset.mem_range.mp hi
  have hts : (0 : ℝ) ≤ t - s := sub_nonneg.mpr hst
  have hmesh : |part s t n (i + 1) - part s t n i| < δ := by
    rw [part_succ_sub hn0, abs_of_nonneg (div_nonneg hts hnpos.le), div_lt_iff₀ hnpos]
    have h2 : (t - s) / δ < n := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hδ] at h2
    linarith [h2, mul_comm (n : ℝ) δ]
  have h1 : part s t n (i + 1) ∈ Icc s t := part_mem_Icc hst hn0 hi'
  have h0 : part s t n i ∈ Icc s t := part_mem_Icc hst hn0 (le_of_lt hi')
  have hbound := hδb _ h1 _ h0 (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at hbound
  rw [exponent_eq_sub hker (part_nonneg hs hst n i) (part_le_succ hst n i) ω]
  exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hbound)

/-- **The null-array limit.** `g_{s,t}(ω)` is the limit of the pairings of `1 - cos ωx` against
the finite measures `Π_n`.

This is `thm:increments-levy` up to the extraction of the limiting pair. -/
theorem tendsto_integral_partitionMeasure (hker : IsKernelFamily Fam.Φ μ) (hs : 0 ≤ s)
    (hst : s ≤ t) (ω : ℝ) :
    Tendsto (fun n => ∫ x, (1 - Real.cos (ω * x)) ∂(partitionMeasure μ s t n)) atTop
      (𝓝 (exponent (μ s t) ω)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set g := exponent (μ s t) ω with hgdef
  have hgnn : 0 ≤ g := exponent_nonneg hker hs hst ω
  set m : ℝ := ε / (2 * (g + 1)) with hmdef
  have hm : 0 < m := by positivity
  have hmg : m * g < ε := by
    rw [hmdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (exists_partition_increment_le hker hs hst ω hm)
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (le_trans (le_max_right N₀ 1) hn)
  have hbound := abs_sub_integral_partitionMeasure_le hker hs hst hn0 ω
    (hN₀ n (le_trans (le_max_left N₀ 1) hn))
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hbound hmg

end SpatialLine
