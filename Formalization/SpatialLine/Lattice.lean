/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Additivity
import SpatialLine.LatticeZero
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# The zero set of a transform: a closed subgroup, and its trichotomy

Blueprint: `blueprint/src/parts/02-preliminaries.tex`, `lem:lattice-zero`.

`N(μ) := {ω : μ̂(ω) = 1}` is a closed subgroup of `ℝ`, hence `{0}`, a lattice `cℤ`, or all of
`ℝ`; and it is all of `ℝ` exactly when `μ = δ₀`. This is the single most consequential
difference between the two developments — the causal vanishing lemma says an exponent vanishing
at one interior point vanishes identically, and on the line that is false.

## What the wave-1 merge left here

The node is `lem:lattice-zero` and belongs to **Chapter 2**, whose declarations are the
`SpatialLine.lattice_zero_*` of `SpatialLine/LatticeZero.lean`. This file proved the same
mathematics independently while chapter 2 was being proved in parallel; the merge of 2026-09-09
deleted the duplicated statements — the characterisation `charFun_eq_one_iff`, the trichotomy
and the degenerate case — and left only what chapters 5 and 6 add to them: the zero set
**as a bundled `AddSubgroup`**, which `cor:monotonicity` and `lem:no-lattice` quantify over and
which the node's own existential form (`lattice_zero_isClosedSubgroup`) does not provide.

## What writing it down found

The subgroup property is not a fact about `charFun` but about the **a.e. behaviour of the
integrand**: `μ̂(ω) = 1` for a probability measure forces `cos(ωx) = 1` for `μ`-almost every `x`,
because `1 - cos(ωx) ≥ 0` has integral zero, and then `sin(ωx) = 0` follows pointwise from
`sin² = 1 - cos²`. Closure under addition is the cosine addition formula applied a.e., and no
complex analysis is involved. Stating the characterisation (`charFun_eq_one_iff`, chapter 2's)
first is what makes the rest short.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The zero set as a closed subgroup -/

/-- **`N(μ) = {ω : μ̂(ω) = 1}`** as an additive subgroup of `ℝ`.

Duplicates the content of `Skeleton.lattice_zero_isClosedSubgroup` (`lem:lattice-zero`,
Chapter 2). -/
def transformOne (ν : Measure ℝ) [IsProbabilityMeasure ν] : AddSubgroup ℝ where
  carrier := {ω : ℝ | charFun ν ω = 1}
  zero_mem' := by
    simp only [mem_setOf_eq]
    rw [charFun_zero]
    simp
  add_mem' := by
    intro a b ha hb
    simp only [mem_setOf_eq] at ha hb ⊢
    rw [charFun_eq_one_iff] at ha hb ⊢
    filter_upwards [ha, hb] with x hxa hxb
    have hsa : Real.sin (a * x) = 0 := sin_eq_zero_of_cos_eq_one hxa
    have hsb : Real.sin (b * x) = 0 := sin_eq_zero_of_cos_eq_one hxb
    rw [add_mul, Real.cos_add, hxa, hxb, hsa, hsb]
    ring
  neg_mem' := by
    intro a ha
    simp only [mem_setOf_eq] at ha ⊢
    rw [charFun_neg, ha]
    simp

@[simp] lemma mem_transformOne {ν : Measure ℝ} [IsProbabilityMeasure ν] {ω : ℝ} :
    ω ∈ transformOne ν ↔ charFun ν ω = 1 := Iff.rfl

lemma coe_transformOne (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (transformOne ν : Set ℝ) = {ω : ℝ | charFun ν ω = 1} := rfl

lemma isClosed_transformOne (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsClosed (transformOne ν : Set ℝ) := by
  rw [coe_transformOne]
  exact isClosed_eq continuous_charFun continuous_const

/-! ## The trichotomy -/

/-- The degenerate case: the zero set is everything exactly when the law is `δ₀`. This is
`lattice_zero_eq_univ_iff` (`lem:lattice-zero`, chapter 2) read at the bundled subgroup. -/
theorem transformOne_eq_univ_iff (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (transformOne ν : Set ℝ) = univ ↔ ν = Measure.dirac 0 := by
  rw [coe_transformOne]
  exact lattice_zero_eq_univ_iff ν

/-- **The trichotomy.** A closed subgroup of `ℝ` is `{0}`, a lattice, or all of `ℝ`. This is
`lattice_zero_trichotomy` (`lem:lattice-zero`, chapter 2) read at the bundled subgroup. -/
theorem transformOne_trichotomy (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (transformOne ν : Set ℝ) = {0}
      ∨ (∃ c : ℝ, 0 < c ∧ (transformOne ν : Set ℝ) = {x : ℝ | ∃ n : ℤ, x = c * n})
      ∨ (transformOne ν : Set ℝ) = univ := by
  simpa only [coe_transformOne] using lattice_zero_trichotomy ν

/-- A proper closed subgroup of `ℝ` is countable. -/
theorem countable_transformOne (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : (transformOne ν : Set ℝ) ≠ univ) : (transformOne ν : Set ℝ).Countable := by
  rcases transformOne_trichotomy ν with h0 | ⟨c, _, hc⟩ | huniv
  · rw [h0]; exact countable_singleton 0
  · rw [hc]
    have : {x : ℝ | ∃ n : ℤ, x = c * n} = Set.range (fun n : ℤ => c * (n : ℝ)) := by
      ext x; simp [eq_comm]
    rw [this]
    exact countable_range _
  · exact absurd huniv h

end SpatialLine
