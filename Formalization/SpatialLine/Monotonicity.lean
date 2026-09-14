/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Lattice

/-!
# `cor:monotonicity`: the zero set of an increment, and where the accumulation is strict

Blueprint: `blueprint/src/parts/05-cascade.tex`, `cor:monotonicity`.

This is the **honest** port of the causal `cor:strict-monotonicity`: the causal statement holds
at every value of the transform variable, this one only off a countable set, and the difference
is exactly the lattice laws. The exceptional set is `E := ⋃ N_{p,q}` over rational `0 ≤ p < q` —
*not* `⋃ (N_{p,q} ∖ {0})`, which would leave `0 ∉ E` while `G(·,0) ≡ 0` is not strictly
increasing (the `% CHANGED (skeleton 2026-09-08)` note in the part file).

One clause is read rather than restated: that `N_{s,t}` is a lattice exactly when `μ_{s,t}` is a
lattice law is `lem:lattice-zero`'s own equivalence applied to `μ_{s,t}`, so
`monotonicity_zero_set` names that application instead of duplicating the statement.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- The zero set of an increment exponent **is** the zero set `N(μ)` of `lem:lattice-zero`. -/
theorem exponent_zero_set (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    {ω : ℝ | exponent (μ s t) ω = 0} = {ω : ℝ | charFun (μ s t) ω = 1} := by
  haveI := hker.isProbability s t hs hst
  ext ω
  simp only [mem_setOf_eq]
  have hpos := kernel_transform_pos hker hs hst ω
  constructor
  · intro h
    have hlog : Real.log (fourierCos (μ s t) ω) = 0 := by
      rw [exponent_apply, neg_eq_zero] at h; exact h
    have hone : fourierCos (μ s t) ω = 1 := by
      calc fourierCos (μ s t) ω = Real.exp (Real.log (fourierCos (μ s t) ω)) :=
            (Real.exp_log hpos).symm
        _ = 1 := by rw [hlog, Real.exp_zero]
    rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker hs hst) ω, hone]
    simp
  · intro h
    have hone : fourierCos (μ s t) ω = 1 := by
      have hc := charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker hs hst) ω
      rw [h] at hc
      exact_mod_cast hc.symm
    rw [exponent_apply, hone, Real.log_one, neg_zero]

/-- **`cor:monotonicity`, the zero set of an increment.**

For `s < t` the zero set of `g_{s,t}` is a closed **proper** subgroup — hence `{0}` or a
lattice. "Proper" is stated as `≠ univ`, which with the trichotomy is the dichotomy.

Class (b) — the honest port of `Hemigroup.CascadeCore.strict_monotonicity`. -/
theorem monotonicity_zero_set (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∃ H : AddSubgroup ℝ, IsClosed (H : Set ℝ) ∧
        (H : Set ℝ) = {ω : ℝ | exponent (μ s t) ω = 0}) ∧
      {ω : ℝ | exponent (μ s t) ω = 0} ≠ univ ∧
      ({ω : ℝ | exponent (μ s t) ω = 0} = {0} ∨
        ∃ c : ℝ, 0 < c ∧ {ω : ℝ | exponent (μ s t) ω = 0} = {x : ℝ | ∃ n : ℤ, x = c * n}) := by
  haveI := hker.isProbability s t hs hst.le
  have hset : {ω : ℝ | exponent (μ s t) ω = 0} = (transformOne (μ s t) : Set ℝ) := by
    rw [exponent_zero_set hker hs hst.le, coe_transformOne]
  have hproper : (transformOne (μ s t) : Set ℝ) ≠ univ := by
    intro hcon
    exact kernel_ne_dirac hker hnd hs hst ((transformOne_eq_univ_iff (μ s t)).mp hcon)
  refine ⟨⟨transformOne (μ s t), isClosed_transformOne (μ s t), hset.symm⟩, ?_, ?_⟩
  · rw [hset]
    exact hproper
  · rcases transformOne_trichotomy (μ s t) with h0 | ⟨c, hc, hcset⟩ | huniv
    · exact Or.inl (hset.trans h0)
    · exact Or.inr ⟨c, hc, hset.trans hcset⟩
    · exact absurd huniv hproper

/-- The exceptional set: the union of the zero sets over rational parameter pairs. -/
noncomputable def exceptionalSet (μ : ℝ → ℝ → Measure ℝ) : Set ℝ :=
  ⋃ pq : ℚ × ℚ, if (0:ℚ) ≤ pq.1 ∧ pq.1 < pq.2
    then {ω : ℝ | exponent (μ (pq.1 : ℝ) (pq.2 : ℝ)) ω = 0} else (∅ : Set ℝ)

/-- **`cor:monotonicity`, strict monotonicity off a countable set.**

The statement asks only that `E` be countable and contain every `N_{p,q}` — which is what the
conclusion needs and what the construction supplies — rather than pinning `E` to a particular
union, because the union's exact indexing is a proof device. -/
theorem monotonicity_strict (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) :
    ∃ E : Set ℝ, E.Countable ∧
      (∀ p q : ℚ, 0 ≤ p → p < q →
        {ω : ℝ | exponent (μ (p : ℝ) (q : ℝ)) ω = 0} ⊆ E) ∧
      ∀ ω : ℝ, ω ∉ E → StrictMonoOn (fun t => exponent (μ 0 t) ω) (Ici 0) := by
  refine ⟨exceptionalSet μ, ?_, ?_, ?_⟩
  · refine Set.countable_iUnion fun pq => ?_
    by_cases h : (0:ℚ) ≤ pq.1 ∧ pq.1 < pq.2
    · rw [if_pos h]
      have hp : (0:ℝ) ≤ (pq.1 : ℝ) := by exact_mod_cast h.1
      have hpq : ((pq.1 : ℝ)) < (pq.2 : ℝ) := by exact_mod_cast h.2
      haveI := hker.isProbability (pq.1 : ℝ) (pq.2 : ℝ) hp hpq.le
      have hrw : {ω : ℝ | exponent (μ (pq.1 : ℝ) (pq.2 : ℝ)) ω = 0}
          = (transformOne (μ (pq.1 : ℝ) (pq.2 : ℝ)) : Set ℝ) := by
        rw [exponent_zero_set hker hp hpq.le, coe_transformOne]
      rw [hrw]
      refine countable_transformOne (μ (pq.1 : ℝ) (pq.2 : ℝ)) ?_
      intro hcon
      exact kernel_ne_dirac hker hnd hp hpq
        ((transformOne_eq_univ_iff (μ (pq.1 : ℝ) (pq.2 : ℝ))).mp hcon)
    · rw [if_neg h]
      exact countable_empty
  · intro p q hp hpq
    refine subset_trans ?_ (Set.subset_iUnion (fun pq : ℚ × ℚ => if (0:ℚ) ≤ pq.1 ∧ pq.1 < pq.2
      then {ω : ℝ | exponent (μ (pq.1 : ℝ) (pq.2 : ℝ)) ω = 0} else (∅ : Set ℝ)) (p, q))
    rw [if_pos ⟨hp, hpq⟩]
  · intro ω hω a ha b hb hab
    have ha0 : (0:ℝ) ≤ a := ha
    -- a rational subinterval `[p,q] ⊆ [a,b]`
    obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
    obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
    have hp0 : (0:ℚ) ≤ p := by
      have : (0:ℝ) ≤ (p:ℝ) := le_of_lt (lt_of_le_of_lt ha0 hap)
      exact_mod_cast this
    have hpq' : p < q := by exact_mod_cast hpq
    have hpR : ((p:ℝ)) < (q:ℝ) := by exact_mod_cast hpq
    have hp0R : (0:ℝ) ≤ (p:ℝ) := le_of_lt (lt_of_le_of_lt ha0 hap)
    -- `ω` is not in the zero set of the rational increment
    have hωpq : exponent (μ (p:ℝ) (q:ℝ)) ω ≠ 0 := by
      intro hcon
      refine hω ?_
      refine Set.mem_iUnion.mpr ⟨(p, q), ?_⟩
      rw [if_pos ⟨hp0, hpq'⟩]
      exact hcon
    -- hence not in the zero set of `[a,b]`
    have hsum : exponent (μ a b) ω
        = exponent (μ a (p:ℝ)) ω + exponent (μ (p:ℝ) (q:ℝ)) ω + exponent (μ (q:ℝ) b) ω := by
      rw [exponent_add hker ha0 hap.le (le_trans hpR.le hqb.le) ω,
        exponent_add hker hp0R hpR.le hqb.le ω]
      ring
    have h1 := exponent_nonneg hker ha0 hap.le ω
    have h2 := exponent_nonneg hker hp0R hpR.le ω
    have h3 := exponent_nonneg hker (le_trans hp0R hpR.le) hqb.le ω
    have hgt : 0 < exponent (μ a b) ω := by
      rcases lt_or_eq_of_le h2 with h | h
      · linarith
      · exact absurd h.symm hωpq
    have hsub := exponent_eq_sub hker ha0 hab.le ω
    simp only
    linarith

end SpatialLine
