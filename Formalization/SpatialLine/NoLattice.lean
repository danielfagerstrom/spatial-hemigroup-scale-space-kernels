/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Monotonicity
import SpatialLine.Covariance

/-!
# `lem:no-lattice`: covariance excludes the lattice kernels

Blueprint: `blueprint/src/parts/06-covariance.tex`, `lem:no-lattice`.

The first thing covariance buys on the line: the exclusion of the lattice laws that
`lem:lattice-zero` left open. New — on the half-line the corresponding statement is the causal
vanishing lemma, which is a property of the function class and needs no axiom.

The argument is covariance at a **single non-integer ratio** and nothing else beyond the
cascade. The zero sets `N_t = N(μ_{0,t})` form a chain under inclusion (the increments are
nonnegative), covariance turns `N_{S_λ t}` into `λ⁻¹ N_t`, and two comparable lattices
`λ⁻¹ cℤ` and `cℤ` force `λ` or `λ⁻¹` to be a positive integer; `λ = 3/2` is neither.

Note the range: **only the kernels from the origin**. The argument does not extend to the
increments `μ_{s,t}` with `s > 0`, because `S_λ` moves both endpoints and the increments do not
form a chain.

## What proving it found

The chain comparison is cheaper element-wise than set-wise. Rather than comparing `λ⁻¹cℤ` with
`cℤ` as sets and classifying the inclusions, one member of each is enough: whichever way the
chain runs, a single generator lands in the other lattice and produces the equation `3/2 = n`
or `2/3 = n` in `ℤ`, which `omega` refutes. The skeleton priced the Lean cost as "the lattice
comparison, not the covariance", and that was right, but the comparison is six lines rather
than a classification.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **The zero sets form a chain**: `N_v ⊆ N_u` for `u ≤ v`, because the increment exponent is
nonnegative. -/
theorem zeroSet_chain (hker : IsKernelFamily Fam.Φ μ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    {ω : ℝ | exponent (μ 0 v) ω = 0} ⊆ {ω : ℝ | exponent (μ 0 u) ω = 0} := by
  intro ω hω
  simp only [mem_setOf_eq] at hω ⊢
  have hsub := exponent_eq_sub hker hu huv ω
  have h1 := exponent_nonneg hker hu huv ω
  have h2 := exponent_nonneg hker le_rfl hu ω
  linarith

/-- **`lem:no-lattice`.**

Under (A1)–(A8) and (ND), for every `t > 0` the kernel `μ_{0,t}` is carried by no lattice `pℤ`
with `p > 0`; equivalently `G(t,ω) > 0` for every `ω ≠ 0`.

Class (c). -/
theorem no_lattice (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    (∀ p : ℝ, 0 < p → (μ 0 t) {x : ℝ | ∃ n : ℤ, x = p * n}ᶜ ≠ 0) ∧
      (∀ ω : ℝ, ω ≠ 0 → 0 < exponent (μ 0 t) ω) := by
  haveI := hker.isProbability 0 t le_rfl ht.le
  -- The zero set of `G(t,·)` is `{0}`.
  have hzero : {ω : ℝ | exponent (μ 0 t) ω = 0} = {0} := by
    rcases (monotonicity_zero_set Fam μ hker hnd le_rfl ht).2.2 with h0 | ⟨c, hc, hcset⟩
    · exact h0
    exfalso
    -- The ratio `3/2` is neither an integer nor the reciprocal of one.
    set lam : ℝ := 3 / 2 with hlamdef
    have hlam : (0:ℝ) < lam := by norm_num
    have hlamI : lam ∈ Ioi (0:ℝ) := hlam
    set t' : ℝ := S lam t with ht'def
    have ht' : 0 < t' := hcov.S_pos hlam hlamI ht
    -- `ω ∈ N_{t'} ↔ λω ∈ N_t`
    have hsim : ∀ ω : ℝ, exponent (μ 0 t') ω = exponent (μ 0 t) (lam * ω) := fun ω =>
      covariance_similarity Fam μ hker S hcov lam t ω hlam ht.le
    rcases le_total t t' with hle | hle
    · -- `N_{t'} ⊆ N_t`; the generator `c/λ` of `N_{t'}` lands in `cℤ`
      have hmem : (c / lam) ∈ {ω : ℝ | exponent (μ 0 t') ω = 0} := by
        simp only [mem_setOf_eq, hsim]
        have : lam * (c / lam) = c := by field_simp
        rw [this]
        have : c ∈ {ω : ℝ | exponent (μ 0 t) ω = 0} := by
          rw [hcset]; exact ⟨1, by norm_num⟩
        exact this
      have := zeroSet_chain hker ht.le hle hmem
      rw [hcset] at this
      obtain ⟨n, hn⟩ := this
      have hc' : c ≠ 0 := hc.ne'
      have h23 : (2:ℝ) = 3 * n := by
        have : c / lam = c * n := hn
        rw [hlamdef] at this
        field_simp at this
        linarith
      have : (2:ℤ) = 3 * n := by exact_mod_cast h23
      omega
    · -- `N_t ⊆ N_{t'}`; the generator `c` of `N_t` puts `λc` in `cℤ`
      have hmem : c ∈ {ω : ℝ | exponent (μ 0 t) ω = 0} := by rw [hcset]; exact ⟨1, by norm_num⟩
      have hmem' := zeroSet_chain hker ht'.le hle hmem
      simp only [mem_setOf_eq, hsim] at hmem'
      have : (lam * c) ∈ {ω : ℝ | exponent (μ 0 t) ω = 0} := hmem'
      rw [hcset] at this
      obtain ⟨n, hn⟩ := this
      have hc' : c ≠ 0 := hc.ne'
      have h32 : (3:ℝ) = 2 * n := by
        have hn' : lam * c = c * n := hn
        rw [hlamdef] at hn'
        field_simp at hn'
        linarith
      have : (3:ℤ) = 2 * n := by exact_mod_cast h32
      omega
  constructor
  · -- carried by no lattice
    intro p hp hcon
    have hae : ∀ᵐ x ∂(μ 0 t), ∃ n : ℤ, x = p * n := by
      rw [ae_iff]
      exact hcon
    have h1 : charFun (μ 0 t) (2 * Real.pi / p) = 1 := by
      rw [charFun_eq_one_iff]
      filter_upwards [hae] with x hx
      obtain ⟨n, rfl⟩ := hx
      have hrw : 2 * Real.pi / p * (p * n) = (n : ℝ) * (2 * Real.pi) := by
        field_simp
      rw [hrw]
      exact Real.cos_int_mul_two_pi n
    have hmem : (2 * Real.pi / p) ∈ {ω : ℝ | exponent (μ 0 t) ω = 0} := by
      rw [exponent_zero_set hker le_rfl ht.le]
      exact h1
    rw [hzero] at hmem
    have : 2 * Real.pi / p = 0 := hmem
    have hpi : (0:ℝ) < 2 * Real.pi / p := by positivity
    linarith
  · -- strict positivity off the origin
    intro ω hω
    have hne : exponent (μ 0 t) ω ≠ 0 := by
      intro hcon
      have : ω ∈ {ω : ℝ | exponent (μ 0 t) ω = 0} := hcon
      rw [hzero] at this
      exact hω this
    exact lt_of_le_of_ne (exponent_nonneg hker le_rfl ht.le ω) (Ne.symm hne)

end SpatialLine
