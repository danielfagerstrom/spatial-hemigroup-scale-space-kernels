/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TransformUniqueness
import SpatialLine.ProfileIntegrability
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# The zero set of a symmetric exponent is a closed subgroup

Blueprint: `lem:lattice-zero` (`blueprint/src/parts/02-preliminaries.tex`), the draft's Remark
2.4 promoted to a node because three later proofs turn on it.

This is the single most consequential difference between the spatial and the causal
developments. The causal vanishing lemma
(`Hemigroup.levyExponent_eq_zero_of_eq_zero`) says that an exponent vanishing at one interior
point vanishes identically; on the line that is **false**, and the last declaration here is what
records it: the symmetric compound Poisson exponent `c(1 - cos ω)` is a symmetric Lévy exponent
whose law is carried by `ℤ`. The exclusion of lattices must therefore come from elsewhere, and
it comes from covariance (`lem:no-lattice`).

The zero set is written `{ω | charFun μ ω = 1}` throughout, matching the blueprint's `N(μ)`.
Everything rests on `charFun_eq_one_iff`: for a probability measure, the transform takes the
value `1` exactly where `cos(ωx) = 1` holds `μ`-almost everywhere. That the almost-everywhere
quantifier is over `μ` and not over Lebesgue measure is the point of the node.

Proving campaign, chapter 2 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## When the transform takes the value one -/

/-- Where the cosine is `1` the sine vanishes. -/
theorem sin_eq_zero_of_cos_eq_one {θ : ℝ} (h : Real.cos θ = 1) : Real.sin θ = 0 := by
  have hpy := Real.sin_sq_add_cos_sq θ
  nlinarith [hpy, h]

/-- **The key equivalence.** For a probability measure on `ℝ` the characteristic function takes
the value `1` at `ω` exactly when `cos(ωx) = 1` for `μ`-almost every `x`.

`Re(1 - e^{iωx}) = 1 - cos ωx ≥ 0`, so `μ̂(ω) = 1` forces the integral of a nonnegative function
to vanish; conversely `cos(ωx) = 1` forces `sin(ωx) = 0` and hence `e^{iωx} = 1`. -/
theorem charFun_eq_one_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (ω : ℝ) :
    charFun μ ω = 1 ↔ ∀ᵐ x ∂μ, Real.cos (ω * x) = 1 := by
  constructor
  · intro h
    have hre : fourierCos μ ω = 1 := by
      rw [fourierCos_eq_charFun_re, h]; simp
    have hz : ∫ x, (1 - Real.cos (ω * x)) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) (integrable_cos_mul μ ω)]
      rw [← fourierCos_apply, hre]
      simp
    have hnn : (0 : ℝ → ℝ) ≤ fun x : ℝ => 1 - Real.cos (ω * x) := fun x => by
      simpa using Real.cos_le_one (ω * x)
    have hI : Integrable (fun x : ℝ => 1 - Real.cos (ω * x)) μ :=
      (integrable_const 1).sub (integrable_cos_mul μ ω)
    have := (integral_eq_zero_iff_of_nonneg hnn hI).mp hz
    filter_upwards [this] with x hx
    have : 1 - Real.cos (ω * x) = 0 := hx
    linarith
  · intro h
    have hexp : ∀ᵐ x : ℝ ∂μ, Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) = 1 := by
      filter_upwards [h] with x hx
      have hcast : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]
      refine Complex.ext ?_ ?_
      · rw [Complex.exp_ofReal_mul_I_re, hx]; simp
      · rw [Complex.exp_ofReal_mul_I_im, sin_eq_zero_of_cos_eq_one hx]; simp
    rw [charFun_apply_real, integral_congr_ae hexp]
    simp

/-! ## The subgroup and its classification -/

/-- **`lem:lattice-zero`, the subgroup clause.** `N(μ)` is a closed additive subgroup of `ℝ`.

Rendered as: there is an `AddSubgroup ℝ` whose carrier is closed and equals `N(μ)`. Stating it
this way is what lets the trichotomy below quote Mathlib's classification of the subgroups of a
linearly ordered archimedean group. -/
theorem lattice_zero_isClosedSubgroup (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ H : AddSubgroup ℝ, IsClosed (H : Set ℝ) ∧ (H : Set ℝ) = {ω : ℝ | charFun μ ω = 1} := by
  have hzero : charFun μ 0 = 1 := by simp
  have hadd : ∀ a b : ℝ, charFun μ a = 1 → charFun μ b = 1 → charFun μ (a + b) = 1 := by
    intro a b ha hb
    rw [charFun_eq_one_iff] at ha hb ⊢
    filter_upwards [ha, hb] with x hxa hxb
    rw [add_mul, Real.cos_add, hxa, hxb, sin_eq_zero_of_cos_eq_one hxa,
      sin_eq_zero_of_cos_eq_one hxb]
    ring
  have hneg : ∀ a : ℝ, charFun μ a = 1 → charFun μ (-a) = 1 := by
    intro a ha
    rw [charFun_eq_one_iff] at ha ⊢
    filter_upwards [ha] with x hx
    rw [neg_mul, Real.cos_neg, hx]
  refine ⟨{ carrier := {ω : ℝ | charFun μ ω = 1}
            zero_mem' := hzero
            add_mem' := fun {a b} ha hb => hadd a b ha hb
            neg_mem' := fun {a} ha => hneg a ha }, ?_, rfl⟩
  exact isClosed_eq continuous_charFun continuous_const

/-- **`lem:lattice-zero`, the trichotomy.** `N(μ)` is `{0}`, a lattice `cℤ` with `c > 0`, or all
of `ℝ`.

Mathlib's `AddSubgroup.dense_or_cyclic` is directly usable, and the dense case collapses because
`N(μ)` is closed; the estimate that this could cost **L** was pessimistic. -/
theorem lattice_zero_trichotomy (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    {ω : ℝ | charFun μ ω = 1} = {0}
      ∨ (∃ c : ℝ, 0 < c ∧ {ω : ℝ | charFun μ ω = 1} = {x : ℝ | ∃ n : ℤ, x = c * n})
      ∨ {ω : ℝ | charFun μ ω = 1} = univ := by
  obtain ⟨H, hclosed, hcarrier⟩ := lattice_zero_isClosedSubgroup μ
  rw [← hcarrier]
  have hgen : ∀ b : ℝ, (AddSubgroup.zmultiples b : Set ℝ) = {x : ℝ | ∃ n : ℤ, x = b * n} := by
    intro b
    ext y
    simp only [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff, mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [← hk, zsmul_eq_mul]; ring⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hn, zsmul_eq_mul]; ring⟩
  rcases AddSubgroup.dense_or_cyclic H with hdense | ⟨a, ha⟩
  · exact Or.inr (Or.inr (by rw [← hclosed.closure_eq, hdense.closure_eq]))
  · have hswap : (AddSubgroup.zmultiples a : Set ℝ)
        = (AddSubgroup.zmultiples (-a) : Set ℝ) := by
      rw [hgen, hgen]
      ext y
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨-n, by push_cast; ring⟩
      · rintro ⟨n, rfl⟩; exact ⟨-n, by push_cast; ring⟩
    rcases eq_or_ne a 0 with rfl | hane
    · left
      rw [ha, ← AddSubgroup.zmultiples_eq_closure, hgen]
      ext y
      simp
    · right; left
      refine ⟨|a|, abs_pos.mpr hane, ?_⟩
      rw [ha, ← AddSubgroup.zmultiples_eq_closure]
      rcases abs_choice a with h | h
      · rw [h, hgen]
      · rw [h, hswap, hgen]

/-- **`lem:lattice-zero`, the degenerate case.** `N(μ) = ℝ` exactly when `μ = δ₀`. -/
theorem lattice_zero_eq_univ_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    {ω : ℝ | charFun μ ω = 1} = univ ↔ μ = Measure.dirac 0 := by
  constructor
  · intro h
    refine fourier_uniqueness fun ω => ?_
    have hω : charFun μ ω = 1 := by
      have : ω ∈ {ω : ℝ | charFun μ ω = 1} := by rw [h]; trivial
      exact this
    rw [hω, charFun_apply_real]
    simp
  · rintro rfl
    ext ω
    simp only [mem_setOf_eq, mem_univ, iff_true, charFun_apply_real]
    simp

/-! ## The two equivalences at a nonzero frequency -/

/-- `cos(ω₀u) = 1` describes the lattice `(2π/|ω₀|)ℤ`.

The set equality alone, with no measure in sight. It is the geometric half of
`lattice_zero_mem_iff` below, and it is stated separately because chapter 9 reads it at the
Choquet measure `ϖ` of `prop:bridge-strictness`(3), which is not a probability measure
(`SpatialLine/Strictness.lean`). Lifted here by wave 4's merge (2026-09-10): the fact belongs
to `lem:lattice-zero`, which is this file's node. -/
theorem setOf_cos_eq_one {ω₀ : ℝ} (hω₀ : ω₀ ≠ 0) :
    {u : ℝ | Real.cos (ω₀ * u) = 1} = {u : ℝ | ∃ n : ℤ, u = 2 * Real.pi / |ω₀| * n} := by
  have hab : |ω₀| ≠ 0 := abs_ne_zero.mpr hω₀
  ext x
  simp only [mem_setOf_eq, Real.cos_eq_one_iff]
  have hsign : (∃ n : ℤ, (n : ℝ) * (2 * Real.pi) = ω₀ * x)
      ↔ ∃ n : ℤ, (n : ℝ) * (2 * Real.pi) = |ω₀| * x := by
    rcases abs_choice ω₀ with h | h
    · rw [h]
    · rw [h]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨-n, by push_cast; linear_combination -hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨-n, by push_cast; linear_combination -hn⟩
  rw [hsign]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hab]
    linear_combination -hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    field_simp

/-- **`lem:lattice-zero`, the two equivalences at a nonzero frequency.**

"Carried by the lattice `(2π/|ω₀|)ℤ`" is `μ` of the complement being zero — the honest reading,
since `μ` is a measure on `ℝ` and the lattice is a Lebesgue-null set. The almost-everywhere
quantifier in the middle condition is over `μ`, not over Lebesgue measure. -/
theorem lattice_zero_mem_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] {ω₀ : ℝ} (hω₀ : ω₀ ≠ 0) :
    (charFun μ ω₀ = 1 ↔ ∀ᵐ x ∂μ, Real.cos (ω₀ * x) = 1)
      ∧ (charFun μ ω₀ = 1 ↔ μ {x : ℝ | ∃ n : ℤ, x = 2 * Real.pi / |ω₀| * n}ᶜ = 0) := by
  refine ⟨charFun_eq_one_iff μ ω₀, ?_⟩
  rw [charFun_eq_one_iff, ae_iff, ← setOf_cos_eq_one hω₀, compl_setOf]

/-! ## The exponent form -/

/-- **`lem:lattice-zero`, the exponent form.** A symmetric exponent vanishes at a frequency
exactly when the transform of its law takes the value `1` there — so it vanishes at a nonzero
frequency exactly when its law is a lattice law. -/
theorem lattice_zero_exponent (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsym : IsSymmetric μ)
    {ψ : ℝ → ℝ} (hψ : IsSymNegDef ψ) (h : ∀ ω, fourierCos μ ω = Real.exp (-ψ ω)) :
    {ω : ℝ | charFun μ ω = 1} = {ω : ℝ | ψ ω = 0} := by
  ext ω
  simp only [mem_setOf_eq]
  rw [charFun_eq_fourierCos_of_symmetric hsym, h ω]
  constructor
  · intro hx
    have h1 : Real.exp (-ψ ω) = Real.exp 0 := by
      rw [Real.exp_zero]; exact_mod_cast hx
    have := Real.exp_eq_exp.mp h1
    linarith
  · intro hx
    rw [hx]
    norm_num

/-! ## The example: an infinitely divisible lattice law -/

/-- **`lem:lattice-zero`, the example (membership).** The symmetric compound Poisson exponent
`c(1 - cos ω)` is a symmetric Lévy exponent: the pair is `(0, c δ₁)`. -/
theorem lattice_zero_example_mem (c : ℝ) (hc : 0 ≤ c) :
    IsSymLevyExponent fun ω => c * (1 - Real.cos ω) := by
  have hfolded : IsFolded (ENNReal.ofReal c • Measure.dirac (1 : ℝ)) := by
    show (ENNReal.ofReal c • Measure.dirac (1 : ℝ)) (Iic 0) = 0
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic]
    simp
  have hintegrable :
      ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(ENNReal.ofReal c • Measure.dirac (1 : ℝ)) ≠ ⊤ := by
    rw [lintegral_smul_measure, lintegral_dirac' _ (by fun_prop)]
    simp
  refine ⟨⟨0, ENNReal.ofReal c • Measure.dirac (1 : ℝ), le_rfl, hfolded, hintegrable⟩, fun ω => ?_⟩
  have hL : SymLevyPair.exponentL
      ⟨0, ENNReal.ofReal c • Measure.dirac (1 : ℝ), le_rfl, hfolded, hintegrable⟩ ω
      = ENNReal.ofReal (c * (1 - Real.cos ω)) := by
    rw [SymLevyPair.exponentL]
    simp only [zero_mul, ENNReal.ofReal_zero, zero_add]
    rw [lintegral_smul_measure, lintegral_dirac' _ (by fun_prop), mul_one, smul_eq_mul,
      ← ENNReal.ofReal_mul hc]
  rw [SymLevyPair.exponent, hL,
    ENNReal.toReal_ofReal (by nlinarith [Real.cos_le_one ω, hc])]

/-- **`lem:lattice-zero`, the example (its law is a lattice law).** Any probability measure whose
cosine transform is `e^{-c(1-cos ω)}` is carried by `ℤ` — so membership of `NDₛ` does not exclude
lattice laws, which is what the node exists to record.

The law is *not constructed*; it is quantified over. That is legitimate because such a measure is
unique (`prop:fourier-uniqueness`), and it keeps the compound Poisson construction out of the
development. The argument runs through the transform alone, at `ω₀ = 2π`. -/
theorem lattice_zero_example_lattice (c : ℝ) (hc : 0 < c) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (h : ∀ ω, fourierCos μ ω = Real.exp (-(c * (1 - Real.cos ω)))) :
    μ {x : ℝ | ∃ n : ℤ, x = (n : ℝ)}ᶜ = 0 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : 2 * Real.pi ≠ 0 := ne_of_gt hpi
  -- The transform is real and equal to `1` at `ω₀ = 2π`.
  have hcos : Real.cos (2 * Real.pi) = 1 := by
    rw [Real.cos_two_pi]
  have hval : fourierCos μ (2 * Real.pi) = 1 := by
    rw [h, hcos]; simp
  -- A probability measure's transform has modulus at most `1`, so a real part of `1` forces `1`.
  have hchar : charFun μ (2 * Real.pi) = 1 := by
    have hre : (charFun μ (2 * Real.pi)).re = 1 := by
      rw [← fourierCos_eq_charFun_re, hval]
    have hnorm : ‖charFun μ (2 * Real.pi)‖ ≤ 1 := norm_charFun_le_one _
    have him : (charFun μ (2 * Real.pi)).im = 0 := by
      set z : ℂ := charFun μ (2 * Real.pi) with hzdef
      have hsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      have h0 : z.im * z.im ≤ 0 := by nlinarith [hsq, hre, hnorm, norm_nonneg z]
      exact mul_self_eq_zero.mp (le_antisymm h0 (mul_self_nonneg z.im))
    exact Complex.ext (by simpa using hre) (by simpa using him)
  have := ((lattice_zero_mem_iff μ hne).2).mp hchar
  have hnorm : |2 * Real.pi| = 2 * Real.pi := abs_of_pos hpi
  rw [hnorm, div_self hne] at this
  simpa using this

end SpatialLine
