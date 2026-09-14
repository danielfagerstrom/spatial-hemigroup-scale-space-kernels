/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Growth
import SpatialLine.ProfileIntegrability

/-!
# Continuity of a symmetric Lévy exponent, on Lean core

Blueprint: not a node. This is the one property of `eq:levy-khintchine` that the development
reads off the representation rather than off `def:symmetric-negdef`, and it is separated here
because the route through the definition is not free: `IsSymNegDef` carries continuity as a
field, and the only way this library reaches that structure from a pair is
`profile_integrability_mem`, which spends ledger **A3**. Every consumer of continuity that is
otherwise `[T]` — the uniqueness clause of `thm:main-characterization`, and
`prop:strict-positivity`(2) through `lem:dilation-invariance` — would then carry an axiom for a
fact that dominated convergence gives outright.

The bound is the truncation of `lem:quadratic-growth` read with the frequency in a bounded
neighbourhood: for `|ω| ≤ M`,
`1 - cos(ωx) ≤ 2(1 ∨ M²)(1 ∧ x²)`,
whose `ν`-integral is finite by the Lévy condition, which is a field of `SymLevyPair`. So
`ω ↦ ∫ (1 - cos ωx) ν(dx)` is continuous by dominated convergence in `ℝ≥0∞`, the Gaussian term
is a polynomial, and `lem:quadratic-growth` makes the sum finite, so the `.toReal` is continuous
too.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SymLevyPair

/-- **The truncation bound with the frequency in a bounded set.** For `|ω| ≤ M`,
`1 - cos(ωx) ≤ 2(1 ∨ M²)(1 ∧ x²)`: the two regimes of the truncation, `1 - cos θ ≤ θ²/2` near
the origin and `1 - cos θ ≤ 2` beyond it. -/
theorem one_sub_cos_mul_le {M ω x : ℝ} (hω : |ω| ≤ M) :
    1 - Real.cos (ω * x) ≤ 2 * max 1 (M ^ 2) * min 1 (x ^ 2) := by
  have hq : 1 - Real.cos (ω * x) ≤ (ω * x) ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ω * x)]
  have hb : 1 - Real.cos (ω * x) ≤ 2 := by
    nlinarith [Real.neg_one_le_cos (ω * x)]
  have hωM : ω ^ 2 ≤ M ^ 2 := by
    have h1 : |ω| ≤ M := hω
    have h2 : (0 : ℝ) ≤ M := le_trans (abs_nonneg ω) hω
    nlinarith [sq_abs ω, abs_nonneg ω]
  have hmax : ω ^ 2 ≤ max 1 (M ^ 2) := le_trans hωM (le_max_right _ _)
  have hmax1 : (1 : ℝ) ≤ max 1 (M ^ 2) := le_max_left _ _
  rcases le_total (x ^ 2) 1 with h | h
  · rw [min_eq_right h]
    nlinarith [sq_nonneg x, sq_nonneg ω]
  · rw [min_eq_left h]
    nlinarith

/-- The `ℝ≥0∞` jump term of `eq:levy-khintchine` is measurable in the space variable. -/
theorem measurable_one_sub_cos (ω : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.cos (ω * x)) :=
  (measurable_const.sub
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable)).ennreal_ofReal

/-- **The jump term is continuous in the frequency**, by dominated convergence in `ℝ≥0∞`. -/
theorem continuous_jump (P : SymLevyPair) :
    Continuous fun ω : ℝ => ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := by
  refine continuous_iff_continuousAt.2 fun ω₀ => ?_
  set M : ℝ := |ω₀| + 1 with hM
  have hMnn : (0 : ℝ) ≤ 2 * max 1 (M ^ 2) := by positivity
  refine tendsto_lintegral_filter_of_dominated_convergence
    (bound := fun x => ENNReal.ofReal (2 * max 1 (M ^ 2) * min 1 (x ^ 2)))
    (Filter.Eventually.of_forall fun ω => measurable_one_sub_cos ω) ?_ ?_ ?_
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds ω₀ one_pos) fun ω hω => ?_
    have habs : |ω| ≤ M := by
      have : |ω - ω₀| < 1 := by simpa [Real.dist_eq] using hω
      have := abs_sub_abs_le_abs_sub ω ω₀
      simp only [hM]
      linarith [abs_sub_abs_le_abs_sub ω ω₀]
    exact Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_le_ofReal (one_sub_cos_mul_le habs)
  · have hsplit : ∀ x : ℝ, ENNReal.ofReal (2 * max 1 (M ^ 2) * min 1 (x ^ 2))
        = ENNReal.ofReal (2 * max 1 (M ^ 2)) * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
      rw [ENNReal.ofReal_mul hMnn]
    simp only [hsplit]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.ν_integrable
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_id.mul continuous_const))).tendsto ω₀)

/-- **`eq:levy-khintchine` is continuous in the frequency**, as an `ℝ≥0∞`-valued function. -/
theorem continuous_exponentL (P : SymLevyPair) : Continuous P.exponentL := by
  have h1 : Continuous fun ω : ℝ => ENNReal.ofReal (P.a * ω ^ 2) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))
  exact h1.add P.continuous_jump

/-- **The exponent of a symmetric Lévy pair is continuous.** `#print axioms` reduces to Lean
core: the finiteness is `lem:quadratic-growth` and the limit is dominated convergence, so
`prop:fourier-toolbox`(3) is not spent. -/
theorem continuous_exponent (P : SymLevyPair) : Continuous P.exponent := by
  refine continuous_iff_continuousAt.2 fun ω => ?_
  exact (ENNReal.tendsto_toReal (P.exponentL_ne_top ω)).comp
    (P.continuous_exponentL.continuousAt)

end SymLevyPair

/-- **The exponent of an admissible profile is continuous**, `eq:sd-profile` being
`eq:levy-khintchine` at the pair `lem:profile-integrability` produces. -/
theorem SDProfile.continuous_exponent (P : SDProfile) : Continuous P.exponent := by
  obtain ⟨Q, -, -, hQ⟩ := profile_integrability_pair P
  simpa [funext hQ] using Q.continuous_exponent

end SpatialLine
