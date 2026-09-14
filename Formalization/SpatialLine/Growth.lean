/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Exponent

/-!
# Quadratic growth of a symmetric Lévy exponent

Blueprint: `lem:quadratic-growth` (`blueprint/src/parts/02-preliminaries.tex`). The node
**reroutes** a ledger candidate — Jacob Vol. I, Lemma 3.6.22, the growth bound for a continuous
negative definite function — because the bound is three lines from the truncation split of
`eq:levy-khintchine` and needs nothing classical.

The statement is in `ℝ≥0∞`, so the bound *implies* finiteness of the exponent rather than
presupposing it; that is what lets `SymLevyPair` carry no finiteness field.
`SymLevyPair.exponentL_ne_top` below is the corollary that makes `SymLevyPair.exponent`, a
`.toReal`, faithful to `eq:levy-khintchine`, and every statement of this development that reads
an exponent as a real number rests on it.

Proving campaign, chapter 2 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter Asymptotics
open scoped ENNReal Topology

namespace SymLevyPair

/-! ## The two pieces of the constant are finite -/

/-- The near-origin half of the constant of `lem:quadratic-growth` is finite: on `(0,1]` the
integrand `x²/2` is dominated by `1 ∧ x²`, whose integral is a field of the structure. -/
theorem lintegral_sq_div_two_ne_top (P : SymLevyPair) :
    (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν) ≠ ⊤ := by
  refine ne_top_of_le_ne_top P.ν_integrable ?_
  calc (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
      ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
        rw [min_eq_right hx1]
        nlinarith [sq_nonneg x]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := setLIntegral_le_lintegral _ _

/-- The far half of the constant is finite: on `(1,∞)` the constant `1` is exactly `1 ∧ x²`. -/
theorem measure_Ioi_one_ne_top (P : SymLevyPair) : P.ν (Ioi (1 : ℝ)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top P.ν_integrable ?_
  calc P.ν (Ioi (1 : ℝ))
      = ∫⁻ _ in Ioi (1 : ℝ), 1 ∂P.ν := by
        rw [lintegral_one, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
        have hx' : (1 : ℝ) < x := hx
        have hx1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith [hx']
        rw [min_eq_left hx1, ENNReal.ofReal_one]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := setLIntegral_le_lintegral _ _

/-! ## The bound -/

/-- **`lem:quadratic-growth`.** The constant
`C = a + ½∫_{(0,1]} x² ν + 2 ν((1,∞))` is finite, and `ψ(ω) ≤ C(1 + ω²)` for every `ω`.

The proof is the truncation split of `eq:levy-khintchine` at `x = 1`: below it
`1 - cos ωx ≤ ω²x²/2`, above it `1 - cos ωx ≤ 2`. -/
theorem quadratic_growth (P : SymLevyPair) :
    (ENNReal.ofReal P.a + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
        + 2 * P.ν (Ioi 1)) ≠ ⊤ ∧
      ∀ ω : ℝ, P.exponentL ω
        ≤ (ENNReal.ofReal P.a + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
            + 2 * P.ν (Ioi 1)) * ENNReal.ofReal (1 + ω ^ 2) := by
  set I : ℝ≥0∞ := ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν with hI
  set J : ℝ≥0∞ := P.ν (Ioi 1) with hJ
  have hIne : I ≠ ⊤ := P.lintegral_sq_div_two_ne_top
  have hJne : J ≠ ⊤ := P.measure_Ioi_one_ne_top
  refine ⟨by finiteness, fun ω => ?_⟩
  -- The Lévy measure is carried by `(0,∞)`, which splits as `(0,1] ∪ (1,∞)`.
  have hres : P.ν.restrict (Ioi (0 : ℝ)) = P.ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have hc : P.ν {a : ℝ | a ≤ 0} = 0 := P.ν_folded
    rw [ae_iff]
    simpa using hc
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hint : (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
      = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
        + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := by
    conv_lhs => rw [← hres]
    rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  -- Below the truncation: `1 - cos ωx ≤ ω²·(x²/2)`.
  have hnear : (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
      ≤ ENNReal.ofReal (ω ^ 2) * I := by
    rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun x _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcos := Real.one_sub_sq_div_two_le_cos (x := ω * x)
    nlinarith [hcos]
  -- Above it: `1 - cos ωx ≤ 2`.
  have hfar : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν) ≤ 2 * J := by
    calc (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
        ≤ ∫⁻ _ in Ioi (1 : ℝ), (2 : ℝ≥0∞) ∂P.ν := by
          refine setLIntegral_mono' measurableSet_Ioi fun x _ => ?_
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
            rw [ENNReal.ofReal_ofNat]
          rw [h2]
          exact ENNReal.ofReal_le_ofReal (by linarith [Real.neg_one_le_cos (ω * x)])
      _ = 2 * J := by rw [setLIntegral_const, hJ]
  -- Assemble, comparing each term with its share of `C (1 + ω²)`.
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ω ^ 2) :=
    ENNReal.one_le_ofReal.mpr (by nlinarith [sq_nonneg ω])
  have hsq : ENNReal.ofReal (ω ^ 2) ≤ ENNReal.ofReal (1 + ω ^ 2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hgauss : ENNReal.ofReal (P.a * ω ^ 2) ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2) := by
    rw [ENNReal.ofReal_mul P.a_nonneg]
    gcongr
  calc P.exponentL ω
      = ENNReal.ofReal (P.a * ω ^ 2) + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := rfl
    _ ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2)
        + (ENNReal.ofReal (ω ^ 2) * I + 2 * J) := by
        rw [hint]; exact add_le_add hgauss (add_le_add hnear hfar)
    _ ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2)
        + (I * ENNReal.ofReal (1 + ω ^ 2) + 2 * J * ENNReal.ofReal (1 + ω ^ 2)) := by
        refine add_le_add le_rfl (add_le_add ?_ ?_)
        · rw [mul_comm]
          gcongr
        · calc 2 * J = 2 * J * 1 := (mul_one _).symm
            _ ≤ 2 * J * ENNReal.ofReal (1 + ω ^ 2) := by gcongr
    _ = (ENNReal.ofReal P.a + I + 2 * J) * ENNReal.ofReal (1 + ω ^ 2) := by
        rw [add_mul, add_mul, add_assoc]

/-- **`lem:quadratic-growth`, the corollary that makes `exponent` faithful.** The exponent of a
pair is finite at every frequency, so `SymLevyPair.exponent`, a `.toReal`, is the real number
`eq:levy-khintchine` writes.

Helper, named by no node. -/
theorem exponentL_ne_top (P : SymLevyPair) (ω : ℝ) : P.exponentL ω ≠ ⊤ := by
  obtain ⟨hC, hbound⟩ := P.quadratic_growth
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hbound ω)

/-- **`lem:quadratic-growth`, the `O(ω²)` clause.** Stated for the real-valued exponent, which is
where the asymptotic is used (`cor:semigroup-case` compares `|ω|^α` with `C(1+ω²)` as real
numbers); `|ω| → ∞` is the cocompact filter on `ℝ`. -/
theorem quadratic_growth_isBigO (P : SymLevyPair) :
    (fun ω => P.exponent ω) =O[cocompact ℝ] fun ω : ℝ => ω ^ 2 := by
  obtain ⟨hC, hbound⟩ := P.quadratic_growth
  set C : ℝ≥0∞ := ENNReal.ofReal P.a + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
    + 2 * P.ν (Ioi 1) with hCdef
  refine isBigO_iff.mpr ⟨2 * C.toReal, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (1 : ℝ)] with ω hω
  have hω1 : (1 : ℝ) ≤ |ω| := by simpa [Real.norm_eq_abs] using hω
  have hsq : (1 : ℝ) ≤ ω ^ 2 := by nlinarith [hω1, abs_nonneg ω, sq_abs ω]
  have hle : P.exponent ω ≤ C.toReal * (1 + ω ^ 2) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hbound ω)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by nlinarith [sq_nonneg ω])] at h
  have hnn : 0 ≤ P.exponent ω := ENNReal.toReal_nonneg
  have hCnn : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (sq_nonneg ω)]
  nlinarith [hle, hCnn, hsq]

end SymLevyPair

end SpatialLine
