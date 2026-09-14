/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.SelfDecomposable
import SpatialLine.Interfaces
import SpatialLine.Growth

/-!
# The dilation identity read backwards

Blueprint: the first half of the (1) implies (3) direction of
`lem:selfdecomposable-exponents`, `blueprint/src/parts/07-characterization.tex`, up to and
including `eq:dilation-decrease`.

## What is here, and what is not

The analysis direction of the chapter has two halves that do not resemble each other. The first
is the one this file proves: from "every dilation increment is a symmetric Levy exponent" to

  `D_c nu <= nu` for every `c` in `(0,1)`,

where `D_c nu` is the image of the Levy measure under `x |-> c x`. That is a statement about
measures, and it is where the **uniqueness clause of `prop:fourier-toolbox`(3)** (ledger A3) is
spent -- once, and the only time this chapter spends it. The proof is bookkeeping around the
axiom: the dilate of a symmetric Levy pair is a symmetric Levy pair (the Levy condition
transfers by `min_one_sq_mul_le`, the same truncation comparison the (3) implies (1) direction
needed), the sum of two is a symmetric Levy pair, and the increment supplied by the hypothesis
plus the dilate has the same exponent as the original pair.

The second half -- from `D_c nu <= nu` to `nu(dx) = k(x)x^{-1}dx` with `k` nonincreasing -- is
**not** proved here, and the honest statement of what remains is worth recording because it is
much smaller than the chapter's prose suggests. In the log-displacement coordinate
`theta = log x` the conclusion of this file says exactly that the image measure `m` of `nu` under
`log` **decreases under every right translation**, and what is wanted is that such a measure has
a nonincreasing density. Nothing else about `nu` is used. See the module note below and the
skeleton's annotation at `sd_exponents_one_implies_three` for the cost of that step.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The dilate and the sum of symmetric Lévy pairs -/

/-- **The dilate of a symmetric Lévy pair.** The image of the Lévy measure under `x ↦ cx`,
with Gaussian coefficient `c²a`, is again a symmetric Lévy pair, and its exponent is `F(c·)`.

The Lévy condition is the truncation comparison `min_one_sq_mul_le`, exactly as in the
(3) ⟹ (1) direction; there it was applied to a dilated *profile*, here to a dilated measure. -/
theorem symLevyPair_dilate (P : SymLevyPair) {c : ℝ} (hc : 0 < c) :
    ∃ R : SymLevyPair, R.ν = Measure.map (fun x : ℝ => c * x) P.ν ∧
      ∀ ω, R.exponentL ω = P.exponentL (c * ω) := by
  have hmeas : Measurable fun x : ℝ => c * x := measurable_const_mul c
  have hmap : ∀ g : ℝ → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x ∂(Measure.map (fun x : ℝ => c * x) P.ν)) = ∫⁻ x, g (c * x) ∂P.ν := by
    intro g hg
    rw [lintegral_map hg hmeas]
  have hfold : IsFolded (Measure.map (fun x : ℝ => c * x) P.ν) := by
    rw [IsFolded, Measure.map_apply hmeas measurableSet_Iic]
    have hpre : (fun x : ℝ => c * x) ⁻¹' Iic (0 : ℝ) = Iic (0 : ℝ) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      constructor
      · intro hx
        nlinarith
      · intro hx
        nlinarith
    rw [hpre]
    exact P.ν_folded
  have hint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(Measure.map (fun x : ℝ => c * x) P.ν))
      ≠ ⊤ := by
    rw [hmap _ (by fun_prop)]
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal (max 1 (c ^ 2))) ENNReal.ofReal_ne_top
        P.ν_integrable) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 (c ^ 2)))]
    exact ENNReal.ofReal_le_ofReal (min_one_sq_mul_le c x)
  refine ⟨⟨c ^ 2 * P.a, Measure.map (fun x : ℝ => c * x) P.ν,
    mul_nonneg (sq_nonneg c) P.a_nonneg, hfold, hint⟩, rfl, fun ω => ?_⟩
  rw [SymLevyPair.exponentL, SymLevyPair.exponentL, hmap _ (by fun_prop),
    show c ^ 2 * P.a * ω ^ 2 = P.a * (c * ω) ^ 2 from by ring]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [show ω * (c * x) = c * ω * x from by ring]

/-- **The sum of two symmetric Lévy pairs**, with the exponents adding. -/
theorem symLevyPair_add (P R : SymLevyPair) :
    ∃ S : SymLevyPair, S.ν = P.ν + R.ν ∧
      ∀ ω, S.exponentL ω = P.exponentL ω + R.exponentL ω := by
  have hfold : IsFolded (P.ν + R.ν) := by
    rw [IsFolded, Measure.coe_add, Pi.add_apply, P.ν_folded, R.ν_folded, add_zero]
  have hint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(P.ν + R.ν)) ≠ ⊤ := by
    rw [lintegral_add_measure]
    exact ENNReal.add_ne_top.mpr ⟨P.ν_integrable, R.ν_integrable⟩
  refine ⟨⟨P.a + R.a, P.ν + R.ν, add_nonneg P.a_nonneg R.a_nonneg, hfold, hint⟩, rfl, fun ω => ?_⟩
  rw [SymLevyPair.exponentL, SymLevyPair.exponentL, SymLevyPair.exponentL, lintegral_add_measure,
    show (P.a + R.a) * ω ^ 2 = P.a * ω ^ 2 + R.a * ω ^ 2 by ring,
    ENNReal.ofReal_add (mul_nonneg P.a_nonneg (sq_nonneg ω))
      (mul_nonneg R.a_nonneg (sq_nonneg ω))]
  exact add_add_add_comm _ _ _ _

/-! ## `eq:dilation-decrease` -/

/-- **`eq:dilation-decrease`.** If every dilation increment of `F` is a symmetric Lévy exponent,
the Lévy measure of `F` decreases under every contraction: `D_c ν ≤ ν` for `0 < c ≤ 1`, where
`D_c ν` is the image of `ν` under `x ↦ cx`.

This is the first half of `lem:selfdecomposable-exponents`(1) ⟹ (3), and the **only** place this
chapter spends the uniqueness clause of `prop:fourier-toolbox`(3) (ledger **A3**). The argument
is the blueprint's: the hypothesis at `(s,t) = (c,1)` gives a pair `(a', ν')` for
`F(·) - F(c·)`; the dilate of `(a,ν)` is a pair for `F(c·)`; their sum is a pair with the same
exponent as `(a,ν)`; and uniqueness identifies the two, so `ν' + D_c ν = ν`.

What remains of the direction, once this is in hand, is a statement about measures alone: in the
coordinate `θ = log x` the conclusion says that the image of `ν` under `log` decreases under
every right translation, and what is wanted is that such a measure has a nonincreasing density.
No property of `F` enters after this point. -/
theorem dilate_le_of_increments (P : SymLevyPair) (F : ℝ → ℝ) (hF : ∀ ω, F ω = P.exponent ω)
    (h : ∀ s t : ℝ, 0 < s → s ≤ t → IsSymLevyExponent fun ω => F (t * ω) - F (s * ω))
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Measure.map (fun x : ℝ => c * x) P.ν ≤ P.ν := by
  obtain ⟨R, hR⟩ := h c 1 hc hc1
  obtain ⟨D, hDν, hD⟩ := symLevyPair_dilate P hc
  obtain ⟨S, hSν, hS⟩ := symLevyPair_add R D
  have hexp : ∀ ω, S.exponent ω = P.exponent ω := by
    intro ω
    have h1 : R.exponent ω = F (1 * ω) - F (c * ω) := (hR ω).symm
    have h2 : D.exponent ω = P.exponent (c * ω) := by
      rw [SymLevyPair.exponent, hD ω, ← SymLevyPair.exponent]
    have h3 : S.exponent ω = R.exponent ω + D.exponent ω := by
      rw [SymLevyPair.exponent, hS ω,
        ENNReal.toReal_add (SymLevyPair.exponentL_ne_top R ω)
          (SymLevyPair.exponentL_ne_top D ω)]
      rfl
    rw [h3, h1, h2, hF (1 * ω), hF (c * ω), one_mul]
    ring
  obtain ⟨-, hν⟩ := fourier_toolbox_levy_unique S P hexp
  rw [hSν] at hν
  rw [← hDν, ← hν]
  intro s
  simp only [Measure.coe_add, Pi.add_apply]
  exact le_add_self

end SpatialLine
