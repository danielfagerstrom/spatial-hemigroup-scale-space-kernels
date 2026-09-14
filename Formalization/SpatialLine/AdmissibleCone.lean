/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ProfileIntegrability

/-!
# `lem:admissible-cone`: the admissible exponents form a convex cone

Blueprint: `lem:admissible-cone` (`blueprint/src/parts/07-characterization.tex`).

The content is that all seven fields of `SDProfile` are stable under addition and under
multiplication by a nonnegative scalar, and that the exponent transports: the profile with data
`(a₁+a₂, k₁+k₂)` has exponent `F₁ + F₂`, and the one with data `(c a₁, c k₁)` has exponent
`c F₁`. Five fields are immediate; the two integrability conditions are the ones with content,
and they are exactly the transport statement in `ℝ≥0∞`, a sum of two finite things being finite.

## `ℝ≥0∞` first, and the one place `toReal` costs something

`SDProfile.exponentL` is a `lintegral`, so additivity in `k` needs **no integrability side
condition**: `lintegral_add_left'` asks only for `AEMeasurable` of one summand, which
`aemeasurable_restrict_of_antitoneOn` supplies from `k_antitone`. The classical argument would
first have to know both integrals finite; here finiteness is a conclusion.

The node's statement is about the **real** exponent, though, and `(x + y).toReal` is
`x.toReal + y.toReal` only when both are finite. That finiteness is `lem:quadratic-growth`,
routed through `lem:profile-integrability`: `SDProfile.exponentL_ne_top` below is the one step of
the file that leaves the elementary algebra, and it is why this node depends on chapter 2.

twin: `Hemigroup.SelfDecomposableExponent.admissible_cone` (`AdmissibleCone.lean`), the same
proof over the causal profile structure. This is the strongest `ScaleSpaceCore` candidate of the
chapter: nothing in it mentions the transform, only the profile cone.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## Measurability of a profile, on the three windows the fields use -/

/-- A profile is a.e. measurable on `(0,∞)`: it is antitone there. -/
theorem SDProfile.aemeasurable_k (P : SDProfile) :
    AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
  aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone

/-- The same on any subset of `(0,∞)`; used at `Ioo 0 1` and at `Ioi 1`, the two windows of the
integrability fields. -/
theorem SDProfile.aemeasurable_k_mono (P : SDProfile) {s : Set ℝ} (hs : s ⊆ Ioi (0 : ℝ)) :
    AEMeasurable P.k (volume.restrict s) :=
  P.aemeasurable_k.mono_measure (Measure.restrict_mono hs le_rfl)

/-! ## The two constructions -/

/-- **The sum of two admissible profiles**, with data `(a₁ + a₂, k₁ + k₂)`. -/
noncomputable def SDProfile.add (P₁ P₂ : SDProfile) : SDProfile where
  a := P₁.a + P₂.a
  k := fun x => P₁.k x + P₂.k x
  a_nonneg := add_nonneg P₁.a_nonneg P₂.a_nonneg
  k_nonneg := fun x hx => add_nonneg (P₁.k_nonneg x hx) (P₂.k_nonneg x hx)
  k_antitone := fun _ hx _ hy hxy =>
    add_le_add (P₁.k_antitone hx hy hxy) (P₂.k_antitone hx hy hxy)
  k_zero := by simp [P₁.k_zero, P₂.k_zero]
  integrable_near_zero := by
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
    have hm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (x * P₁.k x))
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (aemeasurable_id.mul (P₁.aemeasurable_k_mono hsub)).ennreal_ofReal
    have hsplit : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * (P₁.k x + P₂.k x)))
        = (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P₁.k x))
          + ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P₂.k x) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have h1 : 0 ≤ x * P₁.k x := mul_nonneg hx0.le (P₁.k_nonneg x (hsub hx))
      have h2 : 0 ≤ x * P₂.k x := mul_nonneg hx0.le (P₂.k_nonneg x (hsub hx))
      rw [← ENNReal.ofReal_add h1 h2]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨P₁.integrable_near_zero, P₂.integrable_near_zero⟩
  integrable_at_top := by
    have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi zero_le_one
    have hm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P₁.k x / x))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((P₁.aemeasurable_k_mono hsub).div aemeasurable_id).ennreal_ofReal
    have hsplit : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal ((P₁.k x + P₂.k x) / x))
        = (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P₁.k x / x))
          + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P₂.k x / x) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hsub hx
      have h1 : 0 ≤ P₁.k x / x := div_nonneg (P₁.k_nonneg x (hsub hx)) hx0.le
      have h2 : 0 ≤ P₂.k x / x := div_nonneg (P₂.k_nonneg x (hsub hx)) hx0.le
      rw [← ENNReal.ofReal_add h1 h2]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨P₁.integrable_at_top, P₂.integrable_at_top⟩

/-- **A nonnegative multiple of an admissible profile**, with data `(c a, c k)`. -/
noncomputable def SDProfile.smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) : SDProfile where
  a := c * P.a
  k := fun x => c * P.k x
  a_nonneg := mul_nonneg hc P.a_nonneg
  k_nonneg := fun x hx => mul_nonneg hc (P.k_nonneg x hx)
  k_antitone := fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (P.k_antitone hx hy hxy) hc
  k_zero := by simp [P.k_zero]
  integrable_near_zero := by
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
    have hsplit : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * (c * P.k x)))
        = ENNReal.ofReal c * ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P.k x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have h1 : 0 ≤ x * P.k x := mul_nonneg hx0.le (P.k_nonneg x (hsub hx))
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.integrable_near_zero
  integrable_at_top := by
    have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi zero_le_one
    have hsplit : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (c * P.k x / x))
        = ENNReal.ofReal c * ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P.k x / x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hsub hx
      have h1 : 0 ≤ P.k x / x := div_nonneg (P.k_nonneg x (hsub hx)) hx0.le
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.integrable_at_top

@[simp] theorem SDProfile.add_a (P₁ P₂ : SDProfile) : (P₁.add P₂).a = P₁.a + P₂.a := rfl

@[simp] theorem SDProfile.add_k (P₁ P₂ : SDProfile) (x : ℝ) :
    (P₁.add P₂).k x = P₁.k x + P₂.k x := rfl

@[simp] theorem SDProfile.smul_a (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) :
    (P.smul hc).a = c * P.a := rfl

@[simp] theorem SDProfile.smul_k (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    (P.smul hc).k x = c * P.k x := rfl

/-! ## Finiteness of the exponent -/

/-- **`lem:quadratic-growth` at a profile.** The exponent `eq:sd-profile` is finite at every
frequency, so `SDProfile.exponent`, a `.toReal`, is the real number the display writes.

Routed through `lem:profile-integrability`: the profile's data is a symmetric Lévy pair with the
same `exponentL`, and `SymLevyPair.exponentL_ne_top` is the growth bound. -/
theorem SDProfile.exponentL_ne_top (P : SDProfile) (ω : ℝ) : P.exponentL ω ≠ ⊤ := by
  obtain ⟨Q, ha, hν, -⟩ := profile_integrability_pair P
  rw [exponentL_eq_of_profileMeasure P Q ha hν ω]
  exact Q.exponentL_ne_top ω

/-! ## Evenness of the exponent

`(-ω)² = ω²` and the cosine is even, so both integrands are unchanged. Three chapter-7 files
need it — the symbol, `prop:strict-positivity`(2) and the analysis direction — and wave 3's
merge collected it here, beside the other general facts about `SDProfile.exponentL`. -/

/-- The exponent is even, in `ℝ≥0∞`. -/
theorem SDProfile.exponentL_neg (Q : SDProfile) (ω : ℝ) :
    Q.exponentL (-ω) = Q.exponentL ω := by
  rw [SDProfile.exponentL, SDProfile.exponentL]
  congr 1
  · congr 1
    ring
  · refine lintegral_congr fun x => ?_
    rw [show -ω * x = -(ω * x) by ring, Real.cos_neg]

/-- The exponent is even. -/
theorem SDProfile.exponent_neg (Q : SDProfile) (ω : ℝ) : Q.exponent (-ω) = Q.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponent, Q.exponentL_neg]

/-! ## Additivity and homogeneity of the exponent -/

/-- The exponent is additive in the data, in `ℝ≥0∞` and with no side condition. -/
theorem SDProfile.exponentL_add (P₁ P₂ : SDProfile) (ω : ℝ) :
    (P₁.add P₂).exponentL ω = P₁.exponentL ω + P₂.exponentL ω := by
  have hm : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₁.k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEMeasurable.ennreal_ofReal ?_
    have hc : AEMeasurable (fun x : ℝ => 1 - Real.cos (ω * x))
        (volume.restrict (Ioi (0 : ℝ))) := by
      fun_prop
    exact (hc.mul P₁.aemeasurable_k).div aemeasurable_id
  have hjump : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * (P₁.k x + P₂.k x) / x))
      = (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₁.k x / x))
        + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₂.k x / x) := by
    rw [← lintegral_add_left' hm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    have h1 : 0 ≤ (1 - Real.cos (ω * x)) * P₁.k x / x :=
      div_nonneg (mul_nonneg hcos (P₁.k_nonneg x hx)) hx0.le
    have h2 : 0 ≤ (1 - Real.cos (ω * x)) * P₂.k x / x :=
      div_nonneg (mul_nonneg hcos (P₂.k_nonneg x hx)) hx0.le
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    ring
  have hgauss : ENNReal.ofReal ((P₁.a + P₂.a) * ω ^ 2)
      = ENNReal.ofReal (P₁.a * ω ^ 2) + ENNReal.ofReal (P₂.a * ω ^ 2) := by
    rw [← ENNReal.ofReal_add (mul_nonneg P₁.a_nonneg (sq_nonneg ω))
      (mul_nonneg P₂.a_nonneg (sq_nonneg ω))]
    congr 1
    ring
  simp only [SDProfile.exponentL, SDProfile.add_a, SDProfile.add_k]
  rw [hgauss, hjump]
  ring

/-- The exponent is homogeneous in the data, for a nonnegative scalar. -/
theorem SDProfile.exponentL_smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (ω : ℝ) :
    (P.smul hc).exponentL ω = ENNReal.ofReal c * P.exponentL ω := by
  have hjump : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * (c * P.k x) / x))
      = ENNReal.ofReal c
        * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    have h1 : 0 ≤ (1 - Real.cos (ω * x)) * P.k x / x :=
      div_nonneg (mul_nonneg hcos (P.k_nonneg x hx)) hx0.le
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  have hgauss : ENNReal.ofReal (c * P.a * ω ^ 2)
      = ENNReal.ofReal c * ENNReal.ofReal (P.a * ω ^ 2) := by
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  simp only [SDProfile.exponentL, SDProfile.smul_a, SDProfile.smul_k]
  rw [hgauss, hjump, mul_add]

/-- **The exponent is additive**: the profile with data `(a₁+a₂, k₁+k₂)` has exponent
`F₁ + F₂`. -/
theorem SDProfile.exponent_add (P₁ P₂ : SDProfile) (ω : ℝ) :
    (P₁.add P₂).exponent ω = P₁.exponent ω + P₂.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponentL_add,
    ENNReal.toReal_add (P₁.exponentL_ne_top ω) (P₂.exponentL_ne_top ω)]
  rfl

/-- **The exponent is homogeneous**: the profile with data `(c a, c k)` has exponent `c F`. -/
theorem SDProfile.exponent_smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (ω : ℝ) :
    (P.smul hc).exponent ω = c * P.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponentL_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc]
  rfl

/-! ## The node -/

/-- **`lem:admissible-cone`.** The admissible exponents are closed under addition and under
multiplication by a nonnegative scalar, and the correspondence with the data `(a,k)` is linear —
so they form a convex cone.

Stated existentially, as the skeleton states it: what has to hold is that a profile with the
summed data and the summed exponent *exists*, not that it is built by any particular
construction. The profile clause is asserted on `(0,∞)`, which is where a profile is a density;
`k 0` is a normalisation and both constructions preserve it. -/
theorem admissible_cone (P₁ P₂ : SDProfile) (c : ℝ) (hc : 0 ≤ c) :
    (∃ Q : SDProfile, Q.a = P₁.a + P₂.a ∧ (∀ x : ℝ, 0 < x → Q.k x = P₁.k x + P₂.k x) ∧
        ∀ ω : ℝ, Q.exponent ω = P₁.exponent ω + P₂.exponent ω) ∧
      (∃ Q : SDProfile, Q.a = c * P₁.a ∧ (∀ x : ℝ, 0 < x → Q.k x = c * P₁.k x) ∧
        ∀ ω : ℝ, Q.exponent ω = c * P₁.exponent ω) :=
  ⟨⟨P₁.add P₂, rfl, fun _ _ => rfl, fun ω => P₁.exponent_add P₂ ω⟩,
   ⟨P₁.smul hc, rfl, fun _ _ => rfl, fun ω => P₁.exponent_smul hc ω⟩⟩

end SpatialLine
