/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.AdmissibleCone
import SpatialLine.ConeDefs

/-!
# `lem:selfdecomposable-exponents`, (3) ⟹ (1): the dilation increments

Blueprint: `lem:selfdecomposable-exponents` (`blueprint/src/parts/07-characterization.tex`),
the implication (3) ⟹ (1) and nothing else. That is the direction
`thm:main-characterization`'s constructive half consumes: it needs exactly
`F(t\,\cdot) - F(s\,\cdot) ∈ LEₛ` for `0 < s ≤ t`, and nothing else from the node.

twin: `Hemigroup.levyExponentD_increment` (`SelfDecomposable.lean`), the same change of
variables with `1 - cos` in place of `1 - e^{-·}` and a Gaussian coefficient in place of a
drift.

## Why the direction is elementary from the representation

`dx/x` is the Haar measure of the multiplicative group, so `u = c x` carries it to `du/u`: a
dilation of the argument acts on the *density alone*, and on the Gaussian coefficient by `c²`.
The increment's density

  `u ↦ k(u/t) - k(u/s)`

is nonnegative precisely because `k` is nonincreasing and `u/t ≤ u/s`, and the Gaussian
coefficient `a(t² - s²)` is nonnegative because `s ≤ t`. No closure theorem, no derivative, no
appeal to `prop:fourier-toolbox`.

Note what the increment is **not**: `u ↦ k(u/t) - k(u/s)` need not be nonincreasing, so the
increment is a symmetric Lévy exponent but generally *not* an admissible one. Condition (1)
asks only for the former.

## The one thing that is not in the causal twin

Paper I's `SelfDecomposableExponent` bundles a single finiteness field, so its increment is a
Lévy exponent as soon as the increment's *exponent* is finite. `SymLevyPair` carries the Lévy
condition `∫ (1 ∧ x²) ν < ∞` instead, which is a statement about the measure, and the increment
measure inherits it from the dilated one rather than from the original: hence
`lintegral_min_profileMeasure_comp_div_ne_top` below, the only lemma of the file with no causal
counterpart. It rests on `min 1 (cx)² ≤ max 1 c² · min 1 x²`, which is where the two regimes of
the truncation meet.

`setLIntegral_Ioi_comp_mul` is the change of variables both halves run on, stated for an
arbitrary `ℝ≥0∞`-valued integrand so that it is proved once: the map is a measurable embedding,
so no measurability of the integrand is needed.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The change of variables on `(0,∞)` -/

/-- Lebesgue measure on the half-line, pushed forward by `x ↦ c x`, is `c⁻¹` times itself. The
half-line is invariant because `c > 0`.

twin: `Hemigroup.map_mul_restrict_Ioi`, verbatim. -/
theorem map_mul_restrict_Ioi {c : ℝ} (hc : 0 < c) :
    Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ)))
      = ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hc]
  have h1 : Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ)))
      = (Measure.map (fun x : ℝ => c * x) volume).restrict (Ioi (0 : ℝ)) := by
    rw [Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi, hpre]
  rw [h1, Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hc)]

/-- **The change of variables `u = c x` on the half-line**, for an arbitrary `ℝ≥0∞`-valued
integrand: `∫_{(0,∞)} G = c ∫_{(0,∞)} G(c\,\cdot)`.

No measurability of `G` is needed — `x ↦ c x` is a measurable embedding. This is the one
computation the whole file runs on: with `G(x) = (1 - \cos \omega x) k(x/c)/x` it is the
dilation invariance of `dx/x`, and with `G(x) = (1 ∧ x²) k(x/c)/x` it is the transfer of the
Lévy condition. -/
theorem setLIntegral_Ioi_comp_mul {c : ℝ} (hc : 0 < c) (G : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (0 : ℝ), G u) = ENNReal.ofReal c * ∫⁻ x in Ioi (0 : ℝ), G (c * x) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => c * x) :=
    (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv.measurableEmbedding
  have hpush : ∫⁻ u, G u ∂(Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ))))
      = ∫⁻ x in Ioi (0 : ℝ), G (c * x) := hemb.lintegral_map G
  rw [map_mul_restrict_Ioi hc, lintegral_smul_measure, smul_eq_mul] at hpush
  rw [← hpush, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-! ## The jump part of a profile exponent -/

/-- The jump part of `eq:sd-profile`: `∫₀^∞ (1 - \cos \omega x) k(x)\,dx/x`.

The second summand of `SDProfile.exponentL`, named because every lemma below is a statement
about it alone and because the increment's density is not a profile. -/
noncomputable def profileJumpL (k : ℝ → ℝ) (ω : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * k x / x)

theorem SDProfile.exponentL_eq_add_jump (P : SDProfile) (ω : ℝ) :
    P.exponentL ω = ENNReal.ofReal (P.a * ω ^ 2) + profileJumpL P.k ω := rfl

/-- The integrand of `profileJumpL` is a.e. measurable when the profile is. -/
theorem aemeasurable_profileJump_integrand {k : ℝ → ℝ}
    (hk : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) (ω : ℝ) :
    AEMeasurable (fun x : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * x)) * k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hw : Measurable fun x : ℝ => 1 - Real.cos (ω * x) := by fun_prop
  exact ((hw.aemeasurable.mul hk).div aemeasurable_id).ennreal_ofReal

/-- Precomposition with a dilation preserves antitonicity on the half-line.

twin: `Hemigroup.antitoneOn_comp_div`, verbatim. -/
theorem antitoneOn_comp_div {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi (0 : ℝ))) {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun u => k (u / c)) (Ioi (0 : ℝ)) := fun _ hx _ hy hxy =>
  hk (mem_Ioi.mpr (div_pos (mem_Ioi.mp hx) hc)) (mem_Ioi.mpr (div_pos (mem_Ioi.mp hy) hc))
    (by gcongr)

/-- **Dilation acts on the density alone.** `profileJumpL k (c ω) = profileJumpL (k(·/c)) ω`.

The Jacobian `c` of `u = c x` cancels exactly against the `c` produced by `x = u/c` in the
denominator, which is the statement that `dx/x` is invariant under the multiplicative group.

twin: `Hemigroup.levyJump_comp_mul`. -/
theorem profileJumpL_comp_div (k : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    profileJumpL (fun u => k (u / c)) ω = profileJumpL k (c * ω) := by
  rw [profileJumpL, setLIntegral_Ioi_comp_mul hc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    profileJumpL]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [← ENNReal.ofReal_mul hc.le]
  congr 1
  rw [show c * x / c = x by field_simp, show ω * (c * x) = c * ω * x by ring]
  field_simp

/-! ## Reading the jump part off the profile measure -/

/-- The `ℝ≥0∞` integral of a measurable function against a profile measure, with the density
unfolded. -/
theorem lintegral_profileMeasure {k : ℝ → ℝ}
    (hk : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, g x ∂(profileMeasure k))
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (k x / x) * g x := by
  have hdens : AEMeasurable (fun x : ℝ => ENNReal.ofReal (k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := (hk.div aemeasurable_id).ennreal_ofReal
  rw [profileMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdens hg.aemeasurable]
  rfl

/-- The jump part of a Lévy pair whose measure is a profile measure is the profile's jump
part. -/
theorem lintegral_one_sub_cos_profileMeasure {k : ℝ → ℝ}
    (hk₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    (hk : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) (ω : ℝ) :
    (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(profileMeasure k)) = profileJumpL k ω := by
  rw [lintegral_profileMeasure hk (by fun_prop), profileJumpL]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hkx : 0 ≤ k x := hk₀ x hx
  have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  rw [← ENNReal.ofReal_mul (div_nonneg hkx hx0.le)]
  congr 1
  field_simp

/-! ## The Lévy condition survives a dilation -/

/-- The truncation `1 ∧ x²` under a dilation: `1 ∧ (cx)² ≤ (1 ∨ c²)(1 ∧ x²)`.

The two regimes of the truncation meet here: for small `x` both sides are quadratic, for large
`x` both are constant, and the middle range is covered because `(cx)² > 1 ≥ x²` forces
`(1 ∨ c²)x² ≥ c²x² > 1`. -/
theorem min_one_sq_mul_le (c x : ℝ) :
    min 1 ((c * x) ^ 2) ≤ max 1 (c ^ 2) * min 1 (x ^ 2) := by
  have hm1 : (1 : ℝ) ≤ max 1 (c ^ 2) := le_max_left _ _
  have hm2 : c ^ 2 ≤ max 1 (c ^ 2) := le_max_right _ _
  rcases le_total (x ^ 2) 1 with hx | hx
  · rw [min_eq_right hx]
    rcases le_total ((c * x) ^ 2) 1 with hcx | hcx
    · rw [min_eq_right hcx]
      nlinarith [sq_nonneg x]
    · rw [min_eq_left hcx]
      nlinarith [sq_nonneg x, sq_nonneg (c * x)]
  · rw [min_eq_left hx]
    calc min 1 ((c * x) ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ max 1 (c ^ 2) * 1 := by rw [mul_one]; exact hm1

/-- **The Lévy condition transfers to a dilated profile.** If `∫ (1 ∧ x²) ν < ∞` for the profile
measure of `k`, the same holds for the profile measure of `k(·/c)`, `c > 0`.

This has no causal counterpart: Paper I's structure carries the finiteness of the *exponent*,
which transports by `levyJump_comp_mul` alone, while `SymLevyPair` carries the Lévy condition on
the measure and so needs the truncation comparison `min_one_sq_mul_le`. -/
theorem lintegral_min_profileMeasure_comp_div_ne_top {k : ℝ → ℝ}
    (hk : AntitoneOn k (Ioi (0 : ℝ))) (hk₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    (hfin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k)) ≠ ⊤)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure fun u => k (u / c))) ≠ ⊤ := by
  have hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hk
  have hkcm : AEMeasurable (fun u : ℝ => k (u / c)) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (antitoneOn_comp_div hk hc)
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) := by fun_prop
  rw [lintegral_profileMeasure hkcm hmeas, setLIntegral_Ioi_comp_mul hc,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hbound : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal c *
        (ENNReal.ofReal (k (c * x / c) / (c * x)) * ENNReal.ofReal (min 1 ((c * x) ^ 2))))
      ≤ ENNReal.ofReal (max 1 (c ^ 2))
        * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (k x / x) * ENNReal.ofReal (min 1 (x ^ 2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hkx : 0 ≤ k x := hk₀ x hx
    have hcx : c * x / c = x := by field_simp
    have hstep : ENNReal.ofReal c * ENNReal.ofReal (k (c * x / c) / (c * x))
        = ENNReal.ofReal (k x / x) := by
      rw [hcx, ← ENNReal.ofReal_mul hc.le]
      congr 1
      field_simp
    rw [← mul_assoc, hstep, mul_left_comm]
    gcongr
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 (c ^ 2)))]
    exact ENNReal.ofReal_le_ofReal (min_one_sq_mul_le c x)
  refine ne_top_of_le_ne_top ?_ hbound
  rw [← lintegral_profileMeasure hkm hmeas]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

/-! ## The increment -/

/-- The increment density is nonnegative: the *only* place monotonicity of `k` is used, and what
makes the increment a symmetric Lévy exponent rather than a mere difference.

twin: `Hemigroup.increment_density_nonneg`. -/
theorem incrementProfile_nonneg {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi (0 : ℝ)))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    0 ≤ incrementProfile k s t x := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hx0 : (0 : ℝ) < x := hx
  exact sub_nonneg.mpr <|
    hk (mem_Ioi.mpr (div_pos hx0 ht)) (mem_Ioi.mpr (div_pos hx0 hs)) (by gcongr)

/-- The increment density is dominated by the upper dilate: `k(x/t) - k(x/s) ≤ k(x/t)`, because
`k ≥ 0`. -/
theorem incrementProfile_le {k : ℝ → ℝ} (hk₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    {s t : ℝ} (hs : 0 < s) {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    incrementProfile k s t x ≤ k (x / t) := by
  have hx0 : (0 : ℝ) < x := hx
  have := hk₀ (x / s) (mem_Ioi.mpr (div_pos hx0 hs))
  simpa [incrementProfile] using this

theorem aemeasurable_incrementProfile {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi (0 : ℝ)))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    AEMeasurable (incrementProfile k s t) (volume.restrict (Ioi (0 : ℝ))) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  exact (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (antitoneOn_comp_div hk ht)).sub
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (antitoneOn_comp_div hk hs))

/-- **The jump parts add**: the jump part of the lower dilate plus that of the increment density
is the jump part of the upper dilate.

twin: `Hemigroup.levyJump_add_increment`. -/
theorem profileJumpL_add_increment {k : ℝ → ℝ} (hk : AntitoneOn k (Ioi (0 : ℝ)))
    (hk₀ : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : ℝ) :
    profileJumpL (fun u => k (u / s)) ω + profileJumpL (incrementProfile k s t) ω
      = profileJumpL (fun u => k (u / t)) ω := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [profileJumpL, profileJumpL, profileJumpL,
    ← lintegral_add_left' (aemeasurable_profileJump_integrand
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (antitoneOn_comp_div hk hs)) ω)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  have h1 : 0 ≤ (1 - Real.cos (ω * x)) * k (x / s) / x :=
    div_nonneg (mul_nonneg hcos (hk₀ _ (mem_Ioi.mpr (div_pos hx0 hs)))) hx0.le
  have h2 : 0 ≤ (1 - Real.cos (ω * x)) * incrementProfile k s t x / x :=
    div_nonneg (mul_nonneg hcos (incrementProfile_nonneg hk hs hst hx)) hx0.le
  rw [← ENNReal.ofReal_add h1 h2]
  congr 1
  simp only [incrementProfile]
  ring

/-- **The increment of a profile exponent is a symmetric Lévy exponent**, in additive form:
`F(s ω) + G(ω) = F(t ω)` with `G` the exponent of the pair `(a(t² - s²), profile measure of the
increment density)`.

Stated additively rather than as a truncated `ℝ≥0∞` subtraction: the two agree where `F(sω)` is
finite, and the additive form is what `thm:main-characterization`'s constructive direction uses,
since it needs exponents to add along a cascade.

twin: `Hemigroup.levyExponentD_increment`. -/
theorem sd_increment_pair (Q : SDProfile) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ∃ R : SymLevyPair, R.a = Q.a * (t ^ 2 - s ^ 2)
      ∧ R.ν = profileMeasure (incrementProfile Q.k s t)
      ∧ ∀ ω : ℝ, Q.exponentL (s * ω) + R.exponentL ω = Q.exponentL (t * ω) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hkm : AEMeasurable Q.k (volume.restrict (Ioi (0 : ℝ))) := Q.aemeasurable_k
  have hjm := aemeasurable_incrementProfile Q.k_antitone hs hst
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) := by fun_prop
  -- The Lévy condition for the increment: dominated by the upper dilate, which inherits it.
  have hνQ : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure Q.k)) ≠ ⊤ :=
    (profile_integrability Q.k_nonneg hkm).mpr ⟨Q.integrable_near_zero, Q.integrable_at_top⟩
  have hνt : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2))
      ∂(profileMeasure fun u => Q.k (u / t))) ≠ ⊤ :=
    lintegral_min_profileMeasure_comp_div_ne_top Q.k_antitone Q.k_nonneg hνQ ht
  have hνj : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2))
      ∂(profileMeasure (incrementProfile Q.k s t))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hνt ?_
    rw [lintegral_profileMeasure hjm hmeas,
      lintegral_profileMeasure (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (antitoneOn_comp_div Q.k_antitone ht)) hmeas]
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    gcongr
    exact incrementProfile_le Q.k_nonneg hs hx
  refine ⟨⟨Q.a * (t ^ 2 - s ^ 2), profileMeasure (incrementProfile Q.k s t),
    mul_nonneg Q.a_nonneg (by nlinarith), isFolded_profileMeasure _, hνj⟩, rfl, rfl, fun ω => ?_⟩
  have hjump : profileJumpL Q.k (s * ω) + profileJumpL (incrementProfile Q.k s t) ω
      = profileJumpL Q.k (t * ω) := by
    rw [← profileJumpL_comp_div Q.k hs ω, ← profileJumpL_comp_div Q.k ht ω]
    exact profileJumpL_add_increment Q.k_antitone Q.k_nonneg hs hst ω
  have hR : (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x))
      ∂(profileMeasure (incrementProfile Q.k s t)))
      = profileJumpL (incrementProfile Q.k s t) ω :=
    lintegral_one_sub_cos_profileMeasure
      (fun x hx => incrementProfile_nonneg Q.k_antitone hs hst hx) hjm ω
  have hgauss : ENNReal.ofReal (Q.a * (s * ω) ^ 2)
      + ENNReal.ofReal (Q.a * (t ^ 2 - s ^ 2) * ω ^ 2)
      = ENNReal.ofReal (Q.a * (t * ω) ^ 2) := by
    rw [← ENNReal.ofReal_add (mul_nonneg Q.a_nonneg (sq_nonneg _))
      (mul_nonneg (mul_nonneg Q.a_nonneg (by nlinarith)) (sq_nonneg ω))]
    congr 1
    ring
  rw [Q.exponentL_eq_add_jump, Q.exponentL_eq_add_jump, SymLevyPair.exponentL, hR,
    add_add_add_comm, hgauss, hjump]

/-! ## Dilating a profile, and the increment at a lower endpoint of zero -/

/-- A profile exponent vanishes at the origin. -/
@[simp] theorem SDProfile.exponent_zero (Q : SDProfile) : Q.exponent 0 = 0 := by
  have h : Q.exponentL 0 = 0 := by
    rw [SDProfile.exponentL]
    simp
  rw [SDProfile.exponent, h, ENNReal.toReal_zero]

/-- **Dilating the argument of a profile exponent** gives a symmetric Lévy exponent, with pair
`(a c², ϖ` the dilated profile measure`)`.

This is `eq:dilation-difference` at the lower endpoint `s = 0`, the case
`sd_exponents_three_implies_one` deliberately excludes and `thm:main-characterization`'s
constructive direction needs. -/
theorem sd_dilate_pair (Q : SDProfile) {c : ℝ} (hc : 0 < c) :
    ∃ R : SymLevyPair, ∀ ω, R.exponentL ω = Q.exponentL (c * ω) := by
  have hkm : AEMeasurable Q.k (volume.restrict (Ioi (0 : ℝ))) := Q.aemeasurable_k
  have hkc : AntitoneOn (fun u => Q.k (u / c)) (Ioi (0 : ℝ)) := antitoneOn_comp_div Q.k_antitone hc
  have hkcm : AEMeasurable (fun u : ℝ => Q.k (u / c)) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hkc
  have hkc0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Q.k (x / c) := fun x hx =>
    Q.k_nonneg _ (mem_Ioi.mpr (div_pos hx hc))
  have hνQ : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure Q.k)) ≠ ⊤ :=
    (profile_integrability Q.k_nonneg hkm).mpr ⟨Q.integrable_near_zero, Q.integrable_at_top⟩
  refine ⟨⟨Q.a * c ^ 2, profileMeasure fun u => Q.k (u / c), mul_nonneg Q.a_nonneg (sq_nonneg c),
    isFolded_profileMeasure _,
    lintegral_min_profileMeasure_comp_div_ne_top Q.k_antitone Q.k_nonneg hνQ hc⟩, fun ω => ?_⟩
  rw [SymLevyPair.exponentL, SDProfile.exponentL_eq_add_jump,
    lintegral_one_sub_cos_profileMeasure hkc0 hkcm ω, profileJumpL_comp_div Q.k hc ω]
  congr 2
  ring

/-- **The increment of a profile exponent over `0 ≤ c ≤ d`**, with the lower endpoint allowed to
be the origin.

Three cases, and the boundary ones are why the declaration exists: at `c = d = 0` the increment
is the zero exponent, at `c = 0 < d` it is the dilate `F(d\,\cdot)` itself, and at `0 < c` it is
`sd_increment_pair`. `thm:main-characterization`'s constructive direction quantifies over
`0 ≤ s ≤ t`, so all three occur. -/
theorem sd_increment_isSymLevyExponent (Q : SDProfile) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    IsSymLevyExponent fun ω => Q.exponent (d * ω) - Q.exponent (c * ω) := by
  rcases eq_or_lt_of_le hc with h0 | hcpos
  · -- `c = 0`: the increment is the dilate, or the zero exponent.
    have hd : 0 ≤ d := h0 ▸ hcd
    rcases eq_or_lt_of_le hd with hd0 | hdpos
    · refine ⟨⟨0, 0, le_rfl, by simp [IsFolded], by simp⟩, fun ω => ?_⟩
      show Q.exponent (d * ω) - Q.exponent (c * ω) = _
      rw [← h0, ← hd0]
      simp [SymLevyPair.exponent, SymLevyPair.exponentL]
    · obtain ⟨R, hR⟩ := sd_dilate_pair Q hdpos
      refine ⟨R, fun ω => ?_⟩
      show Q.exponent (d * ω) - Q.exponent (c * ω) = R.exponent ω
      rw [← h0, zero_mul, Q.exponent_zero, sub_zero, SDProfile.exponent, SymLevyPair.exponent, hR]
  · -- `0 < c`: the genuine increment.
    obtain ⟨R, -, -, hadd⟩ := sd_increment_pair Q hcpos hcd
    refine ⟨R, fun ω => ?_⟩
    show Q.exponent (d * ω) - Q.exponent (c * ω) = R.exponent ω
    have h1 : Q.exponentL (c * ω) ≠ ⊤ := Q.exponentL_ne_top _
    have h2 : R.exponentL ω ≠ ⊤ := R.exponentL_ne_top ω
    have h := congrArg ENNReal.toReal (hadd ω)
    rw [ENNReal.toReal_add h1 h2] at h
    rw [SDProfile.exponent, SDProfile.exponent, SymLevyPair.exponent]
    linarith [h]

/-- **`lem:selfdecomposable-exponents`, (3) ⟹ (1).** The dilation identity: for `0 < s ≤ t` the
increment `F(t\,\cdot) - F(s\,\cdot)` of a profile exponent is again a symmetric Lévy exponent.

The range is `0 < s`, not `0 ≤ s`; the case `s = 0` is `F(t\,\cdot)` itself and is handled
separately in `thm:main-characterization`'s constructive direction. -/
theorem sd_exponents_three_implies_one (P : SymLevyPair) (F : ℝ → ℝ)
    (hF : ∀ ω, F ω = P.exponent ω) (Q : SDProfile) (ha : Q.a = P.a)
    (hν : P.ν = profileMeasure Q.k) :
    ∀ s t : ℝ, 0 < s → s ≤ t → IsSymLevyExponent fun ω => F (t * ω) - F (s * ω) := by
  intro s t hs hst
  have hFQ : ∀ ω, F ω = Q.exponent ω := by
    intro ω
    rw [hF ω, SymLevyPair.exponent, SDProfile.exponent,
      exponentL_eq_of_profileMeasure Q P ha.symm hν ω]
  obtain ⟨R, -, -, hadd⟩ := sd_increment_pair Q hs hst
  refine ⟨R, fun ω => ?_⟩
  have hfin := hadd ω
  have h1 : Q.exponentL (s * ω) ≠ ⊤ := Q.exponentL_ne_top _
  have h2 : R.exponentL ω ≠ ⊤ := R.exponentL_ne_top ω
  have := congrArg ENNReal.toReal hfin
  rw [ENNReal.toReal_add h1 h2] at this
  show F (t * ω) - F (s * ω) = R.exponent ω
  rw [hFQ (t * ω), hFQ (s * ω), SDProfile.exponent, SDProfile.exponent, SymLevyPair.exponent]
  linarith [this]

end SpatialLine
