/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.StrictPositivity
import SpatialLine.MainAnalysis

/-!
# `prop:strict-positivity`(2) and its consequences

Blueprint: `prop:strict-positivity`, clause (2) and the sentence after it.

## The three steps, and what each one cost

The route is the one wave 2 wrote down at the statement, and it held.

1. **From the increment to its pair.** `sd_increment_pair` (for `s > 0`) and the value
   `P.exponent 0 = 0` (for `s = 0`) turn a vanishing increment into a vanishing `ℝ≥0∞`
   exponent, hence into `a = 0` together with a vanishing jump integral.

2. **From that integral to the density.** `1 - cos(ωx)` is strictly positive off the countable
   set `(2π/ω)ℤ`, which is Lebesgue-null, so the density vanishes almost everywhere on `(0,∞)`.

3. **The rigidity step.** For `k` antitone and `k(y) = k(κy)` almost everywhere with `κ > 1`:
   the tail integral `J(ε) = ∫_ε^∞ k(u) du/u` is finite for every `ε > 0`, and the change of
   variables `u = κx` on `(ε,∞)` gives `J(κε) = J(ε)`; splitting `J(ε)` at `κε` makes the
   integral over `(ε,κε]` vanish.

**What writing step 3 down improved on the plan.** The plan then extracted a point of the
interval where `k` vanishes and carried it by antitonicity. That existence step is not needed:
`k` is antitone, so on `(ε,κε]` it is bounded below by `k(κε)`, and an integral that vanishes on
a set of positive measure forces that lower bound to be `0` **at the right endpoint**. Reading
the conclusion at `ε = x/κ` gives `k(x) = 0` for the arbitrary `x > 0` directly, with no
covering, no induction and no almost-everywhere-to-pointwise step. The new library lemma the
plan named, `map_mul_restrict_Ioi` generalised to `Ioi b`, is `setLIntegral_Ioi_comp_mul'` below
and is the only piece of new measure theory.

**And what it improved on the plan for the consequences.** The lattice clause was priced
against `lem:lattice-zero`; it does not need it. If a kernel is carried by `pℤ` then its cosine
transform at `2π/p` is the integral of the constant `1`, so the increment exponent vanishes at a
nonzero frequency, which clause (2) forbids. `Real.cos_int_mul_two_pi` is the whole of it.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The change of variables `u = c x` on `(b,∞)` -/

/-- **`map_mul_restrict_Ioi` with an arbitrary base point.** Lebesgue measure on `(b,∞)`, pushed
forward by `x ↦ c x`, is `c⁻¹` times Lebesgue measure on `(cb,∞)`. -/
theorem map_mul_restrict_Ioi' {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi b))
      = ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (c * b)) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Ioi (c * b) = Ioi b := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have h1 : Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi b))
      = (Measure.map (fun x : ℝ => c * x) volume).restrict (Ioi (c * b)) := by
    rw [Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi, hpre]
  rw [h1, Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hc)]

/-- **The change of variables `u = c x` on `(cb,∞)`**, for an arbitrary `ℝ≥0∞` integrand: the
`Ioi b` form of `setLIntegral_Ioi_comp_mul`, which is the case `b = 0`. -/
theorem setLIntegral_Ioi_comp_mul' {c : ℝ} (hc : 0 < c) (b : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (c * b), G u) = ENNReal.ofReal c * ∫⁻ x in Ioi b, G (c * x) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => c * x) :=
    (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv.measurableEmbedding
  have hpush : ∫⁻ u, G u ∂(Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi b)))
      = ∫⁻ x in Ioi b, G (c * x) := hemb.lintegral_map G
  rw [map_mul_restrict_Ioi' hc b, lintegral_smul_measure, smul_eq_mul] at hpush
  rw [← hpush, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Scaling a measure by a nonzero constant does not change what happens almost everywhere. -/
theorem ae_smul_iff {α : Type*} [MeasurableSpace α] {m : Measure α} {r : ℝ≥0∞} (hr : r ≠ 0)
    {p : α → Prop} : (∀ᵐ x ∂(r • m), p x) ↔ ∀ᵐ x ∂m, p x := by
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hr, false_or]

/-- **A dilation of the half-line preserves almost-everywhere statements.** -/
theorem ae_restrict_Ioi_mul_iff {c : ℝ} (hc : 0 < c) {p : ℝ → Prop} :
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), p (c * x))
      ↔ ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), p y := by
  have hemb : MeasurableEmbedding (fun x : ℝ => c * x) :=
    (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv.measurableEmbedding
  rw [← hemb.ae_map_iff, map_mul_restrict_Ioi hc,
    ae_smul_iff (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)).ne']

/-! ## The cosine takes the value one on a null set -/

/-- **`1 - cos(ωx)` vanishes on a Lebesgue-null set**, for `ω ≠ 0`: the solutions are the lattice
`(2π/ω)ℤ`, which is countable. -/
theorem ae_cos_ne_one {ω : ℝ} (hω : ω ≠ 0) : ∀ᵐ x : ℝ, Real.cos (ω * x) ≠ 1 := by
  have hsub : {x : ℝ | Real.cos (ω * x) = 1}
      ⊆ Set.range fun n : ℤ => (n : ℝ) * (2 * Real.pi) / ω := by
    intro x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (ω * x)).mp hx
    refine ⟨n, ?_⟩
    field_simp
    linarith [hn]
  have hnull : volume {x : ℝ | Real.cos (ω * x) = 1} = 0 :=
    measure_mono_null hsub ((Set.countable_range _).measure_zero volume)
  rw [ae_iff]
  simpa using hnull

/-- **Step 2.** A vanishing jump integral at one nonzero frequency forces the density to vanish
almost everywhere on the half-line. -/
theorem ae_eq_zero_of_profileJumpL_eq_zero {h : ℝ → ℝ}
    (hmeas : AEMeasurable h (volume.restrict (Ioi (0 : ℝ))))
    (hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ h x) {ω : ℝ} (hω : ω ≠ 0) (hzero : profileJumpL h ω = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), h x = 0 := by
  rw [profileJumpL, lintegral_eq_zero_iff' (aemeasurable_profileJump_integrand hmeas ω)] at hzero
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (ae_cos_ne_one hω)] with x hx hxmem hcos
  have hx0 : (0 : ℝ) < x := hxmem
  have hcpos : 0 < 1 - Real.cos (ω * x) := by
    have hle1 := Real.cos_le_one (ω * x)
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · linarith
    · exact absurd heq hcos
  have hle : (1 - Real.cos (ω * x)) * h x / x ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  have hge : 0 ≤ (1 - Real.cos (ω * x)) * h x / x :=
    div_nonneg (mul_nonneg hcpos.le (hnn x hxmem)) hx0.le
  have hz : (1 - Real.cos (ω * x)) * h x / x = 0 := le_antisymm hle hge
  rcases (div_eq_zero_iff.mp hz) with hnum | hden
  · rcases mul_eq_zero.mp hnum with h1 | h2
    · exact absurd h1 (by linarith : ¬ (1 - Real.cos (ω * x) = 0))
    · exact h2
  · exact absurd hden hx0.ne'

/-! ## Step 3: the rigidity of an antitone profile under a dilation -/

/-- The tail integral of a profile against `dx/x` is finite off the origin: antitonicity bounds
the near part and `SDProfile.integrable_at_top` is the far part. -/
theorem SDProfile.lintegral_tail_ne_top (P : SDProfile) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u)) ≠ ⊤ := by
  set m : ℝ := max ε 1 with hm
  have hεm : ε ≤ m := le_max_left _ _
  have h1m : (1 : ℝ) ≤ m := le_max_right _ _
  have hsplit : (∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u))
      = (∫⁻ u in Ioc ε m, ENNReal.ofReal (P.k u / u))
        + ∫⁻ u in Ioi m, ENNReal.ofReal (P.k u / u) := by
    rw [← lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl), Ioc_union_Ioi_eq_Ioi hεm]
  rw [hsplit]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · have hbd : ∀ u ∈ Ioc ε m, ENNReal.ofReal (P.k u / u) ≤ ENNReal.ofReal (P.k ε / ε) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hε hu.1.le
      refine ENNReal.ofReal_le_ofReal ?_
      have hku : P.k u ≤ P.k ε := P.k_antitone (mem_Ioi.mpr hε) (mem_Ioi.mpr hu0) hu.1.le
      have hknn : 0 ≤ P.k u := P.k_nonneg u (mem_Ioi.mpr hu0)
      have h1 : P.k u / u ≤ P.k ε / u := by gcongr
      have h2 : P.k ε / u ≤ P.k ε / ε := by
        gcongr
        · exact le_trans hknn hku
        · exact hu.1.le
      linarith
    have hb1 : (∫⁻ u in Ioc ε m, ENNReal.ofReal (P.k u / u))
        ≤ ENNReal.ofReal (P.k ε / ε) * volume (Ioc ε m) := by
      calc (∫⁻ u in Ioc ε m, ENNReal.ofReal (P.k u / u))
          ≤ ∫⁻ _ in Ioc ε m, ENNReal.ofReal (P.k ε / ε) :=
            setLIntegral_mono' measurableSet_Ioc hbd
        _ = ENNReal.ofReal (P.k ε / ε) * volume (Ioc ε m) := by rw [setLIntegral_const]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Ioc])) hb1
  · refine ne_top_of_le_ne_top P.integrable_at_top ?_
    exact lintegral_mono' (Measure.restrict_mono (Ioi_subset_Ioi h1m) le_rfl) le_rfl

/-- **Step 3, the rigidity step.** An antitone profile fixed almost everywhere by one dilation of
ratio greater than one vanishes identically on the half-line.

The blueprint's covering argument is replaced by the finiteness of the tail integral: it is
finite off the origin, invariant under the dilation, and therefore has no mass on `(ε,κε]`;
antitonicity then reads off `k(κε) = 0` at the right endpoint, and `ε = x/κ` is an arbitrary
point of the half-line in disguise. -/
theorem SDProfile.k_eq_zero_of_dilation_ae (P : SDProfile) {c : ℝ} (hc : 1 < c)
    (hae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), P.k (c * y) = P.k y) :
    ∀ x ∈ Ioi (0 : ℝ), P.k x = 0 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  -- the tail integral is invariant under the dilation
  have hJ : ∀ ε : ℝ, 0 < ε → (∫⁻ u in Ioi (c * ε), ENNReal.ofReal (P.k u / u))
      = ∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u) := by
    intro ε hε
    rw [setLIntegral_Ioi_comp_mul' hc0 ε]
    have hcong : (∫⁻ x in Ioi ε, ENNReal.ofReal (P.k (c * x) / (c * x)))
        = ENNReal.ofReal c⁻¹ * ∫⁻ x in Ioi ε, ENNReal.ofReal (P.k x / x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi hε.le) hae,
        ae_restrict_mem measurableSet_Ioi] with x hx hxmem
      have hx0 : (0 : ℝ) < x := lt_trans hε hxmem
      rw [hx, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc0))]
      congr 1
      field_simp
    rw [hcong, ← mul_assoc, ← ENNReal.ofReal_mul hc0.le, mul_inv_cancel₀ hc0.ne',
      ENNReal.ofReal_one, one_mul]
  -- so the tail integral has no mass on `(ε, cε]`
  have hIoc : ∀ ε : ℝ, 0 < ε → (∫⁻ u in Ioc ε (c * ε), ENNReal.ofReal (P.k u / u)) = 0 := by
    intro ε hε
    have hεc : ε ≤ c * ε := by nlinarith
    have hsplit : (∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u))
        = (∫⁻ u in Ioc ε (c * ε), ENNReal.ofReal (P.k u / u))
          + ∫⁻ u in Ioi (c * ε), ENNReal.ofReal (P.k u / u) := by
      rw [← lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl), Ioc_union_Ioi_eq_Ioi hεc]
    rw [hJ ε hε] at hsplit
    have hcancel : (∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u))
        + (∫⁻ u in Ioc ε (c * ε), ENNReal.ofReal (P.k u / u))
        = (∫⁻ u in Ioi ε, ENNReal.ofReal (P.k u / u)) + 0 := by
      rw [add_zero, add_comm]
      exact hsplit.symm
    exact (ENNReal.add_right_inj (P.lintegral_tail_ne_top hε)).mp hcancel
  -- antitonicity reads the value off at the right endpoint
  have hk0 : ∀ ε : ℝ, 0 < ε → P.k (c * ε) = 0 := by
    intro ε hε
    have hcε : 0 < c * ε := by positivity
    have hεc : ε < c * ε := by nlinarith
    have hlow : ENNReal.ofReal (P.k (c * ε) / (c * ε)) * volume (Ioc ε (c * ε))
        ≤ ∫⁻ u in Ioc ε (c * ε), ENNReal.ofReal (P.k u / u) := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' measurableSet_Ioc fun u hu => ENNReal.ofReal_le_ofReal ?_
      have hu0 : 0 < u := lt_of_lt_of_le hε hu.1.le
      have hku : P.k (c * ε) ≤ P.k u := P.k_antitone (mem_Ioi.mpr hu0) (mem_Ioi.mpr hcε) hu.2
      have hknn : 0 ≤ P.k (c * ε) := P.k_nonneg _ (mem_Ioi.mpr hcε)
      have h1 : P.k (c * ε) / (c * ε) ≤ P.k u / (c * ε) := by gcongr
      have h2 : P.k u / (c * ε) ≤ P.k u / u := by
        gcongr
        · exact le_trans hknn hku
        · exact hu.2
      linarith
    rw [hIoc ε hε, nonpos_iff_eq_zero, mul_eq_zero] at hlow
    have hvol : volume (Ioc ε (c * ε)) ≠ 0 := by
      simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have hz : ENNReal.ofReal (P.k (c * ε) / (c * ε)) = 0 := by tauto
    have hle : P.k (c * ε) / (c * ε) ≤ 0 := ENNReal.ofReal_eq_zero.mp hz
    have hknn : 0 ≤ P.k (c * ε) := P.k_nonneg _ (mem_Ioi.mpr hcε)
    nlinarith [div_nonneg hknn hcε.le, (div_le_iff₀ hcε).mp hle]
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hval := hk0 (x / c) (div_pos hx0 hc0)
  rwa [mul_div_cancel₀ _ hc0.ne'] at hval

/-! ## The exponent of a degenerate profile -/

/-- An `SDProfile` with no Gaussian part and an almost everywhere vanishing profile has the zero
exponent. -/
theorem SDProfile.exponent_eq_zero_of_ae (P : SDProfile) (ha : P.a = 0)
    (hk : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), P.k x = 0) : ∀ ω : ℝ, P.exponent ω = 0 := by
  intro ω
  have hL : P.exponentL ω = 0 := by
    rw [SDProfile.exponentL, ha]
    have hjump : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)) = 0 := by
      rw [← lintegral_zero (μ := volume.restrict (Ioi (0 : ℝ)))]
      refine lintegral_congr_ae ?_
      filter_upwards [hk] with x hx
      simp [hx]
    simp [hjump]
  rw [SDProfile.exponent, hL, ENNReal.toReal_zero]

/-! ## Clause (2) -/

/-- **`prop:strict-positivity`(2).** Every dilation increment of a nonzero admissible exponent is
strictly positive off the origin. -/
theorem strict_positivity_strict (P : SDProfile) (hne : ∃ ω : ℝ, P.exponent ω ≠ 0) :
    ∀ s t ω : ℝ, 0 ≤ s → s < t → ω ≠ 0 → 0 < P.exponent (t * ω) - P.exponent (s * ω) := by
  -- It suffices to treat a positive frequency, the exponent being even.
  suffices hpos : ∀ s t ω : ℝ, 0 ≤ s → s < t → 0 < ω →
      0 < P.exponent (t * ω) - P.exponent (s * ω) by
    intro s t ω hs hst hω
    rcases lt_or_gt_of_ne hω with h | h
    · have h' := hpos s t (-ω) hs hst (by linarith)
      rwa [show t * -ω = -(t * ω) by ring, show s * -ω = -(s * ω) by ring,
        P.exponent_neg, P.exponent_neg] at h'
    · exact hpos s t ω hs hst h
  intro s t ω hs hst hω
  have ht0 : (0 : ℝ) ≤ t := le_trans hs hst.le
  have hmono : P.exponent (s * ω) ≤ P.exponent (t * ω) :=
    strict_positivity_monotone P (mul_nonneg hs hω.le : (0 : ℝ) ≤ s * ω)
      (mul_nonneg ht0 hω.le : (0 : ℝ) ≤ t * ω) (by nlinarith)
  rcases lt_or_eq_of_le hmono with h | heq
  · linarith
  exfalso
  have hLeq : P.exponentL (s * ω) = P.exponentL (t * ω) :=
    (ENNReal.toReal_eq_toReal_iff' (P.exponentL_ne_top _) (P.exponentL_ne_top _)).mp heq
  obtain ⟨ω₀, hω₀⟩ := hne
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- `s = 0`: the exponent itself vanishes at `tω ≠ 0`.
    have htω : 0 < t * ω := by nlinarith
    have hzero : ENNReal.ofReal (P.a * (t * ω) ^ 2) + profileJumpL P.k (t * ω) = 0 := by
      rw [← SDProfile.exponentL_eq_add_jump, ← hLeq, ← hs0, zero_mul, SDProfile.exponentL]
      simp
    have ha : P.a = 0 := by
      have h1 : ENNReal.ofReal (P.a * (t * ω) ^ 2) = 0 :=
        nonpos_iff_eq_zero.mp (hzero ▸ le_self_add)
      have h2 : P.a * (t * ω) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h1
      have hsq : 0 < (t * ω) ^ 2 := by positivity
      rcases eq_or_lt_of_le P.a_nonneg with h | hpos
      · exact h.symm
      · exact absurd h2 (not_le.2 (mul_pos hpos hsq))
    have hjump : profileJumpL P.k (t * ω) = 0 :=
      nonpos_iff_eq_zero.mp (hzero ▸ le_add_self)
    exact hω₀ (P.exponent_eq_zero_of_ae ha
      (ae_eq_zero_of_profileJumpL_eq_zero P.aemeasurable_k P.k_nonneg htω.ne' hjump) ω₀)
  · -- `0 < s`: the increment's own pair vanishes.
    have ht0' : 0 < t := lt_of_le_of_lt hs hst
    obtain ⟨R, hRa, hRν, hRexp⟩ := sd_increment_pair P hspos hst.le
    have hRzero : R.exponentL ω = 0 := by
      have h := hRexp ω
      rw [hLeq] at h
      exact (ENNReal.add_right_inj (P.exponentL_ne_top (t * ω))).mp (by rw [add_zero]; exact h)
    rw [SymLevyPair.exponentL] at hRzero
    have ha : P.a = 0 := by
      have h1 : ENNReal.ofReal (R.a * ω ^ 2) = 0 :=
        nonpos_iff_eq_zero.mp (hRzero ▸ le_self_add)
      have h2 : R.a * ω ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h1
      rw [hRa] at h2
      have hts : 0 < t ^ 2 - s ^ 2 := by nlinarith
      have hprod : 0 < (t ^ 2 - s ^ 2) * ω ^ 2 := mul_pos hts (by positivity)
      have h3 : P.a * ((t ^ 2 - s ^ 2) * ω ^ 2) ≤ 0 := by rw [← mul_assoc]; exact h2
      rcases eq_or_lt_of_le P.a_nonneg with h | hpos
      · exact h.symm
      · exact absurd h3 (not_le.2 (mul_pos hpos hprod))
    have hjumpν : (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂R.ν) = 0 :=
      nonpos_iff_eq_zero.mp (hRzero ▸ le_add_self)
    have hincnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ incrementProfile P.k s t x := fun x hx =>
      incrementProfile_nonneg P.k_antitone hspos hst.le hx
    have hincm : AEMeasurable (incrementProfile P.k s t) (volume.restrict (Ioi (0 : ℝ))) :=
      aemeasurable_incrementProfile P.k_antitone hspos hst.le
    have hjump : profileJumpL (incrementProfile P.k s t) ω = 0 := by
      rw [← lintegral_one_sub_cos_profileMeasure hincnn hincm ω, ← hRν]
      exact hjumpν
    have haeinc := ae_eq_zero_of_profileJumpL_eq_zero hincm hincnn hω.ne' hjump
    -- `k(x/t) = k(x/s)` almost everywhere, hence `k(κ y) = k(y)` with `κ = t/s > 1`.
    have hshift : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
        incrementProfile P.k s t (t * y) = 0 :=
      (ae_restrict_Ioi_mul_iff ht0'
        (p := fun x => incrementProfile P.k s t x = 0)).mpr haeinc
    have hdil : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), P.k (t / s * y) = P.k y := by
      filter_upwards [hshift] with y hy
      have hy' : P.k (t * y / t) - P.k (t * y / s) = 0 := hy
      rw [mul_div_cancel_left₀ _ ht0'.ne'] at hy'
      have : t * y / s = t / s * y := by field_simp
      rw [this] at hy'
      linarith
    have hκ : 1 < t / s := (one_lt_div hspos).mpr hst
    have hk := P.k_eq_zero_of_dilation_ae hκ hdil
    exact hω₀ (P.exponent_eq_zero_of_ae ha
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => hk x hx) ω₀)

/-! ## The consequences in the canonical gauge -/

/-- **`prop:strict-positivity`(2), the consequences.** In the canonical gauge no increment is a
lattice law, and the accumulated exponent is strictly increasing in scale at every nonzero
frequency, with no exceptional set.

The lattice clause takes the direct route: a law carried by `pℤ` has cosine transform `1` at
`2π/p`, so its exponent vanishes at a nonzero frequency, which clause (2) forbids. -/
theorem strict_positivity_consequences (P : SDProfile) (hne : ∃ ω : ℝ, P.exponent ω ≠ 0)
    (μ : ℝ → ℝ → Measure ℝ) (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hcos : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω = Real.exp (-(P.exponent (t * ω) - P.exponent (s * ω)))) :
    (∀ s t : ℝ, 0 ≤ s → s < t →
        ∀ p : ℝ, 0 < p → (μ s t) {x : ℝ | ∃ n : ℤ, x = p * n}ᶜ ≠ 0) ∧
      (∀ ω : ℝ, ω ≠ 0 → StrictMonoOn (fun t => P.exponent (t * ω)) (Ici 0)) := by
  constructor
  · intro s t hs hst p hp hcon
    haveI := hprob s t hs hst.le
    -- the kernel is carried by the lattice `pℤ`
    have hae : ∀ᵐ x ∂(μ s t), ∃ n : ℤ, x = p * n := by
      rw [ae_iff]; exact hcon
    set ω₀ : ℝ := 2 * Real.pi / p with hω₀def
    have hω₀ : ω₀ ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * Real.pi / p := div_pos (by linarith [Real.pi_pos]) hp
      exact hpos.ne'
    have hone : fourierCos (μ s t) ω₀ = 1 := by
      rw [fourierCos]
      have hcongr : (∫ x, Real.cos (ω₀ * x) ∂(μ s t)) = ∫ _, (1 : ℝ) ∂(μ s t) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        obtain ⟨n, rfl⟩ := hx
        have hrw : ω₀ * (p * n) = (n : ℝ) * (2 * Real.pi) := by
          rw [hω₀def]; field_simp
        rw [hrw]
        exact Real.cos_int_mul_two_pi n
      rw [hcongr]
      simp
    have hzero : P.exponent (t * ω₀) - P.exponent (s * ω₀) = 0 := by
      have h := hcos s t ω₀ hs hst.le
      rw [hone] at h
      have h0 : Real.exp 0 = Real.exp (-(P.exponent (t * ω₀) - P.exponent (s * ω₀))) := by
        rw [Real.exp_zero]; exact h
      have := Real.exp_eq_exp.mp h0
      linarith
    exact absurd hzero (strict_positivity_strict P hne s t ω₀ hs hst hω₀).ne'
  · intro ω hω a ha b hb hab
    have ha0 : (0 : ℝ) ≤ a := ha
    exact sub_pos.mp (strict_positivity_strict P hne a b ω ha0 hab hω)

end SpatialLine
