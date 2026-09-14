/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.BochnerConvolution
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# `lem:convolution-representation`: the operators are convolutions

Blueprint: `blueprint/src/parts/04-representation.tex`, `lem:convolution-representation`.

Under (A1), (A2), (A4), (A5) a single operator on `L¹(ℝ)` is convolution by exactly one
probability measure. The argument is the blueprint's, in four steps: the interchange identity
(`BochnerConvolution.map_bconv`), the approximate identity `ρ_ε = (2ε)⁻¹ 1_{(-ε,ε)}`, tightness,
Prokhorov, and identification against the bounded functionals of `L¹`; uniqueness is the
character pairing of `BochnerConvolution`.

twin: `Hemigroup.CascadeCore.existsUnique_repr`, the same proof on the half-line.

## What the line changes

Two devices of the causal argument fall away and one is new.

* **The tail bound is two-sided and simpler.** The causal proof controls the right tail by
  one-sidedness of causal convolution and kills the left tail by causality outright. Here neither
  is available and neither is needed: convolution with a nonnegative unit-mass density carried by
  `[-1,1]` moves mass by at most `1`, so the tail of `ν_ε` beyond `R+1` is dominated by the tail
  of `ρ₁ * h_ε` beyond `R`, and that converges in `L¹`. The compacts are `[-(R+1), R+1]`. The
  blueprint's remark that this bound "would have served there too" is confirmed by the Lean: the
  set-translation lemma `setIntegral_comp_sub_right` below is stated for an arbitrary measurable
  set, where Paper I's `setIntegral_sub_right` is stated for `Ioi`.

* **The approximate identity is centred.** `ρ_ε = (2ε)⁻¹ 1_{(-ε,ε)}` in place of the causal
  `ε⁻¹ 1_{(0,ε)}`; only the support bound in the convergence proof changes, from `0 < y < ε` to
  `|y| < ε`.

* **Uniqueness is Fourier, not Laplace.** See `BochnerConvolution`.

* **Positivity is a hypothesis, not a field.** The blueprint node names (A1), (A2), (A4), (A5) and
  no others, so the argument is written for a bare bounded operator with three hypotheses spelled
  out. Nothing here mentions a cascade, a reflection or a continuity assumption.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The approximate identity `ρ_ε = (2ε)⁻¹ 1_{(-ε,ε)}` -/

/-- `ρ_ε = (2ε)⁻¹ 1_{(-ε,ε)}`: a probability density carried by `[-ε,ε]`. Total in `ε` — for
`ε ≤ 0` the interval is empty and `ρ_ε = 0` — so no positivity hypothesis is needed to state
integrability.

twin: `Hemigroup.approxId`, centred. -/
noncomputable def approxId (ε : ℝ) : ℝ → ℝ :=
  fun x => (2 * ε)⁻¹ * (Ioo (-ε) ε).indicator (fun _ => (1 : ℝ)) x

lemma approxId_eq_zero {ε x : ℝ} (hx : x ∉ Ioo (-ε) ε) : approxId ε x = 0 := by
  simp [approxId, Set.indicator_of_notMem hx]

lemma approxId_nonneg (ε : ℝ) (x : ℝ) : 0 ≤ approxId ε x := by
  rcases le_or_gt ε 0 with h | h
  · have hempty : (Ioo (-ε) ε) = ∅ := Ioo_eq_empty (by simp; linarith)
    simp [approxId, hempty]
  · exact mul_nonneg (inv_nonneg.mpr (by linarith))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

lemma measurable_approxId (ε : ℝ) : Measurable (approxId ε) :=
  measurable_const.mul (measurable_const.indicator measurableSet_Ioo)

lemma integrable_approxId (ε : ℝ) : Integrable (approxId ε) :=
  (IntegrableOn.integrable_indicator
    (integrableOn_const (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    measurableSet_Ioo).const_mul _

lemma integral_approxId {ε : ℝ} (hε : 0 < ε) : ∫ x, approxId ε x = 1 := by
  simp only [approxId]
  rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Ioo, sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith)]
  rw [show ε + ε = 2 * ε by ring, inv_mul_cancel₀ (by positivity)]

/-- `ρ_ε` as an element of `X`. -/
noncomputable def approxIdL1 (ε : ℝ) : X := (integrable_approxId ε).toL1 _

lemma coeFn_approxIdL1 (ε : ℝ) : ((approxIdL1 ε : X) : ℝ → ℝ) =ᵐ[volume] approxId ε :=
  Integrable.coeFn_toL1 _

lemma isNonneg_approxIdL1 (ε : ℝ) : IsNonneg (approxIdL1 ε) := by
  filter_upwards [coeFn_approxIdL1 ε] with x hx
  simp only [Pi.zero_apply, hx]
  exact approxId_nonneg ε x

lemma integral_approxIdL1 {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ((approxIdL1 ε : X) : ℝ → ℝ) x = 1 := by
  rw [integral_congr_ae (coeFn_approxIdL1 ε)]
  exact integral_approxId hε

@[simp] lemma transL1_zero (g : X) : transL1 0 g = g := by
  refine Lp.ext ((coeFn_transL1 0 g).trans ?_)
  filter_upwards with x
  rw [sub_zero]

/-- **`ρ_ε * g → g` in `L¹`.** The mass sits in `(-ε,ε)`, where `T_y g` is within `δ` of `g` by
continuity of translation — so the average of the translates is too. -/
theorem tendsto_bconv_approxId (g : X) :
    Tendsto (fun ε => bconv (approxId ε) g) (nhdsWithin 0 (Ioi 0)) (nhds g) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hcont : ContinuousAt (fun y => transL1 y g) 0 := (continuous_transL1 g).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, hηb⟩ := hcont (δ / 2) (by linarith)
  refine ⟨η, hη, fun {ε} hε hd => ?_⟩
  have hε0 : 0 < ε := hε
  have hεη : ε < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hd
    exact hd
  have hint0 : Integrable (fun y => approxId ε y • (transL1 y g - g)) := by
    simp only [smul_sub]
    exact (integrable_smul_transL1 (integrable_approxId ε) g).sub
      ((integrable_approxId ε).smul_const g)
  have hsub : bconv (approxId ε) g - g = ∫ y, approxId ε y • (transL1 y g - g) := by
    have hsplit : ∫ y, approxId ε y • (transL1 y g - g)
        = (∫ y, approxId ε y • transL1 y g) - ∫ y, approxId ε y • g := by
      simp only [smul_sub]
      exact integral_sub (integrable_smul_transL1 (integrable_approxId ε) g)
        ((integrable_approxId ε).smul_const g)
    rw [hsplit, bconv, integral_smul_const, integral_approxId hε0, one_smul]
  have hbound : ∀ y, ‖approxId ε y • (transL1 y g - g)‖ ≤ approxId ε y * (δ / 2) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (approxId_nonneg ε y)]
    by_cases hy : y ∈ Ioo (-ε) ε
    · refine mul_le_mul_of_nonneg_left ?_ (approxId_nonneg ε y)
      have hdy : dist y 0 < η := by
        rw [Real.dist_eq, sub_zero, abs_lt]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := hηb hdy
      rw [transL1_zero, dist_eq_norm] at this
      exact this.le
    · rw [approxId_eq_zero hy]
      simp
  calc dist (bconv (approxId ε) g) g = ‖bconv (approxId ε) g - g‖ := dist_eq_norm _ _
    _ = ‖∫ y, approxId ε y • (transL1 y g - g)‖ := by rw [hsub]
    _ ≤ ∫ y, ‖approxId ε y • (transL1 y g - g)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, approxId ε y * (δ / 2) :=
        integral_mono hint0.norm ((integrable_approxId ε).mul_const _) hbound
    _ = δ / 2 := by rw [integral_mul_const, integral_approxId hε0, one_mul]
    _ < δ := by linarith

/-- **`f * ρ_ε → f`**, the form the representation argument consumes: the approximate identity
sits in the second slot, so that `Φ (f * ρ_ε) = f * (Φ ρ_ε)` puts `Φ` on the varying factor. -/
theorem tendsto_bconv_approxIdL1 {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconv f (approxIdL1 ε)) (nhdsWithin 0 (Ioi 0)) (nhds (hf.toL1 f)) := by
  have hcongr : ∀ ε : ℝ, bconv f (approxIdL1 ε) = bconv (approxId ε) (hf.toL1 f) := fun ε => by
    rw [bconv_comm hf (approxIdL1 ε)]
    exact bconv_congr_ae (Integrable.coeFn_toL1 (integrable_approxId ε)) _
  simp only [hcongr]
  exact tendsto_bconv_approxId _


/-! ## The approximants `h_ε = Φ ρ_ε`

(A4) and (A5) say exactly that `h_ε` is a probability density, which is what makes
`ν_ε := h_ε dx` a probability measure — the object Prokhorov will act on.
-/

/-- `h_ε = Φ ρ_ε`, the image of the approximate identity. -/
noncomputable def approx (L : X →L[ℝ] X) (ε : ℝ) : X := L (approxIdL1 ε)

/-- `ν_ε = h_ε dx`. -/
noncomputable def approxMeasure (L : X →L[ℝ] X) (ε : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal ((approx L ε : X) x)

variable {L : X →L[ℝ] X}

lemma isNonneg_approx (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f)) (ε : ℝ) :
    IsNonneg (approx L ε) := hpos _ (isNonneg_approxIdL1 ε)

lemma integral_approx
    (hmass : ∀ f : X, IsNonneg f → ∫ x, ((L f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x)
    {ε : ℝ} (hε : 0 < ε) : ∫ x, ((approx L ε : X) : ℝ → ℝ) x = 1 := by
  rw [approx, hmass _ (isNonneg_approxIdL1 ε)]
  exact integral_approxIdL1 hε

/-- **`f * h_ε = Φ (f * ρ_ε)`**, the identity the whole argument turns on: `map_bconv` with (A2)
supplying the commutation. -/
theorem bconv_approx (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    {f : ℝ → ℝ} (hf : Integrable f) (ε : ℝ) :
    bconv f (approx L ε) = L (bconv f (approxIdL1 ε)) :=
  (map_bconv L htrans hf (approxIdL1 ε)).symm

/-- **`f * h_ε → Φ f`.** The left side is `Φ (f * ρ_ε)` and `f * ρ_ε → f`, so this is continuity
of a bounded operator. -/
theorem tendsto_bconv_approx (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun ε => bconv f (approx L ε)) (nhdsWithin 0 (Ioi 0)) (nhds (L (hf.toL1 f))) := by
  simp only [bconv_approx htrans hf]
  exact (L.continuous.tendsto _).comp (tendsto_bconv_approxIdL1 hf)

lemma isProbabilityMeasure_approxMeasure (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f))
    (hmass : ∀ f : X, IsNonneg f → ∫ x, ((L f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x)
    {ε : ℝ} (hε : 0 < ε) : IsProbabilityMeasure (approxMeasure L ε) := by
  constructor
  rw [approxMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _) (isNonneg_approx hpos ε),
    integral_approx hmass hε, ENNReal.ofReal_one]

/-! ## Tightness

The tail of `ν_ε` beyond `R+1` is dominated by the tail of `ρ₁ * h_ε` beyond `R`, because
convolving with a density carried by `[-1,1]` can only move mass by `1`. And `ρ₁ * h_ε` converges
in `L¹`, so its tails are small uniformly — which is tightness.
-/

/-- The two-sided tail `{|x| > R}`. -/
def tailSet (R : ℝ) : Set ℝ := {x : ℝ | R < |x|}

lemma measurableSet_tailSet (R : ℝ) : MeasurableSet (tailSet R) :=
  measurableSet_lt measurable_const measurable_norm

lemma tailSet_antitone {R R' : ℝ} (h : R ≤ R') : tailSet R' ⊆ tailSet R :=
  fun _ hx => lt_of_le_of_lt h hx

/-- Translating a restricted integral: `∫_A φ(x - y) dx = ∫_{A - y} φ`. Stated for an arbitrary
measurable set, which is what makes the two-sided tail bound no harder than the one-sided one —
Paper I states the same lemma for `Ioi` alone. -/
theorem setIntegral_comp_sub_right (φ : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) (y : ℝ) :
    ∫ x in A, φ (x - y) = ∫ u in (fun u : ℝ => u + y) ⁻¹' A, φ u := by
  have hA2 : MeasurableSet ((fun u : ℝ => u + y) ⁻¹' A) := hA.preimage (measurable_add_const y)
  rw [← integral_indicator hA, ← integral_indicator hA2,
    ← integral_add_right_eq_self (fun x : ℝ => A.indicator (fun z => φ (z - y)) x) y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show A.indicator (fun z => φ (z - y)) (u + y)
      = ((fun u : ℝ => u + y) ⁻¹' A).indicator φ u
  by_cases hu : u + y ∈ A
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u ∈ _ from hu), add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show u ∉ _ from hu)]

/-- **The tail of `ν_ε` beyond `R+1` is dominated by the tail of `ρ₁ * h_ε` beyond `R`.**

Convolution with a nonnegative unit-mass density carried by `[-1,1]` moves mass by at most `1`:
for `|y| < 1` the preimage `{x : |x + y| > R}` contains `{|x| > R + 1}`. -/
theorem tail_le_tail_bconv {h : X} (hnn : IsNonneg h) (R : ℝ) :
    ∫ u in tailSet (R + 1), (h : ℝ → ℝ) u
      ≤ ∫ x in tailSet R, ((bconv (approxId 1) h : X) : ℝ → ℝ) x := by
  have hpass := setIntegral_bconv (tailSet R) (integrable_approxId 1) h
  have hintg := integrable_setIntegral_bconv (tailSet R) (integrable_approxId 1) h
  have hmono : ∀ y, approxId 1 y * (∫ u in tailSet (R + 1), (h : ℝ → ℝ) u)
      ≤ approxId 1 y * ∫ x in tailSet R, (h : ℝ → ℝ) (x - y) := by
    intro y
    by_cases hy : y ∈ Ioo (-1 : ℝ) 1
    · refine mul_le_mul_of_nonneg_left ?_ (approxId_nonneg 1 y)
      rw [setIntegral_comp_sub_right _ (measurableSet_tailSet R) y]
      refine setIntegral_mono_set (L1.integrable_coeFn h).integrableOn
        (ae_restrict_of_ae hnn) (HasSubset.Subset.eventuallyLE fun u hu => ?_)
      simp only [tailSet, Set.mem_setOf_eq, Set.mem_preimage] at hu ⊢
      have h1 : |u| - |y| ≤ |u + y| := by
        have := abs_sub_abs_le_abs_sub u (-y)
        simpa [sub_neg_eq_add, abs_neg] using this
      have h2 : |y| < 1 := abs_lt.mpr ⟨hy.1, hy.2⟩
      linarith
    · rw [approxId_eq_zero hy, zero_mul, zero_mul]
  rw [hpass]
  calc ∫ u in tailSet (R + 1), (h : ℝ → ℝ) u
      = ∫ y, approxId 1 y * ∫ u in tailSet (R + 1), (h : ℝ → ℝ) u := by
        rw [integral_mul_const, integral_approxId one_pos, one_mul]
    _ ≤ ∫ y, approxId 1 y * ∫ x in tailSet R, (h : ℝ → ℝ) (x - y) :=
        integral_mono ((integrable_approxId 1).mul_const _) hintg hmono

/-! ### Tails vanish -/

/-- The two-sided tail of a finite measure can be made as small as wanted. -/
theorem exists_measure_tailSet_le (ν : Measure ℝ) [IsFiniteMeasure ν] {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, ν (tailSet R) ≤ η := by
  have hmono : Antitone fun n : ℕ => tailSet (n : ℝ) := fun m n hmn =>
    tailSet_antitone (by exact_mod_cast hmn)
  have hinter : (⋂ n : ℕ, tailSet (n : ℝ)) = ∅ := by
    ext x
    simp only [Set.mem_iInter, tailSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, hn.le⟩
  have h := tendsto_measure_iInter_atTop
    (fun n : ℕ => (measurableSet_tailSet (n : ℝ)).nullMeasurableSet) hmono
    ⟨0, measure_ne_top ν _⟩
  rw [hinter, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hη)).exists
  exact ⟨n, hn.le⟩

/-- The two-sided tail of the absolute value of an integrable function can be made as small as
wanted. -/
theorem exists_setIntegral_abs_tailSet_le {k : ℝ → ℝ} (hk : Integrable k) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∫ u in tailSet R, |k u| ≤ η := by
  set ν : Measure ℝ := volume.withDensity fun x => ‖k x‖ₑ with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hk.2
  obtain ⟨R, hR⟩ := exists_measure_tailSet_le ν (η := ENNReal.ofReal η)
    (by simp only [ENNReal.ofReal_pos]; linarith)
  refine ⟨R, ?_⟩
  have hval : ν (tailSet R) = ∫⁻ u in tailSet R, ‖k u‖ₑ :=
    withDensity_apply _ (measurableSet_tailSet R)
  have heq : ∫ u in tailSet R, |k u| = (∫⁻ u in tailSet R, ‖k u‖ₑ).toReal := by
    simpa [Real.norm_eq_abs] using
      integral_norm_eq_lintegral_enorm (hk.aestronglyMeasurable.restrict)
  rw [heq, ← hval]
  calc (ν (tailSet R)).toReal ≤ (ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hR
    _ = η := ENNReal.toReal_ofReal hη.le

/-! ### The tightness statement -/

/-- The sequence `ε n = 1/(n+1)` along which the approximants are taken. -/
noncomputable def epsSeq (n : ℕ) : ℝ := 1 / (n + 1)

lemma epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  rw [epsSeq]; positivity

lemma tendsto_epsSeq : Tendsto epsSeq atTop (nhdsWithin 0 (Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => epsSeq_pos n)

/-- **The tails of `ν_{ε n}` are small uniformly in `n`.**

For large `n` the bound comes from `ρ₁ * h_{ε n} → Φ ρ₁` in `L¹` together with
`tail_le_tail_bconv`; for the finitely many small `n` each density is integrable and supplies its
own cutoff, and the maximum serves for all. -/
theorem exists_uniform_tail (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f)) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ n : ℕ, ∫ u in tailSet R, ((approx L (epsSeq n) : X) : ℝ → ℝ) u ≤ η := by
  set k : X := L ((integrable_approxId 1).toL1 (approxId 1)) with hk
  obtain ⟨R₁, hR₁⟩ := exists_setIntegral_abs_tailSet_le (L1.integrable_coeFn k) (η := η / 2)
    (by linarith)
  have hconv : Tendsto (fun n => bconv (approxId 1) (approx L (epsSeq n))) atTop (nhds k) :=
    (tendsto_bconv_approx htrans (integrable_approxId 1)).comp tendsto_epsSeq
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (η / 2) (by linarith)
  have hfin : ∀ m : ℕ, ∃ R : ℝ, ∫ u in tailSet R,
      ((approx L (epsSeq m) : X) : ℝ → ℝ) u ≤ η := by
    intro m
    obtain ⟨R, hR⟩ := exists_setIntegral_abs_tailSet_le
      (L1.integrable_coeFn (approx L (epsSeq m))) hη
    refine ⟨R, le_trans ?_ hR⟩
    exact setIntegral_mono_on (L1.integrable_coeFn _).integrableOn
      (L1.integrable_coeFn (approx L (epsSeq m))).abs.integrableOn (measurableSet_tailSet R)
      fun u _ => le_abs_self _
  choose Rsmall hRsmall using hfin
  obtain ⟨M, hM⟩ := Finset.exists_le ((Finset.range N).image Rsmall)
  refine ⟨max (max R₁ M + 1) M, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hd := hN n hn
    rw [dist_eq_norm] at hd
    set F : X := bconv (approxId 1) (approx L (epsSeq n)) with hF
    have hstep : ∫ x in tailSet (max R₁ M), (F : ℝ → ℝ) x ≤ η := by
      have hdiff : Integrable (fun x => (F : ℝ → ℝ) x - (k : ℝ → ℝ) x) :=
        (L1.integrable_coeFn F).sub (L1.integrable_coeFn k)
      have habsk : Integrable (fun x => |(k : ℝ → ℝ) x|) := (L1.integrable_coeFn k).abs
      calc ∫ x in tailSet (max R₁ M), (F : ℝ → ℝ) x
          ≤ ∫ x in tailSet (max R₁ M),
              (|(k : ℝ → ℝ) x| + |(F : ℝ → ℝ) x - (k : ℝ → ℝ) x|) := by
            refine setIntegral_mono_on (L1.integrable_coeFn F).integrableOn
              (habsk.add hdiff.abs).integrableOn (measurableSet_tailSet _) fun u _ => ?_
            calc (F : ℝ → ℝ) u = (k : ℝ → ℝ) u + ((F : ℝ → ℝ) u - (k : ℝ → ℝ) u) := by ring
              _ ≤ |(k : ℝ → ℝ) u| + |(F : ℝ → ℝ) u - (k : ℝ → ℝ) u| :=
                  add_le_add (le_abs_self _) (le_abs_self _)
        _ = (∫ x in tailSet (max R₁ M), |(k : ℝ → ℝ) x|)
              + ∫ x in tailSet (max R₁ M), |(F : ℝ → ℝ) x - (k : ℝ → ℝ) x| :=
            integral_add habsk.integrableOn hdiff.abs.integrableOn
        _ ≤ η / 2 + η / 2 := by
            refine add_le_add (le_trans ?_ hR₁) ?_
            · exact setIntegral_mono_set habsk.integrableOn
                (ae_restrict_of_ae (Filter.Eventually.of_forall fun u => abs_nonneg _))
                (HasSubset.Subset.eventuallyLE (tailSet_antitone (le_max_left _ _)))
            · calc ∫ x in tailSet (max R₁ M), |(F : ℝ → ℝ) x - (k : ℝ → ℝ) x|
                  ≤ ∫ x, |(F : ℝ → ℝ) x - (k : ℝ → ℝ) x| :=
                    setIntegral_le_integral hdiff.abs
                      (Filter.Eventually.of_forall fun u => abs_nonneg _)
                _ = ‖F - k‖ := by
                    have hnorm : ‖F - k‖
                        = (∫⁻ x, ‖(F : ℝ → ℝ) x - (k : ℝ → ℝ) x‖ₑ).toReal := by
                      rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
                      congr 1
                      refine lintegral_congr_ae ?_
                      filter_upwards [Lp.coeFn_sub F k] with x hx
                      rw [hx]
                      rfl
                    rw [hnorm, ← integral_norm_eq_lintegral_enorm
                      (f := fun x => (F : ℝ → ℝ) x - (k : ℝ → ℝ) x)
                      hdiff.aestronglyMeasurable]
                    simp only [Real.norm_eq_abs]
                _ ≤ η / 2 := hd.le
        _ = η := by ring
    refine le_trans (le_trans ?_ (tail_le_tail_bconv (isNonneg_approx hpos (epsSeq n))
      (max R₁ M))) hstep
    exact setIntegral_mono_set (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonneg_approx hpos _))
      (HasSubset.Subset.eventuallyLE (tailSet_antitone (le_max_left _ _)))
  · rw [not_le] at hn
    refine le_trans ?_ (hRsmall n)
    exact setIntegral_mono_set (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonneg_approx hpos _))
      (HasSubset.Subset.eventuallyLE
        (tailSet_antitone (le_trans
          (hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn)))
          (le_max_right _ _))))

/-- The tail of `ν_ε`, in terms of the density. -/
lemma approxMeasure_tailSet (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f)) (ε R : ℝ) :
    approxMeasure L ε (tailSet R)
      = ENNReal.ofReal (∫ u in tailSet R, ((approx L ε : X) : ℝ → ℝ) u) := by
  rw [approxMeasure, withDensity_apply _ (measurableSet_tailSet R),
    ← ofReal_integral_eq_lintegral_ofReal (L1.integrable_coeFn _).integrableOn
      (ae_restrict_of_ae (isNonneg_approx hpos ε))]

/-- **The approximants are tight.** The compacts are `[-R, R]`; the whole content is
`exists_uniform_tail`. -/
theorem isTightMeasureSet_approxMeasure (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f)) :
    IsTightMeasureSet {ν : Measure ℝ | ∃ n : ℕ, ν = approxMeasure L (epsSeq n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨∅, isCompact_empty, fun ν _ => le_top⟩
  have hη0 : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨R, hR⟩ := exists_uniform_tail htrans hpos hη0
  refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (Icc (-R) R)ᶜ ⊆ tailSet R := by
    intro u hu
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hu
    simp only [tailSet, Set.mem_setOf_eq, lt_abs]
    rcases hu with hu | hu
    · exact Or.inr (by linarith)
    · exact Or.inl hu
  calc approxMeasure L (epsSeq n) ((Icc (-R) R)ᶜ)
      ≤ approxMeasure L (epsSeq n) (tailSet R) := measure_mono hsub
    _ ≤ η := by
        rw [approxMeasure_tailSet hpos]
        calc ENNReal.ofReal (∫ u in tailSet R, ((approx L (epsSeq n) : X) : ℝ → ℝ) u)
            ≤ ENNReal.ofReal η.toReal := ENNReal.ofReal_le_ofReal (hR n)
          _ = η := ENNReal.ofReal_toReal hηtop

/-! ## The limit measure

Prokhorov turns tightness into a convergent subsequence. `ProbabilityMeasure ℝ` is metrizable
because `ℝ` is Polish, so compactness of the closure gives sequential compactness.
-/

/-- **A weak limit exists.** Some subsequence of the approximants converges weakly to a
probability measure. -/
theorem exists_weak_limit (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f))
    (hmass : ∀ f : X, IsNonneg f → ∫ x, ((L f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x) :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ),
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ φ : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun j => ∫ x, φ x ∂(approxMeasure L (epsSeq (σ j)))) atTop
          (nhds (∫ x, φ x ∂μ)) := by
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (approxMeasure L (epsSeq n)) := fun n =>
    isProbabilityMeasure_approxMeasure hpos hmass (epsSeq_pos n)
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨approxMeasure L (epsSeq n), hprob n⟩ with hP
  have hsetEq : {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν}
      = {ν : Measure ℝ | ∃ n : ℕ, ν = approxMeasure L (epsSeq n)} := by
    ext ν
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  have hset : IsTightMeasureSet {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν} := by
    rw [hsetEq]
    exact isTightMeasureSet_approxMeasure htrans hpos
  have hcompact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet hset
  obtain ⟨Q, -, σ, hσ, hQ⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨(Q : Measure ℝ), Q.2, σ, hσ,
    fun φ => (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ) φ⟩

/-! ## The identification

`exists_weak_limit` produces a measure; this section shows it is *the* measure. The proof pairs
both sides against an arbitrary bounded functional and reads off three ingredients: the pairing of
`f * h_ε` as an integral against `ν_ε`, weak convergence of `ν_ε` tested on the bounded continuous
function `pairTrans Ψ f`, and `apply_mconvL1`. Nothing here is pointwise, so — as in Paper I — the
blueprint restriction to `f` continuous with compact support, followed by a density argument,
disappears.
-/

/-- Integration against `ν_ε` is integration against the density `h_ε`. -/
theorem integral_approxMeasure (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f)) (ε : ℝ)
    (G : BoundedContinuousFunction ℝ ℝ) :
    ∫ y, G y ∂(approxMeasure L ε) = ∫ y, ((approx L ε : X) : ℝ → ℝ) y * G y := by
  rw [approxMeasure, integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable (approx L ε)).aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [isNonneg_approx hpos ε] with y hy
  rw [smul_eq_mul, ENNReal.toReal_ofReal hy]

/-- **The pairing identity in the limit.** For every bounded functional, `Ψ (Φ f)` is the integral
of the bounded continuous function `y ↦ Ψ (T_y f)` against the weak limit. -/
theorem apply_eq_integral_pairTrans (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f))
    {μ : Measure ℝ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hweak : ∀ φ : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, φ x ∂(approxMeasure L (epsSeq (σ j)))) atTop
        (nhds (∫ x, φ x ∂μ)))
    (Ψ : X →L[ℝ] ℝ) (f : X) :
    Ψ (L f) = ∫ y, pairTrans Ψ f y ∂μ := by
  have hfL : (L1.integrable_coeFn f).toL1 (f : ℝ → ℝ) = f :=
    Integrable.toL1_coeFn f (L1.integrable_coeFn f)
  have h1 : Tendsto (fun j => Ψ (bconv (f : ℝ → ℝ) (approx L (epsSeq (σ j))))) atTop
      (nhds (Ψ (L f))) := by
    have hlim := (tendsto_bconv_approx htrans (L := L) (L1.integrable_coeFn f)).comp
      (tendsto_epsSeq.comp hσ.tendsto_atTop)
    rw [hfL] at hlim
    exact (Ψ.continuous.tendsto _).comp hlim
  have h2 : ∀ j : ℕ, Ψ (bconv (f : ℝ → ℝ) (approx L (epsSeq (σ j))))
      = ∫ y, pairTrans Ψ f y ∂(approxMeasure L (epsSeq (σ j))) := by
    intro j
    rw [bconv_comm (L1.integrable_coeFn f) (approx L (epsSeq (σ j))), hfL,
      apply_bconv Ψ (L1.integrable_coeFn _) f, integral_approxMeasure hpos]
  refine tendsto_nhds_unique h1 ?_
  simpa only [h2] using hweak (pairTrans Ψ f)

/-- **`lem:convolution-representation`, existence.** A bounded operator on `L¹(ℝ)` satisfying
(A2), (A4) and (A5) is convolution by a probability measure. -/
theorem exists_isProbabilityMeasure_eq_mconvL1
    (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f))
    (hmass : ∀ f : X, IsNonneg f → ∫ x, ((L f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x) :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ), L = mconvL1 μ := by
  obtain ⟨μ, hprob, σ, hσ, hweak⟩ := exists_weak_limit htrans hpos hmass
  refine ⟨μ, hprob, ContinuousLinearMap.ext fun f => Lp.ext ?_⟩
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (L f)).integrableOn)
    (fun A _ _ => (L1.integrable_coeFn (mconvL1 μ f)).integrableOn) fun A _ _ => ?_
  rw [← setIntegralCLM_apply A (L f), ← setIntegralCLM_apply A (mconvL1 μ f),
    apply_eq_integral_pairTrans htrans hpos hσ hweak, apply_mconvL1]


/-! ## Uniqueness, symmetry, and the node

The existence statement above is about the operator; the blueprint node reads the representation
at the level of representatives, `Φ f =ᵐ μ * f`, which is equality in `X`. The bridge is
`eq_mconvL1_of_ae`, and uniqueness is `mconvL1_injective`.
-/

/-- Reading the representation at the level of representatives is equality of operators. -/
theorem eq_mconvL1_of_ae {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : ∀ f : X, ((L f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ)) :
    L = mconvL1 μ :=
  ContinuousLinearMap.ext fun f => Lp.ext ((h f).trans (coeFn_mconvL1 μ f).symm)

/-- **`lem:convolution-representation`, existence and uniqueness, for a single operator.** -/
theorem existsUnique_repr_of_operator
    (htrans : ∀ a f, L (transL1 a f) = transL1 a (L f))
    (hpos : ∀ f : X, IsNonneg f → IsNonneg (L f))
    (hmass : ∀ f : X, IsNonneg f → ∫ x, ((L f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ f : X, ((L f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ) := by
  obtain ⟨μ, hprob, heq⟩ := exists_isProbabilityMeasure_eq_mconvL1 htrans hpos hmass
  refine ⟨μ, ⟨hprob, fun f => ?_⟩, ?_⟩
  · rw [heq]
    exact coeFn_mconvL1 μ f
  · rintro ρ ⟨hρ, hρeq⟩
    haveI := hρ
    exact mconvL1_injective ((eq_mconvL1_of_ae hρeq).symm.trans heq)

/-! ### Reflection

The symmetry rider is a statement about a representing measure already in hand, not a clause of
the existence statement — which is how the blueprint states it, and why: the representation is
wanted in settings where (A3) is present and in settings where it is not.
-/

/-- Reflection is an involution of `L¹`. -/
lemma reflL1_reflL1 (f : X) : reflL1 (reflL1 f) = f := by
  refine Lp.ext ?_
  refine ((coeFn_reflL1 (reflL1 f)).trans (reflect_congr_ae (coeFn_reflL1 f))).trans ?_
  filter_upwards with x
  simp

/-- **The reflected measure gives the conjugated operator**: `(Rμ) * f = R (μ * (R f))`. -/
theorem mconvL1_map_neg (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    mconvL1 (μ.map (fun x : ℝ => -x)) f = reflL1 (mconvL1 μ (reflL1 f)) := by
  haveI : IsFiniteMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isFiniteMeasure_map μ (fun x : ℝ => -x)
  set f₀ := (Lp.aestronglyMeasurable f).mk (f : ℝ → ℝ) with hf₀
  have hfm : StronglyMeasurable f₀ := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hfae : (f : ℝ → ℝ) =ᵐ[volume] f₀ := (Lp.aestronglyMeasurable f).ae_eq_mk
  refine Lp.ext ?_
  have hlhs : ((mconvL1 (μ.map (fun x : ℝ => -x)) f : X) : ℝ → ℝ)
      =ᵐ[volume] mconv (μ.map (fun x : ℝ => -x)) f₀ :=
    (coeFn_mconvL1 _ f).trans (mconv_congr_ae _ hfae)
  have hrhs : ((reflL1 (mconvL1 μ (reflL1 f)) : X) : ℝ → ℝ)
      =ᵐ[volume] fun x => mconv μ (fun u => f₀ (-u)) (-x) :=
    (coeFn_reflL1 _).trans (reflect_congr_ae
      ((coeFn_mconvL1 μ (reflL1 f)).trans
        (mconv_congr_ae μ ((coeFn_reflL1 f).trans (reflect_congr_ae hfae)))))
  refine hlhs.trans (Filter.EventuallyEq.symm (hrhs.trans ?_))
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [mconv_apply]
  have hmap : ∫ y, f₀ (x - y) ∂(μ.map (fun x : ℝ => -x)) = ∫ u, f₀ (x - -u) ∂μ :=
    integral_map measurable_neg.aemeasurable
      ((hfm.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable)
  rw [hmap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  congr 1
  ring

/-- **`lem:convolution-representation`, the symmetry rider, for a single operator.** -/
theorem isSymmetric_of_reflL1 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hL : L = mconvL1 μ) (hrefl : ∀ f : X, L (reflL1 f) = reflL1 (L f)) : IsSymmetric μ := by
  haveI : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  refine mconvL1_injective (ContinuousLinearMap.ext fun f => ?_)
  rw [mconvL1_map_neg, ← hL, hrefl, reflL1_reflL1, hL]

/-! ## The blueprint node -/

/-- **`lem:convolution-representation`, existence and uniqueness.**

Reading: the hypotheses are (A1) — carried by the type `X →L[ℝ] X` — together with (A2), (A4)
and (A5) spelled out, because those are the four axioms the node names. The conclusion is
`∃!` over probability measures, with the representation read at the level of representatives
(`=ᵐ[volume]`), which is equality in `X`.

twin: `Hemigroup.CascadeCore.existsUnique_repr`. -/
theorem representation_existsUnique (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (htrans : ∀ s t, 0 ≤ s → s ≤ t → ∀ a f, Φ s t (transL1 a f) = transL1 a (Φ s t f))
    (hpos : IsPositive Φ)
    (hmass : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f →
      ∫ x, ((Φ s t f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ f : X, ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ) :=
  existsUnique_repr_of_operator (htrans s t hs hst) (hpos s t hs hst) (hmass s t hs hst)

set_option linter.unusedVariables false in
/-- **`lem:convolution-representation`, the symmetry rider.**

Reading: symmetry is a *rider* on a representing measure already in hand, not a clause of the
existence statement — which is how the blueprint states it, and why: the representation is wanted
in settings where (A3) is present and in settings where it is not.

The hypotheses (A2), (A4) and (A5) are carried unused: the reviewed statement lists them because
the node lists them, and the finding is that the *rider* needs only (A3) and a representing
measure already in hand. The linter is silenced rather than the statement changed. -/
theorem representation_symmetric (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (htrans : ∀ s t, 0 ≤ s → s ≤ t → ∀ a f, Φ s t (transL1 a f) = transL1 a (Φ s t f))
    (hpos : IsPositive Φ)
    (hmass : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f →
      ∫ x, ((Φ s t f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x)
    (hrefl : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, Φ s t (reflL1 f) = reflL1 (Φ s t f))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ f : X, ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ)) :
    IsSymmetric μ :=
  isSymmetric_of_reflL1 (eq_mconvL1_of_ae hμ) (hrefl s t hs hst)

end SpatialLine
