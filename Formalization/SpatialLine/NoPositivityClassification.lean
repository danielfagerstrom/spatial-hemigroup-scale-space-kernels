/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.SignedUniqueness
import SpatialLine.MainAnalysis
import SpatialLine.MainConstruction
import SpatialLine.Representation

/-!
# Positivity is exactly admissibility, for a family with function kernels

Blueprint: `prop:no-positivity-no-classification` (`blueprint/src/parts/03-axioms.tex`), the
split half `no_positivity_classification`: for a family satisfying (A1)–(A3), (A5)–(A8) and (ND)
whose off-diagonal operators are convolution by an even integrable `k` with cosine transform
`e^{-(F(t\omega) - F(s\omega))}`, the family satisfies (A4) if and only if `F` is admissible.

## What proving this found

**The `⇐` direction reads three of the node's five hypotheses and none of the three the
estimate named.** It uses `hker` and admissibility of `F`, and *nothing else*: not the
covariance, not the nondegeneracy, not the normalisation `hF0` that wave 5 had to add to make
the split half true. That is hypothesis archaeology in its usual direction — the class of
families the node is about is cited for what it is *for*, and this half consumes two incidental
consequences of it. The reason `hF0` is not needed here is worth naming: the `⇐` direction never
evaluates `F` at a single point, only at differences `F(t\omega) - F(s\omega)`, which is exactly
the invariance that made the *other* direction false without it.

**The signed-uniqueness step is the whole of `⇐`.** Chapter 7's `sd_increment_isSymLevyExponent`
turns the admissible exponent into a symmetric Lévy exponent for every increment `0 ≤ s ≤ t`
(including `s = 0`, which is the case the estimate had to route separately), ledger **A1** and
**A3** turn that into a symmetric probability law, and `ae_nonneg_of_fourierCos_eq`
(`SpatialLine/SignedUniqueness.lean`) identifies `k` with its density. Positivity of the
operators is then positivity of an integral, and the diagonal is `Fam.diag`.

**The `⇒` direction needs no measurable representative and no Lebesgue differentiation.** The
estimate priced "get `k ≥ 0` a.e. out of `IsPositive`" through the approximate identity, and
that is the route; what makes it three lines rather than thirty is that the L¹ positive cone is
*closed* — `Lp` carries an `OrderClosedTopology` instance — so `ρ_ε * k ≥ 0` for every `ε > 0`
passes to the limit `k` directly, with no subsequence and no a.e. convergence argument.
`tendsto_bconv_approxId` is wave 1's, proved for `lem:convolution-representation`, and this is
its second consumer.

**`SDProfile.dilate` is thirty lines and both halves were already in place.** The wave-5
annotation named it as unbuilt and named `profileJumpL_comp_div` and
`lintegral_min_profileMeasure_comp_div_ne_top` as its halves; with `antitoneOn_comp_div` beside
them the structure's six fields and the exponent identity are immediate. It is what carries the
gauge constant `χ 1` out of `main_analysis` and back into an admissible exponent, and it is the
only new definition either direction needs.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## The dilate of an admissible profile -/

/-- **The dilate of an admissible profile**: the profile of `ω ↦ F(cω)`.

Gaussian coefficient `c²a` and profile `k(·/c)`; the monotonicity and the two integrability
conditions are the corresponding facts of `SpatialLine/SelfDecomposable.lean`, proved there for
`lem:selfdecomposable-exponents`. -/
noncomputable def SDProfile.dilate (P : SDProfile) {c : ℝ} (hc : 0 < c) : SDProfile where
  a := c ^ 2 * P.a
  k := fun x => P.k (x / c)
  a_nonneg := mul_nonneg (by positivity) P.a_nonneg
  k_nonneg := fun x hx => P.k_nonneg _ (mem_Ioi.mpr (by
    have hx0 : (0 : ℝ) < x := hx; positivity))
  k_antitone := antitoneOn_comp_div P.k_antitone hc
  k_zero := by simp [P.k_zero]
  integrable_near_zero := by
    have hfin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
      (profile_integrability P.k_nonneg
        (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone)).mpr
        ⟨P.integrable_near_zero, P.integrable_at_top⟩
    exact ((profile_integrability (fun x hx => P.k_nonneg _ (mem_Ioi.mpr (by
        have hx0 : (0 : ℝ) < x := hx; positivity)))
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (antitoneOn_comp_div P.k_antitone hc))).mp
      (lintegral_min_profileMeasure_comp_div_ne_top P.k_antitone P.k_nonneg hfin hc)).1
  integrable_at_top := by
    have hfin : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
      (profile_integrability P.k_nonneg
        (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone)).mpr
        ⟨P.integrable_near_zero, P.integrable_at_top⟩
    exact ((profile_integrability (fun x hx => P.k_nonneg _ (mem_Ioi.mpr (by
        have hx0 : (0 : ℝ) < x := hx; positivity)))
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
        (antitoneOn_comp_div P.k_antitone hc))).mp
      (lintegral_min_profileMeasure_comp_div_ne_top P.k_antitone P.k_nonneg hfin hc)).2

theorem SDProfile.exponentL_dilate (P : SDProfile) {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    (P.dilate hc).exponentL ω = P.exponentL (c * ω) := by
  rw [SDProfile.exponentL_eq_add_jump, SDProfile.exponentL_eq_add_jump]
  congr 1
  · show ENNReal.ofReal (c ^ 2 * P.a * ω ^ 2) = ENNReal.ofReal (P.a * (c * ω) ^ 2)
    ring_nf
  · exact profileJumpL_comp_div P.k hc ω

theorem SDProfile.exponent_dilate (P : SDProfile) {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    (P.dilate hc).exponent ω = P.exponent (c * ω) := by
  rw [SDProfile.exponent, SDProfile.exponent, P.exponentL_dilate hc]

/-! ## Densities and the positive cone of `L¹` -/

/-- Integration against a measure with a nonnegative integrable density.

The wave-6 merge made this the two-line adapter it always was: the general statement, with
`(k y).toNNReal` on the right and no sign hypothesis, is
`SpatialLine.integral_withDensity_ofReal` in `SpatialLine/CosineUniqueness.lean`, and
nonnegativity is spent here and only here, to drop the positive part. -/
theorem integral_withDensity_ofReal_of_nonneg {k : ℝ → ℝ} (hk : Integrable k)
    (hknn : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x) (g : ℝ → ℝ) :
    (∫ y, g y ∂(volume.withDensity fun x => ENNReal.ofReal (k x))) = ∫ y, k y * g y := by
  rw [integral_withDensity_ofReal hk.aemeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hknn] with y hy
  rw [Real.coe_toNNReal _ hy]

/-- A nonnegative integrable density of total mass `1` gives a probability measure. -/
theorem isProbabilityMeasure_withDensity_ofReal {k : ℝ → ℝ} (hk : Integrable k)
    (hknn : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x) (hmass : ∫ x, k x = 1) :
    IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (k x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hk hknn, hmass, ENNReal.ofReal_one]

/-- `IsNonneg` is the order of `L¹`. -/
theorem isNonneg_iff_zero_le (g : X) : IsNonneg g ↔ (0 : X) ≤ g := by
  rw [IsNonneg, ← Lp.coeFn_le]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_zero ℝ 1 (volume : Measure ℝ)] with x hx hz
    rw [hz]; exact hx
  · intro h
    filter_upwards [h, Lp.coeFn_zero ℝ 1 (volume : Measure ℝ)] with x hx hz
    rw [hz] at hx; exact hx

/-- **The positive cone of `L¹` is closed, so a nonnegative approximate-identity smoothing has a
nonnegative limit.** -/
theorem ae_nonneg_of_isNonneg_bconv {k : ℝ → ℝ} (hk : Integrable k)
    (h : ∀ ε : ℝ, 0 < ε → IsNonneg (bconv (approxId ε) (hk.toL1 k))) :
    ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x := by
  have hlim := tendsto_bconv_approxId (hk.toL1 k)
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
      (0 : X) ≤ bconv (approxId ε) (hk.toL1 k) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (isNonneg_iff_zero_le _).mp (h ε hε)
  have hle : (0 : X) ≤ hk.toL1 k := ge_of_tendsto hlim hev
  have hae := (isNonneg_iff_zero_le _).mpr hle
  filter_upwards [hae, hk.coeFn_toL1] with x hx hx2
  rw [← hx2]
  simpa using hx

/-- **(A4) makes a function kernel nonnegative.** -/
theorem ae_nonneg_kernel_of_isPositive {Φ : ℝ → ℝ → (X →L[ℝ] X)} (hpos : IsPositive Φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {k : ℝ → ℝ} (hk : Integrable k)
    (hconv : ∀ f : X, ((Φ s t f : X) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y)) :
    ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ k x := by
  refine ae_nonneg_of_isNonneg_bconv hk fun ε hε => ?_
  have heq : bconv (approxId ε) (hk.toL1 k) = Φ s t (approxIdL1 ε) := by
    rw [← bconv_congr_ae (coeFn_approxIdL1 ε) (hk.toL1 k), ← bconv_comm hk (approxIdL1 ε)]
    exact Lp.ext ((coeFn_bconv hk (approxIdL1 ε)).trans (hconv (approxIdL1 ε)).symm)
  rw [heq]
  exact hpos s t hs hst _ (isNonneg_approxIdL1 ε)

/-! ## The two directions -/

/-- **`no_positivity_classification`, the `⇐` direction.** An admissible `F` makes the family
positive.

**Spends ledger A1 and A3** through `exists_isSymmetric_of_isSymLevyExponent`, and nothing else.
Reads only `hker` and the admissibility: neither the covariance, nor the nondegeneracy, nor the
normalisation `F 0 = 0` is on this direction's path. -/
theorem no_positivity_positive_of_admissible (F : ℝ → ℝ) (Fam : PreCascadeCore)
    (hker : ∀ s t : ℝ, 0 ≤ s → s < t → ∃ k : ℝ → ℝ, Integrable k ∧ (∀ x, k (-x) = k x) ∧
      (∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = Real.exp (-(F (t * ω) - F (s * ω)))) ∧
      (∀ f : X, ((Fam.Φ s t f : X) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y)))
    (hadm : IsAdmissibleExponent F) : IsPositive Fam.Φ := by
  obtain ⟨P, hP⟩ := hadm
  intro s t hs hst f hf
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [Fam.diag s hs]
    simpa using hf
  · obtain ⟨k, hkint, hkeven, hkcos, hkconv⟩ := hker s t hs hlt
    obtain ⟨ν, hνprob, hνsym, hνcos⟩ :=
      exists_isSymmetric_of_isSymLevyExponent (sd_increment_isSymLevyExponent P hs hst)
    have hmatch : ∀ ω, ∫ x, Real.cos (ω * x) * k x = fourierCos ν ω := by
      intro ω
      rw [hkcos ω, hνcos ω, hP, hP]
    obtain ⟨hknn, -⟩ := ae_nonneg_of_fourierCos_eq hkint hkeven hνsym hmatch
    have hfae : ∀ᵐ z ∂(volume : Measure ℝ), 0 ≤ (f : ℝ → ℝ) z := by
      have hf' := hf
      rw [IsNonneg] at hf'
      filter_upwards [hf'] with z hz
      simpa using hz
    filter_upwards [hkconv f] with x hx
    show (0 : ℝ) ≤ ((Fam.Φ s t f : X) : ℝ → ℝ) x
    rw [hx]
    refine integral_nonneg_of_ae ?_
    have hfy : ∀ᵐ y ∂(volume : Measure ℝ), 0 ≤ (f : ℝ → ℝ) (x - y) :=
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae hfae
    filter_upwards [hknn, hfy] with y hy hy2
    exact mul_nonneg hy hy2

/-- **`no_positivity_classification`, the `⇒` direction.** A positive family has an admissible
exponent.

**Spends whatever `main_analysis` spends** — ledger A1 and A3 — and nothing of its own. The
route: (A4) makes each function kernel nonnegative, so it is the density of a probability
measure; the resulting measure family satisfies `IsKernelFamily`, `main_analysis` returns a
gauge `χ` and a profile `P` with `F(ω) = P.exponent (χ 1 · ω)`, and `SDProfile.dilate` absorbs
the constant. `F 0 = 0` is spent at exactly one place, the reading at `s = 0`, which is what
wave 5's counterexample predicted. -/
theorem no_positivity_admissible_of_positive (F : ℝ → ℝ) (hF0 : F 0 = 0) (Fam : PreCascadeCore)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) fun lam t => lam * t)
    (hnd : IsNondegenerate Fam.Φ)
    (hker : ∀ s t : ℝ, 0 ≤ s → s < t → ∃ k : ℝ → ℝ, Integrable k ∧ (∀ x, k (-x) = k x) ∧
      (∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = Real.exp (-(F (t * ω) - F (s * ω)))) ∧
      (∀ f : X, ((Fam.Φ s t f : X) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y)))
    (hpos : IsPositive Fam.Φ) : IsAdmissibleExponent F := by
  classical
  choose kf hkint hkeven hkcos hkconv using hker
  have hknn : ∀ (s t : ℝ) (hs : 0 ≤ s) (hst : s < t),
      ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ kf s t hs hst x := fun s t hs hst =>
    ae_nonneg_kernel_of_isPositive hpos hs hst.le (hkint s t hs hst) (hkconv s t hs hst)
  have hmass : ∀ (s t : ℝ) (hs : 0 ≤ s) (hst : s < t), ∫ x, kf s t hs hst x = 1 := by
    intro s t hs hst
    have h := hkcos s t hs hst 0
    simpa using h
  set μ : ℝ → ℝ → Measure ℝ := fun s t =>
    if h : 0 ≤ s ∧ s < t then volume.withDensity (fun x => ENNReal.ofReal (kf s t h.1 h.2 x))
    else Measure.dirac 0 with hμdef
  have hμlt : ∀ (s t : ℝ) (hs : 0 ≤ s) (hst : s < t),
      μ s t = volume.withDensity fun x => ENNReal.ofReal (kf s t hs hst x) := by
    intro s t hs hst
    rw [hμdef]
    simp only
    rw [dif_pos ⟨hs, hst⟩]
  have hμeq : ∀ s : ℝ, μ s s = Measure.dirac 0 := by
    intro s
    rw [hμdef]
    simp only
    rw [dif_neg (by rintro ⟨-, h⟩; exact lt_irrefl s h)]
  have hkerfam : IsKernelFamily Fam.Φ μ := by
    constructor
    · intro s t hs hst
      rcases eq_or_lt_of_le hst with rfl | hlt
      · rw [hμeq]; infer_instance
      · rw [hμlt s t hs hlt]
        exact isProbabilityMeasure_withDensity_ofReal (hkint s t hs hlt) (hknn s t hs hlt)
          (hmass s t hs hlt)
    · intro s t hs hst f
      rcases eq_or_lt_of_le hst with rfl | hlt
      · rw [hμeq, Fam.diag s hs]
        filter_upwards with x
        simp [mconv]
      · refine (hkconv s t hs hlt f).trans (Filter.EventuallyEq.of_eq (funext fun x => ?_))
        rw [mconv, hμlt s t hs hlt,
          integral_withDensity_ofReal_of_nonneg (hkint s t hs hlt) (hknn s t hs hlt)]
  obtain ⟨χ, P, hχ0, hχm, hχs, -, hPne, -, hfc⟩ :=
    main_analysis ⟨Fam, hpos, hnd⟩ μ hkerfam (fun lam t => lam * t) hcov
  have hχ1 : 0 < χ 1 := by
    have h := hχm (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr zero_le_one) one_pos
    rwa [hχ0] at h
  refine ⟨P.dilate hχ1, fun ω => ?_⟩
  rw [P.exponent_dilate hχ1]
  have h1 := hfc 0 1 ω le_rfl zero_le_one
  have h2 : fourierCos (μ 0 1) ω = Real.exp (-(F (1 * ω) - F (0 * ω))) := by
    rw [hμlt 0 1 le_rfl zero_lt_one, fourierCos,
      integral_withDensity_ofReal_of_nonneg (hkint 0 1 le_rfl zero_lt_one) (hknn 0 1 le_rfl zero_lt_one),
      ← hkcos 0 1 le_rfl zero_lt_one ω]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [h2] at h1
  simp only [hχ0, zero_mul, one_mul, SDProfile.exponent_zero, sub_zero, hF0] at h1
  have h3 := Real.exp_eq_exp.mp h1
  linarith

/-! ## The node's split half -/

/-- **`prop:no-positivity-no-classification`, positivity if and only if admissibility.**

`Skeleton.no_positivity_classification`'s statement verbatim: for a family with the kernel form
of the node, (A4) holds exactly when `F` is an admissible exponent. -/
theorem no_positivity_classification (F : ℝ → ℝ) (hF0 : F 0 = 0) (Fam : PreCascadeCore)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) fun lam t => lam * t)
    (hnd : IsNondegenerate Fam.Φ)
    (hker : ∀ s t : ℝ, 0 ≤ s → s < t → ∃ k : ℝ → ℝ, Integrable k ∧ (∀ x, k (-x) = k x) ∧
      (∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = Real.exp (-(F (t * ω) - F (s * ω)))) ∧
      (∀ f : X, ((Fam.Φ s t f : X) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y))) :
    IsPositive Fam.Φ ↔ IsAdmissibleExponent F :=
  ⟨no_positivity_admissible_of_positive F hF0 Fam hcov hnd hker,
    no_positivity_positive_of_admissible F Fam hker⟩

end SpatialLine
