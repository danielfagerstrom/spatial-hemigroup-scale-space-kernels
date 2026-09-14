/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Symbol
import SpatialLine.SincAverage
import SpatialLine.AnalysisDirection
import SpatialLine.ProfileOfMeasure

/-!
# `lem:selfdecomposable-exponents`, (2) implies (3)

Blueprint: `blueprint/src/parts/07-characterization.tex`, `lem:selfdecomposable-exponents`.

Given a symmetric Lévy exponent `F` whose symbol `B(ω) = ω F'(ω)` is again a symmetric Lévy
exponent, with pair `(a_B, ϖ)`, the profile is the tail function of `ϖ`, `k(x) = ϖ((x,∞))`, and
the claim is that `F` is of the profile form `eq:sd-profile` at `(a_B/2, k)`.

## The ordering, and where the skeleton's estimate was right

The skeleton prices this direction as blocked on the *second* integrability condition of
`SDProfile`, `∫₁^∞ k(x)x⁻¹dx < ∞`, which is `∫ log₊ u ϖ(du) < ∞` and is **not** implied by the
Lévy condition on `ϖ` — the counterexample `ϖ(du) = du/(u log²u)` on `(2,∞)` is decisive. That
is right, and it is what fixes the order of the proof: the profile data cannot be assembled
until both conditions are in hand, so the representation `F(ω) = ½a_Bω² + ∫Cin(ωu)ϖ(du)` cannot
be the step that supplies them.

What supplies the second condition is the finiteness of `F`, as an **inequality**:

`∫ Cin(u) ϖ(du) ≤ ∫₀¹ F'(v) dv ≤ F(1) < ∞`,

the first step by Tonelli over `(0,1) × (0,∞)` with a nonnegative integrand
(`lintegral_swap_cin`), the second by the fundamental theorem of calculus on `[ε,1]` and a
monotone limit (`lintegral_deriv_Ioc_le`). `Cin(u) = log u + O(1)` at infinity then converts it
into the logarithmic condition (`log_max_one_le_cin`).

## What writing this down found

**Three of the skeleton's five steps cost nothing, and one is not stated at all.**

* Step (i), "`F` is continuous at the origin with `F(0) = 0`, priced S", is
  `SymLevyPair.continuous_exponent` (wave 3) together with a two-line `exponent_zero`.
* Step (ii) is needed only as an inequality, which is what keeps the improper endpoint from
  becoming an improper integral: `(0,1] = ⋃ₙ (1/(n+1), 1]` and one `lintegral_iSup`.
* Step (iii), the representation, is **never stated**. Once the profile exists,
  `mul_deriv_exponent` gives its exponent the same derivative as `F` on `(0,∞)`, the two agree
  at the origin and both are even and continuous, so they are equal
  (`eq_zero_of_hasDerivAt_zero_of_continuous`). The skeleton's alternative route — averaging
  over `ω ∈ (0,1)` to avoid the oscillation of the layer cake at the weight `Cin'` — is
  therefore not needed either, and neither is the trap it avoids: no layer cake at `Cin'` is
  taken here.

**And the profile itself was already in the library.** `SpatialLine.tailProfile` and
`SpatialLine.choquetSDProfile` (`ChoquetCone.lean`, wave 3) build exactly this `SDProfile` out
of a folded measure in `prop:choquet-cone`'s domain, and `domain_iff` reduces that domain
condition to the Lévy condition together with the logarithmic one. The first version of this
file re-derived all of it — the tail profile, its antitonicity, its profile-tail property and
both integrability conditions through the layer cake — and the compiler rejected the duplicate
name. That is the failure mode `CLAUDE.md` names, in the same shape it took before: a lemma
about the article's own objects written from scratch and refused as a duplicate. **Only the
logarithmic condition is new**; the rest of the construction is one application of
`choquetSDProfile`.

Proving campaign, wave 5, chapter 7 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## A Lévy measure is σ-finite -/

/-- **A Lévy measure is σ-finite.** It gives `(-∞,0]` no mass and every ray `(r,∞)`, `r > 0`,
finite mass, and `ℝ = ⋃ₙ ((-∞,0] ∪ ((n+1)⁻¹,∞))`.

Not a field of `SymLevyPair` and not an instance: the structure carries the Lévy condition
rather than any tail bound, and this is the lemma that turns one into the other. It is what the
Tonelli step below needs. -/
theorem SymLevyPair.sigmaFinite_nu (P : SymLevyPair) : SigmaFinite P.ν := by
  refine ⟨⟨⟨fun n : ℕ => Iic 0 ∪ Ioi (((n : ℝ) + 1)⁻¹), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [P.ν_folded, zero_add]
    exact lt_top_iff_ne_top.mpr (P.measure_Ioi_ne_top (by positivity))
  · ext x
    simp only [mem_iUnion, mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    rcases le_or_gt x 0 with h | h
    · exact ⟨0, Or.inl h⟩
    · obtain ⟨n, hn⟩ := exists_nat_gt x⁻¹
      refine ⟨n, Or.inr ?_⟩
      have hn1 : x⁻¹ < (n : ℝ) + 1 := by linarith
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ h.ne'
      have hmul : x * x⁻¹ < x * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left hn1 h
      rw [inv_eq_one_div, div_lt_iff₀ hpos]
      nlinarith

/-! ## Elementary facts about a Lévy exponent -/

namespace SymLevyPair

theorem exponent_zero (P : SymLevyPair) : P.exponent 0 = 0 := by
  rw [SymLevyPair.exponent, SymLevyPair.exponentL]
  simp

theorem exponent_nonneg (P : SymLevyPair) (ω : ℝ) : 0 ≤ P.exponent ω := ENNReal.toReal_nonneg

theorem exponentL_neg (P : SymLevyPair) (ω : ℝ) : P.exponentL (-ω) = P.exponentL ω := by
  rw [SymLevyPair.exponentL, SymLevyPair.exponentL]
  congr 1
  · congr 1; ring
  · refine lintegral_congr fun x => ?_
    rw [show -ω * x = -(ω * x) by ring, Real.cos_neg]

theorem exponent_neg (P : SymLevyPair) (ω : ℝ) : P.exponent (-ω) = P.exponent ω := by
  rw [SymLevyPair.exponent, SymLevyPair.exponent, P.exponentL_neg]

end SymLevyPair

/-! ## The logarithmic condition, and where it comes from -/

/-- `log₊ u ≤ Cin u + (2 + |cinConst|)(1 ∧ u²)` on the positive half-line: the expansion
`Cin z = log z + cinConst + O(z⁻¹)` of `lem:cin-rays`(1), read as a one-sided bound and made
global by the truncation. -/
theorem log_max_one_le_cin {u : ℝ} (hu : 0 < u) :
    Real.log (max 1 u) ≤ cin u + (2 + |cinConst|) * min 1 (u ^ 2) := by
  have hmin : 0 ≤ min 1 (u ^ 2) := le_min zero_le_one (sq_nonneg u)
  have habs : 0 ≤ |cinConst| := abs_nonneg _
  rcases le_or_gt u 1 with h | h
  · rw [max_eq_left h, Real.log_one]
    have : 0 ≤ cin u := cin_nonneg' u
    nlinarith
  · have hmax : max 1 u = u := max_eq_right h.le
    have hmin1 : min 1 (u ^ 2) = 1 := min_eq_left (by nlinarith)
    have hb := cin_expansion_top_bound h.le
    have hinv : u⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr h.le
    have h1 : cin u - Real.log u - cinConst ≥ -(2 * u⁻¹) := by
      have := abs_le.mp hb
      linarith [this.1]
    have h2 : -cinConst ≤ |cinConst| := neg_le_abs cinConst
    rw [hmax, hmin1]
    nlinarith

/-- **The logarithmic condition from the finiteness of the `Cin` superposition.**

This is the one condition the Lévy condition does not give, and the only genuinely new
integrability step of this direction. -/
theorem lintegral_log_max_one_ne_top_of_cin {ϖ : Measure ℝ} (hfold : IsFolded ϖ)
    (hsq : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤)
    (hcin : (∫⁻ u, ENNReal.ofReal (cin u) ∂ϖ) ≠ ⊤) :
    (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ) ≠ ⊤ := by
  have hpos : ∀ᵐ u ∂ϖ, (0 : ℝ) < u := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  set C : ℝ := 2 + |cinConst| with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ
      ≤ (∫⁻ u, ENNReal.ofReal (cin u) ∂ϖ)
        + ENNReal.ofReal C * ∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' (by
      exact (ENNReal.continuous_ofReal.comp continuous_cin).measurable.aemeasurable)]
    refine lintegral_mono_ae ?_
    filter_upwards [hpos] with u hu
    rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add (cin_nonneg' u)
      (mul_nonneg hC0 (le_min zero_le_one (sq_nonneg u)))]
    exact ENNReal.ofReal_le_ofReal (log_max_one_le_cin hu)
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hcin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsq⟩) hbound

/-! ## The improper integral of the derivative, as an inequality -/

/-- **`∫₀¹ F' ≤ F(1)`** for a nonnegative `F` continuous on the line and differentiable with a
nonnegative continuous derivative on `(0,∞)`.

Stated as an inequality because that is all the assembly needs, which is what keeps the improper
endpoint from becoming an improper integral: the fundamental theorem of calculus on `[ε,1]`
gives `F(1) - F(ε) ≤ F(1)`, and `(0,1] = ⋃ₙ (1/(n+1), 1]`. -/
theorem lintegral_deriv_Ioc_le {F G : ℝ → ℝ} (hFnn : ∀ ω, 0 ≤ F ω)
    (hGmeas : Measurable G) (hGnn : ∀ ω, 0 < ω → 0 ≤ G ω)
    (hGcont : ContinuousOn G (Ioi 0)) (hderiv : ∀ ω, 0 < ω → HasDerivAt F (G ω) ω) :
    (∫⁻ ω in Ioc (0 : ℝ) 1, ENNReal.ofReal (G ω)) ≤ ENNReal.ofReal (F 1) := by
  set f : ℝ → ℝ≥0∞ := fun ω => ENNReal.ofReal (G ω) with hf
  have hfmeas : Measurable f := hGmeas.ennreal_ofReal
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ ω in Ioc ε 1, f ω) ≤ ENNReal.ofReal (F 1) := by
    intro ε hε hε1
    have hsub : Icc ε 1 ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hε hx.1
    have hcont : ContinuousOn G (Icc ε 1) := hGcont.mono hsub
    have hii : IntervalIntegrable G volume ε 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hε1]
      exact hcont.integrableOn_Icc
    have hftc : ∫ ω in ε..1, G ω = F 1 - F ε := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) hii
      rw [uIcc_of_le hε1] at hx
      exact hderiv x (hsub hx)
    have hon : IntegrableOn G (Ioc ε 1) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hε1]
      exact hii
    have hval : (∫⁻ ω in Ioc ε 1, f ω) = ENNReal.ofReal (F 1 - F ε) := by
      rw [hf, ← ofReal_integral_eq_lintegral_ofReal hon
        ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun ω hω => by
          simp only [Pi.zero_apply]
          exact hGnn ω (lt_of_lt_of_le hε hω.1.le))),
        ← intervalIntegral.integral_of_le hε1, hftc]
    rw [hval]
    exact ENNReal.ofReal_le_ofReal (by linarith [hFnn ε])
  set s : ℕ → Set ℝ := fun n => Ioc (1 / ((n : ℝ) + 1)) 1 with hs
  have hspos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmono : Monotone fun n : ℕ => (s n).indicator f := by
    intro m n hmn
    refine Set.indicator_le_indicator_of_subset ?_ (fun _ => by simp)
    refine Ioc_subset_Ioc_left ?_
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith
  have heq : (Ioc (0 : ℝ) 1).indicator f = fun ω => ⨆ n : ℕ, (s n).indicator f ω := by
    funext ω
    by_cases hω : ω ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hω]
      refine le_antisymm ?_ (iSup_le fun n => ?_)
      · obtain ⟨n, hn⟩ := exists_nat_gt (1 / ω)
        have hω0 : (0 : ℝ) < ω := hω.1
        have hmem : ω ∈ s n := by
          refine ⟨?_, hω.2⟩
          rw [div_lt_iff₀ (by positivity)]
          have h1 : 1 / ω < (n : ℝ) + 1 := by linarith
          rw [div_lt_iff₀ hω0] at h1
          linarith
        exact le_iSup_of_le n (le_of_eq (Set.indicator_of_mem hmem f).symm)
      · exact Set.indicator_le_self' (fun _ _ => by simp) ω
    · rw [Set.indicator_of_notMem hω]
      refine le_antisymm (by simp) (iSup_le fun n => ?_)
      have hsub : s n ⊆ Ioc (0 : ℝ) 1 := Ioc_subset_Ioc_left (hspos n).le
      rw [Set.indicator_of_notMem (fun hc => hω (hsub hc))]
  rw [← lintegral_indicator measurableSet_Ioc, heq,
    lintegral_iSup (fun n => hfmeas.indicator measurableSet_Ioc) hmono]
  refine iSup_le fun n => ?_
  rw [lintegral_indicator measurableSet_Ioc]
  exact hstep _ (hspos n) (hsle n)

/-! ## The Tonelli step -/

/-- **The `Cin` superposition of the symbol's jump part.**

Tonelli with a nonnegative integrand, and the substitution
`∫₀¹ (1 - cos(uω)) dω/ω = Cin(u)` of `Cin.lean`. σ-finiteness of the Lévy measure is
`SymLevyPair.sigmaFinite_nu`. -/
theorem lintegral_swap_cin (R : SymLevyPair) :
    (∫⁻ ω in Ioc (0 : ℝ) 1, ∫⁻ u, ENNReal.ofReal ((1 - Real.cos (u * ω)) / ω) ∂R.ν)
      = ∫⁻ u, ENNReal.ofReal (cin u) ∂R.ν := by
  haveI := R.sigmaFinite_nu
  have hmeas : AEMeasurable (Function.uncurry fun (ω u : ℝ) =>
      ENNReal.ofReal ((1 - Real.cos (u * ω)) / ω))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod R.ν) := by
    refine Measurable.aemeasurable ?_
    exact (((measurable_const.sub
      (Real.measurable_cos.comp (measurable_snd.mul measurable_fst))).div
      measurable_fst)).ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun u => ?_
  have hi : IntegrableOn (fun ω : ℝ => (1 - Real.cos (u * ω)) / ω) (Ioc (0 : ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegrable_dilate_cinIntegrand u zero_le_one
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall fun ω hω => by
      simp only [Pi.zero_apply]
      exact dilate_cinIntegrand_nonneg u hω.1.le)),
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral_dilate_cinIntegrand u 1, mul_one]

/-! ## `lem:selfdecomposable-exponents`, (2) implies (3) -/

/-- A continuous function vanishing at the origin with vanishing derivative on `(0,∞)` vanishes
on `[0,∞)`: it is constant on every `[a,b]` with `a > 0`, and the constant is its value at the
origin by continuity. -/
theorem eq_zero_of_hasDerivAt_zero_of_continuous {h : ℝ → ℝ} (hcont : Continuous h)
    (h0 : h 0 = 0) (hd : ∀ ω, 0 < ω → HasDerivAt h 0 ω) : ∀ ω, 0 ≤ ω → h ω = 0 := by
  intro ω hω
  rcases eq_or_lt_of_le hω with heq | hpos
  · rw [← heq]; exact h0
  have hconst : ∀ a : ℝ, 0 < a → a ≤ ω → h ω = h a := by
    intro a ha haω
    exact constant_of_has_deriv_right_zero hcont.continuousOn
      (fun x hx => (hd x (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt) ω (right_mem_Icc.mpr haω)
  have hlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 (h 0)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hconstlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 (h ω)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
    exact hconst a ha.1 ha.2.le
  rw [tendsto_nhds_unique hconstlim hlim, h0]

/-- **`lem:selfdecomposable-exponents`, (2) implies (3).**

The profile is the tail function of the symbol's Lévy measure and the Gaussian coefficient is
half the symbol's, so the data is `choquetSDProfile`'s at that measure; the domain condition
`prop:choquet-cone` asks of it is the Lévy condition together with `∫ log₊ u ϖ(du) < ∞`, and
the second of those is what the finiteness of `F` supplies, through
`∫ Cin dϖ ≤ ∫₀¹ F' ≤ F(1)`. Once the profile exists, `F` and its exponent have the same
derivative on `(0,∞)`, agree at the origin and are both continuous and even, so they are equal;
`prop:fourier-toolbox`(3)'s uniqueness clause then matches the pairs.

**Spends ledger A3** through `fourier_toolbox_levy_unique`, at the last step and nowhere else. -/
theorem sd_exponents_two_implies_three (P : SymLevyPair) (F : ℝ → ℝ)
    (hF : ∀ ω, F ω = P.exponent ω) (hC1 : ContDiffOn ℝ 1 F (Ioi 0))
    (hB : IsSymLevyExponent fun ω => ω * deriv F ω) :
    ∃ Q : SDProfile, Q.a = P.a ∧ P.ν = profileMeasure Q.k := by
  obtain ⟨R, hR⟩ := hB
  have hFe : F = P.exponent := funext hF
  -- the derivative of `F` on the positive half-line
  set G : ℝ → ℝ := fun ω => R.exponent ω / ω with hG
  have hGmeas : Measurable G :=
    (R.continuous_exponent.measurable).div measurable_id
  have hGnn : ∀ ω, 0 < ω → 0 ≤ G ω := fun ω hω =>
    div_nonneg (R.exponent_nonneg ω) hω.le
  have hGcont : ContinuousOn G (Ioi 0) :=
    R.continuous_exponent.continuousOn.div continuousOn_id fun ω hω => ne_of_gt hω
  have hdiffOn : DifferentiableOn ℝ F (Ioi 0) := hC1.differentiableOn one_ne_zero
  have hderivF : ∀ ω, 0 < ω → HasDerivAt F (G ω) ω := by
    intro ω hω
    have hd := ((hdiffOn ω hω).differentiableAt (isOpen_Ioi.mem_nhds hω)).hasDerivAt
    have hGeq : deriv F ω = G ω := by
      have hRω := hR ω
      rw [hG]
      field_simp
      linarith [hRω]
    rwa [hGeq] at hd
  -- the finiteness of the Cin superposition
  have hcin : (∫⁻ u, ENNReal.ofReal (cin u) ∂R.ν) ≠ ⊤ := by
    have hle : (∫⁻ u, ENNReal.ofReal (cin u) ∂R.ν) ≤ ENNReal.ofReal (F 1) := by
      rw [← lintegral_swap_cin R]
      refine le_trans (setLIntegral_mono' measurableSet_Ioc fun ω hω => ?_)
        (lintegral_deriv_Ioc_le (F := F) (G := G)
          (fun ω => by rw [hFe]; exact P.exponent_nonneg ω) hGmeas hGnn hGcont hderivF)
      have hω0 : (0 : ℝ) < ω := hω.1
      have hint : Integrable (fun u : ℝ => 1 - Real.cos (ω * u)) R.ν :=
        R.integrable_one_sub_cos ω
      have hint2 : Integrable (fun u : ℝ => (1 - Real.cos (u * ω)) / ω) R.ν := by
        refine (hint.div_const ω).congr (Filter.Eventually.of_forall fun u => ?_)
        change (1 - Real.cos (ω * u)) / ω = (1 - Real.cos (u * ω)) / ω
        rw [mul_comm ω u]
      have hnn : (0 : ℝ → ℝ) ≤ᵐ[R.ν] fun u : ℝ => (1 - Real.cos (u * ω)) / ω :=
        Filter.Eventually.of_forall fun u => by
          simp only [Pi.zero_apply]
          exact div_nonneg (by linarith [Real.cos_le_one (u * ω)]) hω0.le
      rw [← ofReal_integral_eq_lintegral_ofReal hint2 hnn]
      refine ENNReal.ofReal_le_ofReal ?_
      have hval : (∫ u, (1 - Real.cos (u * ω)) / ω ∂R.ν)
          = (∫ u, (1 - Real.cos (ω * u)) ∂R.ν) / ω := by
        rw [← integral_div]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        change (1 - Real.cos (u * ω)) / ω = (1 - Real.cos (ω * u)) / ω
        rw [mul_comm u ω]
      rw [hval, hG]
      simp only
      rw [R.exponent_eq ω, add_div]
      have h1 : 0 ≤ R.a * ω ^ 2 / ω :=
        div_nonneg (mul_nonneg R.a_nonneg (sq_nonneg ω)) hω0.le
      linarith
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  -- the domain condition of `prop:choquet-cone`
  have hpos : ∀ᵐ u ∂R.ν, (0 : ℝ) < u := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) R.ν_folded
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  have hlog : (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂R.ν) ≠ ⊤ :=
    lintegral_log_max_one_ne_top_of_cin R.ν_folded R.ν_integrable hcin
  have hdom : (∫⁻ τ, ENNReal.ofReal (domainIntegrand τ) ∂R.ν) ≠ ⊤ := by
    refine (domain_iff R.ν R.ν_folded).mpr ⟨?_, ?_⟩
    · refine ne_top_of_le_ne_top R.ν_integrable (lintegral_mono_ae ?_)
      filter_upwards [hpos] with τ hτ
      refine ENNReal.ofReal_le_ofReal ?_
      rcases le_total τ 1 with h | h
      · rw [min_eq_left h, min_eq_right (by nlinarith)]
        nlinarith
      · rw [min_eq_right h, min_eq_left (by nlinarith)]
        norm_num
    · have hmaxc : ∀ τ : ℝ, Real.log (max τ 1) = Real.log (max 1 τ) := fun τ => by
        rw [max_comm]
      simp only [hmaxc]
      exact hlog
  -- the profile
  set Q : SDProfile :=
    choquetSDProfile (a := R.a / 2) (by linarith [R.a_nonneg]) R.ν R.ν_folded hdom with hQdef
  have hQa : Q.a = R.a / 2 := rfl
  have hpt : HasProfileTail Q.k R.ν :=
    hasProfileTail_choquetSDProfile (by linarith [R.a_nonneg]) R.ν R.ν_folded hdom
  -- the two exponents have the same derivative on the positive half-line
  have hQderiv : ∀ ω, 0 < ω → HasDerivAt Q.exponent (G ω) ω := by
    intro ω hω
    have h := hasDerivAt_exponent Q hpt hω
    have hval : 2 * Q.a * ω + (∫ τ, (1 - Real.cos (ω * τ)) ∂R.ν) / ω = G ω := by
      rw [hG, hQa]
      simp only
      rw [R.exponent_eq ω, add_div]
      field_simp
    rwa [hval] at h
  have hzero : ∀ ω, 0 ≤ ω → Q.exponent ω - F ω = 0 := by
    refine eq_zero_of_hasDerivAt_zero_of_continuous
      (Q.continuous_exponent.sub (by rw [hFe]; exact P.continuous_exponent)) ?_ ?_
    · rw [SDProfile.exponent_zero, hFe, P.exponent_zero, sub_zero]
    · intro ω hω
      have hd := (hQderiv ω hω).sub (hderivF ω hω)
      rw [sub_self] at hd
      exact hd
  have hQF : ∀ ω, Q.exponent ω = F ω := by
    intro ω
    rcases le_or_gt 0 ω with hω | hω
    · linarith [hzero ω hω]
    · have h := hzero (-ω) (by linarith)
      rw [Q.exponent_neg, hFe] at h
      rw [P.exponent_neg] at h
      rw [hFe]
      linarith
  -- the uniqueness clause matches the pairs
  obtain ⟨S, hSa, hSν, hSe⟩ := profile_integrability_pair Q
  have hE : ∀ ω, P.exponent ω = S.exponent ω := by
    intro ω
    rw [← hSe, hQF ω, hFe]
  obtain ⟨ha, hν⟩ := fourier_toolbox_levy_unique P S hE
  exact ⟨Q, by rw [← hSa, ← ha], by rw [hν, hSν]⟩

end SpatialLine
