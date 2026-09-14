/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ProfileTail
import SpatialLine.AdmissibleCone
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The symbol `B(omega) = omega F'(omega)`

Blueprint: `lem:selfdecomposable-exponents`, the (3) implies (2) direction and the identity
`eq:symbol`, in `blueprint/src/parts/07-characterization.tex`.

## Why the `Cin` form and not the profile form

Differentiating `eq:sd-profile` under the integral sign in the profile form would need
`int |sin(omega x)| k(x) dx < infty`, and that is genuinely unavailable: the two conditions on
an admissible profile are `int_0^1 x k(x) dx < infty` and `int_1^infty k(x) x^{-1} dx < infty`,
and `k(x) = (log x)^{-2}` at infinity satisfies the second while `int_1^infty k(x) dx` diverges.
The `Cin` superposition `eq:cin-superposition` replaces the profile by the Choquet measure and
the integrand by `Cin(omega u)`, whose omega-derivative `(1 - cos(omega u))/omega` is bounded on
a compact frequency interval by a constant multiple of `1 wedge u^2` --- and `1 wedge u^2` is
`varpi`-integrable for **every** measure with `HasProfileTail`, which is
`SpatialLine.lintegral_min_one_sq_ne_top`.

## What the file proves

* *(moved to `SpatialLine/Cin.lean` by the wave-6 merge, where the rest of `Cin` lives)* the
  calculus of `Cin` this needs and chapter 8 had not written when this file was: `cinIntegrand`
  is continuous **at the origin too** (the quotient `(1 - cos v)/v` is `0` there both by Lean's
  convention and in the limit), so `Cin` is `C^1` with `Cin' = cinIntegrand` everywhere by the
  fundamental theorem of calculus. Chapter 8 has needed it since — `SpatialLine/CinDelayForm.lean`
  reads the delay ODE off `hasDerivAt_cin` — and a chapter-7 file is the wrong home for it;
* `exponent_eq_integral_cin`, the superposition as a Bochner integral, which is where
  `SDProfile.exponentL_ne_top` is spent;
* `hasDerivAt_exponent`, differentiation under the integral sign at every positive frequency;
* `mul_deriv_exponent`, the identity `omega F'(omega) = 2a omega^2 + int (1 - cos(omega v))
  varpi(dv)` at **every** real frequency --- negative ones by evenness of the exponent, and
  `omega = 0` because the factor `omega` kills whatever `deriv` returns there;
* `sd_exponents_symbol` and `sd_exponents_three_implies_two`, the two blueprint declarations.

The real identity `mul_deriv_exponent` is proved first and the `ℝ≥0∞` one `eq:symbol` is read
off it, rather than the other way round: `ENNReal.ofReal` is not injective, so an identity
between `ofReal`s does not by itself say that `omega F'(omega)` is the symbol, and the pair
`(2a, varpi)` of clause (2) needs the real value.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The two integrands, against a Choquet measure -/

/-- `1 - cos(ωv) ≤ (2 + ω²)(1 ∧ v²)`: the truncation both regimes of the cosine obey. -/
theorem one_sub_cos_le (ω v : ℝ) : 1 - Real.cos (ω * v) ≤ (2 + ω ^ 2) * min 1 (v ^ 2) := by
  rcases le_or_gt (v ^ 2) 1 with hv | hv
  · rw [min_eq_right hv]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ω * v), sq_nonneg ω, sq_nonneg v]
  · rw [min_eq_left hv.le]
    nlinarith [Real.neg_one_le_cos (ω * v), sq_nonneg ω]

/-- The truncation `1 ∧ u²` is `ϖ`-integrable — the one integrability fact the whole
differentiation rests on. -/
theorem integrable_min_one_sq {ϖ : Measure ℝ}
    (h : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤) :
    Integrable (fun τ : ℝ => min 1 (τ ^ 2)) ϖ := by
  refine ⟨(by fun_prop : Continuous fun τ : ℝ => min 1 (τ ^ 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun τ => le_min zero_le_one (sq_nonneg τ))]
  exact lt_top_iff_ne_top.mpr h

/-- The symbol's own integrand is `ϖ`-integrable at every frequency. -/
theorem integrable_one_sub_cos {ϖ : Measure ℝ}
    (h : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤) (ω : ℝ) :
    Integrable (fun v : ℝ => 1 - Real.cos (ω * v)) ϖ := by
  refine Integrable.mono' ((integrable_min_one_sq h).const_mul (2 + ω ^ 2))
    (by fun_prop) (.of_forall fun v => ?_)
  have hnn : 0 ≤ 1 - Real.cos (ω * v) := by linarith [Real.cos_le_one (ω * v)]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact one_sub_cos_le ω v

/-- `u ↦ Cin(uω)` is `ϖ`-integrable, because the superposition is the exponent and the exponent
is finite (`SDProfile.exponentL_ne_top`). -/
theorem integrable_cin_dilate (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ)
    (ω : ℝ) : Integrable (fun τ : ℝ => cin (τ * ω)) ϖ := by
  have hsup := cin_superposition Q ϖ hϖ ω
  have hne : Q.exponentL ω ≠ ⊤ := Q.exponentL_ne_top ω
  rw [hsup, cinSuperpositionL] at hne
  refine ⟨(continuous_cin.comp (continuous_id.mul continuous_const)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun τ => cin_nonneg' _)]
  exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mp hne).2

/-- **`eq:cin-superposition` as a Bochner integral**: `F(ω) = aω² + ∫ Cin(ωu)\,ϖ(du)`. -/
theorem exponent_eq_integral_cin (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ)
    (ω : ℝ) : Q.exponent ω = Q.a * ω ^ 2 + ∫ τ, cin (τ * ω) ∂ϖ := by
  have hsup := cin_superposition Q ϖ hϖ ω
  have hne : Q.exponentL ω ≠ ⊤ := Q.exponentL_ne_top ω
  rw [hsup, cinSuperpositionL] at hne
  have hne2 := (ENNReal.add_ne_top.mp hne).2
  rw [SDProfile.exponent, hsup, cinSuperpositionL,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hne2,
    ENNReal.toReal_ofReal (mul_nonneg Q.a_nonneg (sq_nonneg ω))]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (.of_forall fun τ => cin_nonneg' _)
    (continuous_cin.comp (continuous_id.mul continuous_const)).aestronglyMeasurable).symm

/-! ## Differentiation under the integral sign -/

/-- **The derivative of the exponent at a positive frequency**:
`F'(ω) = 2aω + ω⁻¹∫(1 - cos ωu)\,ϖ(du)`.

The dominating function on `(ω/2, 2ω)` is `(4/ω + 2ω)(1 ∧ u²)`: the derivative
`∂_ω Cin(ωu) = (1 - cos ωu)/ω` is at most `2/ω` and at most `ωu²`, which are the two regimes of
the truncation, and `1 ∧ u²` is `ϖ`-integrable by `lintegral_min_one_sq_ne_top`. -/
theorem hasDerivAt_exponent (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ)
    {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt Q.exponent
      (2 * Q.a * ω + (∫ τ, (1 - Real.cos (ω * τ)) ∂ϖ) / ω) ω := by
  have hsq := lintegral_min_one_sq_ne_top hϖ
  have hae0 : ∀ᵐ τ ∂ϖ, 0 < τ := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hϖ.1
    simp only [not_lt, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht
  set C : ℝ := 4 / ω + 2 * ω with hC
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ϖ)
    (F := fun x τ => cin (τ * x)) (F' := fun x τ => (1 - Real.cos (τ * x)) / x)
    (bound := fun τ => C * min 1 (τ ^ 2)) (x₀ := ω) (s := Ioo (ω / 2) (2 * ω))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (.of_forall fun x =>
      (continuous_cin.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (integrable_cin_dilate Q hϖ ω)
    (by fun_prop)
    ?bound ((integrable_min_one_sq hsq).const_mul C) ?diff
  case bound =>
    filter_upwards [hae0] with τ hτ x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by linarith) hx.1
    have hnn : 0 ≤ (1 - Real.cos (τ * x)) / x :=
      div_nonneg (by linarith [Real.cos_le_one (τ * x)]) hx0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_le_iff₀ hx0]
    rcases le_or_gt (τ ^ 2) 1 with hτ1 | hτ1
    · rw [min_eq_right hτ1]
      have h1 : 1 - Real.cos (τ * x) ≤ (τ * x) ^ 2 / 2 := by
        nlinarith [Real.one_sub_sq_div_two_le_cos (x := τ * x)]
      have h2 : x ≤ 2 * ω := hx.2.le
      have hCge : 2 * ω ≤ C := by
        have h4 : (0 : ℝ) < 4 / ω := by positivity
        linarith
      nlinarith [sq_nonneg τ, sq_nonneg x, hx.1, hτ.le]
    · rw [min_eq_left hτ1.le, mul_one]
      have h1 : 1 - Real.cos (τ * x) ≤ 2 := by linarith [Real.neg_one_le_cos (τ * x)]
      have hCge : 4 / ω ≤ C := by nlinarith
      have hxge : ω / 2 ≤ x := hx.1.le
      have h4 : (4 : ℝ) / ω * (ω / 2) = 2 := by field_simp; norm_num
      have hprod : 4 / ω * (ω / 2) ≤ C * x :=
        mul_le_mul hCge hxge (by positivity) (le_trans (by positivity) hCge)
      rw [h4] at hprod
      linarith
  case diff =>
    filter_upwards [hae0] with τ hτ x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by linarith) hx.1
    have hg : HasDerivAt (fun y : ℝ => τ * y) τ x := by
      simpa using (hasDerivAt_id x).const_mul τ
    have hchain : HasDerivAt (fun y : ℝ => cin (τ * y)) (cinIntegrand (τ * x) * τ) x :=
      (hasDerivAt_cin (τ * x)).comp x hg
    have heq : cinIntegrand (τ * x) * τ = (1 - Real.cos (τ * x)) / x := by
      rw [dilate_cinIntegrand τ x, mul_comm]
    rwa [heq] at hchain
  have hfun : Q.exponent = fun x => Q.a * x ^ 2 + ∫ τ, cin (τ * x) ∂ϖ :=
    funext fun x => exponent_eq_integral_cin Q hϖ x
  rw [hfun]
  have hquad : HasDerivAt (fun x : ℝ => Q.a * x ^ 2) (2 * Q.a * ω) ω := by
    have hp := ((hasDerivAt_pow 2 ω).const_mul Q.a)
    simpa [mul_comm, mul_assoc, mul_left_comm] using hp
  have hsum := hquad.add key.2
  have hval : (∫ τ, (1 - Real.cos (τ * ω)) / ω ∂ϖ)
      = (∫ τ, (1 - Real.cos (ω * τ)) ∂ϖ) / ω := by
    rw [← integral_div]
    congr 1
    ext τ
    rw [mul_comm ω τ]
  rwa [hval] at hsum

/-! ## The symbol -/

/-- **The symbol as a real number**: `ωF'(ω) = 2aω² + ∫(1 - cos ωv)\,ϖ(dv)` at **every** real
frequency.

Positive frequencies are `hasDerivAt_exponent`; negative ones follow because the exponent is
even, so its derivative is odd and both sides are unchanged by `ω ↦ -ω`; at `ω = 0` the factor
`ω` kills whatever `deriv` returns and the integrand vanishes identically. -/
theorem mul_deriv_exponent (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ) (ω : ℝ) :
    ω * deriv Q.exponent ω = 2 * Q.a * ω ^ 2 + ∫ v, (1 - Real.cos (ω * v)) ∂ϖ := by
  rcases lt_trichotomy ω 0 with hneg | rfl | hpos
  · have hω0 : ω ≠ 0 := ne_of_lt hneg
    have hd := hasDerivAt_exponent Q hϖ (neg_pos.mpr hneg)
    have hcomp := hd.comp ω (hasDerivAt_neg ω)
    have hev : Q.exponent ∘ Neg.neg = Q.exponent := funext fun y => Q.exponent_neg y
    rw [hev] at hcomp
    have hI : (∫ τ, (1 - Real.cos (-ω * τ)) ∂ϖ) = ∫ v, (1 - Real.cos (ω * v)) ∂ϖ := by
      congr 1
      ext v
      rw [neg_mul, Real.cos_neg]
    rw [hcomp.deriv, hI]
    field_simp
    ring
  · simp
  · have hω0 : ω ≠ 0 := ne_of_gt hpos
    rw [(hasDerivAt_exponent Q hϖ hpos).deriv]
    field_simp

theorem mul_deriv_exponent_nonneg (Q : SDProfile) {ϖ : Measure ℝ} (hϖ : HasProfileTail Q.k ϖ)
    (ω : ℝ) : 0 ≤ ω * deriv Q.exponent ω := by
  rw [mul_deriv_exponent Q hϖ ω]
  have h1 : 0 ≤ 2 * Q.a * ω ^ 2 := by nlinarith [Q.a_nonneg, sq_nonneg ω]
  have h2 : 0 ≤ ∫ v, (1 - Real.cos (ω * v)) ∂ϖ :=
    integral_nonneg fun v => by
      simp only [Pi.zero_apply]
      linarith [Real.cos_le_one (ω * v)]
  linarith

/-- `symbolL` in the real form its consumers use. -/
theorem symbolL_eq_ofReal (Q : SDProfile) {ϖ : Measure ℝ}
    (hsq : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤) (ω : ℝ) :
    symbolL Q.a ϖ ω
      = ENNReal.ofReal (2 * Q.a * ω ^ 2 + ∫ v, (1 - Real.cos (ω * v)) ∂ϖ) := by
  have hnn : ∀ v : ℝ, 0 ≤ 1 - Real.cos (ω * v) := fun v => by
    linarith [Real.cos_le_one (ω * v)]
  have hfin : (∫⁻ v, ENNReal.ofReal (1 - Real.cos (ω * v)) ∂ϖ) ≠ ⊤ := by
    have h2 := (integrable_one_sub_cos hsq ω).2
    rw [hasFiniteIntegral_iff_ofReal (.of_forall hnn)] at h2
    exact h2.ne
  have hval : (∫ v, (1 - Real.cos (ω * v)) ∂ϖ)
      = (∫⁻ v, ENNReal.ofReal (1 - Real.cos (ω * v)) ∂ϖ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (.of_forall hnn) (by fun_prop)
  rw [symbolL, hval, ENNReal.ofReal_add (mul_nonneg (by linarith [Q.a_nonneg]) (sq_nonneg ω))
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

/-- **`lem:selfdecomposable-exponents`, `eq:symbol`**: the pair of `B` is `(2a, ϖ)`. -/
theorem sd_exponents_symbol (Q : SDProfile) (F : ℝ → ℝ) (hF : ∀ ω, F ω = Q.exponent ω)
    (ϖ : Measure ℝ) (hϖ : HasProfileTail Q.k ϖ) :
    ∀ ω : ℝ, symbolL Q.a ϖ ω = ENNReal.ofReal (ω * deriv F ω) := by
  have hFe : F = Q.exponent := funext hF
  subst hFe
  intro ω
  rw [symbolL_eq_ofReal Q (lintegral_min_one_sq_ne_top hϖ) ω, mul_deriv_exponent Q hϖ ω]

/-! ## `C¹` off the origin, and the clause (2) of the node -/

/-- The symbol's integral is continuous in the frequency, by dominated convergence with the
bound `(2 + (|ω₀|+1)²)(1 ∧ v²)` on the unit ball around `ω₀`. -/
theorem continuous_integral_one_sub_cos {ϖ : Measure ℝ}
    (hsq : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤) :
    Continuous fun ω : ℝ => ∫ v, (1 - Real.cos (ω * v)) ∂ϖ := by
  rw [continuous_iff_continuousAt]
  intro ω₀
  refine continuousAt_of_dominated (bound := fun v => (2 + (|ω₀| + 1) ^ 2) * min 1 (v ^ 2))
    (.of_forall fun x => by fun_prop) ?_ ((integrable_min_one_sq hsq).const_mul _)
    (.of_forall fun v => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds ω₀ one_pos] with x hx
  filter_upwards with v
  have hd : |x - ω₀| < 1 := by
    have h := Metric.mem_ball.mp hx
    rwa [Real.dist_eq] at h
  have hx1 : |x| ≤ |ω₀| + 1 := by
    have h := abs_sub_abs_le_abs_sub x ω₀
    linarith
  have hnn : 0 ≤ 1 - Real.cos (x * v) := by linarith [Real.cos_le_one (x * v)]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine le_trans (one_sub_cos_le x v) ?_
  have hmin : 0 ≤ min 1 (v ^ 2) := le_min zero_le_one (sq_nonneg v)
  have hsq' : x ^ 2 ≤ (|ω₀| + 1) ^ 2 := by
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x, abs_nonneg ω₀]
  nlinarith

/-- **`lem:selfdecomposable-exponents`, (3) implies (2).** -/
theorem sd_exponents_three_implies_two (P : SymLevyPair) (F : ℝ → ℝ)
    (hF : ∀ ω, F ω = P.exponent ω) (Q : SDProfile) (ha : Q.a = P.a)
    (hν : P.ν = profileMeasure Q.k) :
    ContDiffOn ℝ 1 F (Ioi 0) ∧ IsSymLevyExponent fun ω => ω * deriv F ω := by
  obtain ⟨ϖ, hϖ⟩ := cin_superposition_exists Q
  have hsq := lintegral_min_one_sq_ne_top hϖ
  have hFQ : F = Q.exponent := by
    funext ω
    rw [hF ω, SymLevyPair.exponent, SDProfile.exponent,
      exponentL_eq_of_profileMeasure Q P ha.symm hν ω]
  subst hFQ
  refine ⟨?_, ?_⟩
  · have hderiv_eq : ∀ ω ∈ Ioi (0 : ℝ), deriv Q.exponent ω
        = 2 * Q.a * ω + (∫ τ, (1 - Real.cos (ω * τ)) ∂ϖ) / ω :=
      fun ω hω => (hasDerivAt_exponent Q hϖ hω).deriv
    have hcont : ContinuousOn (deriv Q.exponent) (Ioi 0) := by
      refine ContinuousOn.congr ?_ hderiv_eq
      refine ContinuousOn.add (by fun_prop) ?_
      exact ContinuousOn.div (continuous_integral_one_sub_cos hsq).continuousOn
        continuousOn_id fun ω hω => ne_of_gt hω
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioi 0)]
    refine ⟨fun ω hω => ((hasDerivAt_exponent Q hϖ hω).differentiableAt).differentiableWithinAt,
      ?_⟩
    refine hcont.congr fun ω hω => ?_
    exact derivWithin_of_isOpen isOpen_Ioi hω
  · refine ⟨⟨2 * Q.a, ϖ, by linarith [Q.a_nonneg], hϖ.1, hsq⟩, fun ω => ?_⟩
    have hsym : symbolL Q.a ϖ ω = ENNReal.ofReal (ω * deriv Q.exponent ω) :=
      sd_exponents_symbol Q Q.exponent (fun _ => rfl) ϖ hϖ ω
    rw [SymLevyPair.exponent]
    show ω * deriv Q.exponent ω = (symbolL Q.a ϖ ω).toReal
    rw [hsym, ENNReal.toReal_ofReal (mul_deriv_exponent_nonneg Q hϖ ω)]

end SpatialLine
