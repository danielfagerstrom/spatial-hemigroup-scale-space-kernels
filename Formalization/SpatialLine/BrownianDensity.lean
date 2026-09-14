/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The Brownian laws, their density, and mixtures against them

Blueprint: `blueprint/src/parts/09-bridge.tex` — the objects `eq:bridge` and
`eq:bridge-profile` are written in, and the elementary facts about them. Nothing here is a
blueprint node.

`brownianLaw u = g_u` is Mathlib's `gaussianReal 0 u`, and `brownianDensity u x = g_u(x)` its
density; both are thin wrappers whose only job is to let the bridge equations be written the way
the blueprint writes them, with `u` a real time rather than an `ℝ≥0` variance. At `u = 0` the
wrapper is `δ₀`, which is the blueprint's `g_0 = δ_0`, and for `u < 0` it is junk in the phase A
sense — every statement quantifies over `u > 0` or integrates over `(0,∞)`.

## Why a module of its own

The Matérn corner is a Gamma mixture of Gaussian laws (`prop:matern-exponent`(3),
`SpatialLine/MaternMixture.lean`), so it reads the density facts and the three mixture facts
below; `prop:two-members`(2), a Chapter 3 node, reads them through it. Until 2026-09-14 they
stood in `SpatialLine/BridgeExponents.lean`, `SpatialLine/BridgeCorners.lean` and
`SpatialLine/Bridge.lean`, which put the whole of the causal bridge into the release export of
the characterization theorem (ADR-0005). They moved here unchanged; the bridge files import
this one and keep everything that mentions `CausalAdmissible`.

## The two elementary bounds

`brownianDensity_div_le` bounds `g_u(x)/u` by `16/x⁴` uniformly for `u` in `(0,1]`, which is
where the Gaussian's flatness at `u = 0` pays for a missing power of `u` in a mixture carrying
`du/u`; above `1` the density is at most `1` (`brownianDensity_le_one`). Both are used by the
bridge profile of `lem:bridge-exponents` and neither is used here.

## The mixture facts

`Measure.bind brownianLaw` mixes the Gaussian laws against a law on the delay. It is a
probability measure, it is symmetric, and — the one with content —
`fourierCos_bind_brownianLaw` says its cosine transform at `ω` is the Laplace transform of the
delay law at `ω²/2`. The route is through `1 - \cos` rather than through `\cos`, because that
integrand is nonnegative and `Measure.lintegral_bind` is available where a Bochner
`integral_bind` is not. The hypothesis `hcausal` is what makes `g_u` a genuine Gaussian
`ρ`-almost everywhere: off `[0,∞)` the wrapper is `δ₀` and the identity fails.
-/

namespace SpatialLine

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The Brownian laws -/

/-- **`g_u`**, the law of Brownian motion at time `u`: the centred Gaussian of variance `u`,
with `g_0 = δ_0`. -/
noncomputable def brownianLaw (u : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 u.toNNReal

/-- **`g_u(x)`**, the density of `brownianLaw u` for `u > 0`. -/
noncomputable def brownianDensity (u x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 u.toNNReal x

/-- **`brownianLaw` is a measurable family of measures.** -/
theorem measurable_brownianLaw : Measurable brownianLaw := by
  unfold brownianLaw
  fun_prop

/-! ## The Brownian density, explicitly -/

/-- `g_u(x) = (2πu)^{-1/2}e^{-x²/2u}` at every positive time. -/
theorem brownianDensity_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    brownianDensity u x = (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) := by
  unfold brownianDensity gaussianPDFReal
  rw [Real.coe_toNNReal _ hu.le]
  norm_num

theorem brownianDensity_nonneg (u x : ℝ) : 0 ≤ brownianDensity u x :=
  gaussianPDFReal_nonneg _ _ _

theorem measurable_brownianDensity (u : ℝ) : Measurable (brownianDensity u) := by
  unfold brownianDensity; fun_prop

theorem measurable_brownianDensity_time (x : ℝ) :
    Measurable fun u : ℝ => brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; fun_prop

theorem measurable_brownianDensity_uncurry : Measurable (Function.uncurry brownianDensity) := by
  unfold brownianDensity gaussianPDFReal Function.uncurry; fun_prop

/-- `g_u` is even. -/
theorem brownianDensity_neg (u x : ℝ) : brownianDensity u (-x) = brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; simp

theorem brownianLaw_eq_withDensity {u : ℝ} (hu : 0 < u) :
    brownianLaw u = volume.withDensity fun x => ENNReal.ofReal (brownianDensity u x) := by
  unfold brownianLaw brownianDensity
  rw [gaussianReal_of_var_ne_zero _ (by positivity)]
  rfl

/-! ## Two elementary bounds on the density -/

/-- `y² ≤ 4e^y` for `y ≥ 0`: the second-order term of the exponential series, in the form the
near-origin bound uses. -/
theorem sq_le_four_mul_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 4 * Real.exp y := by
  have h := Real.add_one_le_exp (y / 2)
  have h2 : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [← Real.exp_nat_mul]; norm_num; ring_nf
  nlinarith [Real.exp_pos (y / 2), h, h2]

/-- **The near-origin bound.** `g_u(x)/u ≤ 16/x⁴` for `0 < u ≤ 1` and `x ≠ 0`.

This is what lets the mixture integrand, which carries `du/u`, be dominated on `(0,1)` by a
multiple of `k_I(u)` — the *first* integrability field of `def:causal-admissible`, which
carries no `u⁻¹`. The Gaussian's flatness at `u = 0` pays for the missing power. -/
theorem brownianDensity_div_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {x : ℝ} (hx : x ≠ 0) :
    brownianDensity u x / u ≤ 16 / x ^ 4 := by
  have hpi := Real.two_le_pi
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hy : (0 : ℝ) ≤ x ^ 2 / (2 * u) := by positivity
  have hpos : (0 : ℝ) < Real.exp (x ^ 2 / (2 * u)) := Real.exp_pos _
  have h := sq_le_four_mul_exp hy
  have hsq : (x ^ 2 / (2 * u)) ^ 2 = x ^ 4 / (4 * u ^ 2) := by field_simp; ring
  rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * u ^ 2)] at h
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 16 * u ^ 2 / x ^ 4 := by
    have hinv : Real.exp (-x ^ 2 / (2 * u)) = (Real.exp (x ^ 2 / (2 * u)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hinv, inv_le_iff_one_le_mul₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hx4]
    nlinarith [h]
  have hsqrt : u ≤ Real.sqrt (2 * Real.pi * u) := by
    have hle : u ^ 2 ≤ 2 * Real.pi * u := by nlinarith
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0.le).symm
      _ ≤ Real.sqrt (2 * Real.pi * u) := Real.sqrt_le_sqrt hle
  have hspos : (0 : ℝ) < Real.sqrt (2 * Real.pi * u) := by
    apply Real.sqrt_pos.mpr; nlinarith
  rw [brownianDensity_eq hu0, div_le_div_iff₀ (by positivity) hx4]
  have hstep : (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) * x ^ 4
      ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hexp
      (by positivity : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * u))⁻¹)
    nlinarith [hmul]
  have hsimp : (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4
      = 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) := by field_simp
  rw [hsimp] at hstep
  have hfin : 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) ≤ 16 * u := by
    rw [div_le_iff₀ hspos]; nlinarith [hsqrt, hu0.le]
  linarith

/-- **The bound above the origin.** `g_u(x) ≤ 1` for `u ≥ 1`, so the mixture integrand is
dominated there by `k_I(u)/u` — the second integrability field, verbatim. -/
theorem brownianDensity_le_one {u : ℝ} (hu : 1 ≤ u) (x : ℝ) : brownianDensity u x ≤ 1 := by
  have hpi := Real.two_le_pi
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hspos : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * u) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; nlinarith
  have hle : -x ^ 2 / (2 * u) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg x]
    · positivity
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 1 := Real.exp_le_one_iff.mpr hle
  have hinv : (Real.sqrt (2 * Real.pi * u))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hspos
  rw [brownianDensity_eq hu0]
  nlinarith [Real.exp_pos (-x ^ 2 / (2 * u)),
    inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * u))]

/-! ## The Gaussian jump integral -/

theorem lintegral_brownianLaw_one_sub_cos {u : ℝ} (hu : 0 ≤ u) (ω : ℝ) :
    (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(brownianLaw u))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
  set N := brownianLaw u with hN
  have hprob : IsProbabilityMeasure N := by rw [hN, brownianLaw]; infer_instance
  have hcos : Integrable (fun x : ℝ => Real.cos (ω * x)) N := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) (.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (ω * x)
  have hint : Integrable (fun x : ℝ => 1 - Real.cos (ω * x)) N :=
    (integrable_const 1).sub hcos
  have hnn : ∀ᵐ x ∂N, 0 ≤ 1 - Real.cos (ω * x) :=
    .of_forall fun x => by linarith [Real.cos_le_one (ω * x)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_sub (integrable_const 1) hcos]
  have hval : (∫ x, Real.cos (ω * x) ∂N) = Real.exp (-(u * ω ^ 2 / 2)) := by
    have h1 : (∫ x, Real.cos (ω * x) ∂N) = fourierCos N ω := by rw [fourierCos_apply]
    rw [h1, hN, brownianLaw, fourierCos_gaussianReal, Real.coe_toNNReal _ hu]
  rw [hval]
  simp

/-- Integration against `g_u` is integration against its density. -/
theorem lintegral_brownianDensity {u : ℝ} (hu : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (brownianDensity u x) * g x) = ∫⁻ x, g x ∂(brownianLaw u) := by
  rw [brownianLaw_eq_withDensity hu,
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_brownianDensity u).ennreal_ofReal) hg]
  rfl

/-- An even function integrates over the line to twice its integral over the positive axis. -/
theorem lintegral_even_eq_two_mul {g : ℝ → ℝ≥0∞} (heven : ∀ x, g (-x) = g x) :
    (∫⁻ x, g x) = 2 * ∫⁻ x in Ioi (0 : ℝ), g x := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  have hIio : (∫⁻ x in Iio (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    exact setLIntegral_congr_fun measurableSet_Iio fun x _ => (heven x).symm
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ)) g
    (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ x in Ici (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit]
  ring

/-- **The folded Gaussian jump integral**, `2∫₀^∞(1 - cos ωx)g_u(x)dx = 1 - e^{-uω²/2}`.

This is the identity the exponent computation runs on: the folding by `2` is exactly the
folding `k = 2xν₂` of `eq:bridge-profile`, so the factor cancels. -/
theorem lintegral_Ioi_brownianDensity_one_sub_cos {u : ℝ} (hu : 0 < u) (ω : ℝ) :
    (∫⁻ x in Ioi (0 : ℝ), 2 * ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.cos (ω * x)) := by fun_prop
  have hfull : (∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
    rw [← lintegral_brownianLaw_one_sub_cos hu.le ω, ← lintegral_brownianDensity hu _ hg]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (brownianDensity_nonneg u x), mul_comm]
  have heven : ∀ x : ℝ, ENNReal.ofReal ((1 - Real.cos (ω * -x)) * brownianDensity u (-x))
      = ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x) := by
    intro x
    rw [brownianDensity_neg, mul_neg, Real.cos_neg]
  rw [← hfull, lintegral_even_eq_two_mul heven, ← lintegral_const_mul' _ _ (by norm_num)]


/-! ## Mixtures against the Brownian laws -/

/-- The mixture of Gaussian laws against a probability law is a probability measure. -/
theorem isProbabilityMeasure_bind_brownianLaw (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (ρ.bind brownianLaw) := by
  refine isProbabilityMeasure_bind measurable_brownianLaw.aemeasurable (.of_forall fun u => ?_)
  rw [brownianLaw]; infer_instance

/-- The mixture is symmetric: every Gaussian law is, and symmetry passes through the mixture
set by set. -/
theorem isSymmetric_bind_brownianLaw (ρ : Measure ℝ) : IsSymmetric (ρ.bind brownianLaw) := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hneg hs,
    Measure.bind_apply (hneg hs) measurable_brownianLaw.aemeasurable,
    Measure.bind_apply hs measurable_brownianLaw.aemeasurable]
  refine lintegral_congr fun u => ?_
  have hsym : (brownianLaw u).map (fun x : ℝ => -x) = brownianLaw u :=
    isSymmetric_gaussianReal _
  calc brownianLaw u ((fun x : ℝ => -x) ⁻¹' s)
      = ((brownianLaw u).map (fun x : ℝ => -x)) s := (Measure.map_apply hneg hs).symm
    _ = brownianLaw u s := by rw [hsym]

/-- **Conditioning on the delay.** The cosine transform of the mixture at `ω` is the Laplace
transform of the delay law at `ω²/2`.

The route is through `1 - \cos` rather than through `\cos`, because that integrand is
nonnegative and `Measure.lintegral_bind` is available where a Bochner `integral_bind` is not.
The hypothesis `hcausal` is what makes `g_u` a genuine Gaussian `ρ`-almost everywhere: off
`[0,∞)` the wrapper is `δ₀` and the identity fails. -/
theorem fourierCos_bind_brownianLaw {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hcausal : ρ (Iio 0) = 0) (ω : ℝ) :
    fourierCos (ρ.bind brownianLaw) ω = ∫ u, Real.exp (-(ω ^ 2 / 2 * u)) ∂ρ := by
  set σ : ℝ := ω ^ 2 / 2 with hσdef
  have hσ : (0 : ℝ) ≤ σ := by positivity
  have hae : ∀ᵐ u ∂ρ, 0 ≤ u := by
    rw [ae_iff]
    convert hcausal using 2
    ext u; simp
  have hprob := isProbabilityMeasure_bind_brownianLaw ρ
  have hexpint : Integrable (fun u : ℝ => Real.exp (-(σ * u))) ρ := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
    filter_upwards [hae] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hcosint : Integrable (fun x : ℝ => Real.cos (ω * x)) (ρ.bind brownianLaw) := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) (.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (ω * x)
  have hjump : (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(ρ.bind brownianLaw))
      = ∫⁻ u, ENNReal.ofReal (1 - Real.exp (-(σ * u))) ∂ρ := by
    rw [Measure.lintegral_bind measurable_brownianLaw.aemeasurable (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with u hu
    rw [lintegral_brownianLaw_one_sub_cos hu ω,
      show -(u * ω ^ 2 / 2) = -(σ * u) from by rw [hσdef]; ring]
  have hnn1 : ∀ᵐ x ∂(ρ.bind brownianLaw), 0 ≤ 1 - Real.cos (ω * x) :=
    .of_forall fun x => by linarith [Real.cos_le_one (ω * x)]
  have hint1 : Integrable (fun x : ℝ => 1 - Real.cos (ω * x)) (ρ.bind brownianLaw) :=
    (integrable_const 1).sub hcosint
  have hnn2 : ∀ᵐ u ∂ρ, 0 ≤ 1 - Real.exp (-(σ * u)) := by
    filter_upwards [hae] with u hu
    have hle := Real.exp_le_one_iff.mpr (by nlinarith : -(σ * u) ≤ 0)
    linarith
  have hint2 : Integrable (fun u : ℝ => 1 - Real.exp (-(σ * u))) ρ :=
    (integrable_const 1).sub hexpint
  rw [← ofReal_integral_eq_lintegral_ofReal hint1 hnn1,
    ← ofReal_integral_eq_lintegral_ofReal hint2 hnn2] at hjump
  have hreal : (∫ x, (1 - Real.cos (ω * x)) ∂(ρ.bind brownianLaw))
      = ∫ u, (1 - Real.exp (-(σ * u))) ∂ρ :=
    (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn1)
      (integral_nonneg_of_ae hnn2)).mp hjump
  rw [integral_sub (integrable_const 1) hcosint,
    integral_sub (integrable_const 1) hexpint] at hreal
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hreal
  rw [fourierCos_apply]
  linarith

end SpatialLine
