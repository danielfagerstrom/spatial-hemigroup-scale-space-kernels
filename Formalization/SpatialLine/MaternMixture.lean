/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.MaternVariance
import SpatialLine.BrownianDensity
import SpatialLine.TransformUniqueness
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gamma

/-!
# The Matérn kernel as a Gamma mixture of Gaussians, and its even moments

Blueprint: `prop:matern-exponent`(3) — every moment finite, the even moments
`E X_t^{2n} = (2n-1)‼ (2t²)^n Γ(γ+n)/Γ(γ)`, and the variance `2γt²` at `n = 1`.

The route is the printed one, `X_t = B_T` with `T` Gamma of shape `γ` and scale `2t²`, but it
is built here rather than imported from `prop:bridge-families`(2): the mixing law is Mathlib's
`ProbabilityTheory.gammaMeasure`, and the identification of the two laws is one appeal to
`prop:fourier-uniqueness`. Nothing of chapter 9 is used.

## What proving this found

**The node has no symmetry hypothesis and does not need one — but the proof does, so the
symmetrisation has to be named.** `matern_moments` constrains `μ t` only through its cosine
transform, which pins the symmetrisation and nothing more; that is the R7 defect elsewhere in
this chapter and it is *not* a defect here, because every conclusion — integrability of `|x|^n`,
the even moments, the variance — is an integral of an **even** function and so depends on the
symmetrisation alone. The proof cannot ignore the gap, though: it identifies a measure with the
Gaussian mixture, and only the symmetrisation is identifiable. `SpatialLine.symmetrise` and
`lintegral_symmetrise_of_even` are what carry the conclusions back, and they are three lines
each. This is judgement point 3 of the charter — a formal statement must name its reading —
read from the other side: the statement was right and the proof needed a name the statement did
not.

**The Gaussian even moment is one Gamma value, not an induction.** `E B_v^{2n} = (2n-1)‼ v^n`
comes out of `integral_rpow_mul_exp_neg_mul_rpow` at `p = 2`, `q = 2n`, `b = (2v)⁻¹` together
with `Real.Gamma_nat_add_half`, which is exactly the half-integer special value in
double-factorial form. No integration by parts and no recursion: the two Mathlib lemmas meet.

**One Gamma-law lemma serves both purposes.** The mixing law is needed twice — for its Laplace
transform, to identify the mixture, and for its `n`-th moment, to evaluate the answer — and both
are `∫ u^q e^{-su}` against the Gamma density. `lintegral_gammaMeasure_rpow_mul_exp` states that
once, at `q = 0` for the transform and `s = 0` for the moment.

**Ledger A13 is not on this declaration's path either.** Integrability of `|x|^n`, the node's
first conjunct, follows from the even moments by `|x|^n ≤ 1 + x^{2n}`, so `matern_moments` prints
Lean core. `matern_moments_integrable` — wave 4's, by the moment criterion — remains the A13
consumer; the two routes are independent and the node's own proof says as much. Since the
author's decision of 2026-09-10 it is **no longer in the node's `\lean` tag**, a `[T]` node's
tag being read as its grounding.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology Nat

/-! ## The symmetrisation of a measure -/

/-- **The symmetrisation** `(ν + ν(-·))/2`: the measure a cosine transform determines. -/
noncomputable def symmetrise (ν : Measure ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (ν + ν.map (fun x => -x))

theorem isSymmetric_symmetrise (ν : Measure ℝ) : IsSymmetric (symmetrise ν) := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  have hmm : (ν.map (fun x : ℝ => -x)).map (fun x : ℝ => -x) = ν := by
    rw [Measure.map_map hneg hneg]; simp
  rw [IsSymmetric, symmetrise, Measure.map_smul, Measure.map_add _ _ hneg, hmm, add_comm]

instance isProbabilityMeasure_symmetrise (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (symmetrise ν) := by
  constructor
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  rw [symmetrise, Measure.smul_apply, Measure.add_apply, Measure.map_apply hneg MeasurableSet.univ]
  simp only [measure_univ, Set.preimage_univ]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num, smul_eq_mul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- **An even integrand does not see the difference.** -/
theorem lintegral_symmetrise_of_even {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    (heven : ∀ x, g (-x) = g x) (ν : Measure ℝ) :
    (∫⁻ x, g x ∂(symmetrise ν)) = ∫⁻ x, g x ∂ν := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  rw [symmetrise, lintegral_smul_measure, lintegral_add_measure, lintegral_map hg hneg]
  simp only [heven]
  rw [← two_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- The cosine transform is blind to the antisymmetric part. -/
theorem fourierCos_symmetrise (ν : Measure ℝ) [IsFiniteMeasure ν] (ω : ℝ) :
    fourierCos (symmetrise ν) ω = fourierCos ν ω := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  haveI : IsFiniteMeasure (ν.map (fun x : ℝ => -x)) := by
    constructor
    rw [Measure.map_apply hneg MeasurableSet.univ]
    exact measure_lt_top ν _
  have hint : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ →
      Integrable (fun x : ℝ => Real.cos (ω * x)) ρ := by
    intro ρ hρ
    exact Integrable.mono' (integrable_const 1) (by fun_prop)
      (.of_forall fun x => by simpa using Real.abs_cos_le_one (ω * x))
  rw [fourierCos_apply, fourierCos_apply, symmetrise, integral_smul_measure,
    integral_add_measure (hint ν inferInstance) (hint _ inferInstance),
    integral_map hneg.aemeasurable (by fun_prop)]
  have heq : (∫ x : ℝ, Real.cos (ω * -x) ∂ν) = ∫ x : ℝ, Real.cos (ω * x) ∂ν := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    show Real.cos (ω * -x) = Real.cos (ω * x)
    rw [show ω * -x = -(ω * x) by ring, Real.cos_neg]
  rw [heq, ← two_mul, smul_eq_mul,
    show ((2 : ℝ≥0∞)⁻¹).toReal = (2 : ℝ)⁻¹ by simp]
  ring

/-! ## The even moments of a centred Gaussian -/

/-- `∫₀^∞ x^{2n} g_v(x) dx = (2n-1)‼ v^n / 2`.

`integral_rpow_mul_exp_neg_mul_rpow` at `p = 2`, `q = 2n`, `b = (2v)⁻¹` meets
`Real.Gamma_nat_add_half`, and the normalising `(2πv)^{-1/2}` cancels the `√(2v)√π` the two
produce. -/
theorem integral_Ioi_pow_mul_brownianDensity {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * brownianDensity v x)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) * v ^ n / 2 := by
  have hb : (0 : ℝ) < (2 * v)⁻¹ := by positivity
  have hstep : (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * brownianDensity v x)
      = (Real.sqrt (2 * Real.pi * v))⁻¹
          * ∫ x in Ioi (0 : ℝ), x ^ ((2 * n : ℕ) : ℝ) * Real.exp (-(2 * v)⁻¹ * x ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [brownianDensity_eq hv, Real.rpow_natCast, Real.rpow_two]
    have hexp : -x ^ 2 / (2 * v) = -(2 * v)⁻¹ * x ^ 2 := by field_simp
    rw [hexp]
    ring
  rw [hstep, integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by exact_mod_cast lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg (2 * n))
      : (-1 : ℝ) < ((2 * n : ℕ) : ℝ)) hb]
  have hA : (0 : ℝ) < 2 * v := by positivity
  have he : -(((2 * n : ℕ) : ℝ) + 1) / 2 = -((n : ℝ) + 1 / 2) := by push_cast; ring
  have hq : ((((2 * n : ℕ) : ℝ) + 1)) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  rw [he, hq, Real.Gamma_nat_add_half, Real.inv_rpow hA.le, ← Real.rpow_neg hA.le, neg_neg,
    Real.rpow_add hA, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (2 * Real.pi * v) = Real.sqrt (2 * v) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul hA.le, show (2 * v) * Real.pi = 2 * Real.pi * v by ring]
  have hs2v : Real.sqrt (2 * v) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hsq, mul_pow]
  field_simp

theorem integrableOn_Ioi_pow_mul_brownianDensity {v : ℝ} (hv : 0 < v) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * n) * brownianDensity v x) (Ioi (0 : ℝ)) := by
  have hb : (0 : ℝ) < (2 * v)⁻¹ := by positivity
  have hbase : IntegrableOn
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹
        * (x ^ ((2 * n : ℕ) : ℝ) * Real.exp (-(2 * v)⁻¹ * x ^ (2 : ℝ)))) (Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (by exact_mod_cast lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg (2 * n))
        : (-1 : ℝ) < ((2 * n : ℕ) : ℝ)) (by norm_num) hb).const_mul _
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  show (Real.sqrt (2 * Real.pi * v))⁻¹ * (x ^ ((2 * n : ℕ) : ℝ)
      * Real.exp (-(2 * v)⁻¹ * x ^ (2 : ℝ))) = x ^ (2 * n) * brownianDensity v x
  rw [brownianDensity_eq hv, Real.rpow_natCast, Real.rpow_two]
  have hexp : -x ^ 2 / (2 * v) = -(2 * v)⁻¹ * x ^ 2 := by field_simp
  rw [hexp]
  ring

/-- **The even moments of the centred Gaussian**: `E B_v^{2n} = (2n-1)‼ v^n`. -/
theorem lintegral_pow_brownianLaw {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂(brownianLaw v))
      = ENNReal.ofReal ((Nat.doubleFactorial (2 * n - 1) : ℝ) * v ^ n) := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * n)) := by fun_prop
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * n) := fun x => by rw [pow_mul]; positivity
  have h1 : (∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂(brownianLaw v))
      = ∫⁻ x, ENNReal.ofReal (x ^ (2 * n) * brownianDensity v x) := by
    rw [← lintegral_brownianDensity hv _ hmeas]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (brownianDensity_nonneg v x), mul_comm]
  have heven : ∀ x : ℝ, ENNReal.ofReal ((-x) ^ (2 * n) * brownianDensity v (-x))
      = ENNReal.ofReal (x ^ (2 * n) * brownianDensity v x) := by
    intro x
    rw [brownianDensity_neg, pow_mul, pow_mul]
    norm_num
  rw [h1, lintegral_even_eq_two_mul heven,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_pow_mul_brownianDensity hv n)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx =>
        mul_nonneg (hnn x) (brownianDensity_nonneg v x))),
    integral_Ioi_pow_mul_brownianDensity hv n,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-! ## The Gamma mixing law -/

/-- Integration against the Gamma law is integration against its density on `(0,∞)`. -/
theorem lintegral_gammaMeasure {a r : ℝ} {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ u, g u ∂(gammaMeasure a r))
      = ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ a / Real.Gamma a * u ^ (a - 1) * Real.exp (-(r * u))) * g u := by
  have hpdfm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdfm hg]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun u => gammaPDF a r u * g u) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hneg : (∫⁻ u in Iio (0 : ℝ), gammaPDF a r u * g u) = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Iio fun u hu => ?_).trans lintegral_zero
    rw [gammaPDF_of_neg hu, zero_mul]
  have hIci : (∫⁻ u in Ici (0 : ℝ), gammaPDF a r u * g u)
      = ∫⁻ u in Ioi (0 : ℝ), gammaPDF a r u * g u :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hneg, hIci, zero_add] at hsplit
  simp only [Pi.mul_apply]
  rw [← hsplit]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [gammaPDF_of_nonneg (le_of_lt hu)]

/-- **The Gamma law against `u^q e^{-su}`**, the one computation both uses need. -/
theorem lintegral_gammaMeasure_rpow_mul_exp {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {q s : ℝ}
    (hq : 0 < a + q) (hs : 0 ≤ s) :
    (∫⁻ u, ENNReal.ofReal (u ^ q * Real.exp (-(s * u))) ∂(gammaMeasure a r))
      = ENNReal.ofReal
          (r ^ a * (1 / (r + s)) ^ (a + q) * Real.Gamma (a + q) / Real.Gamma a) := by
  have hR : (0 : ℝ) < r + s := by linarith
  have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (u ^ q * Real.exp (-(s * u))) := by
    fun_prop
  rw [lintegral_gammaMeasure hmeas]
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ a / Real.Gamma a * u ^ (a - 1) * Real.exp (-(r * u)))
          * ENNReal.ofReal (u ^ q * Real.exp (-(s * u)))
        = ENNReal.ofReal (r ^ a / Real.Gamma a
            * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (a + q) - 1 = (a - 1) + q by ring, Real.rpow_add hu0,
      show -((r + s) * u) = -(r * u) + -(s * u) by ring, Real.exp_add]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : IntegrableOn (fun u : ℝ => r ^ a / Real.Gamma a
      * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))) (Ioi (0 : ℝ)) := by
    have h0 : IntegrableOn (fun u : ℝ => r ^ a / Real.Gamma a
        * (u ^ ((a + q) - 1) * Real.exp (-(r + s) * u ^ (1 : ℝ)))) (Ioi (0 : ℝ)) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (a + q) - 1) (p := 1) (b := r + s)
        (by linarith) le_rfl hR).const_mul (r ^ a / Real.Gamma a)
    refine h0.congr_fun (fun u hu => ?_) measurableSet_Ioi
    show r ^ a / Real.Gamma a * (u ^ ((a + q) - 1) * Real.exp (-(r + s) * u ^ (1 : ℝ)))
      = r ^ a / Real.Gamma a * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))
    rw [Real.rpow_one]
    ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => by
      have hu0 : (0 : ℝ) < u := hu; positivity))]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hq hR]
  congr 1
  field_simp

/-- The Gamma law lives on the positive axis. -/
theorem gammaMeasure_Iio_zero (a r : ℝ) : gammaMeasure a r (Iio (0 : ℝ)) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ u ∂(gammaMeasure a r), 0 < u := by
  have hIic : gammaMeasure a r (Iic (0 : ℝ)) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
      setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [ae_iff]
  convert hIic using 2
  ext u; simp

/-! ## The mixture and the moments -/

noncomputable def maternDelay (γ t : ℝ) : Measure ℝ := gammaMeasure γ (2 * t ^ 2)⁻¹

theorem isProbabilityMeasure_maternDelay {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) :
    IsProbabilityMeasure (maternDelay γ t) :=
  isProbabilityMeasure_gammaMeasure hγ (by positivity)

/-- **The Laplace transform of the delay law**: `E e^{-σT} = (1 + 2t²σ)^{-γ}`, which is the
Gamma law of shape `γ` and scale `2t²` that `prop:matern-exponent`(3) names. -/
theorem integral_exp_neg_maternDelay {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫ u, Real.exp (-(σ * u)) ∂(maternDelay γ t)) = (1 + 2 * t ^ 2 * σ) ^ (-γ) := by
  have hA : (0 : ℝ) < 2 * t ^ 2 := by positivity
  have hr : (0 : ℝ) < (2 * t ^ 2)⁻¹ := by positivity
  have hGa : (0 : ℝ) < Real.Gamma γ := Real.Gamma_pos_of_pos hγ
  have hlint := lintegral_gammaMeasure_rpow_mul_exp (a := γ) (r := (2 * t ^ 2)⁻¹) hγ hr
    (q := 0) (s := σ) (by simpa using hγ) hσ
  simp only [Real.rpow_zero, one_mul, add_zero] at hlint
  have hnn : (0 : ℝ) ≤ (2 * t ^ 2)⁻¹ ^ γ * (1 / ((2 * t ^ 2)⁻¹ + σ)) ^ γ
      * Real.Gamma γ / Real.Gamma γ := by
    have h1 : (0 : ℝ) ≤ (2 * t ^ 2)⁻¹ ^ γ := Real.rpow_nonneg hr.le γ
    have h2 : (0 : ℝ) ≤ (1 / ((2 * t ^ 2)⁻¹ + σ)) ^ γ := Real.rpow_nonneg (by positivity) γ
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun u => (Real.exp_pos _).le) (by fun_prop),
    maternDelay, hlint, ENNReal.toReal_ofReal hnn,
    mul_div_assoc, div_self hGa.ne', mul_one,
    ← Real.mul_rpow hr.le (by positivity)]
  have hbase : (2 * t ^ 2)⁻¹ * (1 / ((2 * t ^ 2)⁻¹ + σ)) = (1 + 2 * t ^ 2 * σ)⁻¹ := by
    have hpos : (0 : ℝ) < 1 + 2 * t ^ 2 * σ := by positivity
    field_simp
  rw [hbase, ← Real.rpow_neg_one (1 + 2 * t ^ 2 * σ), ← Real.rpow_mul (by positivity)]
  norm_num

/-- **The mixture has the Matern transform.** -/
theorem fourierCos_maternDelay_bind {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (ω : ℝ) :
    fourierCos ((maternDelay γ t).bind brownianLaw) ω
      = Real.exp (-maternExponent γ 1 (t * ω)) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
  haveI := isProbabilityMeasure_maternDelay hγ ht
  rw [fourierCos_bind_brownianLaw (by rw [maternDelay]; exact gammaMeasure_Iio_zero _ _) ω,
    integral_exp_neg_maternDelay hγ ht (σ := ω ^ 2 / 2) (by positivity),
    show 1 + 2 * t ^ 2 * (ω ^ 2 / 2) = 1 + t ^ 2 * ω ^ 2 by ring,
    ← maternTransform_zero γ t ω, show (1 : ℝ) + (0 : ℝ) ^ 2 * ω ^ 2 = 1 by ring,
    one_div, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]

theorem lintegral_pow_maternDelay_bind {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂((maternDelay γ t).bind brownianLaw))
      = ENNReal.ofReal ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
          * Real.Gamma (γ + n) / Real.Gamma γ) := by
  have hA : (0 : ℝ) < 2 * t ^ 2 := by positivity
  have hr : (0 : ℝ) < (2 * t ^ 2)⁻¹ := by positivity
  have hGa : (0 : ℝ) < Real.Gamma γ := Real.Gamma_pos_of_pos hγ
  haveI := isProbabilityMeasure_maternDelay hγ ht
  rw [Measure.lintegral_bind measurable_brownianLaw.aemeasurable (by fun_prop)]
  have hstep : (∫⁻ u, (∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂(brownianLaw u)) ∂(maternDelay γ t))
      = ∫⁻ u, ENNReal.ofReal ((Nat.doubleFactorial (2 * n - 1) : ℝ))
          * ENNReal.ofReal (u ^ ((n : ℕ) : ℝ) * Real.exp (-(0 * u))) ∂(maternDelay γ t) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_gammaMeasure γ (2 * t ^ 2)⁻¹] with u hu
    rw [lintegral_pow_brownianLaw hu n, zero_mul, neg_zero, Real.exp_zero, mul_one,
      Real.rpow_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, maternDelay,
    lintegral_gammaMeasure_rpow_mul_exp hγ hr (q := ((n : ℕ) : ℝ)) (by positivity) le_rfl,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpow : ((2 * t ^ 2)⁻¹ : ℝ) ^ γ * (1 / ((2 * t ^ 2)⁻¹ + 0)) ^ (γ + (n : ℝ))
      = (2 * t ^ 2) ^ n := by
    rw [add_zero, one_div, inv_inv, Real.inv_rpow hA.le, Real.rpow_add hA, Real.rpow_natCast,
      ← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hA γ).ne', one_mul]
  calc (Nat.doubleFactorial (2 * n - 1) : ℝ)
        * ((2 * t ^ 2)⁻¹ ^ γ * (1 / ((2 * t ^ 2)⁻¹ + 0)) ^ (γ + (n : ℝ))
          * Real.Gamma (γ + (n : ℝ)) / Real.Gamma γ)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ)
          * ((2 * t ^ 2)⁻¹ ^ γ * (1 / ((2 * t ^ 2)⁻¹ + 0)) ^ (γ + (n : ℝ)))
          * Real.Gamma (γ + (n : ℝ)) / Real.Gamma γ := by ring
    _ = (Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
          * Real.Gamma (γ + (n : ℝ)) / Real.Gamma γ := by rw [hpow]

theorem matern_moments (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-maternExponent γ 1 (t * ω)))
    {t : ℝ} (ht : 0 < t) :
    (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) (μ t)) ∧
      (∀ n : ℕ, (∫ x, x ^ (2 * n) ∂(μ t))
        = (Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
            * Real.Gamma (γ + n) / Real.Gamma γ) ∧
      (∫ x, x ^ 2 ∂(μ t)) = 2 * γ * t ^ 2 := by
  haveI := hprob t ht
  haveI := isProbabilityMeasure_maternDelay hγ ht
  haveI := isProbabilityMeasure_bind_brownianLaw (maternDelay γ t)
  have hGa : (0 : ℝ) < Real.Gamma γ := Real.Gamma_pos_of_pos hγ
  have hEq : symmetrise (μ t) = (maternDelay γ t).bind brownianLaw := by
    refine fourier_uniqueness fun ω => ?_
    rw [charFun_eq_fourierCos_of_symmetric (isSymmetric_symmetrise _),
      charFun_eq_fourierCos_of_symmetric (isSymmetric_bind_brownianLaw _),
      fourierCos_symmetrise, hcos t ω ht, fourierCos_maternDelay_bind hγ ht]
  have hV : ∀ n : ℕ, (0 : ℝ) ≤ (Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
      * Real.Gamma (γ + n) / Real.Gamma γ := by
    intro n
    have h1 : (0 : ℝ) ≤ Real.Gamma (γ + n) :=
      (Real.Gamma_pos_of_pos (by positivity)).le
    positivity
  have hkey : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂(μ t))
      = ENNReal.ofReal ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
          * Real.Gamma (γ + n) / Real.Gamma γ) := by
    intro n
    rw [← lintegral_symmetrise_of_even (g := fun x => ENNReal.ofReal (x ^ (2 * n)))
      (by fun_prop) (fun x => by rw [pow_mul, pow_mul]; norm_num) (μ t),
      hEq, lintegral_pow_maternDelay_bind hγ ht n]
  have hsq : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) (μ t) := by
    intro n
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (.of_forall fun x => by rw [pow_mul]; positivity)]
    rw [hkey n]
    exact ENNReal.ofReal_lt_top
  have hmom : ∀ n : ℕ, (∫ x, x ^ (2 * n) ∂(μ t))
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) * (2 * t ^ 2) ^ n
          * Real.Gamma (γ + n) / Real.Gamma γ := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae
      (.of_forall fun x => by rw [pow_mul]; positivity) (by fun_prop),
      hkey n, ENNReal.toReal_ofReal (hV n)]
  refine ⟨fun n => ?_, hmom, ?_⟩
  · refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hsq n)) (by fun_prop)
      (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rcases le_total |x| 1 with h | h
    · have h1 : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) h
      have h2 : (0 : ℝ) ≤ x ^ (2 * n) := by rw [pow_mul]; positivity
      linarith
    · have h1 : |x| ^ n ≤ |x| ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      have h2 : |x| ^ (2 * n) = x ^ (2 * n) := by rw [pow_mul, pow_mul, sq_abs]
      linarith [h1, h2.symm.le, h2.le]
  · have h1 := hmom 1
    rw [show 2 * 1 = 2 from rfl] at h1
    rw [h1, show ((1 : ℕ) : ℝ) = 1 from by norm_num, Real.Gamma_add_one hγ.ne']
    have : Nat.doubleFactorial (2 * 1 - 1) = 1 := by decide
    rw [this]
    field_simp
    ring


/-- A symmetric measure is its own symmetrisation. -/
theorem symmetrise_eq_self {ν : Measure ℝ} (hsym : IsSymmetric ν) : symmetrise ν = ν := by
  rw [symmetrise, hsym, ← two_smul ℝ≥0∞ ν, ← smul_assoc, smul_eq_mul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

/-- **`prop:matern-exponent`(3), the mixture representation.** The kernel at canonical scale `t`
*is* the law of `B_T` with `T` Gamma of shape `γ` and scale `2t²`, and the delay law is
identified by its Laplace transform.

This is the sentence `X_t \seq B_T` of clause (3), which `Skeleton.matern_moments` does not
type: that declaration states the moments the sentence is offered as a reason for. The
hypothesis `hsym` is what the moments do not need and this does --- a cosine transform pins only
the symmetrisation, and this clause is an identity of measures. -/
theorem matern_gamma_mixture (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hsym : ∀ t : ℝ, 0 < t → IsSymmetric (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-maternExponent γ 1 (t * ω)))
    {t : ℝ} (ht : 0 < t) :
    μ t = (maternDelay γ t).bind brownianLaw ∧
      ∀ σ : ℝ, 0 ≤ σ →
        (∫ u, Real.exp (-(σ * u)) ∂(maternDelay γ t)) = (1 + 2 * t ^ 2 * σ) ^ (-γ) := by
  haveI := hprob t ht
  haveI := isProbabilityMeasure_maternDelay hγ ht
  haveI := isProbabilityMeasure_bind_brownianLaw (maternDelay γ t)
  refine ⟨?_, fun σ hσ => integral_exp_neg_maternDelay hγ ht hσ⟩
  rw [← symmetrise_eq_self (hsym t ht)]
  refine fourier_uniqueness fun ω => ?_
  rw [charFun_eq_fourierCos_of_symmetric (isSymmetric_symmetrise _),
    charFun_eq_fourierCos_of_symmetric (isSymmetric_bind_brownianLaw _),
    fourierCos_symmetrise, hcos t ω ht, fourierCos_maternDelay_bind hγ ht]

/-! ## `prop:two-members`(2), the moment sentence -/

/-- **`prop:two-members`(2), the moments.** The Matern family at shape `γ` has every moment
finite, mean displacement `0` and variance `2γt²`.

Statement verbatim from `Skeleton.two_members_matern_moments`. The mean and the variance are
`matern_mean_variance`; the integrability conjunct is `matern_moments`, whose own route to it
is the even moments of the Gamma mixture and `|x|^n ≤ 1 + x^{2n}`. So all three conjuncts are
**Lean core**.

Moved here from `SpatialLine/MaternMoments.lean` on 2026-09-14 (R156), with the integrability
conjunct re-routed from `matern_moments_integrable` — the moment criterion, ledger **A13** —
to `matern_moments`. The declaration has to sit in this file because `matern_moments` is
proved here and this file imports `MaternMoments.lean`, not the other way round. The A13 route
remains as `matern_moments_integrable`, a second and independent part-proof with its own guard
line; nothing reads it any longer. -/
theorem two_members_matern_moments (γ : ℝ) (hγ : 0 < γ) (ρ : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ρ s t))
    (hsym : ∀ s t, 0 ≤ s → s ≤ t → IsSymmetric (ρ s t))
    (hcos : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ,
      fourierCos (ρ s t) ω = ((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ) :
    ∀ t : ℝ, 0 < t →
      (∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) (ρ 0 t)) ∧
        (∫ x, x ∂(ρ 0 t)) = 0 ∧ (∫ x, x ^ 2 ∂(ρ 0 t)) = 2 * γ * t ^ 2 := by
  intro t ht
  have hprob' : ∀ s : ℝ, 0 < s → IsProbabilityMeasure (ρ 0 s) :=
    fun s hs => hprob 0 s le_rfl hs.le
  have hsym' : ∀ s : ℝ, 0 < s → IsSymmetric (ρ 0 s) := fun s hs => hsym 0 s le_rfl hs.le
  have hcos' : ∀ s ω : ℝ, 0 < s →
      fourierCos (ρ 0 s) ω = Real.exp (-maternExponent γ 1 (s * ω)) := by
    intro s ω hs
    rw [hcos 0 s le_rfl hs.le ω, maternTransform_zero]
  refine ⟨fun n => ?_, matern_mean_variance γ hγ (fun s => ρ 0 s) hprob' hsym' hcos' ht⟩
  have habs := (matern_moments γ hγ (fun s => ρ 0 s) hprob' hcos' ht).1 n
  refine Integrable.mono' habs (by fun_prop) (.of_forall fun x => ?_)
  exact le_of_eq (by rw [Real.norm_eq_abs, abs_pow])

end SpatialLine
