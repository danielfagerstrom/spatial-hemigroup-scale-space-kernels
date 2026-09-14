/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.SelfDecomposable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The variance of an admissible kernel

Blueprint: the `[T]` half of `prop:moments-tails`(1) — the mean is `0` by symmetry and the
variance is `t²(2a + ∫₀^∞ x k(x) dx)` whenever the catalogue has a finite first moment
against `dx`.

**The file was called `SpatialLine.Variance` and imported `SpatialLine.Moments` until
2026-09-14.** Nothing here consumes ledger A13 or A14 — the note below on Fatou's lemma is why —
and the one lemma it took from `Moments.lean`, the finiteness bridge
`lintegral_ofReal_ne_top_iff_integrableOn`, has moved here, `Moments.lean` now importing this
file for it. So the variance formula sits on Chapter 7 (`SelfDecomposable`, for `profileJumpL`)
and the moment criterion sits above it. That is what `prop:two-members`(2)'s variance sentence
needs: a Chapter 3 node reaches the formula without reaching the criterion (ADR-0005).

## What proving this found

**The obligation is a limit at the origin, not a second derivative.** The node's printed proof
reads `E X_t² = -∂²_ω e^{-F(tω)}|_{ω=0} = t²F''(0)` and then differentiates
`eq:levy-khintchine` twice under the integral sign. Nothing in the statement asks for a
derivative: both sides are pinned by the *second difference* of the transform at the origin,
and the whole proof is the single limit

  `lim_{ω → 0} (1 - μ̂_t(ω)) · 2/ω²`,

evaluated once on the measure side and once on the exponent side. Two differentiations under
the integral sign — each of which would need its own dominating function, and the second of
which is exactly the step the estimate priced — become one dominated convergence. The proof of
record is rewritten to this route.

**One identity carries the whole argument.** For `ω ≠ 0`,

  `(1 - cos(cω)) · 2/ω² = c² sinc(cω/2)²`,

which is the half-angle formula `1 - cos u = 2 sin²(u/2)` divided by `ω²`. It is an *equality*,
so it supplies at one stroke the pointwise limit (`sinc` is continuous and `sinc 0 = 1`), the
dominating function (`|sinc| ≤ 1`, hence the bound `c²`), and the elementary inequality
`1 - cos u ≤ u²/2` that the integrability arguments need. Mathlib's `Real.sinc` and
`Real.continuous_sinc` are what make this cheap; without them the same three facts are three
separate estimates.

**The second moment is finite for free, so ledger A13 is not spent here.** The natural fear is
circularity — dominated convergence on the measure side needs `x²` integrable, which is
`prop:moments-tails`(1)'s criterion at `n = 2`, an `[A]` interface. It is not needed: Fatou's
lemma applied to the same sequence of integrands bounds `∫ x² dμ_t` by `t²(2a + ∫ x k)` *before*
any integrability is known, and the domination then upgrades the inequality to an equality. So
this development prints Lean core, and the finiteness of the second moment is a conclusion of it
rather than a hypothesis.

**The exponential is squeezed, not expanded.** Passing from `F` to `1 - e^{-F}` needs no Taylor
remainder: `y e^{-y} ≤ 1 - e^{-y} ≤ y` for `y ≥ 0`, both halves being `Real.add_one_le_exp` read
at `y` and at `-y`, and the two bounds have the same limit because `F(tω) → 0`.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## A finiteness bridge -/

/-- A nonnegative measurable function has a finite `lintegral` of its `ofReal` exactly when it
is integrable. The `←` direction is `lintegral_ofReal_ne_top_of_integrableOn`; the `→`
direction is `hasFiniteIntegral_iff_ofReal` read backwards, and it is what turns the moment
criterion's right-hand side into a question about an improper integral. -/
theorem lintegral_ofReal_ne_top_iff_integrableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ᵐ x ∂(volume.restrict s), 0 ≤ f x) :
    (∫⁻ x in s, ENNReal.ofReal (f x)) ≠ ⊤ ↔ IntegrableOn f s :=
  ⟨fun h => ⟨hm, by rw [hasFiniteIntegral_iff_ofReal hnn]; exact lt_top_iff_ne_top.mpr h⟩,
    fun h => lintegral_ofReal_ne_top_of_integrableOn h hnn⟩

/-! ## The half-angle identity in `sinc` form -/

/-- `1 - cos u = 2 sin²(u/2)`. -/
theorem one_sub_cos_eq_two_mul_sin_sq (u : ℝ) : 1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
  have h := Real.cos_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring] at h
  have h2 := Real.sin_sq (u / 2)
  rw [h2, h]; ring

/-- `sinc² ≤ 1`, from `|sinc| ≤ 1`. -/
theorem sinc_sq_le_one (y : ℝ) : Real.sinc y ^ 2 ≤ 1 := by
  have h := Real.abs_sinc_le_one y
  nlinarith [abs_nonneg (Real.sinc y), sq_abs (Real.sinc y)]

/-- **The identity the variance argument runs on.** For `ω ≠ 0`,
`(1 - cos(cω)) · 2/ω² = c² sinc(cω/2)²`. -/
theorem one_sub_cos_mul_two_div (c : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (1 - Real.cos (c * ω)) * (2 / ω ^ 2) = c ^ 2 * Real.sinc (c * ω / 2) ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hne : c * ω / 2 ≠ 0 := by positivity
  rw [one_sub_cos_eq_two_mul_sin_sq, Real.sinc_of_ne_zero hne, div_pow]
  field_simp

/-- `1 - cos u ≤ u²/2`, in the product form the estimates below use. -/
theorem one_sub_cos_le_sq (c ω : ℝ) : (1 - Real.cos (c * ω)) * 2 ≤ c ^ 2 * ω ^ 2 := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simp
  have hω2 : (0:ℝ) < ω ^ 2 := by positivity
  have h := one_sub_cos_mul_two_div c hω
  have h' : (1 - Real.cos (c * ω)) * 2 = c ^ 2 * Real.sinc (c * ω / 2) ^ 2 * ω ^ 2 := by
    field_simp at h
    linarith [h]
  rw [h']
  have hkey : 0 ≤ c ^ 2 * ω ^ 2 * (1 - Real.sinc (c * ω / 2) ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg c) hω2.le)
      (sub_nonneg.mpr (sinc_sq_le_one (c * ω / 2)))
  nlinarith [hkey]

/-! ## The exponent side

Throughout, `hfin` is the node's "when finite": the catalogue has a finite first moment against
`dx` on `(0,∞)`, which is `∫₀^∞ x k(x) dx < ∞`.
-/

variable (P : SDProfile)

/-- The catalogue's first moment is a Bochner integral when it is finite. -/
theorem integrableOn_id_mul_k
    (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤) :
    IntegrableOn (fun x : ℝ => x * P.k x) (Ioi (0 : ℝ)) := by
  refine (lintegral_ofReal_ne_top_iff_integrableOn ?_ ?_).mp hfin
  · exact (aemeasurable_id.mul P.aemeasurable_k).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    exact mul_nonneg (le_of_lt hx) (P.k_nonneg x hx)

/-- Under `hfin` the Lévy integrand is dominated by `ω² x k(x)/2`, hence integrable. -/
theorem integrableOn_profileJump
    (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤) (ω : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (ω * x)) * P.k x / x) (Ioi (0 : ℝ)) := by
  have hb := (integrableOn_id_mul_k P hfin).const_mul (ω ^ 2 / 2)
  refine Integrable.mono' hb
    ((((Measurable.aemeasurable (by fun_prop)).mul P.aemeasurable_k).div
      aemeasurable_id).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  have hk : 0 ≤ P.k x := P.k_nonneg x hx
  have hc : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : (1 - Real.cos (ω * x)) * 2 ≤ x ^ 2 * ω ^ 2 := by
    have := one_sub_cos_le_sq x ω
    rwa [show x * ω = ω * x by ring] at this
  rw [div_le_iff₀ hx0]
  nlinarith [hk, hx0, mul_nonneg hk (le_of_lt hx0)]

/-- The jump part of an admissible exponent is finite at every frequency. -/
theorem profileJumpL_ne_top (ω : ℝ) : profileJumpL P.k ω ≠ ⊤ := by
  intro h
  exact P.exponentL_ne_top ω (by rw [SDProfile.exponentL_eq_add_jump, h, add_top])

/-- The jump part as a Bochner integral. -/
theorem integral_profileJump_eq (ω : ℝ) :
    (∫ x in Ioi (0 : ℝ), (1 - Real.cos (ω * x)) * P.k x / x)
      = (profileJumpL P.k ω).toReal := by
  rw [profileJumpL]
  refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    have hk : 0 ≤ P.k x := P.k_nonneg x hx
    have hc : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    positivity
  · exact ((((Measurable.aemeasurable (by fun_prop)).mul P.aemeasurable_k).div
      aemeasurable_id).aestronglyMeasurable)

/-- **`eq:sd-profile` in real form**: `F(ω) = aω² + ∫₀^∞ (1 - cos ωx) k(x) dx/x`, with the
second term a Bochner integral. -/
theorem exponent_eq_add_integral (ω : ℝ) :
    P.exponent ω = P.a * ω ^ 2 + ∫ x in Ioi (0 : ℝ), (1 - Real.cos (ω * x)) * P.k x / x := by
  rw [integral_profileJump_eq, SDProfile.exponent, SDProfile.exponentL_eq_add_jump,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (profileJumpL_ne_top P ω),
    ENNReal.toReal_ofReal (mul_nonneg P.a_nonneg (sq_nonneg ω))]

/-- **The catalogue's contribution to the second difference.** As `ω → 0`,
`2ω⁻² ∫₀^∞ (1 - cos tωx) k(x) dx/x → t² ∫₀^∞ x k(x) dx`.

The dominating function is `t² x k(x)`, supplied by `hfin`, and the pointwise limit is the
continuity of `sinc` at the origin. -/
theorem tendsto_profileJump_div
    (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤) (t : ℝ) :
    Tendsto (fun ω : ℝ => (∫ x in Ioi (0 : ℝ), (1 - Real.cos (t * ω * x)) * P.k x / x)
        * (2 / ω ^ 2)) (𝓝[≠] (0 : ℝ))
      (𝓝 (t ^ 2 * ∫ x in Ioi (0 : ℝ), x * P.k x)) := by
  have hbnd : IntegrableOn (fun x : ℝ => t ^ 2 * (x * P.k x)) (Ioi (0 : ℝ)) :=
    (integrableOn_id_mul_k P hfin).const_mul _
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * P.k x := fun x hx =>
    mul_nonneg (le_of_lt hx) (P.k_nonneg x hx)
  have key : ∀ ω : ℝ, ω ≠ 0 →
      (∫ x in Ioi (0 : ℝ), (1 - Real.cos (t * ω * x)) * P.k x / x) * (2 / ω ^ 2)
        = ∫ x in Ioi (0 : ℝ), t ^ 2 * (x * P.k x) * Real.sinc (x * t * ω / 2) ^ 2 := by
    intro ω hω
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    have h := one_sub_cos_mul_two_div (x * t) hω
    rw [show (x * t) * ω = t * ω * x by ring] at h
    rw [show (1 - Real.cos (t * ω * x)) * P.k x / x * (2 / ω ^ 2)
        = ((1 - Real.cos (t * ω * x)) * (2 / ω ^ 2)) * P.k x / x by ring, h]
    field_simp
  have hDCT : Tendsto (fun ω : ℝ =>
      ∫ x in Ioi (0 : ℝ), t ^ 2 * (x * P.k x) * Real.sinc (x * t * ω / 2) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x in Ioi (0 : ℝ), t ^ 2 * (x * P.k x) * 1)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => t ^ 2 * (x * P.k x)) (.of_forall fun ω => ?_) (.of_forall fun ω => ?_) hbnd ?_
    · exact ((aemeasurable_const.mul (aemeasurable_id.mul P.aemeasurable_k)).mul
        (((Real.continuous_sinc.comp (by fun_prop)).pow 2).aemeasurable)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
      have h0 := hnn x hx
      have hs := sinc_sq_le_one (x * t * ω / 2)
      have hs0 : 0 ≤ Real.sinc (x * t * ω / 2) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg t) h0) hs
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
      have hc : Continuous fun ω : ℝ => t ^ 2 * (x * P.k x) * Real.sinc (x * t * ω / 2) ^ 2 := by
        fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := {(0:ℝ)}ᶜ))
      simpa using this
  simp only [mul_one] at hDCT
  rw [integral_const_mul] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (key ω hω).symm

/-- **The second difference of the exponent at the origin.** -/
theorem tendsto_exponent_div (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤)
    (t : ℝ) :
    Tendsto (fun ω : ℝ => P.exponent (t * ω) * (2 / ω ^ 2)) (𝓝[≠] (0 : ℝ))
      (𝓝 (t ^ 2 * (2 * P.a + ∫ x in Ioi (0 : ℝ), x * P.k x))) := by
  have h := (tendsto_profileJump_div P hfin t).const_add (2 * P.a * t ^ 2)
  rw [show 2 * P.a * t ^ 2 + t ^ 2 * (∫ x in Ioi (0 : ℝ), x * P.k x)
      = t ^ 2 * (2 * P.a + ∫ x in Ioi (0 : ℝ), x * P.k x) by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hω' : ω ≠ 0 := hω
  rw [exponent_eq_add_integral P (t * ω)]
  field_simp

/-- The exponent vanishes at the origin in the limit, being the second difference times
`ω²/2`. -/
theorem tendsto_exponent_zero (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤)
    (t : ℝ) :
    Tendsto (fun ω : ℝ => P.exponent (t * ω)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hq := tendsto_exponent_div P hfin t
  have hs : Tendsto (fun ω : ℝ => ω ^ 2 / 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous fun ω : ℝ => ω ^ 2 / 2 := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := hq.mul hs
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hω' : ω ≠ 0 := hω
  field_simp

/-- **The second difference of the transform, computed on the exponent side.**

`y e^{-y} ≤ 1 - e^{-y} ≤ y` squeezes `2ω⁻²(1 - e^{-F(tω)})` between two families with the same
limit. -/
theorem tendsto_one_sub_exp_div
    (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤) (t : ℝ) :
    Tendsto (fun ω : ℝ => (1 - Real.exp (-(P.exponent (t * ω)))) * (2 / ω ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (t ^ 2 * (2 * P.a + ∫ x in Ioi (0 : ℝ), x * P.k x))) := by
  have hq := tendsto_exponent_div P hfin t
  have hE0 := tendsto_exponent_zero P hfin t
  have hnegE : Tendsto (fun ω : ℝ => -(P.exponent (t * ω))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using hE0.neg
  have hexp : Tendsto (fun ω : ℝ => Real.exp (-(P.exponent (t * ω)))) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hnegE
  have hlow := hq.mul hexp
  rw [mul_one] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ω hω
    have hω' : ω ≠ 0 := hω
    have hs : (0:ℝ) < 2 / ω ^ 2 := by positivity
    have h1 : P.exponent (t * ω) * Real.exp (-(P.exponent (t * ω)))
        ≤ 1 - Real.exp (-(P.exponent (t * ω))) := by
      have hle := Real.add_one_le_exp (P.exponent (t * ω))
      have hE1 : 0 < Real.exp (P.exponent (t * ω)) := Real.exp_pos _
      have hinv : (0:ℝ) ≤ (Real.exp (P.exponent (t * ω)))⁻¹ := (inv_pos.mpr hE1).le
      have hmul := mul_le_mul_of_nonneg_right hle hinv
      rw [mul_inv_cancel₀ hE1.ne'] at hmul
      rw [Real.exp_neg]
      nlinarith [hmul]
    calc P.exponent (t * ω) * (2 / ω ^ 2) * Real.exp (-(P.exponent (t * ω)))
        = (P.exponent (t * ω) * Real.exp (-(P.exponent (t * ω)))) * (2 / ω ^ 2) := by ring
      _ ≤ (1 - Real.exp (-(P.exponent (t * ω)))) * (2 / ω ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hs.le
  · filter_upwards [self_mem_nhdsWithin] with ω hω
    have hω' : ω ≠ 0 := hω
    have hs : (0:ℝ) < 2 / ω ^ 2 := by positivity
    have h2 : 1 - Real.exp (-(P.exponent (t * ω))) ≤ P.exponent (t * ω) := by
      have := Real.add_one_le_exp (-(P.exponent (t * ω)))
      linarith
    exact mul_le_mul_of_nonneg_right h2 hs.le

/-! ## The measure side -/

/-- `1 - cos(ωx)` scaled by a constant is integrable against a finite measure. -/
theorem integrable_one_sub_cos_mul (ν : Measure ℝ) [IsFiniteMeasure ν] (ω c : ℝ) :
    Integrable (fun x : ℝ => (1 - Real.cos (ω * x)) * c) ν := by
  refine Integrable.mono' (integrable_const (2 * |c|)) (by fun_prop) (.of_forall fun x => ?_)
  have h1 : |1 - Real.cos (ω * x)| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [Real.cos_le_one (ω * x)])]
    linarith [Real.neg_one_le_cos (ω * x)]
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg c)

/-- The second difference of a probability measure's cosine transform is the integral of
`1 - cos(ωx)`. -/
theorem one_sub_fourierCos_mul (ν : Measure ℝ) [IsProbabilityMeasure ν] (ω c : ℝ) :
    (1 - fourierCos ν ω) * c = ∫ x, (1 - Real.cos (ω * x)) * c ∂ν := by
  have hcos : Integrable (fun x : ℝ => Real.cos (ω * x)) ν := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) (.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (ω * x)
  have hkey : (∫ x, (1 - Real.cos (ω * x)) ∂ν) = 1 - fourierCos ν ω := by
    rw [integral_sub (integrable_const 1) hcos, fourierCos_apply]
    simp
  rw [integral_mul_const, hkey]

/-- **Fatou at the origin.** If the second difference of the transform converges, the second
moment is at most its limit — *before* any integrability is known. This is what keeps ledger
A13 off the variance clause. -/
theorem lintegral_sq_le_of_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν] {C : ℝ}
    (h : Tendsto (fun ω : ℝ => (1 - fourierCos ν ω) * (2 / ω ^ 2)) (𝓝[≠] (0 : ℝ)) (𝓝 C)) :
    (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂ν) ≤ ENNReal.ofReal C := by
  set w : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹ with hwdef
  have hwpos : ∀ m, 0 < w m := fun m => by positivity
  have hw0 : Tendsto w atTop (𝓝 (0 : ℝ)) := by
    simpa [hwdef, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hwW : Tendsto w atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hw0
      (.of_forall fun m => (hwpos m).ne')
  have h' := h.comp hwW
  set f : ℕ → ℝ → ℝ≥0∞ :=
    fun m x => ENNReal.ofReal ((1 - Real.cos (w m * x)) * (2 / (w m) ^ 2)) with hfdef
  have hmeas : ∀ m, Measurable (f m) := fun m => by fun_prop
  have hnn : ∀ m, ∀ x : ℝ, 0 ≤ (1 - Real.cos (w m * x)) * (2 / (w m) ^ 2) := by
    intro m x
    have h1 : 0 ≤ 1 - Real.cos (w m * x) := by linarith [Real.cos_le_one (w m * x)]
    have h2 : (0:ℝ) < 2 / (w m) ^ 2 := by positivity
    exact mul_nonneg h1 h2.le
  have hint : ∀ m, (∫⁻ x, f m x ∂ν)
      = ENNReal.ofReal ((1 - fourierCos ν (w m)) * (2 / (w m) ^ 2)) := by
    intro m
    rw [one_sub_fourierCos_mul ν (w m) (2 / (w m) ^ 2),
      ofReal_integral_eq_lintegral_ofReal (integrable_one_sub_cos_mul ν _ _)
        (.of_forall (hnn m))]
  have hlim : ∀ x : ℝ, Tendsto (fun m => f m x) atTop (𝓝 (ENNReal.ofReal (x ^ 2))) := by
    intro x
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hid : ∀ m, (1 - Real.cos (w m * x)) * (2 / (w m) ^ 2)
        = x ^ 2 * Real.sinc (x * w m / 2) ^ 2 := by
      intro m
      have h0 := one_sub_cos_mul_two_div x (hwpos m).ne'
      rw [show Real.cos (x * w m) = Real.cos (w m * x) by rw [mul_comm]] at h0
      exact h0
    simp only [hid]
    have hc : Continuous fun u : ℝ => x ^ 2 * Real.sinc (x * u / 2) ^ 2 := by fun_prop
    have := (hc.tendsto 0).comp hw0
    simpa [Function.comp_def] using this
  calc (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂ν)
      = ∫⁻ x, liminf (fun m => f m x) atTop ∂ν :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ x, f m x ∂ν) atTop := lintegral_liminf_le hmeas
    _ = ENNReal.ofReal C := by
        simp only [hint]
        exact ((ENNReal.continuous_ofReal.tendsto C).comp h').liminf_eq

/-! ## `prop:moments-tails`(1), the variance -/

/-- **`prop:moments-tails`(1), the variance.** The mean displacement is `0` and
`E X_t² = t²(2a + ∫₀^∞ x k(x) dx)` whenever the catalogue's first moment is finite.

Statement verbatim from `Skeleton.moments_tails_variance`. Lean core: the moment criterion
(ledger **A13**) is not spent, the finiteness of the second moment being a *conclusion* of the
argument rather than a hypothesis of it. -/
theorem moments_tails_variance (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hsym : ∀ t : ℝ, 0 < t → IsSymmetric (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {t : ℝ} (ht : 0 < t)
    (hfin : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)) ≠ ⊤) :
    (∫ x, x ∂(μ t)) = 0 ∧
      (∫ x, x ^ 2 ∂(μ t))
        = t ^ 2 * (2 * P.a + (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)).toReal) := by
  haveI := hprob t ht
  have hInn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun x : ℝ => x * P.k x :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun x hx => mul_nonneg (le_of_lt hx) (P.k_nonneg x hx))
  have hI : (∫ x in Ioi (0 : ℝ), x * P.k x)
      = (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * P.k x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hInn
      (aemeasurable_id.mul P.aemeasurable_k).aestronglyMeasurable
  have hlim : Tendsto (fun ω : ℝ => (1 - fourierCos (μ t) ω) * (2 / ω ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (t ^ 2 * (2 * P.a + ∫ x in Ioi (0 : ℝ), x * P.k x))) := by
    refine (tendsto_one_sub_exp_div P hfin t).congr fun ω => ?_
    rw [hcos t ω ht]
  have hle := lintegral_sq_le_of_tendsto (μ t) hlim
  have hsqint : Integrable (fun x : ℝ => x ^ 2) (μ t) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x => sq_nonneg x)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have hDCT : Tendsto (fun ω : ℝ => ∫ x, x ^ 2 * Real.sinc (x * ω / 2) ^ 2 ∂(μ t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x, x ^ 2 * 1 ∂(μ t))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => x ^ 2) (.of_forall fun ω => by fun_prop) (.of_forall fun ω => ?_) hsqint
      (.of_forall fun x => ?_)
    · refine .of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (sq_nonneg x) (sinc_sq_le_one _)
    · have hc : Continuous fun ω : ℝ => x ^ 2 * Real.sinc (x * ω / 2) ^ 2 := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := {(0:ℝ)}ᶜ))
      simpa using this
  simp only [mul_one] at hDCT
  have hDCT' : Tendsto (fun ω : ℝ => (1 - fourierCos (μ t) ω) * (2 / ω ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x, x ^ 2 ∂(μ t))) := by
    refine hDCT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω hω
    have hω' : ω ≠ 0 := hω
    rw [one_sub_fourierCos_mul (μ t) ω (2 / ω ^ 2)]
    refine (integral_congr_ae (.of_forall fun x => ?_)).symm
    have h0 := one_sub_cos_mul_two_div x hω'
    rw [show Real.cos (x * ω) = Real.cos (ω * x) by rw [mul_comm]] at h0
    exact h0
  have hvar : (∫ x, x ^ 2 ∂(μ t)) = t ^ 2 * (2 * P.a + ∫ x in Ioi (0 : ℝ), x * P.k x) :=
    tendsto_nhds_unique hDCT' hlim
  have hxint : Integrable (fun x : ℝ => x) (μ t) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsqint) (by fun_prop)
      (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  refine ⟨?_, ?_⟩
  · have hmap : (μ t).map (fun y : ℝ => -y) = μ t := hsym t ht
    have h1 : (∫ x, x ∂((μ t).map (fun y : ℝ => -y))) = ∫ x, (-x) ∂(μ t) :=
      integral_map measurable_neg.aemeasurable (by rw [hmap]; fun_prop)
    rw [hmap, integral_neg] at h1
    linarith
  · rw [hvar, hI]

end SpatialLine
