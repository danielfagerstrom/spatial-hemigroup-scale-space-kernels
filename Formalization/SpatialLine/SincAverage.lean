/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.AdmissibleCone
import SpatialLine.ExponentContinuity
import SpatialLine.Truncation

/-!
# The Cesàro average of a Lévy exponent, and what its two limits see

Blueprint: `prop:no-positivity-no-classification` (`blueprint/src/parts/03-axioms.tex`), steps
(A)–(C) of `no_positivity_example`.

The one identity this file exists for is

`(1/T) ∫₀^T ψ(ω) dω = a T²/3 + ∫ (1 - sinc(Tx)) ν(dx)`,

for `ψ` the symmetric Lévy exponent `eq:levy-khintchine` of a pair `(a, ν)`. It is Tonelli and
the elementary primitive `∫₀^T (1 - cos ωx) dω = T (1 - sinc(Tx))`, and it is the whole content
of the chapter-3 negative result: the two sides are read at two different rates, `T²` and `1`,
and the two readings give the Gaussian coefficient and the total mass of the Lévy measure.

Both readings are one dominated convergence against the Lévy condition `∫ (1 ∧ x²) ν < ∞`:

* `tendsto_sincDefect_div_sq` — `T⁻² ∫ (1 - sinc(Tx)) ν(dx) → 0`, because `1 - sinc u ≤ u²/6`
  near the origin and `≤ 2` beyond it, so the integrand is `o(T²)` pointwise and dominated by
  `2 (1 ∧ x²)`. This is what makes the `T²/3` terms on the two sides comparable.
* `eq_zero_of_tendsto_sincDefect` — if `∫ (1 - sinc(Tx)) ν(dx) → 0` along the integers then
  `ν = 0`. This is **Fatou**, not dominated convergence: `1 - sinc(nx) → 1` for every `x ≠ 0`,
  so the liminf of the integrands is `1` off the origin, and a folded measure gives the origin
  no mass.

## What writing this down found

The route recorded in `Skeleton/Chapter3.lean` after wave 3 had three steps (A), (B),
(C): fix the Gaussian coefficient, prove the Lévy measure *finite* by a sinc lower bound on a
tail, then let `T → ∞` in Cesàro form. **Step (B) is not needed.** Fatou asks nothing of the
measure's finiteness -- it bounds `ν(ℝ)` by the liminf of integrals that are already known
finite for each `T` -- so the tail estimate `1 - sinc u ≥ 1/2 for u ≥ 2` and the monotone
exhaustion it feeds never have to be written. What remains is (A) and (C), and (C) is three
lines given Fatou. The saving is real: the finiteness step was the one that needed a uniform
bound on the right-hand side, and with it goes the only place the example's constant `ε` would
have had to be tracked quantitatively.

Proving campaign, wave 5, chapter 3 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-! ## Elementary bounds on the sinc defect -/

/-- `1 - sinc u ≥ 0`. -/
theorem one_sub_sinc_nonneg (u : ℝ) : 0 ≤ 1 - Real.sinc u := by
  linarith [Real.sinc_le_one u]

/-- `1 - sinc u ≤ 2`. -/
theorem one_sub_sinc_le_two (u : ℝ) : 1 - Real.sinc u ≤ 2 := by
  linarith [Real.neg_one_le_sinc u]

/-- **`1 - sinc u ≤ u²/6`.** The primitive `u - sin u = ∫₀^u (1 - cos v) dv` of
`SpatialLine/Truncation.lean` against `1 - cos v ≤ v²/2`; the constant is sharp and is the one
the `T²` reading of the Cesàro identity needs to be `o(1)`. -/
theorem one_sub_sinc_le_sq (u : ℝ) : 1 - Real.sinc u ≤ u ^ 2 / 6 := by
  have key : ∀ v : ℝ, 0 < v → 1 - Real.sinc v ≤ v ^ 2 / 6 := by
    intro v hv
    have hup : v - Real.sin v ≤ v ^ 3 / 6 := by
      rw [sub_sin_eq_intervalIntegral v]
      have hmono : ∫ w in (0:ℝ)..v, (1 - Real.cos w) ≤ ∫ w in (0:ℝ)..v, w ^ 2 / 2 := by
        refine intervalIntegral.integral_mono_on hv.le
          (IntervalIntegrable.sub intervalIntegrable_const
            intervalIntegral.intervalIntegrable_cos)
          ((intervalIntegral.intervalIntegrable_pow 2).div_const _) fun w _ => ?_
        linarith [Real.one_sub_sq_div_two_le_cos (x := w)]
      refine le_trans hmono (le_of_eq ?_)
      rw [intervalIntegral.integral_div, integral_pow]
      norm_num
      ring
    rw [Real.sinc_of_ne_zero hv.ne',
      show 1 - Real.sin v / v = (v - Real.sin v) / v by field_simp]
    rw [div_le_iff₀ hv]
    nlinarith
  rcases lt_trichotomy u 0 with h | h | h
  · have := key (-u) (by linarith)
    rwa [Real.sinc_neg, neg_pow, show ((-1:ℝ)) ^ 2 = 1 by norm_num, one_mul] at this
  · simp [h]
  · exact key u h

/-- **The truncation bound for the sinc defect**, in the shape `one_sub_cos_mul_le` has it for
the cosine defect: `1 - sinc(Tx) ≤ 2 (1 ∨ T²) (1 ∧ x²)`. -/
theorem one_sub_sinc_mul_le (T x : ℝ) :
    1 - Real.sinc (T * x) ≤ 2 * max 1 (T ^ 2) * min 1 (x ^ 2) := by
  have hq : 1 - Real.sinc (T * x) ≤ (T * x) ^ 2 / 6 := one_sub_sinc_le_sq (T * x)
  have hb : 1 - Real.sinc (T * x) ≤ 2 := one_sub_sinc_le_two (T * x)
  have hmax : T ^ 2 ≤ max 1 (T ^ 2) := le_max_right _ _
  have hmax1 : (1 : ℝ) ≤ max 1 (T ^ 2) := le_max_left _ _
  rcases le_total (x ^ 2) 1 with h | h
  · rw [min_eq_right h]
    nlinarith [sq_nonneg x, sq_nonneg T]
  · rw [min_eq_left h]
    nlinarith

/-! ## The primitive -/

/-- **`∫₀^T (1 - cos ωx) dω = T (1 - sinc(Tx))`.** The identity the Cesàro average rests on;
`x = 0` and `T = 0` are the two degenerate cases and both sides vanish at each. -/
theorem intervalIntegral_one_sub_cos (x T : ℝ) :
    ∫ ω in (0:ℝ)..T, (1 - Real.cos (ω * x)) = T * (1 - Real.sinc (T * x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne T 0 with rfl | hT
  · simp
  have hcos : ∫ ω in (0:ℝ)..T, Real.cos (ω * x) = x⁻¹ * (Real.sin (T * x)) := by
    rw [intervalIntegral.integral_comp_mul_right Real.cos hx, integral_cos]
    simp
  have hint : IntervalIntegrable (fun w : ℝ => Real.cos (w * x)) volume 0 T :=
    (by fun_prop : Continuous fun w : ℝ => Real.cos (w * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint, hcos, Real.sinc_of_ne_zero (mul_ne_zero hT hx)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at *
  field_simp
  ring

/-- **`sinc(nx) → 0` along the integers**, for every `x ≠ 0`: `|sinc u| ≤ |u|⁻¹`. Used twice —
by the Fatou step below and by the chapter-3 example's own dominated convergence. -/
theorem tendsto_sinc_natCast_mul {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => Real.sinc ((n:ℝ) * x)) atTop (𝓝 0) := by
  have hx' : (0:ℝ) < |x| := abs_pos.2 hx
  have hbound : Tendsto (fun n : ℕ => |((n:ℝ) * x)|⁻¹) atTop (𝓝 0) := by
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    have habs : ∀ n : ℕ, |((n:ℝ) * x)| = (n:ℝ) * |x| := fun n => by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    simpa [habs] using tendsto_natCast_atTop_atTop.atTop_mul_const hx'
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn0 : ((n:ℝ)) ≠ 0 := by positivity
  have hz : ((n:ℝ) * x) ≠ 0 := mul_ne_zero hn0 hx
  have hle : |Real.sin ((n:ℝ) * x)| * |(n:ℝ) * x|⁻¹ ≤ 1 * |(n:ℝ) * x|⁻¹ :=
    mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (inv_nonneg.2 (abs_nonneg _))
  rw [Real.norm_eq_abs, Real.sinc_of_ne_zero hz, abs_div, div_eq_mul_inv]
  linarith [hle]

/-! ## Integrability against a Lévy measure -/

namespace SymLevyPair

/-- The truncation `1 ∧ x²` is integrable against the Lévy measure: this is the Lévy condition
`ν_integrable`, read as a Bochner statement. -/
theorem integrable_min_one_sq (Q : SymLevyPair) :
    Integrable (fun x : ℝ => min 1 (x ^ 2)) Q.ν := by
  refine ⟨(measurable_const.min (measurable_id.pow_const 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one
    (sq_nonneg x))]
  exact lt_top_iff_ne_top.2 Q.ν_integrable

/-- The cosine defect is integrable against the Lévy measure. -/
theorem integrable_one_sub_cos (Q : SymLevyPair) (ω : ℝ) :
    Integrable (fun x : ℝ => 1 - Real.cos (ω * x)) Q.ν := by
  refine (Q.integrable_min_one_sq.const_mul (2 * max 1 (ω ^ 2))).mono'
    ((continuous_const.sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x : ℝ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.cos_le_one (ω * x)])]
  exact one_sub_cos_mul_le (le_refl |ω|) |>.trans_eq (by rw [sq_abs])

/-- The sinc defect is integrable against the Lévy measure. -/
theorem integrable_one_sub_sinc (Q : SymLevyPair) (T : ℝ) :
    Integrable (fun x : ℝ => 1 - Real.sinc (T * x)) Q.ν := by
  refine (Q.integrable_min_one_sq.const_mul (2 * max 1 (T ^ 2))).mono'
    ((continuous_const.sub
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_sinc_nonneg _)]
  exact one_sub_sinc_mul_le T x

/-- The sinc defect has nonnegative integral. -/
theorem integral_one_sub_sinc_nonneg (Q : SymLevyPair) (T : ℝ) :
    0 ≤ ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν :=
  integral_nonneg fun _ => one_sub_sinc_nonneg _

/-- **`eq:levy-khintchine` in real form.** The `.toReal` of the definition is the sum the
display writes, `lem:quadratic-growth` being what makes both summands finite. -/
theorem exponent_eq (Q : SymLevyPair) (ω : ℝ) :
    Q.exponent ω = Q.a * ω ^ 2 + ∫ x, (1 - Real.cos (ω * x)) ∂Q.ν := by
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[Q.ν] fun x : ℝ => 1 - Real.cos (ω * x) :=
    Filter.Eventually.of_forall fun x => by
      simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * x)]
  have hnn' : (0:ℝ) ≤ ∫ x, (1 - Real.cos (ω * x)) ∂Q.ν :=
    integral_nonneg fun x => by
      simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * x)]
  have haω : (0:ℝ) ≤ Q.a * ω ^ 2 := mul_nonneg Q.a_nonneg (sq_nonneg ω)
  have hL : Q.exponentL ω
      = ENNReal.ofReal (Q.a * ω ^ 2 + ∫ x, (1 - Real.cos (ω * x)) ∂Q.ν) := by
    rw [ENNReal.ofReal_add haω hnn', SymLevyPair.exponentL,
      ofReal_integral_eq_lintegral_ofReal (Q.integrable_one_sub_cos ω) hnn]
  rw [SymLevyPair.exponent, hL, ENNReal.toReal_ofReal (by linarith)]

/-! ## The Cesàro identity -/

/-- **The Cesàro average of a symmetric Lévy exponent.**

`∫₀^T ψ(ω) dω = a T³/3 + T ∫ (1 - sinc(Tx)) ν(dx)`: Tonelli against the primitive
`intervalIntegral_one_sub_cos`. The `σ`-finiteness of `ν` is a hypothesis rather than a field —
a Lévy measure is `σ`-finite, but the only instance this article feeds the lemma is a profile
measure, which carries `SFinite` by construction. -/
theorem intervalIntegral_exponent (Q : SymLevyPair) (hsf : SFinite Q.ν) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω in (0:ℝ)..T, Q.exponent ω
      = Q.a * T ^ 3 / 3 + T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν := by
  haveI := hsf
  have hcosnn : ∀ ω : ℝ, (0 : ℝ → ℝ) ≤ᵐ[Q.ν] fun x : ℝ => 1 - Real.cos (ω * x) := fun ω =>
    Filter.Eventually.of_forall fun x => by
      simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * x)]
  set G : ℝ → ℝ := fun ω => ∫ x, (1 - Real.cos (ω * x)) ∂Q.ν with hG
  have hGcont : Continuous G := by
    have : G = fun ω => Q.exponent ω - Q.a * ω ^ 2 := by
      funext ω; rw [hG, Q.exponent_eq ω]; ring
    rw [this]
    exact Q.continuous_exponent.sub (continuous_const.mul (continuous_pow 2))
  have hGnn : ∀ ω, 0 ≤ G ω := fun ω =>
    integral_nonneg fun x => by
      simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * x)]
  -- the Fubini step, in `ℝ≥0∞`
  have hswap : ∫ ω in (0:ℝ)..T, G ω = T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν := by
    have hmeas : AEMeasurable (Function.uncurry fun (ω x : ℝ) =>
        ENNReal.ofReal (1 - Real.cos (ω * x)))
        ((volume.restrict (Ioc (0:ℝ) T)).prod Q.ν) := by
      refine Measurable.aemeasurable ?_
      exact (ENNReal.continuous_ofReal.comp (continuous_const.sub
        (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)))).measurable
    have hinner : ∀ x : ℝ, ∫⁻ ω in Ioc (0:ℝ) T, ENNReal.ofReal (1 - Real.cos (ω * x))
        = ENNReal.ofReal (T * (1 - Real.sinc (T * x))) := by
      intro x
      have hi : IntegrableOn (fun ω : ℝ => 1 - Real.cos (ω * x)) (Ioc (0:ℝ) T) volume := by
        refine Continuous.integrableOn_Ioc ?_
        exact continuous_const.sub (Real.continuous_cos.comp (continuous_id.mul continuous_const))
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun ω : ℝ => by
          simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * x)]),
        ← intervalIntegral.integral_of_le hT, intervalIntegral_one_sub_cos]
    have hL : ENNReal.ofReal (∫ ω in Ioc (0:ℝ) T, G ω)
        = ENNReal.ofReal (T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (hGcont.integrableOn_Ioc)
        (Filter.Eventually.of_forall fun ω : ℝ => by
          simp only [Pi.zero_apply]; exact hGnn ω)]
      have hstep : ∀ ω : ℝ, ENNReal.ofReal (G ω)
          = ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂Q.ν := fun ω =>
        ofReal_integral_eq_lintegral_ofReal (Q.integrable_one_sub_cos ω) (hcosnn ω)
      simp only [hstep]
      rw [lintegral_lintegral_swap hmeas]
      simp only [hinner]
      rw [← MeasureTheory.integral_const_mul,
        ofReal_integral_eq_lintegral_ofReal
          ((Q.integrable_one_sub_sinc T).const_mul T)
          (Filter.Eventually.of_forall fun x : ℝ => by
            simp only [Pi.zero_apply]
            exact mul_nonneg hT (one_sub_sinc_nonneg _))]
    have h1 : 0 ≤ ∫ ω in Ioc (0:ℝ) T, G ω := integral_nonneg fun ω => hGnn ω
    have h2 : 0 ≤ T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν :=
      mul_nonneg hT (Q.integral_one_sub_sinc_nonneg T)
    rw [intervalIntegral.integral_of_le hT]
    exact (ENNReal.ofReal_eq_ofReal_iff h1 h2).1 hL
  have hquad : ∫ ω in (0:ℝ)..T, Q.a * ω ^ 2 = Q.a * T ^ 3 / 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  calc ∫ ω in (0:ℝ)..T, Q.exponent ω
      = ∫ ω in (0:ℝ)..T, (Q.a * ω ^ 2 + G ω) := by
        refine intervalIntegral.integral_congr fun ω _ => ?_
        exact Q.exponent_eq ω
    _ = (∫ ω in (0:ℝ)..T, Q.a * ω ^ 2) + ∫ ω in (0:ℝ)..T, G ω :=
        intervalIntegral.integral_add
          ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
          (hGcont.intervalIntegrable _ _)
    _ = Q.a * T ^ 3 / 3 + T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν := by rw [hquad, hswap]

/-! ## The two readings of the identity -/

/-- **The `T²` reading.** `T⁻² ∫ (1 - sinc(Tx)) ν(dx) → 0` along the integers: the integrand is
`≤ 2 (1 ∧ x²)` uniformly and vanishes pointwise, so this is one dominated convergence against
the Lévy condition. It is what makes the Gaussian coefficients on the two sides of the Cesàro
identity comparable. -/
theorem tendsto_sincDefect_div_sq (Q : SymLevyPair) :
    Tendsto (fun n : ℕ => (∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) / (n:ℝ) ^ 2)
      atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun n x => (1 - Real.sinc ((n:ℝ) * x)) / (n:ℝ) ^ 2 with hF
  have hnn : ∀ (n : ℕ) (x : ℝ), 0 ≤ F n x := fun n x =>
    div_nonneg (one_sub_sinc_nonneg _) (sq_nonneg _)
  have hbdd : ∀ (n : ℕ) (x : ℝ), F n x ≤ 2 * min 1 (x ^ 2) := by
    intro n x
    have hmin : (0:ℝ) ≤ min 1 (x ^ 2) := le_min zero_le_one (sq_nonneg x)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [hF] using by positivity
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hmax : max 1 ((n:ℝ) ^ 2) = (n:ℝ) ^ 2 := max_eq_right (by nlinarith)
    have hkey := one_sub_sinc_mul_le ((n:ℝ)) x
    rw [hmax] at hkey
    rw [hF]
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) Q.ν := fun n =>
    ((continuous_const.sub (Real.continuous_sinc.comp
      (continuous_const.mul continuous_id))).div_const _).aestronglyMeasurable
  have hsq : Tendsto (fun n : ℕ => ((n:ℝ) ^ 2)) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hptw : ∀ x : ℝ, Tendsto (fun n : ℕ => F n x) atTop (𝓝 0) := by
    intro x
    refine squeeze_zero (fun n => hnn n x) (fun n => ?_) (hsq.const_div_atTop 2)
    change (1 - Real.sinc ((n:ℝ) * x)) / (n:ℝ) ^ 2 ≤ 2 / (n:ℝ) ^ 2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (one_sub_sinc_le_two _) (by positivity)
  have hconv := tendsto_integral_of_dominated_convergence (μ := Q.ν) (F := F)
    (f := fun _ : ℝ => (0:ℝ)) (fun x => 2 * min 1 (x ^ 2)) hmeas
    (Q.integrable_min_one_sq.const_mul 2)
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn n x)]; exact hbdd n x)
    (Filter.Eventually.of_forall hptw)
  simpa [hF, integral_div] using hconv

/-- **The `1` reading.** A Lévy pair whose sinc defect tends to `0` along the integers has the
zero Lévy measure.

This is **Fatou**, and it is where the wave-3 route's step (B) — proving the measure finite
first — turns out to be unnecessary: `1 - sinc(nx) → 1` for every `x ≠ 0`, a folded measure
gives the origin no mass, so `ν(ℝ)` is bounded by the liminf of quantities that are already
known finite. -/
theorem eq_zero_of_tendsto_sincDefect (Q : SymLevyPair)
    (h : Tendsto (fun n : ℕ => ∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) atTop (𝓝 0)) :
    Q.ν = 0 := by
  -- the origin is null
  have hzero : Q.ν {(0:ℝ)} = 0 := measure_mono_null (by simp) Q.ν_folded
  have hae : ∀ᵐ x ∂Q.ν, x ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  -- the integrands converge to `1` off the origin
  have hptw : ∀ x : ℝ, x ≠ 0 →
      Tendsto (fun n : ℕ => ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x))) atTop (𝓝 1) := by
    intro x hx
    have hs : Tendsto (fun n : ℕ => Real.sinc ((n:ℝ) * x)) atTop (𝓝 0) :=
      tendsto_sinc_natCast_mul hx
    have hlim1 : Tendsto (fun n : ℕ => (1 - Real.sinc ((n:ℝ) * x))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hs
    have hc := (ENNReal.continuous_ofReal.tendsto 1).comp hlim1
    simpa [Function.comp_def] using hc
  -- Fatou
  have hmeasn : ∀ n : ℕ, Measurable fun x : ℝ =>
      ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x)) := fun n =>
    (ENNReal.continuous_ofReal.comp (continuous_const.sub
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id)))).measurable
  have hfatou := lintegral_liminf_le (μ := Q.ν) (u := atTop)
    (f := fun n : ℕ => fun x : ℝ => ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x))) hmeasn
  have hleft : ∫⁻ x, liminf (fun n : ℕ =>
      ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x))) atTop ∂Q.ν = Q.ν univ := by
    rw [← lintegral_one (μ := Q.ν)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact (hptw x hx).liminf_eq
  have hright : liminf (fun n : ℕ => ∫⁻ x,
      ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) atTop = 0 := by
    have hstep : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν
        = ENNReal.ofReal (∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) := fun n =>
      (ofReal_integral_eq_lintegral_ofReal (Q.integrable_one_sub_sinc _)
        (Filter.Eventually.of_forall fun x : ℝ => by
          simp only [Pi.zero_apply]; exact one_sub_sinc_nonneg _)).symm
    simp only [hstep]
    refine Filter.Tendsto.liminf_eq ?_
    have hc := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using hc
  rw [hleft, hright] at hfatou
  exact Measure.measure_univ_eq_zero.1 (le_zero_iff.1 hfatou)

end SymLevyPair

end SpatialLine
