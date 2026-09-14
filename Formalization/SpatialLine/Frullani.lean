/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ProfileIntegrability

/-!
# The elementary integral behind the Matérn and Thorin exponents

Blueprint: `prop:matern-exponent`(1) and the Tonelli step of `prop:thorin-subclass`((1) ⟹ (2)).
Both rest on one identity,
`∫₀^∞ (1 - cos ωx) e^{-px} x⁻¹ dx = ½ log(1 + ω²/p²)`  (`p > 0`),
which the blueprint obtains by differentiating in `ω` under the integral sign. That is the route
taken here, and it is the spatial twin of Paper I's `ClosedForms.lean`, where the causal
`∫₀^∞ (1 - e^{-st}) e^{-t} t⁻¹ dt = log(1+s)` is proved the same way rather than by quoting
Frullani.

## Why the derivative and not Frullani

Frullani's integral is not in Mathlib, and neither is the cosine variant. What *is* available is
the parametric-derivative theorem `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, and the
dominating function it needs is `e^{-px}` itself: differentiating the integrand in `ω` cancels
the `x⁻¹` exactly, leaving `sin(ωx)e^{-px}`, whose modulus is bounded by `e^{-px}` **uniformly
in `ω`**. So the domination is global, no local ball is needed, and the two sides are then
matched by `is_const_of_deriv_eq_zero` at the common value `0` at `ω = 0`.

The evaluated derivative `∫₀^∞ sin(ωx)e^{-px}dx = ω/(p²+ω²)` is the imaginary part of Mathlib's
`integral_exp_mul_complex_Ioi` at `a = -p + iω`; that is the only place a complex number enters.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The evaluated derivative -/

/-- `∫₀^∞ e^{-px} sin(ωx) dx = ω/(p²+ω²)`, the imaginary part of the exponential integral at
`a = -p + iω`. -/
theorem integral_sin_mul_exp_neg_Ioi {p : ℝ} (hp : 0 < p) (ω : ℝ) :
    ∫ x in Ioi (0:ℝ), Real.exp (-(p * x)) * Real.sin (ω * x) = ω / (p ^ 2 + ω ^ 2) := by
  set a : ℂ := ⟨-p, ω⟩ with ha_def
  have ha : a.re < 0 := by simpa [ha_def] using hp
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have h := integral_exp_mul_complex_Ioi ha 0
  have him := congrArg Complex.im h
  rw [← RCLike.im_to_complex, ← integral_im hint] at him
  simp only [RCLike.im_to_complex] at him
  have hpt : ∀ x : ℝ, (Complex.exp (a * x)).im = Real.exp (-(p * x)) * Real.sin (ω * x) := by
    intro x
    rw [Complex.exp_im]
    congr 1 <;> simp [ha_def, Complex.mul_re, Complex.mul_im]
  simp only [hpt] at him
  rw [him]
  have hne : a ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  simp [Complex.div_im, Complex.normSq_apply, ha_def]
  ring

/-! ## Integrability of the integrand and of its dominating functions -/

/-- `x e^{-px}` is integrable on `(0,∞)`. -/
theorem integrableOn_id_mul_exp_neg {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(p * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := p)
    (by norm_num) le_rfl hp
  simpa [Real.rpow_one, neg_mul] using h

/-- `e^{-px}` is integrable on `(0,∞)`. -/
theorem integrableOn_exp_neg_Ioi_zero {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Real.exp (-(p * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := p)
    (by norm_num) le_rfl hp
  simpa [Real.rpow_one, Real.rpow_zero, neg_mul] using h

/-- The integrand of the identity is measurable; it is not continuous at the origin, the `x⁻¹`
being there. -/
theorem measurable_frullani (p ω : ℝ) :
    Measurable (fun x : ℝ => (1 - Real.cos (ω * x)) * Real.exp (-(p * x)) / x) := by
  fun_prop

/-- The integrand is integrable on `(0,∞)`: `1 - cos ωx ≤ (ωx)²/2` cancels the `x⁻¹` and leaves
`x e^{-px}`. -/
theorem integrableOn_frullani {p : ℝ} (hp : 0 < p) (ω : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (ω * x)) * Real.exp (-(p * x)) / x) (Ioi 0) := by
  refine Integrable.mono' (g := fun x : ℝ => ω ^ 2 / 2 * (x * Real.exp (-(p * x))))
    ((integrableOn_id_mul_exp_neg hp).const_mul _)
    (measurable_frullani p ω).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  have hub : 1 - Real.cos (ω * x) ≤ (ω * x) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := ω * x)]
  have hexp : (0:ℝ) < Real.exp (-(p * x)) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hx0]
  calc (1 - Real.cos (ω * x)) * Real.exp (-(p * x))
      ≤ ((ω * x) ^ 2 / 2) * Real.exp (-(p * x)) := by nlinarith
    _ = ω ^ 2 / 2 * (x * Real.exp (-(p * x))) * x := by ring

/-! ## The identity -/

/-- The parametric derivative: differentiating in `ω` cancels the `x⁻¹`, and the dominating
function `e^{-px}` works for every `ω` at once. -/
theorem hasDerivAt_frullani {p : ℝ} (hp : 0 < p) (ω : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∫ x in Ioi (0:ℝ), (1 - Real.cos (y * x)) * Real.exp (-(p * x)) / x)
      (ω / (p ^ 2 + ω ^ 2)) ω := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun y x => (1 - Real.cos (y * x)) * Real.exp (-(p * x)) / x)
    (F' := fun y x => Real.exp (-(p * x)) * Real.sin (y * x))
    (x₀ := ω) (s := Set.univ) (bound := fun x => Real.exp (-(p * x)))
    Filter.univ_mem
    (.of_forall fun y => (measurable_frullani p y).aestronglyMeasurable)
    (integrableOn_frullani hp ω)
    (by fun_prop)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x _ y _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [Real.abs_sin_le_one (y * x), Real.exp_pos (-(p * x)),
        abs_nonneg (Real.sin (y * x))]))
    (integrableOn_exp_neg_Ioi_zero hp)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx y _ => by
      have hx0 : (0:ℝ) < x := hx
      have h1 : HasDerivAt (fun z : ℝ => z * x) x y := by
        simpa using (hasDerivAt_id y).mul_const x
      have h2 : HasDerivAt (fun z : ℝ => Real.cos (z * x)) (-Real.sin (y * x) * x) y := by
        simpa [Function.comp_def] using (Real.hasDerivAt_cos (y * x)).comp y h1
      have h3 : HasDerivAt (fun z : ℝ => 1 - Real.cos (z * x)) (Real.sin (y * x) * x) y := by
        simpa using h2.const_sub 1
      have h4 := (h3.mul_const (Real.exp (-(p * x)))).div_const x
      have heq : Real.sin (y * x) * x * Real.exp (-(p * x)) / x
          = Real.exp (-(p * x)) * Real.sin (y * x) := by
        field_simp
      rw [heq] at h4
      exact h4))
  rw [← integral_sin_mul_exp_neg_Ioi hp ω]
  exact key.2

/-- The derivative of the right-hand side. -/
theorem hasDerivAt_half_log {p : ℝ} (hp : 0 < p) (y : ℝ) :
    HasDerivAt (fun z : ℝ => 1 / 2 * Real.log (1 + z ^ 2 / p ^ 2)) (y / (p ^ 2 + y ^ 2)) y := by
  have hupos : (0:ℝ) < 1 + y ^ 2 / p ^ 2 := by positivity
  have hu : HasDerivAt (fun z : ℝ => 1 + z ^ 2 / p ^ 2) (2 * y / p ^ 2) y := by
    simpa using ((hasDerivAt_pow 2 y).div_const (p ^ 2)).const_add (1 : ℝ)
  have hlog := hu.log hupos.ne'
  have h := hlog.const_mul (1 / 2 : ℝ)
  have hval : 1 / 2 * (2 * y / p ^ 2 / (1 + y ^ 2 / p ^ 2)) = y / (p ^ 2 + y ^ 2) := by
    have hp2 : (p : ℝ) ^ 2 ≠ 0 := by positivity
    have hd : (1 : ℝ) + y ^ 2 / p ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hval] at h
  exact h

/-- **The identity.** `∫₀^∞ (1 - cos ωx) e^{-px} x⁻¹ dx = ½ log(1 + ω²/p²)`.

Both sides have derivative `ω/(p²+ω²)` on all of `ℝ` and both vanish at `ω = 0`. -/
theorem integral_frullani {p : ℝ} (hp : 0 < p) (ω : ℝ) :
    (∫ x in Ioi (0:ℝ), (1 - Real.cos (ω * x)) * Real.exp (-(p * x)) / x)
      = 1 / 2 * Real.log (1 + ω ^ 2 / p ^ 2) := by
  set G : ℝ → ℝ := fun y => ∫ x in Ioi (0:ℝ), (1 - Real.cos (y * x)) * Real.exp (-(p * x)) / x
    with hGdef
  set H : ℝ → ℝ := fun y => 1 / 2 * Real.log (1 + y ^ 2 / p ^ 2) with hHdef
  have hG : ∀ y, HasDerivAt G (y / (p ^ 2 + y ^ 2)) y := hasDerivAt_frullani hp
  have hH : ∀ y, HasDerivAt H (y / (p ^ 2 + y ^ 2)) y := hasDerivAt_half_log hp
  have hconst : ∀ y : ℝ, (G - H) y = (G - H) 0 := by
    refine fun y => is_const_of_deriv_eq_zero (f := G - H) ?_ ?_ y 0
    · exact fun z => ((hG z).sub (hH z)).differentiableAt
    · exact fun z => ((hG z).sub (hH z)).deriv.trans (by ring)
  have h0 : G 0 = 0 := by simp [hGdef]
  have hH0 : H 0 = 0 := by simp [hHdef]
  have hc := hconst ω
  simp only [Pi.sub_apply, h0, hH0, sub_zero] at hc
  show G ω = H ω
  linarith [hc]

end SpatialLine
