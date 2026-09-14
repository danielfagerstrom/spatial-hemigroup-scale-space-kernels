/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.SincAverage
import SpatialLine.CosineUniqueness

/-!
# `prop:no-positivity-no-classification`, the example

Blueprint: `blueprint/src/parts/03-axioms.tex`, `prop:no-positivity-no-classification`.

The exponent `F(ω) = ω² + ε ∫ (1 - cos ωx) q(x) dx` of the proposition's example is not of the
form `eq:sd-profile`, whatever the even integrable sign-changing `q` of mean zero and whatever
the nonzero `ε`. The argument is the Cesàro average of `SpatialLine/SincAverage.lean`, read at
two rates:

* at rate `T²` the average forces the Gaussian coefficient of any representing profile to be
  the coefficient `1` of the quadratic term;
* at rate `1` — with the quadratic terms now cancelling — the average of the perturbation tends
  to `∫ q = 0`, so Fatou makes the Lévy measure null;
* what is left is `ε ∫ (1 - cos ωx) q(x) dx = 0` at every frequency, hence, `q` being even with
  `∫ q = 0`, a vanishing cosine transform, hence `q = 0` a.e. by
  `ae_eq_zero_of_even_of_integral_cos_eq_zero` — against the hypothesis that `q` changes sign.

## What writing this down found

* **`hqsupp` is not consumed**, confirming what wave 2 read off the statement: the support
  hypothesis is what puts the article's `q` in the class of Lévy-density candidates, and the
  falsity of admissibility does not use it. It is kept because it is the node's.
* **`hqmean` is consumed exactly once**, at the rate-`1` reading, where it is what makes the
  Cesàro average of the perturbation tend to `0`; the closing uniqueness step derives it again
  from the vanishing cosine transform at `ω = 0`.
* The uniqueness of the *signed* Lévy–Khintchine representation, which wave 2 named as the
  obligation and priced M–L, is **never stated**. The two Cesàro readings identify the Gaussian
  coefficient and the Lévy measure of a representing profile directly, so the only uniqueness
  spent is uniqueness for the cosine transform of an `L¹` function, which the previous wave had
  already proved. That is the difference between the surveyed route and the written one.

Proving campaign, wave 5, chapter 3 (2026-09-10).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-- **`prop:no-positivity-no-classification`, the example.** The exponent
`ω² + ε ∫ (1 - cos ωx) q(x) dx` is not admissible.

`#print axioms` reduces to Lean core: no ledger interface is on this path. -/
theorem no_positivity_example (q : ℝ → ℝ) (hq : Integrable q) (hqeven : ∀ x, q (-x) = q x)
    (hqsupp : ∀ x : ℝ, |x| < 1 → q x = 0) (hqmean : ∫ x, q x = 0)
    (hqneg : ¬ (0 ≤ᵐ[volume] q)) (ε : ℝ) (hε : ε ≠ 0) :
    ¬ IsAdmissibleExponent
      (fun ω => ω ^ 2 + ε * ∫ x, (1 - Real.cos (ω * x)) * q x) := by
  rintro ⟨P, hP⟩
  obtain ⟨Q, hQa, hQν, hQe⟩ := profile_integrability_pair P
  haveI hsf : SFinite Q.ν := by rw [hQν]; infer_instance
  set g : ℝ → ℝ := fun ω => ∫ x, (1 - Real.cos (ω * x)) * q x with hg
  have hF : ∀ ω, ω ^ 2 + ε * g ω = Q.exponent ω := fun ω => (hP ω).trans (hQe ω)
  -- the cosine transform of `q`, and the mean-zero rewriting of `g`
  have hqcos : ∀ ω : ℝ, Integrable (fun x : ℝ => Real.cos (ω * x) * q x) volume := by
    intro ω
    refine hq.bdd_mul' (c := 1)
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
  have hgeq : ∀ ω, g ω = -∫ x, Real.cos (ω * x) * q x := by
    intro ω
    have hsplit : ∀ x : ℝ, (1 - Real.cos (ω * x)) * q x = q x - Real.cos (ω * x) * q x :=
      fun x => by ring
    rw [hg]
    simp only [hsplit]
    rw [integral_sub hq (hqcos ω), hqmean, zero_sub]
  -- `g` is continuous, being the exponent minus the quadratic term
  have hgcont : Continuous g := by
    have hgform : g = fun ω => (Q.exponent ω - ω ^ 2) / ε := by
      funext ω
      rw [← hF ω]
      field_simp
      ring
    rw [hgform]
    exact (Q.continuous_exponent.sub (continuous_pow 2)).div_const ε
  -- the Fubini step on the perturbation
  have hA : ∀ T : ℝ, 0 ≤ T →
      ∫ ω in Ioc (0:ℝ) T, g ω = T * ∫ x, (1 - Real.sinc (T * x)) * q x := by
    intro T hT
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) T)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact measure_Ioc_lt_top
    have hqsnd : Integrable (fun p : ℝ × ℝ => q p.2)
        ((volume.restrict (Ioc (0:ℝ) T)).prod volume) := hq.comp_snd _
    have hprod : Integrable (Function.uncurry fun (ω x : ℝ) => (1 - Real.cos (ω * x)) * q x)
        ((volume.restrict (Ioc (0:ℝ) T)).prod volume) := by
      refine ((hq.abs.const_mul 2).comp_snd _).mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable
          (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))).mul
          hqsnd.aestronglyMeasurable
      · filter_upwards with p
        obtain ⟨w, y⟩ := p
        have h1 : |1 - Real.cos (w * y)| ≤ 2 := by
          rw [abs_of_nonneg (by linarith [Real.cos_le_one (w * y)])]
          linarith [Real.neg_one_le_cos (w * y)]
        have h2 : (0:ℝ) ≤ |q y| := abs_nonneg _
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
        nlinarith
    calc ∫ ω in Ioc (0:ℝ) T, g ω
        = ∫ x, (∫ ω in Ioc (0:ℝ) T, (1 - Real.cos (ω * x)) * q x) :=
          integral_integral_swap hprod
      _ = ∫ x, (T * (1 - Real.sinc (T * x))) * q x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [integral_mul_const, ← intervalIntegral.integral_of_le hT,
            intervalIntegral_one_sub_cos]
      _ = T * ∫ x, (1 - Real.sinc (T * x)) * q x := by
          rw [← MeasureTheory.integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- the Cesàro identity of the two sides, divided by `T`
  have hkey : ∀ T : ℝ, 0 < T →
      T ^ 2 / 3 + ε * (∫ x, (1 - Real.sinc (T * x)) * q x)
        = Q.a * T ^ 2 / 3 + ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν := by
    intro T hT
    have h1 : ∫ ω in (0:ℝ)..T, Q.exponent ω
        = Q.a * T ^ 3 / 3 + T * ∫ x, (1 - Real.sinc (T * x)) ∂Q.ν :=
      Q.intervalIntegral_exponent hsf hT.le
    have h2 : ∫ ω in (0:ℝ)..T, Q.exponent ω
        = T ^ 3 / 3 + ε * (T * ∫ x, (1 - Real.sinc (T * x)) * q x) := by
      have hc : ∫ ω in (0:ℝ)..T, Q.exponent ω = ∫ ω in (0:ℝ)..T, (ω ^ 2 + ε * g ω) :=
        intervalIntegral.integral_congr fun ω _ => (hF ω).symm
      have hi1 : IntervalIntegrable (fun ω : ℝ => ω ^ 2) volume 0 T :=
        (continuous_pow 2).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun ω : ℝ => ε * g ω) volume 0 T :=
        (continuous_const.mul hgcont).intervalIntegrable _ _
      rw [hc, intervalIntegral.integral_add hi1 hi2,
        intervalIntegral.integral_const_mul, integral_pow,
        intervalIntegral.integral_of_le hT.le, hA T hT.le]
      norm_num
    have h5 := h2.symm.trans h1
    refine mul_left_cancel₀ hT.ne' ?_
    linear_combination h5
  -- the two dominated convergences
  have hae0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hAtend : Tendsto (fun n : ℕ => ∫ x, (1 - Real.sinc ((n:ℝ) * x)) * q x)
      atTop (𝓝 0) := by
    have hlim := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
      (F := fun (n : ℕ) (x : ℝ) => (1 - Real.sinc ((n:ℝ) * x)) * q x)
      (f := q) (fun x => 2 * |q x|)
      (fun n => ((continuous_const.sub (Real.continuous_sinc.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable).mul
        hq.aestronglyMeasurable)
      (hq.abs.const_mul 2)
      (fun n => Filter.Eventually.of_forall fun x => by
        have h1 : |1 - Real.sinc ((n:ℝ) * x)| ≤ 2 := by
          rw [abs_of_nonneg (one_sub_sinc_nonneg _)]
          exact one_sub_sinc_le_two _
        have h2 : (0:ℝ) ≤ |q x| := abs_nonneg _
        simp only [Real.norm_eq_abs, abs_mul]
        nlinarith)
      (by
        filter_upwards [hae0] with x hx
        have hs := tendsto_sinc_natCast_mul hx
        have h1 : Tendsto (fun n : ℕ => 1 - Real.sinc ((n:ℝ) * x)) atTop (𝓝 1) := by
          simpa using tendsto_const_nhds.sub hs
        simpa using h1.mul_const (q x))
    rwa [hqmean] at hlim
  have hsq : Tendsto (fun n : ℕ => ((n:ℝ) ^ 2)) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n:ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  have hAdiv : Tendsto (fun n : ℕ => (∫ x, (1 - Real.sinc ((n:ℝ) * x)) * q x) / (n:ℝ) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hAtend.mul hinv
  have hDdiv : Tendsto (fun n : ℕ => (∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) / (n:ℝ) ^ 2)
      atTop (𝓝 0) := Q.tendsto_sincDefect_div_sq
  -- step (A): the Gaussian coefficient is the coefficient of the quadratic term
  have hQa1 : Q.a = 1 := by
    have hcomb : Tendsto (fun n : ℕ => (ε * (∫ x, (1 - Real.sinc ((n:ℝ) * x)) * q x)
        - ∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) / (n:ℝ) ^ 2) atTop (𝓝 0) := by
      have h := (hAdiv.const_mul ε).sub hDdiv
      simp only [mul_zero, sub_zero] at h
      exact h.congr fun n => by ring
    have hlim : Tendsto (fun _ : ℕ => Q.a / 3 - 1 / 3) atTop (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ hcomb
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have hne : ((n:ℝ)) ^ 2 ≠ 0 := by positivity
      rw [div_eq_iff hne]
      linear_combination hkey (n:ℝ) hn0
    have hzero := tendsto_nhds_unique tendsto_const_nhds hlim
    linarith
  -- step (C): the Lévy measure is null
  have hD0 : Tendsto (fun n : ℕ => ∫ x, (1 - Real.sinc ((n:ℝ) * x)) ∂Q.ν) atTop (𝓝 0) := by
    have hepsA : Tendsto (fun n : ℕ => ε * ∫ x, (1 - Real.sinc ((n:ℝ) * x)) * q x)
        atTop (𝓝 0) := by simpa using hAtend.const_mul ε
    refine Filter.Tendsto.congr' ?_ hepsA
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hk := hkey (n:ℝ) hn0
    rw [hQa1] at hk
    linarith
  have hnu0 : Q.ν = 0 := Q.eq_zero_of_tendsto_sincDefect hD0
  -- what is left is the vanishing of the cosine transform of `q`
  have hexp : ∀ ω, Q.exponent ω = ω ^ 2 := by
    intro ω
    rw [Q.exponent_eq ω, hnu0, hQa1, integral_zero_measure]
    ring
  have hgz : ∀ ω, g ω = 0 := by
    intro ω
    have hom := hF ω
    rw [hexp ω] at hom
    have hepsg : ε * g ω = 0 := by linarith
    exact (mul_eq_zero.1 hepsg).resolve_left hε
  have hcos0 : ∀ ω : ℝ, ∫ x, Real.cos (ω * x) * q x = 0 := by
    intro ω
    have hom := hgeq ω
    rw [hgz ω] at hom
    linarith
  refine hqneg ?_
  filter_upwards [ae_eq_zero_of_even_of_integral_cos_eq_zero hq hqeven hcos0] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  exact hx.ge

end SpatialLine
