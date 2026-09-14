/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Covariance
import SpatialLine.Dilation

/-!
# `lem:action-rigidity`: the relabellings are unique, compose, are continuous, and move
every point

Blueprint: `blueprint/src/parts/06-covariance.tex`, `lem:action-rigidity`.

Nothing in (A8) says that the relabellings `S_λ` are unique, that they compose, or that they
move every point; this file says all three, and adds continuity in the ratio.

Clauses (1), (2) and (4) are the function-injectivity of the accumulated exponent and port from
`Hemigroup.CascadeCore.action_rigidity`. Clause (3) is the one with a **new proof**: the causal
argument read the action off the accumulated exponent at one fixed value of the transform
variable, which `cor:monotonicity` does not licence here, and what replaces it is the smoothed
transmittance `Θ` of `cor:smoothed-transmittance` — a single strictly monotone number attached
to each scale.

## What proving clause (3) found

The blueprint proof reads "`Θ` is a continuous strict antitone with a continuous inverse on its
image, so `S_λ t = Θ⁻¹(θ_t(λ))` is continuous", and the Lean cost was priced as "the continuous
inverse, not the domination". Written out, **no inverse function is needed at all**: the
order-theoretic characterisation of a limit in `ℝ` (`tendsto_order`) turns the claim into two
one-sided statements, each of which follows from `StrictAntiOn` by contraposition against a
bound that `θ_t`'s own continuity supplies. What the argument uses of `Θ` is exactly
injectivity-with-a-direction, and `Set.invFunOn` never appears. The estimate was right about
which half was expensive but wrong about what the expensive half was: the domination is three
lines, and the "continuous inverse" is not an obligation.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-! ## The similarity relation at the transform -/

/-- `eq:similarity` at the level of the transform rather than the exponent. -/
theorem fourierCos_similarity (hker : IsKernelFamily Fam.Φ μ) {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t)
    (ω : ℝ) : fourierCos (μ 0 (S lam t)) ω = fourierCos (μ 0 t) (lam * ω) := by
  have hmap := map_mul_kernel_of_covariant hker hcov hlam hlam (le_refl (0:ℝ)) ht
  rw [hcov.S_zero hlam hlam] at hmap
  rw [← hmap, fourierCos_map_mul _ hlam.ne']

/-! ## Clauses (1), (2) and (4) -/

/-- **`lem:action-rigidity`(1).** The accumulated exponent determines the scale, and hence `S` is
determined by `eq:similarity`.

"As functions on `ℝ`" is the pointwise-in-`ω` hypothesis; the second half is stated as "any
other `S'` making the family covariant agrees with `S`", which is what "uniquely determined by
`eq:similarity`" means for a bundled action.

Class **(a)** — twin `Hemigroup.CascadeCore.action_rigidity`(1). -/
theorem action_rigidity_injective (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
        (∀ ω, exponent (μ 0 t₁) ω = exponent (μ 0 t₂) ω) → t₁ = t₂) ∧
      (∀ S' : ℝ → ℝ → ℝ, IsScaleCovariant Fam.Φ (Ioi 0) S' →
        ∀ lam t : ℝ, 0 < lam → 0 ≤ t → S lam t = S' lam t) := by
  -- The key half: a vanishing increment is `δ₀`, against (ND).
  have key : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      (∀ ω, exponent (μ 0 t₁) ω = exponent (μ 0 t₂) ω) → t₁ = t₂ := by
    have half : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ →
        (∀ ω, exponent (μ 0 t₁) ω = exponent (μ 0 t₂) ω) → False := by
      intro t₁ t₂ h1 hlt h
      haveI := hker.isProbability t₁ t₂ h1 hlt.le
      refine kernel_ne_dirac hker hnd h1 hlt ?_
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      have hzero : exponent (μ t₁ t₂) ω = 0 := by
        rw [exponent_eq_sub hker h1 hlt.le ω, h ω]
        ring
      have hpos := kernel_transform_pos hker h1 hlt.le ω
      have hlog : Real.log (fourierCos (μ t₁ t₂) ω) = 0 := by
        rw [exponent_apply, neg_eq_zero] at hzero
        exact hzero
      have hone : fourierCos (μ t₁ t₂) ω = 1 := by
        calc fourierCos (μ t₁ t₂) ω = Real.exp (Real.log (fourierCos (μ t₁ t₂) ω)) :=
              (Real.exp_log hpos).symm
          _ = 1 := by rw [hlog, Real.exp_zero]
      rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker h1 hlt.le) ω, hone]
      simp
    intro t₁ t₂ h1 h2 h
    rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
    · exact absurd (half t₁ t₂ h1 hlt h) not_false
    · exact heq
    · exact absurd (half t₂ t₁ h2 hgt fun ω => (h ω).symm) not_false
  refine ⟨key, fun S' hcov' lam t hlam ht => ?_⟩
  refine key _ _ (hcov.S_mapsTo lam hlam hlam ht) (hcov'.S_mapsTo lam hlam hlam ht) fun ω => ?_
  rw [covariance_similarity Fam μ hker S hcov lam t ω hlam ht,
    covariance_similarity Fam μ hker S' hcov' lam t ω hlam ht]

/-- **`lem:action-rigidity`(2).** The action is a group action.

Class **(a)**. -/
theorem action_rigidity_group (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    (∀ lam κ t : ℝ, 0 < lam → 0 < κ → 0 ≤ t → S lam (S κ t) = S (lam * κ) t) ∧
      (∀ t : ℝ, 0 ≤ t → S 1 t = t) := by
  have hinj := (action_rigidity_injective Fam μ hker hnd S hcov).1
  constructor
  · intro lam κ t hlam hκ ht
    have hκt : 0 ≤ S κ t := hcov.S_mapsTo κ hκ hκ ht
    refine hinj _ _ (hcov.S_mapsTo lam hlam hlam hκt)
      (hcov.S_mapsTo (lam * κ) (mul_pos hlam hκ) (mul_pos hlam hκ) ht) fun ω => ?_
    rw [covariance_similarity Fam μ hker S hcov lam (S κ t) ω hlam hκt,
      covariance_similarity Fam μ hker S hcov κ t (lam * ω) hκ ht,
      covariance_similarity Fam μ hker S hcov (lam * κ) t ω (mul_pos hlam hκ) ht]
    ring_nf
  · intro t ht
    have h1 : (1:ℝ) ∈ Ioi (0:ℝ) := by norm_num
    refine hinj _ _ (hcov.S_mapsTo 1 one_pos h1 ht) ht fun ω => ?_
    rw [covariance_similarity Fam μ hker S hcov 1 t ω one_pos ht, one_mul]

/-- **`lem:action-rigidity`(4).** The action has no fixed point in `(0,∞)`, in the strong form:
one `lam ≠ 1` suffices.

Class **(a)** — the iteration is `lem:dilation-invariance`. -/
theorem action_rigidity_no_fixed_point (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ∀ lam t : ℝ, 0 < lam → lam ≠ 1 → 0 ≤ t → S lam t = t → t = 0 := by
  intro lam t hlam hlam1 ht hfix
  have hinj := (action_rigidity_injective Fam μ hker hnd S hcov).1
  have hdil : ∀ ω : ℝ, exponent (μ 0 t) ω = exponent (μ 0 t) (lam * ω) := by
    intro ω
    have := covariance_similarity Fam μ hker S hcov lam t ω hlam ht
    rwa [hfix] at this
  have hvanish : ∀ ω : ℝ, exponent (μ 0 t) ω = 0 :=
    dilation_invariance (exponent (μ 0 t)) (continuous_exponent hker ht).continuousAt
      (exponent_atZero hker ht) lam hlam hlam1 hdil
  refine hinj t 0 ht le_rfl fun ω => ?_
  rw [hvanish ω, exponent_self hker le_rfl ω]

/-! ## Clause (3): continuity in the ratio -/

/-- The smoothed transmittance along the orbit, in its frequency-side form. -/
lemma transmittance_similarity (hker : IsKernelFamily Fam.Φ μ) {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {lam : ℝ} (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, Real.exp (-(x ^ 2) / 2) ∂(μ 0 (S lam t)))
      = ∫ ω, fourierCos (μ 0 t) (lam * ω) * gaussTest ω := by
  haveI := hker.isProbability 0 (S lam t) le_rfl (hcov.S_mapsTo lam hlam hlam ht)
  rw [← integral_fourierCos_mul_gaussTest (μ 0 (S lam t))]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [fourierCos_similarity hker hcov hlam ht ω]

/-- `λ ↦ Θ(S_λ t)` is continuous — dominated convergence with the bound `ρ`. -/
lemma continuous_transmittance_orbit (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun lam : ℝ => ∫ ω, fourierCos (μ 0 t) (lam * ω) * gaussTest ω) := by
  haveI := hker.isProbability 0 t le_rfl ht
  refine continuous_iff_continuousAt.mpr fun lam₀ => ?_
  refine tendsto_integral_filter_of_dominated_convergence gaussTest
    (.of_forall fun lam => ?_) (.of_forall fun lam => ?_) integrable_gaussTest
    (ae_of_all _ fun ω => ?_)
  · exact (((continuous_fourierCos (μ 0 t)).comp (continuous_const.mul continuous_id)).mul
      continuous_gaussTest).aestronglyMeasurable
  · refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussTest_pos ω)]
    exact mul_le_of_le_one_left (gaussTest_pos ω).le (abs_fourierCos_le_one _ _)
  · exact (((continuous_fourierCos (μ 0 t)).comp
      (continuous_id.mul continuous_const)).continuousAt).mul_const _

/-- **`lem:action-rigidity`(3).** The action is continuous in the ratio.

Class (c) — the clause with a new proof; see the module docstring for what writing it down
found. -/
theorem action_rigidity_continuous (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun lam => S lam t) (Ioi 0) := by
  set Θ : ℝ → ℝ := fun u => ∫ x, Real.exp (-(x ^ 2) / 2) ∂(μ 0 u) with hΘdef
  have hanti : StrictAntiOn Θ (Ici 0) := strictAntiOn_transmittance hker hnd
  have hθ : Continuous (fun lam : ℝ => ∫ ω, fourierCos (μ 0 t) (lam * ω) * gaussTest ω) :=
    continuous_transmittance_orbit hker ht.le
  have hval : ∀ lam : ℝ, 0 < lam →
      Θ (S lam t) = ∫ ω, fourierCos (μ 0 t) (lam * ω) * gaussTest ω :=
    fun lam hlam => transmittance_similarity hker hcov hlam ht.le
  intro lam₀ hlam₀
  have hlam₀' : (0:ℝ) < lam₀ := hlam₀
  set θ : ℝ → ℝ := fun lam => ∫ ω, fourierCos (μ 0 t) (lam * ω) * gaussTest ω with hθdef
  have hval' : ∀ lam : ℝ, 0 < lam → θ lam = Θ (S lam t) := fun lam hlam => (hval lam hlam).symm
  have hθ0 : θ lam₀ = Θ (S lam₀ t) := hval' lam₀ hlam₀'
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `a < S_{λ₀} t`: eventually `a < S_λ t`
    rcases lt_or_ge a 0 with hneg | hnn
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact lt_of_lt_of_le hneg (hcov.S_mapsTo lam hlam hlam ht.le)
    · have haS : a < S lam₀ t := ha
      have hstart : θ lam₀ < Θ a := by
        rw [hθ0]
        exact hanti hnn (hcov.S_mapsTo lam₀ hlam₀' hlam₀' ht.le) haS
      have hev : ∀ᶠ lam in 𝓝[Ioi (0:ℝ)] lam₀, θ lam < Θ a :=
        (Filter.Tendsto.eventually_lt_const hstart hθ.continuousAt).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev, self_mem_nhdsWithin] with lam hlt hlam
      by_contra hcon
      rw [not_lt] at hcon
      have hSnn : (0:ℝ) ≤ S lam t := hcov.S_mapsTo lam hlam hlam ht.le
      have hge : Θ a ≤ Θ (S lam t) := by
        rcases eq_or_lt_of_le hcon with h | h
        · rw [h]
        · exact (hanti hSnn hnn h).le
      rw [hval' lam hlam] at hlt
      linarith
  · -- `S_{λ₀} t < b`: eventually `S_λ t < b`
    have hbnn : (0:ℝ) ≤ b := le_of_lt (lt_trans (hcov.S_pos hlam₀' hlam₀' ht) hb)
    have hstart : Θ b < θ lam₀ := by
      rw [hθ0]
      exact hanti (hcov.S_mapsTo lam₀ hlam₀' hlam₀' ht.le) hbnn hb
    have hev : ∀ᶠ lam in 𝓝[Ioi (0:ℝ)] lam₀, Θ b < θ lam :=
      (Filter.Tendsto.eventually_const_lt hstart hθ.continuousAt).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev, self_mem_nhdsWithin] with lam hlt hlam
    by_contra hcon
    rw [not_lt] at hcon
    have hSnn : (0:ℝ) ≤ S lam t := hcov.S_mapsTo lam hlam hlam ht.le
    have hle : Θ (S lam t) ≤ Θ b := by
      rcases eq_or_lt_of_le hcon with h | h
      · rw [h]
      · exact (hanti hbnn hSnn h).le
    rw [hval' lam hlam] at hlt
    linarith

end SpatialLine
