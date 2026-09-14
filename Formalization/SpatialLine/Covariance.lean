/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transmittance

/-!
# `lem:covariance-fourier`: (A8) as an identity of measures and of exponents

Blueprint: `blueprint/src/parts/06-covariance.tex`, `lem:covariance-fourier`.

The compatibility `D_λ(μ * f) = (D_λ μ) * (D_λ f)` turns (A8) into the statement that
`D_λ μ_{s,t}` and `μ_{S_λ s, S_λ t}` represent the same operator, and the uniqueness clause of
`lem:convolution-representation` makes that an identity of measures; the exponent form is
`(D_λ μ)^(ω) = μ̂(λω)` and `-log`.

twin: `Hemigroup.CascadeCore.covariance_laplace`.

## The two narrowings, recorded rather than silently taken

The blueprint states the three-way equivalence under (A1)–(A5), with clause (3) carrying
"whenever the exponents exist", because (A1)–(A5) alone do not give `lem:nonvanishing`. The Lean
statement takes `PreCascadeCore` — which carries (A6)–(A7) — plus a kernel family, and clause
(3) is unconditional; the (A1)–(A5)-only version is not stated because nothing consumes it
(finding **F5**). And the equivalence is stated on the `scale` field of `IsScaleCovariant` with
the three `S`-shape fields as hypotheses, since those are conditions on `S` alone and are shared
by all three clauses.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## Dilation of a measure, against `mconv` -/

/-- **The compatibility of dilation with convolution**, at the level of functions:
`(D_λ ν) * f = D_λ (ν * D_{λ⁻¹} f)`. The measurable-embedding form of `integral_map` is used, so
no measurability of `f` is needed — which matters, because `f` is an `L¹` representative at
every use. -/
lemma mconv_map_mul (ν : Measure ℝ) {lam : ℝ} (hlam : 0 < lam) (f : ℝ → ℝ) (x : ℝ) :
    mconv (ν.map (fun y => lam * y)) f x = dilate lam (mconv ν (dilate lam⁻¹ f)) x := by
  rw [mconv_apply, (measurableEmbedding_mulLeft₀ hlam.ne').integral_map]
  simp only [dilate, mconv_apply, inv_inv]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  have hy : lam * (lam⁻¹ * x - y) = x - lam * y := by field_simp
  rw [hy, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

/-- Dilations compose. -/
lemma dilate_dilate (lam κ : ℝ) (f : ℝ → ℝ) :
    dilate lam (dilate κ f) = dilate (lam * κ) f := by
  funext x
  simp only [dilate]
  rw [mul_inv, ← mul_assoc]
  congr 2
  ring

@[simp] lemma dilate_one (f : ℝ → ℝ) : dilate 1 f = f := by
  funext x
  simp [dilate]

/-- `D_{λ⁻¹}` undoes `D_λ`. -/
lemma dilate_inv_dilate {lam : ℝ} (hlam : lam ≠ 0) (f : ℝ → ℝ) :
    dilate lam⁻¹ (dilate lam f) = f := by
  rw [dilate_dilate, inv_mul_cancel₀ hlam, dilate_one]

/-- `D_λ` undoes `D_{λ⁻¹}`. -/
lemma dilate_dilate_inv {lam : ℝ} (hlam : lam ≠ 0) (f : ℝ → ℝ) :
    dilate lam (dilate lam⁻¹ f) = f := by
  rw [dilate_dilate, mul_inv_cancel₀ hlam, dilate_one]

/-- The transform of a dilated measure. -/
lemma fourierCos_map_mul (ν : Measure ℝ) {lam : ℝ} (hlam : lam ≠ 0) (ω : ℝ) :
    fourierCos (ν.map (fun y => lam * y)) ω = fourierCos ν (lam * ω) := by
  rw [fourierCos_apply, fourierCos_apply, (measurableEmbedding_mulLeft₀ hlam).integral_map]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  congr 1
  ring

/-- **An increasing bijection of `[0,∞)` fixes `0`.** Part of the obligation of
`eq:similarity` rather than a hypothesis. -/
lemma IsScaleCovariant.S_zero {Φ : ℝ → ℝ → (X →L[ℝ] X)} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Φ Gs S) {lam : ℝ} (hlam : 0 < lam) (hmem : lam ∈ Gs) :
    S lam 0 = 0 := by
  obtain ⟨u, hu, hSu⟩ := hcov.S_surjOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
  have hu0 : (0:ℝ) ≤ u := hu
  rcases eq_or_lt_of_le hu0 with h | h
  · rw [← h] at hSu; exact hSu
  · exfalso
    have hlt := hcov.S_strictMonoOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0) hu h
    have hnn : (0:ℝ) ≤ S lam 0 := hcov.S_mapsTo lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
    rw [hSu] at hlt
    linarith

/-- **The action moves `(0,∞)` into itself.** -/
lemma IsScaleCovariant.S_pos {Φ : ℝ → ℝ → (X →L[ℝ] X)} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Φ Gs S) {lam : ℝ} (hlam : 0 < lam) (hmem : lam ∈ Gs)
    {t : ℝ} (ht : 0 < t) : 0 < S lam t := by
  have := hcov.S_strictMonoOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
    (le_of_lt ht : t ∈ Ici (0:ℝ)) ht
  rwa [hcov.S_zero hlam hmem] at this

/-! ## `lem:covariance-fourier` -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- (A8) implies the identity of measures. -/
theorem map_mul_kernel_of_covariant (hker : IsKernelFamily Fam.Φ μ) {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Fam.Φ Gs S) {lam : ℝ} (hlam : 0 < lam) (hmem : lam ∈ Gs)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (μ s t).map (fun x => lam * x) = μ (S lam s) (S lam t) := by
  have hS0 : 0 ≤ S lam s := hcov.S_mapsTo lam hlam hmem hs
  have hSle : S lam s ≤ S lam t :=
    (hcov.S_strictMonoOn lam hlam hmem).monotoneOn hs (hs.trans hst) hst
  haveI := hker.isProbability s t hs hst
  haveI := hker.isProbability (S lam s) (S lam t) hS0 hSle
  haveI : IsProbabilityMeasure ((μ s t).map (fun x => lam * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine eq_of_mconv_gaussTest_ae ?_
  -- `D_λ` applied to the test function, pushed through both representations
  set f : X := dilL1 (inv_pos.mpr hlam) gaussL1 with hfdef
  have hcoeF : ((f : X) : ℝ → ℝ) =ᵐ[volume] dilate lam⁻¹ gaussTest :=
    (coeFn_dilL1 _ _).trans (dilate_congr_ae (inv_ne_zero hlam.ne') coeFn_gaussL1_gaussTest)
  have hop := congrArg (fun T : X →L[ℝ] X => T f) (hcov.scale lam hlam hmem s t hs hst)
  simp only [ContinuousLinearMap.comp_apply] at hop
  have hleft : ((dilL1 hlam (Fam.Φ s t f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv ((μ s t).map (fun x => lam * x)) gaussTest := by
    refine (coeFn_dilL1 hlam _).trans ?_
    refine (dilate_congr_ae hlam.ne' ((hker.conv s t hs hst f).trans
      (mconv_congr_ae _ hcoeF))).trans ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [mconv_map_mul (μ s t) hlam gaussTest x]
  have hright : ((Fam.Φ (S lam s) (S lam t) (dilL1 hlam f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv (μ (S lam s) (S lam t)) gaussTest := by
    refine (hker.conv _ _ hS0 hSle _).trans (mconv_congr_ae _ ?_)
    refine (coeFn_dilL1 hlam f).trans ?_
    refine (dilate_congr_ae hlam.ne' hcoeF).trans ?_
    rw [dilate_dilate_inv hlam.ne']
  exact hleft.symm.trans ((by rw [hop] : ((dilL1 hlam (Fam.Φ s t f) : X) : ℝ → ℝ)
    =ᵐ[volume] ((Fam.Φ (S lam s) (S lam t) (dilL1 hlam f) : X) : ℝ → ℝ)).trans hright)

/-- The identity of measures implies (A8). -/
theorem isScaleCovariant_of_map_mul (hker : IsKernelFamily Fam.Φ μ) {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hmapsTo : ∀ lam, 0 < lam → lam ∈ Gs → MapsTo (S lam) (Ici 0) (Ici 0))
    (hmono : ∀ lam, 0 < lam → lam ∈ Gs → StrictMonoOn (S lam) (Ici 0))
    (hsurj : ∀ lam, 0 < lam → lam ∈ Gs → SurjOn (S lam) (Ici 0) (Ici 0))
    (h : ∀ lam, 0 < lam → lam ∈ Gs → ∀ s t, 0 ≤ s → s ≤ t →
      (μ s t).map (fun x => lam * x) = μ (S lam s) (S lam t)) :
    IsScaleCovariant Fam.Φ Gs S := by
  refine ⟨hmapsTo, hmono, hsurj, fun lam hlam hmem s t hs hst => ?_⟩
  have hS0 : 0 ≤ S lam s := hmapsTo lam hlam hmem hs
  have hSle : S lam s ≤ S lam t := (hmono lam hlam hmem).monotoneOn hs (hs.trans hst) hst
  haveI := hker.isProbability s t hs hst
  haveI := hker.isProbability (S lam s) (S lam t) hS0 hSle
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine Lp.ext_iff.mpr ?_
  have hleft : ((dilL1 hlam (Fam.Φ s t f) : X) : ℝ → ℝ)
      =ᵐ[volume] dilate lam (mconv (μ s t) ((f : X) : ℝ → ℝ)) :=
    (coeFn_dilL1 hlam _).trans (dilate_congr_ae hlam.ne' (hker.conv s t hs hst f))
  have hright : ((Fam.Φ (S lam s) (S lam t) (dilL1 hlam f) : X) : ℝ → ℝ)
      =ᵐ[volume] dilate lam (mconv (μ s t) ((f : X) : ℝ → ℝ)) := by
    refine (hker.conv _ _ hS0 hSle _).trans ?_
    refine (mconv_congr_ae _ (coeFn_dilL1 hlam f)).trans ?_
    rw [← h lam hlam hmem s t hs hst]
    refine Filter.Eventually.of_forall fun x => ?_
    rw [mconv_map_mul (μ s t) hlam _ x, dilate_inv_dilate hlam.ne']
  exact hleft.trans hright.symm

/-- The identity of exponents implies the identity of measures. -/
theorem map_mul_kernel_of_exponent (hker : IsKernelFamily Fam.Φ μ) {S : ℝ → ℝ → ℝ}
    {lam : ℝ} (_hlam : 0 < lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hS0 : 0 ≤ S lam s) (hSle : S lam s ≤ S lam t)
    (h : ∀ ω : ℝ, exponent (μ (S lam s) (S lam t)) ω = exponent (μ s t) (lam * ω)) :
    (μ s t).map (fun x => lam * x) = μ (S lam s) (S lam t) := by
  haveI := hker.isProbability s t hs hst
  haveI := hker.isProbability (S lam s) (S lam t) hS0 hSle
  have hfc : ∀ ω : ℝ, fourierCos (μ (S lam s) (S lam t)) ω = fourierCos (μ s t) (lam * ω) := by
    intro ω
    have h1 := kernel_transform_pos hker hS0 hSle ω
    have h2 := kernel_transform_pos hker hs hst (lam * ω)
    have := h ω
    rw [exponent_apply, exponent_apply, neg_inj, Real.log_injOn_pos.eq_iff (by simpa using h1)
      (by simpa using h2)] at this
    exact this
  refine (Measure.ext_of_charFun (funext fun ω => ?_)).symm
  rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker hS0 hSle) ω]
  rw [charFun_map_mul lam ω,
    charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker hs hst) (lam * ω), hfc ω]

/-- **`lem:covariance-fourier`.** (A8) as an identity of measures and as an identity of
exponents.

Class **(a)** — twin `Hemigroup.CascadeCore.covariance_laplace`. -/
theorem covariance_fourier (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (Gs : Set ℝ) (S : ℝ → ℝ → ℝ)
    (hmapsTo : ∀ lam, 0 < lam → lam ∈ Gs → MapsTo (S lam) (Ici 0) (Ici 0))
    (hmono : ∀ lam, 0 < lam → lam ∈ Gs → StrictMonoOn (S lam) (Ici 0))
    (hsurj : ∀ lam, 0 < lam → lam ∈ Gs → SurjOn (S lam) (Ici 0) (Ici 0)) :
    (IsScaleCovariant Fam.Φ Gs S ↔
        ∀ lam, 0 < lam → lam ∈ Gs → ∀ s t, 0 ≤ s → s ≤ t →
          (μ s t).map (fun x => lam * x) = μ (S lam s) (S lam t)) ∧
      (IsScaleCovariant Fam.Φ Gs S ↔
        ∀ lam, 0 < lam → lam ∈ Gs → ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
          exponent (μ (S lam s) (S lam t)) ω = exponent (μ s t) (lam * ω)) := by
  have hmeas : IsScaleCovariant Fam.Φ Gs S ↔
      ∀ lam, 0 < lam → lam ∈ Gs → ∀ s t, 0 ≤ s → s ≤ t →
        (μ s t).map (fun x => lam * x) = μ (S lam s) (S lam t) :=
    ⟨fun hcov lam hlam hmem s t hs hst =>
      map_mul_kernel_of_covariant hker hcov hlam hmem hs hst,
     isScaleCovariant_of_map_mul hker hmapsTo hmono hsurj⟩
  refine ⟨hmeas, ?_⟩
  constructor
  · intro hcov lam hlam hmem s t ω hs hst
    rw [← map_mul_kernel_of_covariant hker hcov hlam hmem hs hst, exponent_apply,
      exponent_apply, fourierCos_map_mul _ hlam.ne']
  · intro h
    refine hmeas.mpr fun lam hlam hmem s t hs hst => ?_
    exact map_mul_kernel_of_exponent hker hlam hs hst (hmapsTo lam hlam hmem hs)
      ((hmono lam hlam hmem).monotoneOn hs (hs.trans hst) hst)
      (fun ω => h lam hlam hmem s t ω hs hst)

/-- **`eq:similarity`**, the accumulated form.

The case `s = 0` of the exponent identity, using `S_λ 0 = 0`, which holds because an increasing
bijection of `[0,∞)` fixes `0` — part of the obligation rather than a hypothesis. -/
theorem covariance_similarity (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ∀ lam t ω : ℝ, 0 < lam → 0 ≤ t →
      exponent (μ 0 (S lam t)) ω = exponent (μ 0 t) (lam * ω) := by
  intro lam t ω hlam ht
  have hS0 : S lam 0 = 0 := hcov.S_zero hlam hlam
  have := ((covariance_fourier Fam μ hker (Ioi 0) S
    (fun lam hlam _ => hcov.S_mapsTo lam hlam hlam)
    (fun lam hlam _ => hcov.S_strictMonoOn lam hlam hlam)
    (fun lam hlam _ => hcov.S_surjOn lam hlam hlam)).2.mp hcov) lam hlam hlam 0 t ω le_rfl ht
  rwa [hS0] at this

end SpatialLine
