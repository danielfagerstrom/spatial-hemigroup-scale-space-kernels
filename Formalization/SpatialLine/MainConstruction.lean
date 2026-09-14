/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Construction
import SpatialLine.Dilation
import SpatialLine.SelfDecomposable
import SpatialLine.Interfaces

/-!
# `thm:main-characterization`, the construction direction

Blueprint: `thm:main-characterization` (⇐), `blueprint/src/parts/07-characterization.tex`.

Given an admissible exponent `F ≢ 0` of the form `eq:sd-profile` and any gauge `χ` — an
increasing bijection of `[0,∞)` — the kernels with cosine transform
`e^{-(F(χ(t)ω) - F(χ(s)ω))}` exist and their convolution operators satisfy (A1)–(A8) and (ND).

twin: `Hemigroup.SelfDecomposableExponent.cascadeFamily`.

## The route, and where each clause comes from

* Each increment `F(χ(t)\,\cdot) - F(χ(s)\,\cdot)` is a symmetric Lévy exponent, by
  `sd_increment_isSymLevyExponent` — the (3) ⟹ (1) direction of
  `lem:selfdecomposable-exponents` at `0 < χ(s)`, its dilation form at `χ(s) = 0`, and the zero
  exponent at `s = t = 0`.
* Such an exponent is the exponent of a symmetric probability law: ledger **A3**'s converse
  clause (`fourier_toolbox_levy_converse`, already on the trust boundary) followed by ledger
  **A1** (`fourier_toolbox_bochner_symm`, admitted in `Interfaces.lean`). These are the only
  two axioms the theorem spends.
* (A1)–(A7) then come from `CascadeData` — the transport block of chapter 4 and the `L¹`
  continuity block of chapter 3, assembled generically in `SpatialLine/Construction.lean`.
* (ND) is **not** `prop:strict-positivity`: it needs only that *some* frequency is moved, and
  that is `lem:dilation-invariance` applied to `F(ω) = F(χ(s)χ(t)^{-1}ω)`. See the note at
  `ConstructionData.kernel_ne_dirac`.
* (A8) is the gauge conjugate `S_λ = χ^{-1}(λ χ(·))`, whose three order properties are the
  gauge's own and whose intertwining is the dilation identity read on transforms.

## The gauge is continuous, and that is a theorem, not a hypothesis

(A7) needs `(s,t) ↦ e^{-(F(χ(t)ω) - F(χ(s)ω))}` continuous, hence `χ` continuous on `[0,∞)`.
The statement assumes only that `χ` is a strictly increasing surjection of `[0,∞)`; continuity
follows, because a strictly monotone bijection between linear orders with the order topology is
an order isomorphism and order isomorphisms are continuous
(`ConstructionData.chi_continuousOn`). The blueprint's proof leaves this implicit, which is the
same omission `prop:canonical-gauge`'s surjectivity argument made in the other direction — see
SKELETON.md § 6 — and it costs four lines here rather than a hypothesis.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## From a symmetric Lévy exponent to its law -/

/-- **A symmetric Lévy exponent is the exponent of a symmetric probability law.**

Ledger **A3**'s converse clause followed by ledger **A1**: the first makes `e^{-ψ}` positive
definite, the second turns that into a measure. This is the only place in chapter 7 where a
measure is produced from an exponent, and the two axioms it spends are the two the trust
boundary carries for this chapter. -/
theorem exists_isSymmetric_of_isSymLevyExponent {ψ : ℝ → ℝ} (h : IsSymLevyExponent ψ) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧
      ∀ ω, fourierCos μ ω = Real.exp (-ψ ω) := by
  obtain ⟨P, hP⟩ := h
  have hψ : ψ = P.exponent := funext hP
  have hnd : IsSymNegDef ψ := by
    rw [hψ]; exact fourier_toolbox_levy_converse P
  have hcont : Continuous fun ω => Real.exp (-ψ ω) :=
    Real.continuous_exp.comp hnd.continuous.neg
  have hpd : IsPositiveDefinite fun ω => ((Real.exp (-ψ ω) : ℝ) : ℂ) := by
    have h1 := hnd.exp_posDef 1 one_pos
    simpa using h1
  have hone : Real.exp (-ψ 0) = 1 := by rw [hnd.map_zero]; simp
  obtain ⟨μ, hprob, hsym, hcos⟩ :=
    fourier_toolbox_bochner_symm (fun ω => Real.exp (-ψ ω)) ⟨hcont, hpd, hone⟩
  exact ⟨μ, hprob, hsym, fun ω => by rw [hcos]⟩

/-! ## The data of the construction -/

/-- **The hypotheses of `thm:main-characterization`(⇐)**: an admissible profile and a gauge.

Bundled because a dozen consequences of the three gauge conditions are used, and because the
kernels are then a function of the data rather than of six loose hypotheses. -/
structure ConstructionData where
  /-- The admissible exponent, as its profile. -/
  P : SDProfile
  /-- The gauge: an increasing bijection of `[0,∞)`. -/
  χ : ℝ → ℝ
  chi_zero : χ 0 = 0
  chi_mono : StrictMonoOn χ (Ici 0)
  chi_surj : SurjOn χ (Ici 0) (Ici 0)

namespace ConstructionData

variable (D : ConstructionData)

theorem chi_pos {t : ℝ} (ht : 0 < t) : 0 < D.χ t := by
  have h := D.chi_mono (le_refl (0 : ℝ)) ht.le ht
  rwa [D.chi_zero] at h

theorem chi_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ D.χ t := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, D.chi_zero]
  · exact (D.chi_pos h).le

theorem chi_mapsTo : MapsTo D.χ (Ici (0 : ℝ)) (Ici 0) := fun _ ht => D.chi_nonneg ht

theorem chi_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : D.χ s ≤ D.χ t :=
  (D.chi_mono.monotoneOn) hs (hs.trans hst) hst

/-- **The gauge is continuous on `[0,∞)`**: a strictly monotone surjection between linear orders
carrying the order topology is an order isomorphism, and order isomorphisms are continuous. -/
theorem chi_continuousOn : ContinuousOn D.χ (Ici (0 : ℝ)) := by
  set e : Ici (0 : ℝ) → Ici (0 : ℝ) := fun x => ⟨D.χ x, D.chi_mapsTo x.2⟩ with he
  have hmono : StrictMono e := fun x y hxy => D.chi_mono x.2 y.2 hxy
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨x, hx, hxy⟩ := D.chi_surj y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcont : Continuous e := by
    have := (hmono.orderIsoOfSurjective e hsurj).continuous
    simpa [StrictMono.coe_orderIsoOfSurjective] using this
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp hcont

/-! ## The exponents of the increments -/

/-- The exponent accumulated from scale `s` to scale `t`, in the gauge `χ`. -/
noncomputable def expo (s t ω : ℝ) : ℝ := D.P.exponent (D.χ t * ω) - D.P.exponent (D.χ s * ω)

theorem expo_isSymLevyExponent {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsSymLevyExponent (D.expo s t) :=
  sd_increment_isSymLevyExponent D.P (D.chi_nonneg hs) (D.chi_le hs hst)

@[simp] theorem expo_self (t ω : ℝ) : D.expo t t ω = 0 := by simp [expo]

theorem expo_add {r s t : ℝ} (ω : ℝ) : D.expo r s ω + D.expo s t ω = D.expo r t ω := by
  simp only [expo]; ring

/-! ## The kernels -/

open scoped Classical in
/-- **The kernels of the construction**, defined by their transform and totalised by `δ₀` off
the index set `0 ≤ s ≤ t`. -/
noncomputable def kernel (s t : ℝ) : Measure ℝ :=
  if h : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧
      ∀ ω, fourierCos μ ω = Real.exp (-(D.expo s t ω))
    then h.choose else Measure.dirac 0

theorem kernel_prob (s t : ℝ) : IsProbabilityMeasure (D.kernel s t) := by
  unfold kernel
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

instance instIsProbabilityMeasureKernel (s t : ℝ) : IsProbabilityMeasure (D.kernel s t) :=
  D.kernel_prob s t

theorem kernel_sym (s t : ℝ) : IsSymmetric (D.kernel s t) := by
  unfold kernel
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [IsSymmetric, Measure.map_dirac' measurable_neg, neg_zero]

theorem fourierCos_kernel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (D.kernel s t) ω = Real.exp (-(D.expo s t ω)) := by
  have hex : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧
      ∀ ω, fourierCos μ ω = Real.exp (-(D.expo s t ω)) :=
    exists_isSymmetric_of_isSymLevyExponent (D.expo_isSymLevyExponent hs hst)
  rw [kernel, dif_pos hex]
  exact hex.choose_spec.2.2 ω

theorem charFun_kernel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    charFun (D.kernel s t) ω = ((Real.exp (-(D.expo s t ω)) : ℝ) : ℂ) := by
  rw [charFun_eq_fourierCos_of_symmetric (D.kernel_sym s t), D.fourierCos_kernel hs hst]

/-! ## The axioms at the kernel -/

/-- **(A6), the diagonal.** -/
theorem kernel_self {t : ℝ} (ht : 0 ≤ t) : D.kernel t t = Measure.dirac 0 := by
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [D.charFun_kernel ht le_rfl, charFun_dirac, D.expo_self]
  simp

/-- **(A6), the cascade law.** The exponents telescope, so the transforms multiply. -/
theorem kernel_conv {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    (D.kernel r s) ∗ (D.kernel s t) = D.kernel r t := by
  haveI : IsFiniteMeasure ((D.kernel r s) ∗ (D.kernel s t)) := by
    rw [Measure.conv]; infer_instance
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_conv, D.charFun_kernel hr hrs, D.charFun_kernel (hr.trans hrs) hst,
    D.charFun_kernel hr (hrs.trans hst), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  rw [← D.expo_add (r := r) (s := s) (t := t) ω]
  ring

/-- **(A7)'s hypothesis**: the transform is continuous in the pair of scales.

This is where the continuity of the gauge is spent, and where `F` is read as a continuous
function — which it is because it is a member of `NDₛ` (ledger A3's converse clause, through
`lem:profile-integrability`'s "consequently" clause). -/
theorem cos_continuousOn (ω : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => fourierCos (D.kernel p.1 p.2) ω)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  have hFcont : Continuous D.P.exponent := (profile_integrability_mem D.P).2.continuous
  have h1 : ContinuousOn (fun p : ℝ × ℝ => D.χ p.1) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    D.chi_continuousOn.comp continuousOn_fst fun _ hp => hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ => D.χ p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    D.chi_continuousOn.comp continuousOn_snd fun _ hp => hp.1.trans hp.2
  have hg : ContinuousOn
      (fun p : ℝ × ℝ => Real.exp (-(D.P.exponent (D.χ p.2 * ω) - D.P.exponent (D.χ p.1 * ω))))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg (ContinuousOn.sub ?_ ?_))
    · exact hFcont.comp_continuousOn (h2.mul continuousOn_const)
    · exact hFcont.comp_continuousOn (h1.mul continuousOn_const)
  refine hg.congr fun p hp => ?_
  rw [D.fourierCos_kernel hp.1 hp.2]
  rfl

/-- **(ND) at the kernel.**

Only that *some* frequency is moved is needed, which is strictly weaker than
`prop:strict-positivity`(2) and is why this direction of the main theorem does not depend on
that node. At `s = 0` the gauge kills the lower term and `F ≢ 0` is immediate; for `s > 0`, if
every frequency were fixed then `F(ω) = F(cω)` with `c = χ(s)/χ(t) ∈ (0,1)`, and
`lem:dilation-invariance` forces `F ≡ 0`. -/
theorem kernel_ne_dirac (hne : ∃ ω : ℝ, D.P.exponent ω ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    D.kernel s t ≠ Measure.dirac 0 := by
  intro hdir
  obtain ⟨ω₀, hω₀⟩ := hne
  have hFcont : Continuous D.P.exponent := (profile_integrability_mem D.P).2.continuous
  have ht : 0 < D.χ t := D.chi_pos (lt_of_le_of_lt hs hst)
  -- Every frequency is fixed by the increment.
  have hzero : ∀ ω : ℝ, D.P.exponent (D.χ t * ω) = D.P.exponent (D.χ s * ω) := by
    intro ω
    have h1 : fourierCos (D.kernel s t) ω = 1 := by rw [hdir]; simp
    rw [D.fourierCos_kernel hs hst.le] at h1
    have h2 : -(D.expo s t ω) = 0 := by
      have h3 := congrArg Real.log h1
      rwa [Real.log_exp, Real.log_one] at h3
    have : D.expo s t ω = 0 := by linarith
    simpa [expo, sub_eq_zero] using this
  rcases eq_or_lt_of_le hs with h0 | hspos
  · -- `s = 0`: the lower term is `F(0) = 0`.
    apply hω₀
    have := hzero (ω₀ / D.χ t)
    rwa [← h0, D.chi_zero, zero_mul, D.P.exponent_zero, mul_div_cancel₀ _ ht.ne'] at this
  · -- `0 < s`: the exponent is invariant under a dilation ratio different from 1.
    have hcs : 0 < D.χ s := D.chi_pos hspos
    set c : ℝ := D.χ s / D.χ t with hc
    have hcpos : 0 < c := div_pos hcs ht
    have hcne : c ≠ 1 := by
      have : D.χ s < D.χ t := D.chi_mono hs (hs.trans hst.le) hst
      intro hce
      rw [hc, div_eq_one_iff_eq ht.ne'] at hce
      exact absurd hce this.ne
    have hinv : ∀ ω : ℝ, D.P.exponent ω = D.P.exponent (c * ω) := by
      intro ω
      have := hzero (ω / D.χ t)
      rw [mul_div_cancel₀ _ ht.ne'] at this
      rw [this, hc]
      congr 1
      field_simp
    exact hω₀ (dilation_invariance D.P.exponent hFcont.continuousAt D.P.exponent_zero c hcpos
      hcne hinv ω₀)

/-! ## The gauge conjugate, and (A8) -/

open scoped Classical in
/-- The inverse gauge, by choice from surjectivity. -/
noncomputable def chiInv (y : ℝ) : ℝ :=
  if h : ∃ x, x ∈ Ici (0 : ℝ) ∧ D.χ x = y then h.choose else 0

theorem chiInv_spec {y : ℝ} (hy : 0 ≤ y) : 0 ≤ D.chiInv y ∧ D.χ (D.chiInv y) = y := by
  have hex : ∃ x, x ∈ Ici (0 : ℝ) ∧ D.χ x = y := by
    obtain ⟨x, hx, hxy⟩ := D.chi_surj hy
    exact ⟨x, hx, hxy⟩
  rw [chiInv, dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩

theorem chiInv_chi {x : ℝ} (hx : 0 ≤ x) : D.chiInv (D.χ x) = x := by
  obtain ⟨h1, h2⟩ := D.chiInv_spec (D.chi_nonneg hx)
  exact D.chi_mono.injOn h1 hx h2

/-- **The gauge conjugate `S_λ = χ^{-1}(λ χ(·))`.** -/
noncomputable def gaugeAction (lam t : ℝ) : ℝ := D.chiInv (lam * D.χ t)

theorem gaugeAction_nonneg {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 ≤ D.gaugeAction lam t :=
  (D.chiInv_spec (mul_nonneg hlam.le (D.chi_nonneg ht))).1

theorem chi_gaugeAction {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    D.χ (D.gaugeAction lam t) = lam * D.χ t :=
  (D.chiInv_spec (mul_nonneg hlam.le (D.chi_nonneg ht))).2

theorem gaugeAction_strictMonoOn {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (D.gaugeAction lam) (Ici 0) := by
  intro s hs t ht hst
  have h1 : D.χ (D.gaugeAction lam s) < D.χ (D.gaugeAction lam t) := by
    rw [D.chi_gaugeAction hlam hs, D.chi_gaugeAction hlam ht]
    exact mul_lt_mul_of_pos_left (D.chi_mono hs ht hst) hlam
  rcases lt_or_ge (D.gaugeAction lam s) (D.gaugeAction lam t) with h | hcon
  · exact h
  · exact absurd (D.chi_mono.monotoneOn (D.gaugeAction_nonneg hlam ht)
      (D.gaugeAction_nonneg hlam hs) hcon) (not_le.mpr h1)

theorem gaugeAction_surjOn {lam : ℝ} (hlam : 0 < lam) :
    SurjOn (D.gaugeAction lam) (Ici 0) (Ici 0) := by
  intro u hu
  have hu0 : (0 : ℝ) ≤ u := hu
  set t : ℝ := D.chiInv (lam⁻¹ * D.χ u) with htdef
  have hchi : 0 ≤ lam⁻¹ * D.χ u := mul_nonneg (inv_nonneg.mpr hlam.le) (D.chi_nonneg hu0)
  obtain ⟨ht0, hchit⟩ := D.chiInv_spec hchi
  refine ⟨t, ht0, ?_⟩
  have : lam * D.χ t = D.χ u := by
    rw [hchit, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
  rw [gaugeAction, this, D.chiInv_chi hu0]

/-- **(A8) at the kernel.** -/
theorem kernel_map_const_mul {lam s t : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hst : s ≤ t) :
    (D.kernel s t).map (fun x => lam * x)
      = D.kernel (D.gaugeAction lam s) (D.gaugeAction lam t) := by
  have hSs : 0 ≤ D.gaugeAction lam s := D.gaugeAction_nonneg hlam hs
  have hSst : D.gaugeAction lam s ≤ D.gaugeAction lam t := by
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
    · exact le_of_lt (D.gaugeAction_strictMonoOn hlam hs (hs.trans hst) h)
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_map_const_mul, D.charFun_kernel hs hst, D.charFun_kernel hSs hSst]
  congr 2
  simp only [expo, D.chi_gaugeAction hlam hs, D.chi_gaugeAction hlam (hs.trans hst)]
  ring_nf

/-! ## The family -/

/-- The kernels of the construction, as a `CascadeData`. -/
noncomputable def cascadeData : CascadeData where
  κ := D.kernel
  prob := D.kernel_prob
  sym := D.kernel_sym
  self _ ht := D.kernel_self ht
  conv _ _ _ hr hrs hst := D.kernel_conv hr hrs hst
  cos_continuousOn := D.cos_continuousOn

@[simp] theorem cascadeData_κ : D.cascadeData.κ = D.kernel := rfl

end ConstructionData

/-! ## The node -/

/-- **`thm:main-characterization`, the construction direction (⇐).**

Given an admissible `F ≢ 0` and any gauge `χ`, a family satisfying (A1)–(A8) and (ND) exists
whose kernels are symmetric with transform `e^{-(F(χ(t)ω) - F(χ(s)ω))}`.

The range is `0 ≤ s ≤ t`, including `s = 0`: that case is `F(χ(t)\,\cdot)` itself, which is why
`sd_exponents_three_implies_one`'s range starts at `0 < s` and why
`sd_increment_isSymLevyExponent` exists.

**Spends ledger A1 and A3** and nothing else — A1 through `fourier_toolbox_bochner_symm`, A3
through `fourier_toolbox_levy_converse`, both only to turn an exponent into a law and to know
that `F` is continuous. -/
theorem main_construction (P : SDProfile) (F : ℝ → ℝ) (hF : ∀ ω, F ω = P.exponent ω)
    (hne : ∃ ω : ℝ, F ω ≠ 0) (χ : ℝ → ℝ) (hχ0 : χ 0 = 0) (hχmono : StrictMonoOn χ (Ici 0))
    (hχsurj : SurjOn χ (Ici 0) (Ici 0)) :
    ∃ (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ) (S : ℝ → ℝ → ℝ),
      IsKernelFamily Fam.Φ μ ∧ IsScaleCovariant Fam.Φ (Ioi 0) S ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
        ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
          fourierCos (μ s t) ω = Real.exp (-(F (χ t * ω) - F (χ s * ω))) := by
  set D : ConstructionData := ⟨P, χ, hχ0, hχmono, hχsurj⟩ with hD
  have hneP : ∃ ω : ℝ, D.P.exponent ω ≠ 0 := by
    obtain ⟨ω, hω⟩ := hne
    exact ⟨ω, by rwa [hF ω] at hω⟩
  have hnd : ∀ s t : ℝ, 0 ≤ s → s < t → D.cascadeData.κ s t ≠ Measure.dirac 0 :=
    fun s t hs hst => D.kernel_ne_dirac hneP hs hst
  refine ⟨D.cascadeData.cascadeCore hnd, D.kernel, D.gaugeAction, ?_, ?_, ?_, ?_⟩
  · exact D.cascadeData.isKernelFamily
  · exact D.cascadeData.isScaleCovariant D.gaugeAction
      (fun lam hlam _ ht => D.gaugeAction_nonneg hlam ht)
      (fun lam hlam => D.gaugeAction_strictMonoOn hlam)
      (fun lam hlam => D.gaugeAction_surjOn hlam)
      (fun lam hlam s t hs hst => D.kernel_map_const_mul hlam hs hst)
  · exact fun s t _ _ => D.kernel_sym s t
  · intro s t ω hs hst
    rw [D.fourierCos_kernel hs hst, hF, hF]
    rfl

end SpatialLine
