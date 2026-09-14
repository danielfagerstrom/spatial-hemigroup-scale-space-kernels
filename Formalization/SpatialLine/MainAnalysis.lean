/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.GaugeLevy
import SpatialLine.ExponentContinuity
import SpatialLine.MainConstruction
import SpatialLine.AnalysisDirection

/-!
# `thm:main-characterization`, the analysis and uniqueness directions

Blueprint: `thm:main-characterization` (⇒) and its uniqueness clause,
`blueprint/src/parts/07-characterization.tex`.

twin: `Hemigroup.CascadeCore.main_analysis` and
`Hemigroup.SelfDecomposableExponent.gauge_and_exponent_unique`.

## What each direction consumes

The **uniqueness** clause is self-contained and rests on Lean core. Read at `s = 0`, the two
representations give `e^{-F_i(χ_i(t)ω)}` for the same transform, so `F₁ = F₂` at `t = 1` by the
normalisation, and then `F₁(χ₁(t)ω) = F₁(χ₂(t)ω)` for every `ω`; a gauge fixing `0` and
strictly increasing is positive on `(0,∞)`, so the two values differ by a dilation ratio, and
`lem:dilation-invariance` forces `F₁ ≡ 0` unless the ratio is `1`.

The **analysis** direction is assembly: `prop:canonical-gauge` supplies the gauge and the
similarity form, `thm:increments-levy` supplies condition (1) of
`lem:selfdecomposable-exponents` at every pair of canonical scales — surjectivity of the gauge
is what makes "every pair" available — and that lemma's (1) ⟹ (3) leg turns the Lévy pair into
an `SDProfile`. Everything except the last step is proved here, and the last step is taken as a
hypothesis of `main_analysis_of_profileForm`, in exactly the shape
`Skeleton.sd_exponents_one_implies_three` states it. **The assembly waits on that declaration
and on nothing else**: when it is proved and moved, `main_analysis` is
`main_analysis_of_profileForm sd_exponents_one_implies_three`.

## What writing this round down found

Every step of the analysis direction other than the profile form is `[T]` and elementary given
chapters 4–6, so the direction is not "L inherited from its parts" in the sense of new
analysis: it is one deep leg and a page of bookkeeping. The bookkeeping is the passage from a
pair of canonical scales `0 < c ≤ d` back to a pair of the family's own scales, which is
`prop:canonical-gauge`'s surjectivity clause and is the only place in the chapter it is used.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The uniqueness clause -/

/-- **`thm:main-characterization`, uniqueness.** Two normalised representations of the same
kernel family agree: the gauges on `[0,∞)` and the exponents everywhere.

The gauge hypotheses `χ_i 0 = 0` and `StrictMonoOn χ_i (Ici 0)` are the review's R1 — without
them the statement is false, `SDProfile.exponent` being even. Surjectivity is not needed.

`#print axioms` reduces to Lean core: continuity of the exponent is
`SDProfile.continuous_exponent`, proved by dominated convergence rather than through
`prop:fourier-toolbox`(3). -/
theorem main_uniqueness (μ : ℝ → ℝ → Measure ℝ) (χ₁ χ₂ : ℝ → ℝ) (P₁ P₂ : SDProfile)
    (hχ₁ : χ₁ 1 = 1) (hχ₂ : χ₂ 1 = 1)
    (hχ₁0 : χ₁ 0 = 0) (hχ₂0 : χ₂ 0 = 0)
    (hχ₁m : StrictMonoOn χ₁ (Ici 0)) (hχ₂m : StrictMonoOn χ₂ (Ici 0))
    (hne : ∃ ω : ℝ, P₁.exponent ω ≠ 0)
    (h₁ : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω = Real.exp (-(P₁.exponent (χ₁ t * ω) - P₁.exponent (χ₁ s * ω))))
    (h₂ : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω = Real.exp (-(P₂.exponent (χ₂ t * ω) - P₂.exponent (χ₂ s * ω)))) :
    (∀ t : ℝ, 0 ≤ t → χ₁ t = χ₂ t) ∧ ∀ ω : ℝ, P₁.exponent ω = P₂.exponent ω := by
  -- Read at `s = 0`: the two accumulated exponents are the same function of `ω`.
  have key : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, P₁.exponent (χ₁ t * ω) = P₂.exponent (χ₂ t * ω) := by
    intro t ht ω
    have a1 := h₁ 0 t ω le_rfl ht
    have a2 := h₂ 0 t ω le_rfl ht
    rw [hχ₁0, zero_mul, SDProfile.exponent_zero, sub_zero] at a1
    rw [hχ₂0, zero_mul, SDProfile.exponent_zero, sub_zero] at a2
    have h := Real.exp_eq_exp.mp (a1.symm.trans a2)
    linarith
  -- The normalisation `χ_i 1 = 1` identifies the two exponents.
  have hexp : ∀ ω : ℝ, P₁.exponent ω = P₂.exponent ω := by
    intro ω
    have h := key 1 zero_le_one ω
    rwa [hχ₁, hχ₂, one_mul] at h
  refine ⟨?_, hexp⟩
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | htpos
  · rw [← h0, hχ₁0, hχ₂0]
  · -- A gauge fixing `0` and strictly increasing is positive on `(0,∞)`.
    have hc1 : 0 < χ₁ t := by
      have h := hχ₁m Set.self_mem_Ici (le_of_lt htpos : t ∈ Ici (0 : ℝ)) htpos
      rwa [hχ₁0] at h
    have hc2 : 0 < χ₂ t := by
      have h := hχ₂m Set.self_mem_Ici (le_of_lt htpos : t ∈ Ici (0 : ℝ)) htpos
      rwa [hχ₂0] at h
    by_contra hcon
    set c : ℝ := χ₂ t / χ₁ t with hc
    have hcpos : 0 < c := div_pos hc2 hc1
    have hcne : c ≠ 1 := by
      intro hce
      rw [hc, div_eq_one_iff_eq hc1.ne'] at hce
      exact hcon hce.symm
    have hinv : ∀ ω : ℝ, P₁.exponent ω = P₁.exponent (c * ω) := by
      intro ω
      have h := key t ht (ω / χ₁ t)
      rw [mul_div_cancel₀ _ hc1.ne'] at h
      rw [h, ← hexp]
      congr 1
      rw [hc]
      field_simp
    obtain ⟨ω₀, hω₀⟩ := hne
    exact hω₀ (dilation_invariance P₁.exponent P₁.continuous_exponent.continuousAt
      P₁.exponent_zero c hcpos hcne hinv ω₀)

/-! ## The analysis direction -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **The transform is the exponential of minus the exponent**, for a kernel of a family
satisfying (A1)–(A3) and (A5)–(A7): `lem:nonvanishing` is what makes the logarithm
single-valued. -/
theorem fourierCos_eq_exp_neg_exponent (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ω : ℝ) : fourierCos (μ s t) ω = Real.exp (-(exponent (μ s t) ω)) := by
  rw [exponent_apply, neg_neg, Real.exp_log (kernel_transform_pos hker hs hst ω)]

/-- **Condition (1) of `lem:selfdecomposable-exponents` holds at every pair of canonical
scales.** Given the gauge of `prop:canonical-gauge`, the dilate difference `F(dω) - F(cω)` with
`0 ≤ c ≤ d` *is* an increment exponent of the family, because the gauge is onto `[0,∞)`; and
every increment exponent is a symmetric Lévy exponent by `thm:increments-levy`. -/
theorem isSymLevyExponent_dilate_diff (hker : IsKernelFamily Fam.Φ μ) {χ : ℝ → ℝ}
    (hχm : StrictMonoOn χ (Ici 0)) (hχs : SurjOn χ (Ici 0) (Ici 0))
    (hgauge : ∀ t ω : ℝ, 0 ≤ t → exponent (μ 0 t) ω = exponent (μ 0 1) (χ t * ω))
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    IsSymLevyExponent fun ω => exponent (μ 0 1) (d * ω) - exponent (μ 0 1) (c * ω) := by
  obtain ⟨c', hc'mem, hc'⟩ := hχs (hc : c ∈ Ici (0 : ℝ))
  obtain ⟨d', hd'mem, hd'⟩ := hχs (le_trans hc hcd : d ∈ Ici (0 : ℝ))
  have hc'0 : (0 : ℝ) ≤ c' := hc'mem
  have hd'0 : (0 : ℝ) ≤ d' := hd'mem
  have hle : c' ≤ d' := by
    by_contra hcon
    have hlt : d' < c' := lt_of_not_ge hcon
    have h := hχm hd'mem hc'mem hlt
    rw [hc', hd'] at h
    exact absurd hcd (not_le.2 h)
  obtain ⟨R, hR⟩ := increments_levy Fam μ hker hc'0 hle
  refine ⟨R, fun ω => ?_⟩
  rw [← hR ω, exponent_eq_sub hker hc'0 hle ω, hgauge d' ω hd'0, hgauge c' ω hc'0, hc', hd']

/-- **`thm:main-characterization`, the analysis direction (⇒)**, with the profile form of
`lem:selfdecomposable-exponents` as a hypothesis.

The hypothesis `hsd` is `Skeleton.sd_exponents_one_implies_three` verbatim. Everything else is
proved here; see the module docstring.

The gauge produced is **normalised**, `χ 1 = 1` (fidelity review R17); it comes straight from
`prop:canonical-gauge`, which builds `χ` as the inverse of the orbit coordinate.

The kernels are asserted **symmetric** (fidelity review R19), one application of
`kernel_symmetric`, which is (A3) read through the uniqueness half of
`lem:convolution-representation`. That conjunct is not decoration: `fourierCos` is the
article's transform only on a symmetric measure — off symmetry it is the real part of the
characteristic function and the transform identity says less than it appears to — and the
construction clause states it, so the two halves of the equivalence now speak of the same
class of kernels. -/
theorem main_analysis_of_profileForm
    (hsd : ∀ (P : SymLevyPair) (F : ℝ → ℝ), (∀ ω, F ω = P.exponent ω) →
      (∀ s t : ℝ, 0 < s → s ≤ t → IsSymLevyExponent fun ω => F (t * ω) - F (s * ω)) →
      ∃ Q : SDProfile, Q.a = P.a ∧ P.ν = profileMeasure Q.k)
    (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ∃ (χ : ℝ → ℝ) (P : SDProfile),
      χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ χ 1 = 1 ∧
        (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
        ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
          fourierCos (μ s t) ω
            = Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω))) := by
  obtain ⟨-, χ, hχ0, hχm, hχs, hχ1, -, hgauge, hLE, hFne⟩ :=
    canonical_gauge Fam.toPreCascadeCore μ hker Fam.nondegenerate S hcov
  obtain ⟨P, hP⟩ := hLE
  obtain ⟨Q, hQa, hQν⟩ := hsd P (exponent (μ 0 1)) hP
    (fun c d hc hcd => isSymLevyExponent_dilate_diff hker hχm hχs hgauge hc.le hcd)
  -- The profile has the same exponent as the pair.
  have hQ : ∀ ω : ℝ, exponent (μ 0 1) ω = Q.exponent ω := by
    intro ω
    rw [hP ω, SymLevyPair.exponent, SDProfile.exponent,
      exponentL_eq_of_profileMeasure Q P hQa.symm hQν ω]
  refine ⟨χ, Q, hχ0, hχm, hχs, hχ1, ?_, fun s t hs hst => kernel_symmetric hker hs hst, ?_⟩
  · obtain ⟨ω₀, hω₀⟩ := hFne
    exact ⟨ω₀, fun h => hω₀ (by rw [hQ ω₀, h])⟩
  · intro s t ω hs hst
    rw [fourierCos_eq_exp_neg_exponent hker hs hst ω, exponent_eq_sub hker hs hst ω,
      hgauge t ω (hs.trans hst), hgauge s ω hs, hQ, hQ]

/-! ## The analysis direction, closed -/

/-- **`thm:main-characterization`, the analysis direction (⇒).** A family satisfying
(A1)-(A8) and (ND) is a convolution cascade in a gauge, with an exponent of the form
`eq:sd-profile`.

`Skeleton.main_analysis`'s statement verbatim. The assembly is
`main_analysis_of_profileForm`, whose single hypothesis is
`lem:selfdecomposable-exponents`(1) ⇒ (3); wave 3's merge is where the two halves, written in
separate worktrees, first met. It spends `fourier_toolbox_levy_unique` (ledger **A3**) through
that leg and nothing else.

The gauge is produced **normalised**, `χ 1 = 1` (fidelity review R17), so that what the
necessity direction hands back is a representation of the kind the uniqueness clause compares,
and the kernels are asserted **symmetric** (fidelity review R19), which is what makes
`fourierCos` the article's transform of them. -/
theorem main_analysis (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ∃ (χ : ℝ → ℝ) (P : SDProfile),
      χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ χ 1 = 1 ∧
        (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
        ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
          fourierCos (μ s t) ω
            = Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω))) :=
  main_analysis_of_profileForm sd_exponents_one_implies_three Fam μ hker S hcov

/-- **`thm:main-characterization`, the analysis direction (⇒), with the representation
concluded rather than assumed** (fidelity review R18).

The article's necessity direction reads: a family satisfying (A1)-(A8) and (ND) *is* a
convolution cascade — there are kernels `μ_{s,t}` with `Φ_{s,t}f = μ_{s,t} * f`, and their
transforms are `exp(-(F(χ(t)ω) - F(χ(s)ω)))`. `main_analysis` states the second half with the
first as a hypothesis, which is the right shape for a lemma and the wrong shape for the
theorem: a reader of that statement alone gets "if the family is *already* represented by `μ`
then …" where the article derives the representation from the axioms.

Nothing is lost by concluding it. `lem:convolution-representation` is a `∃!` at each admissible
pair, so the kernel family is unique where the statement reads it, and `exists_kernelFamily`
assembles one; `main_analysis` is then applied to it. Both forms are kept and both are named on
the node's tag: this one is the article's sentence, and `main_analysis` is the lemma that
proves it and the form every consumer in the development uses.

Spends exactly what `main_analysis` spends — `fourier_toolbox_levy_unique`, ledger **A3** —
since `exists_kernelFamily` is Lean core. -/
theorem main_analysis_exists (Fam : CascadeCore) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ∃ (μ : ℝ → ℝ → Measure ℝ) (χ : ℝ → ℝ) (P : SDProfile),
      IsKernelFamily Fam.Φ μ ∧
        χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ χ 1 = 1 ∧
        (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
        ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
          fourierCos (μ s t) ω
            = Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω))) := by
  obtain ⟨μ, hker⟩ := exists_kernelFamily Fam.toPreCascadeCore Fam.positive
  obtain ⟨χ, P, hrest⟩ := main_analysis Fam μ hker S hcov
  exact ⟨μ, χ, P, hker, hrest⟩

/-! ## The node, assembled -/

/-- **`thm:main-characterization`**, the three clauses in one declaration.

The node is an equivalence together with a uniqueness statement, and its `\lean` tag has to name
declarations covering all three. This bundles them, over nothing: each conjunct is the statement
of one of `main_construction`, `main_analysis_exists`, `main_analysis` and `main_uniqueness`,
binder for binder, and nothing new is proved here.

**The necessity direction appears twice, and deliberately** (fidelity review R18). The second
conjunct is the article's sentence: from the axioms alone, *there are* kernels representing the
family, with a gauge and a profile. The third is the same conclusion with the representation as
a hypothesis — the lemma that proves the second, and the form every consumer in the development
uses, which quantifies over *every* kernel family of `Fam` and so says strictly more about a
given one. Keeping both is what makes the bundle at least as strong as either.

**What the bundling does not do.** The three clauses do not share a quantifier. Sufficiency
starts from a profile and a gauge and produces a family; necessity starts from a family and
produces a gauge and a profile; uniqueness compares two normalised representations of one
family. So the conjunction is of three closed statements rather than of three conclusions drawn
from common hypotheses, which is what the node's own three-way split says it should be. The
node's closing sentence, that in the canonical gauge the kernel at scale `t` has transform
`e^{-F(t·)}`, is the second conjunct read at `χ = id` and is not a fourth clause.

**The normalisation is carried across the join** (fidelity review R17). The necessity conjunct
now produces `χ 1 = 1`, which is the hypothesis the uniqueness conjunct demands; before, the
node's "unique up to the normalisation `χ(1) = 1`" applied to nothing the necessity direction
delivered, and the whole body of the necessity conclusion was invariant under
`(χ, P) ↦ (χ/c, P.dilate c)` for every `c > 0`.

**Spends ledger A1 and A3.** `main_construction` spends `fourier_toolbox_bochner_symm` (A1) and
`fourier_toolbox_levy_converse` (A3's converse); `main_analysis` spends
`fourier_toolbox_levy_unique` (A3's uniqueness) through
`lem:selfdecomposable-exponents`(1) ⇒ (3); `main_uniqueness` is Lean core. -/
theorem main_characterization :
    (∀ (P : SDProfile) (F : ℝ → ℝ), (∀ ω, F ω = P.exponent ω) → (∃ ω : ℝ, F ω ≠ 0) →
        ∀ χ : ℝ → ℝ, χ 0 = 0 → StrictMonoOn χ (Ici 0) → SurjOn χ (Ici 0) (Ici 0) →
          ∃ (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ) (S : ℝ → ℝ → ℝ),
            IsKernelFamily Fam.Φ μ ∧ IsScaleCovariant Fam.Φ (Ioi 0) S ∧
              (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
              ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
                fourierCos (μ s t) ω = Real.exp (-(F (χ t * ω) - F (χ s * ω)))) ∧
      (∀ (Fam : CascadeCore) (S : ℝ → ℝ → ℝ), IsScaleCovariant Fam.Φ (Ioi 0) S →
        ∃ (μ : ℝ → ℝ → Measure ℝ) (χ : ℝ → ℝ) (P : SDProfile),
          IsKernelFamily Fam.Φ μ ∧
            χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ χ 1 = 1 ∧
            (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
            (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
            ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
              fourierCos (μ s t) ω
                = Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω)))) ∧
      (∀ (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ), IsKernelFamily Fam.Φ μ →
        ∀ S : ℝ → ℝ → ℝ, IsScaleCovariant Fam.Φ (Ioi 0) S →
          ∃ (χ : ℝ → ℝ) (P : SDProfile),
            χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧ χ 1 = 1 ∧
              (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
              (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)) ∧
              ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
                fourierCos (μ s t) ω
                  = Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω)))) ∧
      ∀ (μ : ℝ → ℝ → Measure ℝ) (χ₁ χ₂ : ℝ → ℝ) (P₁ P₂ : SDProfile),
        χ₁ 1 = 1 → χ₂ 1 = 1 → χ₁ 0 = 0 → χ₂ 0 = 0 →
          StrictMonoOn χ₁ (Ici 0) → StrictMonoOn χ₂ (Ici 0) →
            (∃ ω : ℝ, P₁.exponent ω ≠ 0) →
              (∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
                fourierCos (μ s t) ω
                  = Real.exp (-(P₁.exponent (χ₁ t * ω) - P₁.exponent (χ₁ s * ω)))) →
                (∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
                  fourierCos (μ s t) ω
                    = Real.exp (-(P₂.exponent (χ₂ t * ω) - P₂.exponent (χ₂ s * ω)))) →
                  (∀ t : ℝ, 0 ≤ t → χ₁ t = χ₂ t) ∧ ∀ ω : ℝ, P₁.exponent ω = P₂.exponent ω :=
  ⟨main_construction, main_analysis_exists, main_analysis, main_uniqueness⟩

end SpatialLine
