/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.TransformBridge
import SpatialLine.L1Continuity

/-!
# From kernels to a cascade family: the axioms of `def:cascade-family` at a prescribed transform

Blueprint: `thm:main-characterization`, the construction direction, and — retrospectively —
`prop:two-members`.

## What this file is

`CascadeData` is the *hypotheses* a family of kernels has to meet for `Φ_{s,t} f = μ_{s,t} * f`
to satisfy (A1)–(A7): the kernels are symmetric probability measures, the diagonal is `δ₀`, the
cascade law holds at the level of measures, and the cosine transform is continuous in the pair of
scales. From those the whole of `PreCascadeCore`, positivity, and — under one further hypothesis
each — nondegeneracy and covariance follow, with no reference to which family it is.

**A finding, recorded here rather than acted on.** Chapter 3's `Matern.lean` proves exactly this
block for `MaternData`, and every step of it uses only the five properties above; the same is
true of `Gaussian.lean`. The `\lean` tags of `prop:two-members` are not this prover's to change,
so `Matern.lean` is left alone and the block is written once more, generically, here. At the
merge the Matérn and Gaussian families should be rebuilt on `CascadeData` and their copies
deleted, exactly as wave 1's deduplication rebuilt four provers' copies on one; the survivor
should be this file. Nothing in it mentions a transform's formula.

The one genuinely new lemma is `CascadeData.cascadeCore`, which needs no proof beyond assembling
the fields, and `CascadeData.continuousOn_mconvL1`, which is (A7) — the expensive clause, where
a hemigroup's two endpoints have to be moved separately because there is no `t - s` to move.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The hypotheses under which a family of kernels is a cascade measurement family.**

The kernels are *totalised* — defined for every pair of reals — with nothing asserted off the
index set `0 ≤ s ≤ t`; that is what lets the probability-measure instance be registered, which is
what `mconvL1` needs in order to be written at all.

twin: the hypotheses `Hemigroup.CascadeCore` is built from in `Construction.lean` there, with
reflection symmetry in place of causal support. -/
structure CascadeData where
  /-- The kernels. -/
  κ : ℝ → ℝ → Measure ℝ
  /-- Each kernel is a probability measure. -/
  prob : ∀ s t, IsProbabilityMeasure (κ s t)
  /-- Each kernel is symmetric — what (A3) needs. -/
  sym : ∀ s t, IsSymmetric (κ s t)
  /-- **(A6), the diagonal.** -/
  self : ∀ t, 0 ≤ t → κ t t = Measure.dirac 0
  /-- **(A6), the cascade law**, at the level of measures. -/
  conv : ∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → (κ r s) ∗ (κ s t) = κ r t
  /-- **(A7)'s hypothesis**: the cosine transform is continuous in the pair of scales. -/
  cos_continuousOn : ∀ ω : ℝ, ContinuousOn (fun p : ℝ × ℝ => fourierCos (κ p.1 p.2) ω)
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}

namespace CascadeData

variable (D : CascadeData)

instance instIsProbabilityMeasure (s t : ℝ) : IsProbabilityMeasure (D.κ s t) := D.prob s t

theorem charFun_kernel (s t : ℝ) (ω : ℝ) :
    charFun (D.κ s t) ω = ((fourierCos (D.κ s t) ω : ℝ) : ℂ) :=
  charFun_eq_fourierCos_of_symmetric (D.sym s t) ω

/-! ## (A7): the operators depend continuously on the pair of scales -/

/-- **Concentration of a collapsing increment.** If both endpoints tend to the same limit, the
increments tend to `δ₀` and the modulus of continuity averages away.

twin: `MaternData.tendsto_integral_transDiff`, with the concrete transform replaced by the
`cos_continuousOn` field. -/
theorem tendsto_integral_transDiff (f : X) {a b : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hac : Tendsto a atTop (𝓝 c)) (hbc : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => ∫ y, transDiff f y ∂(D.κ (a n) (b n))) atTop (𝓝 0) := by
  refine tendsto_integral_transDiff_of_tendsto_charFun (fun ω => ?_) f
  have hS : Tendsto (fun n => ((a n, b n) : ℝ × ℝ)) atTop
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}] (c, c)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hac.prodMk_nhds hbc,
      Eventually.of_forall fun n => ⟨ha n, hab n⟩⟩
  have hcw := (D.cos_continuousOn ω (c, c) ⟨hc, le_rfl⟩).tendsto.comp hS
  rw [Function.comp_def] at hcw
  simp only [D.self c hc, fourierCos_dirac_zero] at hcw
  have hcast : Tendsto (fun n => ((fourierCos (D.κ (a n) (b n)) ω : ℝ) : ℂ)) atTop (𝓝 1) := by
    have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hcw
    simpa [Function.comp_def] using this
  exact hcast.congr fun n => (D.charFun_kernel (a n) (b n) ω).symm

/-- **Moving the left endpoint.** The increment is applied *first*, so the contraction bound
absorbs it and the estimate is at `f`.

twin: `MaternData.norm_sub_left`, verbatim. -/
theorem norm_sub_left (f : X) {s s' t : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hst : s ≤ t) (hs't : s' ≤ t) :
    ‖mconvL1 (D.κ s t) f - mconvL1 (D.κ s' t) f‖
      ≤ ‖mconvL1 (D.κ (min s s') (max s s')) f - f‖ := by
  have key : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ t →
      ‖mconvL1 (D.κ u t) f - mconvL1 (D.κ v t) f‖ ≤ ‖mconvL1 (D.κ u v) f - f‖ := by
    intro u v hu huv hvt
    haveI : IsFiniteMeasure ((D.κ u v) ∗ (D.κ v t)) := by rw [Measure.conv]; infer_instance
    have hcomp : mconvL1 (D.κ u t) f = mconvL1 (D.κ v t) (mconvL1 (D.κ u v) f) := by
      rw [← mconvL1_congr (D.conv u v t hu huv hvt), ← mconvL1_comp]
      rfl
    rw [hcomp, ← ContinuousLinearMap.map_sub]
    exact norm_mconvL1_le _ _
  rcases le_total s s' with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact key s s' hs h hs't
  · rw [min_eq_right h, max_eq_left h, ← norm_neg, neg_sub]
    exact key s' s hs' h hst

/-- **Moving the right endpoint.** The increment is applied *last*, to an element that varies
with the parameters, so the estimate is read there.

twin: `MaternData.norm_sub_right`, verbatim. -/
theorem norm_sub_right (f : X) {s t t' : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hst' : s ≤ t') :
    ‖mconvL1 (D.κ s t) f - mconvL1 (D.κ s t') f‖
      ≤ ∫ y, transDiff f y ∂(D.κ (min t t') (max t t')) := by
  have key : ∀ u v : ℝ, s ≤ u → u ≤ v →
      ‖mconvL1 (D.κ s v) f - mconvL1 (D.κ s u) f‖ ≤ ∫ y, transDiff f y ∂(D.κ u v) := by
    intro u v hsu huv
    haveI : IsFiniteMeasure ((D.κ s u) ∗ (D.κ u v)) := by rw [Measure.conv]; infer_instance
    have hcomp : mconvL1 (D.κ s v) f = mconvL1 (D.κ u v) (mconvL1 (D.κ s u) f) := by
      rw [← mconvL1_congr (D.conv s u v hs hsu huv), ← mconvL1_comp]
      rfl
    rw [hcomp]
    exact norm_mconvL1_comp_sub_le _ _ f
  rcases le_total t t' with h | h
  · rw [min_eq_left h, max_eq_right h, ← norm_neg, neg_sub]
    exact key t t' hst h
  · rw [min_eq_right h, max_eq_left h]
    exact key t' t hst' h

/-- **(A7).**

twin: `MaternData.continuousOn_mconvL1`, verbatim. -/
theorem continuousOn_mconvL1 (f : X) :
    ContinuousOn (fun p : ℝ × ℝ => mconvL1 (D.κ p.1 p.2) f)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  rintro p ⟨hp0, hp12⟩
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro q hq
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, 0 ≤ (q n).1 ∧ (q n).1 ≤ (q n).2 :=
    Filter.eventually_atTop.mp (hq self_mem_nhdsWithin)
  set q' : ℕ → ℝ × ℝ := fun n => q (n + N₀) with hq'def
  have hmem : ∀ n, 0 ≤ (q' n).1 ∧ (q' n).1 ≤ (q' n).2 := fun n => hN₀ _ (Nat.le_add_left _ _)
  have hqn : Tendsto q atTop (𝓝 p) := hq.mono_right nhdsWithin_le_nhds
  have hq'n : Tendsto q' atTop (𝓝 p) := hqn.comp (tendsto_add_atTop_nat N₀)
  have ha : Tendsto (fun n => (q' n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hq'n
  have hb : Tendsto (fun n => (q' n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hq'n
  suffices hmain : Tendsto (fun n => mconvL1 (D.κ (q' n).1 (q' n).2) f) atTop
      (𝓝 (mconvL1 (D.κ p.1 p.2) f)) by
    rw [← tendsto_add_atTop_iff_nat N₀]
    exact hmain
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rcases eq_or_lt_of_le hp12 with heq | hlt
  · have hid : mconvL1 (D.κ p.1 p.2) f = f := by
      rw [← heq, mconvL1_congr (D.self p.1 hp0), mconvL1_dirac_zero]
      rfl
    simp only [hid]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_mconvL1_sub_le (D.κ (q' n).1 (q' n).2) f) ?_
    exact D.tendsto_integral_transDiff f hp0 (fun n => (hmem n).1) (fun n => (hmem n).2) ha
      (by rw [heq]; exact hb)
  · have hev : ∀ᶠ n in atTop, p.1 < (q' n).2 := hb.eventually_const_lt hlt
    have hleft : Tendsto (fun n => ‖mconvL1
        (D.κ (min (q' n).1 p.1) (max (q' n).1 p.1)) f - f‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_mconvL1_sub_le _ f) ?_
      refine D.tendsto_integral_transDiff (c := p.1) f hp0 (fun n => le_min (hmem n).1 hp0)
        (fun n => min_le_max) ?_ ?_
      · simpa using ha.min (tendsto_const_nhds (x := p.1))
      · simpa using ha.max (tendsto_const_nhds (x := p.1))
    have hright : Tendsto (fun n => ∫ y, transDiff f y
        ∂(D.κ (min (q' n).2 p.2) (max (q' n).2 p.2))) atTop (𝓝 0) := by
      refine D.tendsto_integral_transDiff (c := p.2) f (hp0.trans hp12)
        (fun n => le_min ((hmem n).1.trans (hmem n).2) (hp0.trans hp12))
        (fun n => min_le_max) ?_ ?_
      · simpa using hb.min (tendsto_const_nhds (x := p.2))
      · simpa using hb.max (tendsto_const_nhds (x := p.2))
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hleft.add hright)
    filter_upwards [hev] with n hn
    have htri : ‖mconvL1 (D.κ (q' n).1 (q' n).2) f - mconvL1 (D.κ p.1 p.2) f‖
        ≤ ‖mconvL1 (D.κ (q' n).1 (q' n).2) f - mconvL1 (D.κ p.1 (q' n).2) f‖
          + ‖mconvL1 (D.κ p.1 (q' n).2) f - mconvL1 (D.κ p.1 p.2) f‖ := by
      simpa [dist_eq_norm] using dist_triangle (mconvL1 (D.κ (q' n).1 (q' n).2) f)
        (mconvL1 (D.κ p.1 (q' n).2) f) (mconvL1 (D.κ p.1 p.2) f)
    refine htri.trans (add_le_add ?_ ?_)
    · exact D.norm_sub_left f (hmem n).1 hp0 (hmem n).2 hn.le
    · exact D.norm_sub_right f hp0 hn.le hp12

/-! ## The axioms -/

/-- **(A1)–(A3) and (A5)–(A7)**, for convolution by the kernels. -/
noncomputable def preCore : PreCascadeCore where
  Φ s t := mconvL1 (D.κ s t)
  translation _ _ _ _ a f := mconvL1_transL1 a f
  reflection s t _ _ f := mconvL1_reflL1 (D.sym s t) f
  unit_mass _ _ _ _ f _ := integral_mconvL1 f
  diag t ht := by
    rw [mconvL1_congr (D.self t ht)]
    exact mconvL1_dirac_zero
  cascade r s t hr hrs hst := by
    haveI : IsFiniteMeasure ((D.κ r s) ∗ (D.κ s t)) := by rw [Measure.conv]; infer_instance
    rw [mconvL1_comp, mconvL1_congr (D.conv r s t hr hrs hst)]
  continuous f := D.continuousOn_mconvL1 f

@[simp] theorem preCore_Φ (s t : ℝ) : D.preCore.Φ s t = mconvL1 (D.κ s t) := rfl

/-- **(A4).** -/
theorem isPositive : IsPositive D.preCore.Φ := fun _ _ _ _ f hf => isNonneg_mconvL1 f hf

/-- The kernels represent the operators, which is the hypothesis Chapters 5–7 take in place of
`lem:convolution-representation`. -/
theorem isKernelFamily : IsKernelFamily D.preCore.Φ D.κ where
  isProbability s t _ _ := D.prob s t
  conv s t _ _ f := coeFn_mconvL1 (D.κ s t) f

/-- **(ND)**, from nondegeneracy at the level of kernels. -/
theorem isNondegenerate (h : ∀ s t : ℝ, 0 ≤ s → s < t → D.κ s t ≠ Measure.dirac 0) :
    IsNondegenerate D.preCore.Φ := fun s t hs hst hid =>
  h s t hs hst (eq_dirac_of_mconvL1_eq_id hid)

/-- **(A1)–(A7) and (ND)**: the cascade core. -/
noncomputable def cascadeCore (h : ∀ s t : ℝ, 0 ≤ s → s < t → D.κ s t ≠ Measure.dirac 0) :
    CascadeCore where
  toPreCascadeCore := D.preCore
  positive := D.isPositive
  nondegenerate := D.isNondegenerate h

@[simp] theorem cascadeCore_Φ (h : ∀ s t : ℝ, 0 ≤ s → s < t → D.κ s t ≠ Measure.dirac 0)
    (s t : ℝ) : (D.cascadeCore h).Φ s t = mconvL1 (D.κ s t) := rfl

/-- **(A8)**, from the dilation identity at the level of kernels. -/
theorem isScaleCovariant (S : ℝ → ℝ → ℝ)
    (hmap : ∀ lam, 0 < lam → MapsTo (S lam) (Ici 0) (Ici 0))
    (hmono : ∀ lam, 0 < lam → StrictMonoOn (S lam) (Ici 0))
    (hsurj : ∀ lam, 0 < lam → SurjOn (S lam) (Ici 0) (Ici 0))
    (hdil : ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (D.κ s t).map (fun x => lam * x) = D.κ (S lam s) (S lam t)) :
    IsScaleCovariant D.preCore.Φ (Ioi 0) S where
  S_mapsTo lam hlam _ := hmap lam hlam
  S_strictMonoOn lam hlam _ := hmono lam hlam
  S_surjOn lam hlam _ := hsurj lam hlam
  scale lam hlam _ s t hs hst := by
    rw [preCore_Φ, preCore_Φ, dilL1_comp_mconvL1 hlam (D.κ s t),
      mconvL1_congr (hdil lam hlam s t hs hst)]

end CascadeData

end SpatialLine
