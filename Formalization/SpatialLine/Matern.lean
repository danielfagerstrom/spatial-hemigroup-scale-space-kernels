/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Construction

/-!
# `prop:two-members`(2): the Matérn family is a symmetric cascade measurement family

Blueprint: `blueprint/src/parts/03-axioms.tex`, `prop:two-members`, clause (2).

The kernels are *quantified over rather than constructed*: the node hypothesises a family of
symmetric probability measures with the cosine transform
`((1 + s²ω²)/(1 + t²ω²))^γ` and concludes that it satisfies the axioms. Existence is
`prop:matern-exponent` with `prop:matern-density`, Chapter 10, which is the forward reference
the node's `\uses` edges already record; the specification determines the kernels, so nothing is
lost by quantifying (SKELETON.md, F1's companion remark).

## Which interface the proof consumes, and which it does not

The Matérn *density* at general `γ` is a Bessel-`K` closed form and an `[A]` interface (ledger
A15/A16, through `prop:matern-density`). **This file does not touch it.** Everything the axioms
need is read off the transform: the exponent `γ log(1 + t²ω²)` is elementary, the axioms are
identities between transforms, and the passage back to measures is `Measure.ext_of_charFun` —
Mathlib, not a ledger entry. So the route taken is the one consuming the *smaller* interface:
no axiom is added to `blueprint/trust-boundary.txt` by this node, and `#print axioms` reduces to
Lean core.

The `[A]` interface the skeleton expected here, `prop:levy-continuity` (ledger A6), is also not
spent: its first clause — the only one the article consumes — is Mathlib's
`ProbabilityMeasure.tendsto_of_tendsto_charFun`, and it is proved in
`SpatialLine/L1Continuity.lean` rather than assumed. SKELETON.md's question Q2 asked whether
`prop:fourier-uniqueness` and `prop:levy-continuity` should be demoted to `[T]`; this chapter's
proofs are evidence that they can be, because they use no more than the Mathlib declarations
those two nodes' annotations name.

## (A7) for a hemigroup

The Gaussian argument does not transfer unchanged: a hemigroup has no single increment
parameter, so `Φ_{s,t} - Φ_{s',t'}` factors only after the two endpoints are moved one at a
time, through the intermediate `Φ_{s',t}`. Moving the **left** endpoint leaves an increment
applied first, absorbed by the contraction bound; moving the **right** endpoint leaves one
applied last, to an element that varies with the parameters, and there the estimate has to be
read at that element — which costs nothing because `Θ` decreases under convolution
(`transDiff_mconvL1_le`). Both remainders are increments `Φ_{a,b}` whose endpoints collapse
together, so each tends to `0` by Lévy's theorem applied to the transform. The one case the
intermediate is unavailable is the diagonal `s = t`, where the limit operator is the identity
and a single increment suffices.

Cost: **M**, as the skeleton priced it, but the M is nearly all in the two-endpoint bookkeeping
of (A7); the axioms proper are one transform identity each.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The transform -/

/-- **The Matérn transform** `((1 + s²ω²)/(1 + t²ω²))^γ` of `prop:two-members`(2). -/
noncomputable def maternTransform (γ s t ω : ℝ) : ℝ :=
  ((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ

theorem maternBase_pos (s ω : ℝ) : 0 < 1 + s ^ 2 * ω ^ 2 := by positivity

theorem maternTransform_nonneg (γ s t ω : ℝ) : 0 ≤ maternTransform γ s t ω :=
  Real.rpow_nonneg (le_of_lt (div_pos (maternBase_pos s ω) (maternBase_pos t ω))) γ

/-- **(A6) at the transform**: the increments multiply. -/
theorem maternTransform_mul (γ r s t ω : ℝ) :
    maternTransform γ r s ω * maternTransform γ s t ω = maternTransform γ r t ω := by
  rw [maternTransform, maternTransform, maternTransform,
    ← Real.mul_rpow (le_of_lt (div_pos (maternBase_pos r ω) (maternBase_pos s ω)))
      (le_of_lt (div_pos (maternBase_pos s ω) (maternBase_pos t ω)))]
  congr 1
  field_simp

/-- **(A6), the diagonal clause, at the transform.** -/
@[simp]
theorem maternTransform_self (γ t ω : ℝ) : maternTransform γ t t ω = 1 := by
  rw [maternTransform, div_self (maternBase_pos t ω).ne', Real.one_rpow]

/-- **(A8) at the transform**: dilating the frequency is dilating both scales. -/
theorem maternTransform_dilate (γ lam s t ω : ℝ) :
    maternTransform γ s t (lam * ω) = maternTransform γ (lam * s) (lam * t) ω := by
  rw [maternTransform, maternTransform]
  congr 2 <;> ring

/-- **(ND) at the transform**: a nondegenerate increment has transform `< 1` at `ω = 1`. -/
theorem maternTransform_lt_one {γ s t : ℝ} (hγ : 0 < γ) (hs : 0 ≤ s) (hst : s < t) :
    maternTransform γ s t 1 < 1 := by
  refine Real.rpow_lt_one (le_of_lt (div_pos (maternBase_pos s 1) (maternBase_pos t 1))) ?_ hγ
  rw [div_lt_one (maternBase_pos t 1)]
  nlinarith

/-- The transform depends continuously on the pair of scales. -/
theorem continuous_maternTransform {γ : ℝ} (hγ : 0 ≤ γ) (ω : ℝ) :
    Continuous fun p : ℝ × ℝ => maternTransform γ p.1 p.2 ω := by
  have hden : Continuous fun p : ℝ × ℝ => 1 + p.2 ^ 2 * ω ^ 2 :=
    continuous_const.add ((continuous_snd.pow 2).mul continuous_const)
  have hnum : Continuous fun p : ℝ × ℝ => 1 + p.1 ^ 2 * ω ^ 2 :=
    continuous_const.add ((continuous_fst.pow 2).mul continuous_const)
  have hdiv : Continuous fun p : ℝ × ℝ => (1 + p.1 ^ 2 * ω ^ 2) / (1 + p.2 ^ 2 * ω ^ 2) :=
    hnum.div hden fun p => (maternBase_pos p.2 ω).ne'
  refine continuous_iff_continuousAt.mpr fun p => ?_
  exact (Real.continuousAt_rpow_const _ γ (Or.inr hγ)).comp hdiv.continuousAt

/-! ## The data of `prop:two-members`(2) -/

/-- **The hypotheses of `prop:two-members`(2), bundled.**

The node quantifies over a kernel family with a prescribed cosine transform; bundling the three
hypotheses is what lets the probability-measure instance be *registered* for the totalised
kernel, which is what `mconvL1` needs in order to be written at all. Nothing is assumed off the
index set `0 ≤ s ≤ t`. -/
structure MaternData (γ : ℝ) where
  /-- The kernels. -/
  ρ : ℝ → ℝ → Measure ℝ
  gamma_pos : 0 < γ
  prob : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ρ s t)
  sym : ∀ s t, 0 ≤ s → s ≤ t → IsSymmetric (ρ s t)
  transform : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ, fourierCos (ρ s t) ω = maternTransform γ s t ω

namespace MaternData

variable {γ : ℝ} (D : MaternData γ)

/-- The kernels, totalised by `δ₀` off the index set — the same device the Gaussian family's
positive part is, and read nowhere. -/
noncomputable def kernel (s t : ℝ) : Measure ℝ :=
  if 0 ≤ s ∧ s ≤ t then D.ρ s t else Measure.dirac 0

instance instIsProbabilityMeasureKernel (s t : ℝ) : IsProbabilityMeasure (D.kernel s t) := by
  unfold kernel
  split_ifs with h
  · exact D.prob s t h.1 h.2
  · infer_instance

theorem kernel_eq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : D.kernel s t = D.ρ s t :=
  if_pos ⟨hs, hst⟩

theorem isSymmetric_kernel (s t : ℝ) : IsSymmetric (D.kernel s t) := by
  unfold kernel
  split_ifs with h
  · exact D.sym s t h.1 h.2
  · rw [IsSymmetric, Measure.map_dirac' measurable_neg, neg_zero]

theorem fourierCos_kernel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (D.kernel s t) ω = maternTransform γ s t ω := by
  rw [D.kernel_eq hs hst]
  exact D.transform s t hs hst ω

theorem charFun_kernel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    charFun (D.kernel s t) ω = (maternTransform γ s t ω : ℂ) := by
  rw [charFun_eq_fourierCos_of_symmetric (D.isSymmetric_kernel s t), D.fourierCos_kernel hs hst]

/-! ## The axioms at the kernel -/

/-- **(A6), the diagonal clause.** -/
theorem kernel_self {t : ℝ} (ht : 0 ≤ t) : D.kernel t t = Measure.dirac 0 := by
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [D.charFun_kernel ht le_rfl, charFun_dirac, maternTransform_self]
  simp

/-- **(A6), the cascade clause.** -/
theorem kernel_conv {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    (D.kernel r s) ∗ (D.kernel s t) = D.kernel r t := by
  haveI : IsFiniteMeasure ((D.kernel r s) ∗ (D.kernel s t)) := by
    rw [Measure.conv]; infer_instance
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_conv, D.charFun_kernel hr hrs, D.charFun_kernel (hr.trans hrs) hst,
    D.charFun_kernel hr (hrs.trans hst), ← Complex.ofReal_mul, maternTransform_mul]

/-- **(A8) at the kernel.** -/
theorem kernel_map_const_mul {lam s t : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hst : s ≤ t) :
    (D.kernel s t).map (fun x => lam * x) = D.kernel (lam * s) (lam * t) := by
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_map_const_mul, D.charFun_kernel hs hst,
    D.charFun_kernel (by positivity) (by nlinarith), maternTransform_dilate]

/-- **(ND) at the kernel**: a proper increment is not `δ₀`, because its transform is `< 1`.

Stated at the kernel rather than at the operator since wave 2's merge (2026-09-09):
`CascadeData.isNondegenerate` takes the kernel form and supplies the passage to the operator
through `eq_dirac_of_mconvL1_eq_id`, which is chapter 3's general fact and was inlined here. -/
theorem kernel_ne_dirac_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    D.kernel s t ≠ Measure.dirac 0 := by
  intro hdirac
  have h1 : fourierCos (D.kernel s t) 1 = 1 := by rw [hdirac]; simp
  rw [D.fourierCos_kernel hs hst.le] at h1
  exact absurd h1 (maternTransform_lt_one D.gamma_pos hs hst).ne

/-! ## (A7), from the generic construction -/

/-- **The Matérn kernels as `CascadeData`**, which is where (A1)-(A7) now come from.

Wave 2's merge (2026-09-09) rebuilt this file on `SpatialLine.CascadeData`. The four
declarations that used to stand here -- the concentration of a collapsing increment, the two
endpoint estimates and (A7) itself -- were the generic block of `SpatialLine/Construction.lean`
written with `maternTransform` in place of the `cos_continuousOn` field, and they are deleted;
the only Matérn-specific input is that field, which is the continuity of the transform in the
pair of scales, `continuous_maternTransform`. `two_members_matern` is unchanged. -/
noncomputable def toCascadeData : CascadeData where
  κ := D.kernel
  prob := D.instIsProbabilityMeasureKernel
  sym := D.isSymmetric_kernel
  self := fun _ ht => D.kernel_self ht
  conv := fun _ _ _ hr hrs hst => D.kernel_conv hr hrs hst
  cos_continuousOn := fun ω =>
    ((continuous_maternTransform D.gamma_pos.le ω).continuousOn).congr
      fun _ hp => D.fourierCos_kernel hp.1 hp.2 ω

@[simp] theorem toCascadeData_kappa (s t : ℝ) : D.toCascadeData.κ s t = D.kernel s t := rfl

/-! ## The family -/

/-- **`prop:two-members`(2)**: the Matérn family, as a `CascadeFamily`.

Every clause of `def:cascade-family` for `Φ_{s,t} f = ρ_{s,t} * f`, with `ρ_{s,t}` any family of
symmetric probability measures carrying the prescribed cosine transform. -/
noncomputable def cascadeFamily : CascadeFamily where
  toCascadeCore := D.toCascadeData.cascadeCore fun _ _ hs hst => D.kernel_ne_dirac_zero hs hst
  S lam t := lam * t
  covariant := D.toCascadeData.isScaleCovariant (fun lam t => lam * t)
    (fun lam hlam t ht => by simpa using mul_nonneg hlam.le ht)
    (fun lam hlam s _ t _ hst => by simpa using mul_lt_mul_of_pos_left hst hlam)
    (fun lam hlam t ht => ⟨lam⁻¹ * t, by
      simp only [mem_Ici] at ht ⊢
      exact mul_nonneg (inv_nonneg.mpr hlam.le) ht, by field_simp⟩)
    (fun lam hlam s t hs hst => D.kernel_map_const_mul hlam hs hst)

@[simp] theorem cascadeFamily_Phi (s t : ℝ) :
    D.cascadeFamily.Φ s t = mconvL1 (D.kernel s t) := rfl

end MaternData

/-- **`prop:two-members`(2), the Matérn family — the axioms.**

Reading: the kernels are quantified over rather than constructed (see the module docstring), by
their cosine transform `((1 + s²ω²)/(1 + t²ω²))^γ`. Existence of such a family is
`prop:matern-exponent` with `prop:matern-density`, Chapter 10, which is the forward reference the
node's `\uses` edges already record.

**Priced M; paid M.** The axioms proper are one transform identity each, read back to measures by
`Measure.ext_of_charFun`; the cost is (A7), where a hemigroup's two endpoints have to be moved
separately. The Bessel-`K` interface (ledger A15/A16) is *not* consumed: the exponent side is
elementary and that is all the axioms need, which is the route the smaller interface. -/
theorem two_members_matern (γ : ℝ) (hγ : 0 < γ) (ρ : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (ρ s t))
    (hsym : ∀ s t, 0 ≤ s → s ≤ t → IsSymmetric (ρ s t))
    (hcos : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ,
      fourierCos (ρ s t) ω = ((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ) :
    ∃ Fam : CascadeFamily, Fam.S = (fun lam t => lam * t) ∧ IsKernelFamily Fam.Φ ρ := by
  set D : MaternData γ := ⟨ρ, hγ, hprob, hsym, hcos⟩ with hD
  refine ⟨D.cascadeFamily, rfl, ?_, ?_⟩
  · intro s t hs hst
    exact hprob s t hs hst
  · intro s t hs hst f
    refine (coeFn_mconvL1 (D.kernel s t) f).trans ?_
    rw [D.kernel_eq hs hst]

end SpatialLine
