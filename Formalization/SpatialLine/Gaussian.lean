/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Construction
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# `prop:two-members`(1): the Gaussian family is a symmetric cascade measurement family

Blueprint: `blueprint/src/parts/03-axioms.tex`, `prop:two-members`, clause (1).

The kernels are Mathlib's `gaussianReal 0 v` at `v = (t² - s²)⁺`. The positive part is a
total-function device: it agrees with `t² - s²` on the index set `s ≤ t`, and on the diagonal
`gaussianReal 0 0 = δ₀`, which is what makes (A6)'s diagonal clause hold on the nose rather than
in a limit.

## What Mathlib supplies, and what it does not

Every *kernel* identity the proof needs is already in Mathlib and none of it had to be redone:
`gaussianReal_conv_gaussianReal` is (A6), `gaussianReal_zero_var` the diagonal,
`gaussianReal_map_const_mul` is (A8), `gaussianReal_map_neg` is the symmetry (A3) reads, and
and `gaussianReal_ext_iff` is (ND) once the kernel of the identity has been identified. What
Mathlib does not supply is the passage from a kernel to an operator on `L¹`; that is
`SpatialLine/Transport.lean` — including `eq_dirac_of_mconvL1_eq_id`, which (ND) reads — and
(A7), which is `SpatialLine/L1Continuity.lean`.

## (A7), and why the estimate the review asked for was not needed

The skeleton priced this node **M–L** and the review (R30) warned that (A7) at a concrete family
is `main_construction`'s own `ε/3` argument written again. It is not, and the reason is
structural rather than particular to the Gaussian: the kernels of *any* family whose variance
parameter is additive form a convolution semigroup in one parameter, so for `w ≤ w + u`

  `g_{w+u} * f - g_w * f = g_w * (g_u * f - f)`,

and the left-hand side is bounded by `‖g_u * f - f‖₁` because `g_w *` is a contraction. That
turns continuity in `(s,t)` into continuity *at the origin of the one-parameter family*, which
`norm_mconvL1_sub_le` reduces to the concentration of `g_u` at `0` against a fixed bounded
continuous test function. No compact, no density argument, no tail estimate. The cost paid was
**M** and the argument is reusable: it needs of the kernels only that they convolve additively in
a real parameter and concentrate at the origin.

The concentration itself is the one place a Gaussian-specific fact enters, and it is a change of
variables: `g_v` is the image of `g_1` under `z ↦ √v z`, so the average of the modulus of
continuity against `g_v` is `∫ Θ_f(√v z) g_1(dz)`, and dominated convergence with the constant
bound `2‖f‖` sends it to `Θ_f(0) = 0`.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology NNReal

/-! ## The kernels -/

/-- **The Gaussian kernel of `prop:two-members`(1)**: the centred Gaussian law of variance
`(t² - s²)⁺`.

The positive part is a totality device. On the index set `0 ≤ s ≤ t` the variance is `t² - s²`;
off it the kernel is `δ₀`, and no statement of the article reads it there. -/
noncomputable def gaussianKernel (s t : ℝ) : Measure ℝ :=
  gaussianReal 0 (t ^ 2 - s ^ 2).toNNReal

instance instIsProbabilityMeasureGaussianKernel (s t : ℝ) :
    IsProbabilityMeasure (gaussianKernel s t) := by
  rw [gaussianKernel]; infer_instance

/-- **(A3) at the kernel**: the centred Gaussian law is symmetric. -/
theorem isSymmetric_gaussianReal (v : ℝ≥0) : IsSymmetric (gaussianReal 0 v) := by
  rw [IsSymmetric, gaussianReal_map_neg, neg_zero]

theorem isSymmetric_gaussianKernel (s t : ℝ) : IsSymmetric (gaussianKernel s t) :=
  isSymmetric_gaussianReal _

/-- The Gaussian law of variance `v` is the image of the standard law under `z ↦ √v z`. -/
theorem gaussianReal_eq_map_sqrt (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun z => Real.sqrt v * z) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  rw [mul_one]
  refine NNReal.coe_inj.mp ?_
  simp only [NNReal.coe_mk]
  exact (Real.sq_sqrt v.coe_nonneg).symm

/-! ## The variance is additive along the cascade, and quadratic under dilation -/

/-- **(A6) at the variance.** On the index set the positive parts add. -/
theorem gaussianVar_add {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    (s ^ 2 - r ^ 2).toNNReal + (t ^ 2 - s ^ 2).toNNReal = (t ^ 2 - r ^ 2).toNNReal := by
  have hs : 0 ≤ s := hr.trans hrs
  rw [← Real.toNNReal_add (by nlinarith) (by nlinarith)]
  congr 1
  ring

/-- **(A8) at the variance.** Dilating by `λ` multiplies the variance by `λ²`. -/
theorem gaussianVar_dilate (lam s t : ℝ) :
    (lam ^ 2).toNNReal * (t ^ 2 - s ^ 2).toNNReal
      = ((lam * t) ^ 2 - (lam * s) ^ 2).toNNReal := by
  have hrw : (lam * t) ^ 2 - (lam * s) ^ 2 = lam ^ 2 * (t ^ 2 - s ^ 2) := by ring
  rw [hrw, Real.toNNReal_mul (sq_nonneg lam)]

/-- **(ND) at the variance.** -/
theorem gaussianVar_ne_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (t ^ 2 - s ^ 2).toNNReal ≠ 0 := by
  rw [ne_eq, Real.toNNReal_eq_zero, not_le]
  nlinarith

/-! ## (A7), from the generic construction -/

/-- **The Gaussian kernels as `CascadeData`**, which is where (A1)-(A7) now come from.

Wave 2's merge (2026-09-09) rebuilt this file on `SpatialLine.CascadeData`. The four
declarations that used to stand here -- the concentration of the Gaussian at small variance,
the strong convergence to the identity, the semigroup step and (A7) in the variance -- proved
(A7) along the *semigroup* parameter, which the general hemigroup argument of
`SpatialLine/Construction.lean` does not need; they are deleted, and the only Gaussian-specific
input left is the continuity of the transform in the pair of scales.
`two_members_gaussian` is unchanged. -/
noncomputable def gaussianData : CascadeData where
  κ := gaussianKernel
  prob := instIsProbabilityMeasureGaussianKernel
  sym := isSymmetric_gaussianKernel
  self := fun t _ => by
    rw [gaussianKernel, sub_self, Real.toNNReal_zero, gaussianReal_zero_var]
  conv := fun r s t hr hrs hst => by
    rw [gaussianKernel, gaussianKernel, gaussianKernel, gaussianReal_conv_gaussianReal,
      add_zero, gaussianVar_add hr hrs hst]
  cos_continuousOn := fun ω => Continuous.continuousOn (by
    have hrw : (fun p : ℝ × ℝ => fourierCos (gaussianKernel p.1 p.2) ω)
        = fun p : ℝ × ℝ => Real.exp (-(max (p.2 ^ 2 - p.1 ^ 2) 0 * ω ^ 2 / 2)) := by
      funext p
      rw [gaussianKernel, fourierCos_gaussianReal, Real.coe_toNNReal']
    rw [hrw]
    exact Real.continuous_exp.comp (((((continuous_snd.pow 2).sub
      (continuous_fst.pow 2)).max continuous_const).mul continuous_const).div_const 2).neg)

@[simp] theorem gaussianData_kappa (s t : ℝ) : gaussianData.κ s t = gaussianKernel s t := rfl

/-! ## (ND) -/

/-- **(ND) at the kernel**: a proper Gaussian increment is not `δ₀`.

Stated at the kernel rather than at the operator since wave 2's merge (2026-09-09):
`CascadeData.isNondegenerate` takes the kernel form and supplies the passage to the operator
through `eq_dirac_of_mconvL1_eq_id`, chapter 3's general fact that convolution by a probability
measure is the identity only for `δ₀`. `gaussianReal_ext_iff` then reads off the variance. -/
theorem gaussianKernel_ne_dirac_zero {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussianKernel s t ≠ Measure.dirac 0 := by
  intro hdirac
  rw [gaussianKernel, ← gaussianReal_zero_var (0 : ℝ)] at hdirac
  exact gaussianVar_ne_zero hs hst (gaussianReal_ext_iff.mp hdirac).2

/-! ## The family -/

/-- **`prop:two-members`(1)**: the Gaussian family, as a `CascadeFamily`.

Every clause of `def:cascade-family` for `Φ_{s,t} f = g_{t²-s²} * f`. This is the model the
specification is checked against: a mis-stated axiom makes the article's theorems vacuous rather
than unprovable, and the only thing that catches it is a family known independently to satisfy
the mathematics. -/
noncomputable def gaussianCascadeFamily : CascadeFamily where
  toCascadeCore := gaussianData.cascadeCore fun _ _ hs hst => gaussianKernel_ne_dirac_zero hs hst
  S lam t := lam * t
  covariant := gaussianData.isScaleCovariant (fun lam t => lam * t)
    (fun lam hlam t ht => by simpa using mul_nonneg hlam.le ht)
    (fun lam hlam s _ t _ hst => by simpa using mul_lt_mul_of_pos_left hst hlam)
    (fun lam hlam t ht => ⟨lam⁻¹ * t, by
      simp only [mem_Ici] at ht ⊢
      exact mul_nonneg (inv_nonneg.mpr hlam.le) ht, by field_simp⟩)
    (fun lam hlam s t _ _ => by
      show (gaussianKernel s t).map (fun x => lam * x)
        = gaussianKernel (lam * s) (lam * t)
      rw [gaussianKernel, gaussianKernel, gaussianReal_map_const_mul, mul_zero]
      congr 1
      rw [← gaussianVar_dilate lam s t, Real.toNNReal_of_nonneg (sq_nonneg lam)])

@[simp] theorem gaussianCascadeFamily_Phi (s t : ℝ) :
    gaussianCascadeFamily.Φ s t = mconvL1 (gaussianKernel s t) := rfl

/-- **`prop:two-members`(1), the Gaussian family.**

Reading: the kernels are *named*, as Mathlib's `gaussianReal 0 v` with `v = (t² - s²)⁺`; the
positive part is a total-function device and agrees with `t² - s²` on the index set `s ≤ t`, and
on the diagonal `gaussianReal 0 0 = δ₀`, which is what makes (A6)'s diagonal clause hold on the
nose. The action is `S lam t = lam t`, as an equation between the family's `S` field and that
function.

Class (c) — the causal members are the pure delay and the Gamma family and are stated in prose
there; here both members are claims.

**Priced M–L (skeleton, re-priced by review R30); paid M.** The transport block (A1)–(A6), (A8)
is `SpatialLine/Transport.lean`, ported from Paper I with reflection replacing causality, and
(A7) turned out cheaper than either estimate: see the module docstring. The one clause that cost
more than expected is (ND), which needed a general fact the skeleton had not anticipated —
`eq_dirac_of_mconvL1_eq_id`, that convolution by a probability measure is the identity only for
`δ₀` — because the blueprint's Fourier argument for (ND) is about the *kernel* and the axiom is
about the *operator*. That lemma is in `SpatialLine/Transport.lean` and is what
`lem:convolution-representation`'s uniqueness clause will start from. -/
theorem two_members_gaussian :
    ∃ Fam : CascadeFamily,
      Fam.S = (fun lam t => lam * t) ∧
        IsKernelFamily Fam.Φ
          (fun s t => ProbabilityTheory.gaussianReal 0 (t ^ 2 - s ^ 2).toNNReal) := by
  refine ⟨gaussianCascadeFamily, rfl, ?_, ?_⟩
  · intro s t _ _
    infer_instance
  · intro s t _ _ f
    exact coeFn_mconvL1 (gaussianKernel s t) f

end SpatialLine
