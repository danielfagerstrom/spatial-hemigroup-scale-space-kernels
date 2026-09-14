/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Pairing

/-!
# The kernels of a cascade family, and the positivity of their transforms

Blueprint: `blueprint/src/parts/04-representation.tex` and `05-cascade.tex`.

What Chapters 5 and 6 actually consume from Chapter 4 is not the *existence* half of
`lem:convolution-representation` — that is supplied to every statement as the hypothesis
`IsKernelFamily` — but four consequences of its **uniqueness** half, together with
`lem:nonvanishing`:

* `kernel_symmetric` — the kernels are symmetric, which is (A3) read through uniqueness;
* `kernel_conv` — the cascade law at the level of measures, which is (A6) read through it;
* `kernel_diag` — `μ_{t,t} = δ₀`;
* `kernel_ne_dirac` — (ND) at the level of measures;
* `kernel_transform_pos` — the transform never vanishes.

## What the wave-1 merge did with this file

All five were proved twice: here for chapters 5 and 6, and in `SpatialLine/Nonvanishing.lean`
for `lem:nonvanishing`, whose own proof needs the same consequences of uniqueness. The merge of
2026-09-09 kept the copies in `Nonvanishing.lean` — the file that proves the node the facts
belong to — and left three one-line adapters here, because two of the surviving statements are
in a different but equivalent form and one node's statement fixes the form it needs:

* `kernel_symmetric` is `isSymmetric_kernel` with the `IsProbabilityMeasure` instance supplied
  from `IsKernelFamily.isProbability` instead of taken as an instance argument;
* `kernel_conv_comm` is `kernel_conv` with the factors commuted, because `lem:additivity`'s
  reviewed statement writes the cascade law as `μ_{r,t} = μ_{s,t} ∗ μ_{r,s}` and a node
  statement is not rewritten to suit a lemma;
* `fourierCos_kernel_mul_comm` likewise;
* `kernel_transform_pos` is `lem:nonvanishing`'s own declaration, `SpatialLine.nonvanishing`,
  applied. Chapters 5 and 6 do **not** stand apart from chapter 4: `lem:additivity`,
  `cor:monotonicity`, `cor:smoothed-transmittance` and `lem:covariance-fourier` all consume the
  nonvanishing node and the uniqueness clause of the representation, and the import of
  `SpatialLine.Nonvanishing` now records that. It corrects `SKELETON.md` F4.

The sixty-line proof this file carried for `kernel_transform_pos` — the least-zero argument on
`[s,t]` with joint continuity of `(s,t) ↦ μ̂_{s,t}(ω)` at the end — is therefore gone; the
surviving proof of the same statement is in `Nonvanishing.lean`, and it is the blueprint's.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The representation, at the level of the family -/

/-- **`lem:convolution-representation`, existence, read over the whole index set**: a family
satisfying (A1)-(A5) *is* a kernel family, for a kernel family assembled pairwise.

`representation_existsUnique` produces one measure per admissible pair; every statement of
chapters 5 to 7 quantifies over a family `μ` and carries `IsKernelFamily Fam.Φ μ` as a
hypothesis, which is right for a lemma but leaves the *existence* unstated. This supplies it
(fidelity review R18), so that `thm:main-characterization`'s necessity direction can conclude
the representation rather than assume it.

The choice is `Classical.choose` at each pair, read only under `dif_pos` with the existence
proof in hand, and it loses nothing: `representation_existsUnique` is a `∃!`, so any two
kernel families of one `Fam` agree on the admissible pairs. Off them the value is `δ₀`, which
no statement of the development reads. -/
theorem exists_kernelFamily (Fam : PreCascadeCore) (hpos : IsPositive Fam.Φ) :
    ∃ μ : ℝ → ℝ → Measure ℝ, IsKernelFamily Fam.Φ μ := by
  classical
  refine ⟨fun s t => if h : 0 ≤ s ∧ s ≤ t then
    (representation_existsUnique Fam.Φ Fam.translation hpos Fam.unit_mass h.1 h.2).choose
    else Measure.dirac 0, ?_, ?_⟩
  · intro s t hs hst
    rw [dif_pos ⟨hs, hst⟩]
    exact (representation_existsUnique Fam.Φ Fam.translation hpos Fam.unit_mass
      hs hst).choose_spec.1.1
  · intro s t hs hst f
    rw [dif_pos ⟨hs, hst⟩]
    exact (representation_existsUnique Fam.Φ Fam.translation hpos Fam.unit_mass
      hs hst).choose_spec.1.2 f

/-! ## What the representation's uniqueness clause gives -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **(A3) through uniqueness**: the kernels are symmetric. This is the rider
`representation_symmetric` of `lem:convolution-representation`, read at the form chapters 5 and
6 use: the `IsProbabilityMeasure` instance comes from `IsKernelFamily.isProbability` rather than
from the caller. -/
theorem kernel_symmetric (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsSymmetric (μ s t) :=
  haveI := hker.isProbability s t hs hst
  isSymmetric_kernel hker hs hst

/-- **(A6) through uniqueness**: the cascade law at the level of measures, with the factors in
the order `lem:additivity`'s statement fixes. -/
theorem kernel_conv_comm (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) : μ r t = (μ s t) ∗ (μ r s) := by
  haveI := hker.isProbability r s hr hrs
  haveI := hker.isProbability s t (hr.trans hrs) hst
  rw [kernel_conv hker hr hrs hst, Measure.conv_comm]

/-- **(ND) at the level of measures**: strictly below the diagonal the kernel is not `δ₀`. -/
theorem kernel_ne_dirac (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : μ s t ≠ Measure.dirac 0 := by
  intro hcon
  refine hnd s t hs hst ?_
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext_iff.mpr ?_
  refine (hker.conv s t hs hst.le f).trans ?_
  rw [hcon, mconv_dirac_zero]
  simp

/-! ## The transform along the cascade -/

/-- `μ̂_{t,t} = 1`. -/
lemma fourierCos_kernel_diag (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) (ω : ℝ) :
    fourierCos (μ t t) ω = 1 := by
  rw [kernel_diag hker ht, fourierCos_dirac_zero]

/-- **The transform is multiplicative along the cascade**, with the factors in the order the
chapter-5 statements read them. -/
theorem fourierCos_kernel_mul_comm (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (μ r t) ω = fourierCos (μ s t) ω * fourierCos (μ r s) ω := by
  rw [fourierCos_kernel_mul hker hr hrs hst ω, mul_comm]

/-! ## Joint continuity of the transform, from (A7) -/

/-- The slice `t ↦ μ̂_{0,t}(ω)` of the joint continuity, the one every later chapter uses. -/
lemma continuousOn_fourierCos_kernel_zero (hker : IsKernelFamily Fam.Φ μ) (ω : ℝ) :
    ContinuousOn (fun t => fourierCos (μ 0 t) ω) (Ici 0) := by
  have hmap : MapsTo (fun t : ℝ => ((0:ℝ), t)) (Ici 0) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    fun t ht => ⟨le_rfl, ht⟩
  exact (continuousOn_fourierCos_kernel hker ω).comp
    ((continuous_const.prodMk continuous_id).continuousOn) hmap

/-! ## `lem:nonvanishing`, the nonvanishing clause -/

/-- **The transform of a kernel is strictly positive at every frequency** — `lem:nonvanishing`,
applied at the hypotheses chapters 5 and 6 carry. The node's own declaration is
`SpatialLine.nonvanishing` in `SpatialLine/Nonvanishing.lean`; this is the name the later
chapters cite it by. -/
theorem kernel_transform_pos (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ℝ) : 0 < fourierCos (μ s t) ω :=
  nonvanishing Fam μ hker hs hst ω

end SpatialLine
