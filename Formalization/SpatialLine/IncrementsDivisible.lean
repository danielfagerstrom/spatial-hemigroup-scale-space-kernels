/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Increments
import SpatialLine.ConvolutionVariation
import SpatialLine.TransformUniqueness
import SpatialLine.Pairing
import SpatialLine.Cascade

/-!
# `thm:increments-levy`'s divisibility clause, at the law

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`.

The node's closing sentence is that every kernel `μ_{s,t}` **is** the `n`-fold convolution of a
symmetric probability measure, for every `n ≥ 1`. `increments_levy_infinitely_divisible` states
that at the *transform* — there is a symmetric probability measure whose cosine transform is the
`n`-th root — and its docstring gives the reason: Mathlib has no convolution power of measures,
and the article consumes the fact through transforms anyway.

The first half of that reason is true and the second does not follow from it (fidelity review
R35). The convolution power is four lines of recursion, and the last step of the blueprint's own
proof — that the `n`-fold convolution *is* `μ_{s,t}`, by `prop:fourier-uniqueness` — is then one
application of `fourier_uniqueness`. So the law-level statement is stated here, and the
transform-level one is kept: it is the form every consumer uses, and it is what the recursion
below is proved against.

**What this changes in the node's cost.** `prop:fourier-uniqueness` *is* now spent, by this
declaration, and it is Lean core (`SpatialLine.fourier_uniqueness`), so the trust boundary is
unchanged: `increments_levy_id_measure` prints exactly what
`increments_levy_infinitely_divisible` prints, ledger **A1** with **A3**'s converse.
-/

namespace SpatialLine

open MeasureTheory

/-- The `n`-fold convolution power of a measure, with `convPow ρ 0 = δ₀` — the unit of
convolution, so that the recursion `convPow ρ (n+1) = convPow ρ n ∗ ρ` needs no side condition.
Mathlib has `Measure.conv` but no power of it. -/
noncomputable def convPow (ρ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | (n + 1) => (convPow ρ n) ∗ ρ

instance instIsProbabilityMeasureConvPow (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ∀ n, IsProbabilityMeasure (convPow ρ n)
  | 0 => by unfold convPow; infer_instance
  | (n + 1) => by
      unfold convPow
      haveI := instIsProbabilityMeasureConvPow ρ n
      infer_instance

/-- A convolution power of a symmetric measure is symmetric. -/
theorem isSymmetric_convPow {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hsym : IsSymmetric ρ) :
    ∀ n, IsSymmetric (convPow ρ n)
  | 0 => by
      unfold convPow
      rw [IsSymmetric]
      simp [measurable_neg]
  | (n + 1) => by
      unfold convPow
      haveI := instIsProbabilityMeasureConvPow ρ n
      exact isSymmetric_conv (isSymmetric_convPow hsym n) hsym

/-- The cosine transform of a convolution power is the power of the cosine transform. -/
theorem fourierCos_convPow {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hsym : IsSymmetric ρ)
    (ω : ℝ) : ∀ n, fourierCos (convPow ρ n) ω = (fourierCos ρ ω) ^ n
  | 0 => by unfold convPow; simp [fourierCos_dirac_zero]
  | (n + 1) => by
      unfold convPow
      haveI := instIsProbabilityMeasureConvPow ρ n
      rw [fourierCos_conv (isSymmetric_convPow hsym n) hsym, fourierCos_convPow hsym ω n,
        pow_succ]

/-- **`thm:increments-levy`, infinite divisibility, at the law.** Every kernel of a family
satisfying (A1)-(A3) and (A5)-(A7) *is* the `n`-fold convolution of a symmetric probability
measure, at every `n ≥ 1`.

This is the node's closing sentence as the node states it: `μ_{s,t}` is infinitely divisible,
not merely the carrier of a transform with an `n`-th root. The proof is
`increments_levy_infinitely_divisible` for the root, `fourierCos_convPow` for the transform of
the power, and `prop:fourier-uniqueness` to identify the two measures — the last step of the
blueprint's own proof, which the transform-level statement stopped one line short of.

`fourier_uniqueness` compares characteristic functions, so the two symmetry facts are what
carry the cosine transforms across: `kernel_symmetric` for `μ_{s,t}` and `isSymmetric_convPow`
for the power. `#print axioms` is unchanged from the transform-level statement, ledger **A1**
with **A3**'s converse, `fourier_uniqueness` being Lean core. -/
theorem increments_levy_id_measure (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) (hn : 0 < n) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ IsSymmetric ρ ∧ μ s t = convPow ρ n := by
  obtain ⟨ρ, hprob, hsym, hfc⟩ :=
    increments_levy_infinitely_divisible Fam μ hker hs hst n hn
  haveI := hprob
  haveI := hker.isProbability s t hs hst
  haveI := instIsProbabilityMeasureConvPow ρ n
  refine ⟨ρ, hprob, hsym, ?_⟩
  refine fourier_uniqueness fun ω => ?_
  rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker hs hst),
    charFun_eq_fourierCos_of_symmetric (isSymmetric_convPow hsym n),
    fourierCos_convPow hsym ω n, hfc ω]

end SpatialLine
