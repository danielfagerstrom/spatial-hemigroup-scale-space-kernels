/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Basic
import Mathlib.Data.ENat.Lattice

/-!
# Sign changes, variation diminution, and the Pólya frequency exponents, defined

Blueprint: `blueprint/src/parts/13-noncreation.tex` — `prop:polya-frequency` and
`thm:scale-monotone-noncreation`. Nothing here is a blueprint node.

**Definitions only**, and the file imports `SpatialLine.Basic` — `mconv` is all it needs of this
development — together with Mathlib's lattice structure on `ℕ∞`, which the two counts below take
a supremum and an infimum in.
The four notions are what ledger **A21** and **A22** are stated in
(`SpatialLine/Interfaces.lean`), and an interface file that reaches Chapter 11's generator to
read them would carry the whole of Chapters 8–11 into the release export of the characterization
theorem (ADR-0005). It was called `SpatialLine.Variation` until 2026-09-14; the theorems that
stood beside these definitions were already elsewhere.

## `S^-` by alternation, and "in the essential sense"

`prop:polya-frequency` writes `S^-(g)` for "the number of sign changes of `g` on `ℝ`, in the
essential sense", which is a definition the article does not spell out. The reading formalised
here is the standard one, in the form that avoids deleting zeros from a sequence: **`g` has at
least `n` sign changes iff there are `n+1` points in increasing order at which `g` is nonzero
with strictly alternating signs.** `signChanges` is the supremum of such `n` in `ℕ∞`; a
function of one sign has `0`, and the zero function has `0` because it has no alternations at
all.

"In the essential sense" is then the infimum over representatives: `signChangesAE g` is the
least `signChanges h` over `h =ᵐ[volume] g`. That is what makes the notion meaningful for a
density, which is only defined up to a null set, and it is the reading under which
`prop:polya-frequency`(2) is a statement about `u(t,\cdot)` rather than about a choice of
representative for it.

## Variation diminution is the notion consumed, not total positivity

`prop:polya-frequency`(1) is an equivalence between "the family has Pólya frequency kernels, so
that convolution with `μ_{0,t}` is variation-diminishing" and a form for `F`. What the proofs
use is the variation-diminishing property; that it coincides with total positivity is ledger
**A22**, an interface, so no notion of total positivity is defined here. The `g` the definition
quantifies over is the node's "every integrable or bounded `g`".

## The Pólya frequency exponents are parametrised by `λ_i = 1/θ_i`

`prop:polya-frequency`(1) writes `F(ω) = aω^2 + \sum_i\log(1 + ω^2/θ_i^2)` with `θ_i > 0` and
`\sum_iθ_i^{-2} < ∞`, a countable — possibly finite — family. `IsPolyaExponent` indexes by `ℕ`
and carries `λ_i = 1/θ_i ≥ 0` instead: a finite family is then the case `λ_i = 0` for large `i`,
whose factors contribute `\log 1 = 0`, and the summability condition is `\sum λ_i^2 < ∞`, which
is A21's own condition on its own parameters. Nothing is lost and the finite case needs no
separate clause; repetition of a `θ` is free, which is the node's "integer-weighted" Thorin
atoms.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## Sign changes -/

/-- `g` has at least `n` sign changes: `n+1` points in increasing order at which `g` is nonzero
with strictly alternating signs. The sign `ε` fixes which of the two alternating patterns. -/
def HasAlternations (g : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ (x : Fin (n + 1) → ℝ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ StrictMono x ∧
    ∀ i : Fin (n + 1), 0 < ε * (-1) ^ (i : ℕ) * g (x i)

/-- **`S^-(g)`**, the number of sign changes of `g`, valued in `ℕ∞`. -/
noncomputable def signChanges (g : ℝ → ℝ) : ℕ∞ :=
  ⨆ n ∈ {n : ℕ | HasAlternations g n}, (n : ℕ∞)

/-- **`S^-(g)` in the essential sense**: the least number of sign changes of a representative
of `g`. -/
noncomputable def signChangesAE (g : ℝ → ℝ) : ℕ∞ :=
  ⨅ h ∈ {h : ℝ → ℝ | h =ᵐ[volume] g}, signChanges h

/-! ## Variation diminution -/

/-- **Convolution by `μ` is variation-diminishing**: `S^-(μ * g) \le S^-(g)` for every
integrable or bounded `g`. -/
def IsVariationDiminishing (μ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℝ, AEStronglyMeasurable g volume →
    (Integrable g volume ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C) →
      signChangesAE (mconv μ g) ≤ signChangesAE g

/-- **Convolution by `μ` is variation-diminishing in the ordinary sense**: `S^-(μ * g) \le
S^-(g)` for every *measurable* integrable or bounded `g`, with the ordinary sign-change count on
both sides.

This is Karlin's own reading — Ch. 5, Thm. 3.1(i) counts `S^-` on a bounded Borel function — and
it is the form ledger **A21** is admitted at. It is **not** implied by `IsVariationDiminishing`,
nor does it imply it by monotonicity alone: `signChangesAE \le signChanges` points the wrong way
on the left of the inequality. What carries the ordinary form to the essential one is the
measurable-hull lemma of `SpatialLine/MeasurableHull.lean` — the infimum defining `signChangesAE`
is already attained along measurable representatives — and the passage is
`isVariationDiminishing_of_ord` (fidelity review row **R14**, proved 2026-09-11). -/
def IsVariationDiminishingOrd (μ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Measurable g →
    (Integrable g volume ∨ ∃ C : ℝ, ∀ x, |g x| ≤ C) →
      signChanges (mconv μ g) ≤ signChanges g

/-! ## The Pólya frequency exponents -/

/-- **`prop:polya-frequency`(1)'s form**: `F(ω) = aω^2 + \sum_i\log(1 + λ_i^2ω^2)` with
`a \ge 0`, `λ_i \ge 0` and `\sum_iλ_i^2 < ∞` — Gaussian jitter together with integer-weighted
symmetric Thorin atoms at `θ_i = 1/λ_i`.

See the module docstring for why the parametrisation is by `λ_i` and not by `θ_i`. -/
def IsPolyaExponent (F : ℝ → ℝ) : Prop :=
  ∃ (a : ℝ) (lam : ℕ → ℝ), 0 ≤ a ∧ (∀ i, 0 ≤ lam i) ∧ Summable (fun i => lam i ^ 2) ∧
    ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + lam i ^ 2 * ω ^ 2)

end SpatialLine
