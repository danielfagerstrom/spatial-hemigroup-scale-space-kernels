/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Exponent

/-!
# `def:cascade-family`: the axioms, as a structure on `L¹(ℝ)`

Blueprint: `blueprint/src/parts/03-axioms.tex`, `def:cascade-family`.

The primitive object of the article. This is the only file in the development where an error is
silent — a mis-stated axiom makes the theorems vacuous or false rather than unprovable — so each
field is the blueprint clause and not a convenient variant, and `prop:two-members` is the guard
against that: the specification is checked against two models known independently to satisfy the
mathematics.

twin: `Hemigroup.CascadeCore` / `Hemigroup.IsScaleCovariant` / `Hemigroup.CascadeFamily`,
identical except that **(A3) reads reflection symmetry** where the causal (A3) read causal
support, and that the ambient space is `L¹(ℝ)` rather than `L¹` of a half-line. TWINS.md calls
this the strongest structural candidate for `ScaleSpaceCore`: a core carrying (A1), (A2),
(A4)–(A8) and (ND) with the third axiom a parameter.

## Fidelity notes

* **(A1)** is carried by the type: `X →L[ℝ] X` *is* "bounded linear operator on `X`".
* **(A2)** and **(A3)** are stated pointwise in `f`, which is the same as the blueprint's
  operator identity `Φ T_a = T_a Φ`, `Φ R = R Φ`.
* **(A3)** needs no a.e. hedging, unlike its causal twin: `reflL1` is an operator on `L¹`, so
  the identity is between elements of `L¹` and the a.e. quantifier is inside the type. That the
  causal (A3) had to be stated a.e. — `Operator.lean`'s note there — is an artefact of causality
  being a property of a *representative*, and it does not recur here.
* **(A5)** is stated on the positive cone only, as the blueprint states it. It happens to hold
  on all of `X` for a convolution operator, but strengthening the field would *narrow* the
  structure, and a narrower specification is a different theorem.
* **(A8)** carries the action `S` as data together with the requirement that each `S lam` be an
  increasing bijection of `[0,∞)`; the blueprint quantifies `S` existentially, and bundling it is
  the standard Lean rendering of that.
* **`IsScaleCovariant`** is stated relative to a set `G` of admissible dilation ratios, as in
  Paper I, so that the pyramid module (`spatial-hemigroup-pyramids`) can instantiate `G = q^ℤ`
  without restating the core. `CascadeFamily` demands `G = Ioi 0`. Unlike Paper I's, it takes the
  *operator family* rather than a `CascadeCore`: it only ever uses `Fam.Φ`, and the negative
  result below needs covariance of a family that is not a `CascadeCore`.

## Positivity is split off, and why

`prop:no-positivity-no-classification` exhibits a family satisfying **(A1)–(A3), (A5)–(A8) and
(ND) but not (A4)**, and asks when (A4) holds. That statement cannot be made against a structure
that bundles (A4), so the axioms other than positivity are `PreCascadeCore`, positivity is the
predicate `IsPositive` on an operator family, and `CascadeCore extends PreCascadeCore` with the
positivity field. Every field name of `def:cascade-family` is still reachable from a
`CascadeCore`, and the blueprint node is unchanged; what changes is that the article's own
negative result is now expressible. Paper I did not need the split because it proves no such
result, and the `ScaleSpaceCore` lift should adopt this shape rather than Paper I's.

## The kernel family is a hypothesis, not a definition

Paper I defines `CascadeCore.repr` by choice from its *proved* representation theorem. This
library takes the hypothesis instead: `IsKernelFamily` names a family of kernels representing
the operators, and every downstream statement quantifies over any `μ` meeting the
specification, which loses nothing because `lem:convolution-representation` asserts existence
*and* uniqueness. That node is now proved -- wave 1 of the proving campaign, 2026-09-09,
`SpatialLine.representation_existsUnique` and its two riders -- so `repr` could be introduced
by choice at any time; it has not been, because nothing consumes it and the hypothesis form
keeps the statements of chapters 5-7 free of a definition. (The sentence this paragraph
replaces said the node was `sorry`, which stopped being true with wave 1; corrected by wave
2's merge, 2026-09-09.)
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-- **`def:cascade-family` without (A4) and without (ND)**: exactly (A1)–(A3) and (A5)–(A7).

This is the axiom list `lem:nonvanishing` states its hypotheses as, and — once the representation
is in hand as `IsKernelFamily` — the list `lem:additivity`, `thm:increments-levy` and
`cor:smoothed-transmittance` state theirs as too. Positivity and nondegeneracy are separate
predicates so that each node can carry the hypotheses the blueprint gives it and no more; see the
module docstring for why `prop:no-positivity-no-classification` forces the split. -/
structure PreCascadeCore where
  /-- The operators, indexed by ordered pairs of scales. **(A1)** is the type. -/
  Φ : ℝ → ℝ → (X →L[ℝ] X)
  /-- **(A2)** Translation covariance. -/
  translation : ∀ s t, 0 ≤ s → s ≤ t → ∀ a f, Φ s t (transL1 a f) = transL1 a (Φ s t f)
  /-- **(A3)** Reflection symmetry — the one axiom that differs from the causal system. -/
  reflection : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, Φ s t (reflL1 f) = reflL1 (Φ s t f)
  /-- **(A5)** Unit mass, on the positive cone.

  The restriction to `IsNonneg f` is the blueprint's own — (A5) is stated on the cone — and it is
  where `representation_existsUnique` reads it. **Do not "strengthen" it to all of `X`**: the
  approximants `ρ_ε` of that proof are nonnegative, so the restricted field loses nothing, while
  a strengthened field would exclude families the axioms admit (review 2026-09-09, R31). -/
  unit_mass : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f →
    ∫ x, ((Φ s t f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x
  /-- **(A6)** The diagonal is the identity. -/
  diag : ∀ t, 0 ≤ t → Φ t t = ContinuousLinearMap.id ℝ X
  /-- **(A6)** The cascade law — a hemigroup, not a semigroup: no dependence on `t - s`. -/
  cascade : ∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → (Φ s t).comp (Φ r s) = Φ r t
  /-- **(A7)** Continuity in the parameters, into `X`. -/
  continuous : ∀ f : X, ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 f)
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}

/-- **(A4)**, as a predicate on an operator family. -/
def IsPositive (Φ : ℝ → ℝ → (X →L[ℝ] X)) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f → IsNonneg (Φ s t f)

/-- **(ND)**, as a predicate on an operator family. -/
def IsNondegenerate (Φ : ℝ → ℝ → (X →L[ℝ] X)) : Prop :=
  ∀ s t, 0 ≤ s → s < t → Φ s t ≠ ContinuousLinearMap.id ℝ X

/-- **`def:cascade-family`, (A1)–(A7) and (ND)**: everything in the definition that does not
mention the covariance group.

The split from (A8) is Paper I's and is not cosmetic: (A8) is the clause the pyramid module
varies, and everything Chapters 4 and 5 prove lives here — the convolution representation and
the nonvanishing of the transforms use (A1)–(A7) and no covariance at all. -/
structure CascadeCore extends PreCascadeCore where
  /-- **(A4)** Positivity. -/
  positive : IsPositive toPreCascadeCore.Φ
  /-- **(ND)** Nondegeneracy. -/
  nondegenerate : IsNondegenerate toPreCascadeCore.Φ

/-- **(A8), relative to a set `G` of admissible dilation ratios.**

twin: `Hemigroup.IsScaleCovariant`, with the first argument the operator family rather than the
core — the causal version uses only `Fam.Φ`, and the negative result of Chapter 3 needs
covariance of a family that is not a `CascadeCore`. `G` is an arbitrary set rather than a
subgroup: the axiom is a condition *for each* `lam`, and which sets `G` can occur is a theorem,
not part of the statement. -/
structure IsScaleCovariant (Φ : ℝ → ℝ → (X →L[ℝ] X)) (G : Set ℝ) (S : ℝ → ℝ → ℝ) : Prop where
  /-- Each `S lam` maps `[0,∞)` into itself, ... -/
  S_mapsTo : ∀ lam, 0 < lam → lam ∈ G → MapsTo (S lam) (Ici 0) (Ici 0)
  /-- ... increasingly, ... -/
  S_strictMonoOn : ∀ lam, 0 < lam → lam ∈ G → StrictMonoOn (S lam) (Ici 0)
  /-- ... and onto. -/
  S_surjOn : ∀ lam, 0 < lam → lam ∈ G → SurjOn (S lam) (Ici 0) (Ici 0)
  /-- The intertwining itself. -/
  scale : ∀ (lam : ℝ) (hlam : 0 < lam), lam ∈ G → ∀ s t, 0 ≤ s → s ≤ t →
    (dilL1 hlam).comp (Φ s t) = (Φ (S lam s) (S lam t)).comp (dilL1 hlam)

/-- **`def:cascade-family`**: a symmetric cascade measurement family — the core, with (A8)
demanded for every `lam > 0`. -/
structure CascadeFamily extends CascadeCore where
  /-- The scaling action `S_lam` of (A8), carried as data. -/
  S : ℝ → ℝ → ℝ
  /-- **(A8)** Scale covariance, under the full dilation group. -/
  covariant : IsScaleCovariant toCascadeCore.Φ (Ioi 0) S

/-- **`μ` represents `Fam`**: each operator is convolution by the probability measure `μ s t`.

This is the conclusion of `lem:convolution-representation` turned into a hypothesis, so that
Chapters 5–7 can be stated before it is proved. The conclusion `Φ f = μ * f` is read at the
level of representatives — the two sides are elements of `L¹`, so a.e. equality of
representatives is equality in `X`, and stating it this way avoids carrying an
`IsFiniteMeasure` instance argument through every signature. -/
structure IsKernelFamily (Φ : ℝ → ℝ → (X →L[ℝ] X)) (μ : ℝ → ℝ → Measure ℝ) : Prop where
  /-- Each kernel is a probability measure. -/
  isProbability : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)
  /-- Each operator is convolution by its kernel. -/
  conv : ∀ s t, 0 ≤ s → s ≤ t → ∀ f : X,
    ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv (μ s t) (f : ℝ → ℝ)

/-- The kernels are symmetric — the rider (A3) adds to the representation. -/
def IsSymmetricKernelFamily (μ : ℝ → ℝ → Measure ℝ) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)

end SpatialLine
