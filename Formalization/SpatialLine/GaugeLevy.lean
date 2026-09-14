/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Gauge
import SpatialLine.Increments

/-!
# `prop:canonical-gauge`, closed

Blueprint: `blueprint/src/parts/06-covariance.tex`, `prop:canonical-gauge`.

Wave 1 left this node one application wide. `SpatialLine/Gauge.lean` proved
`canonical_gauge_of_levy`, which produces the gauge and the similarity form `eq:gauge` from
`IsSymLevyExponent (exponent (μ 0 1))` **as a hypothesis** — the specification-as-hypothesis
move, taken because the only clause of the node that waited on anything was `F ∈ LEₛ`, which is
`thm:increments-levy` at `(0,1)`. Wave 2 proved that theorem, so the node closes here by
supplying the hypothesis.

The file exists rather than the theorem going into `SpatialLine/Gauge.lean` only because of the
import graph: `Gauge.lean` sits above `Rigidity.lean` and knows nothing of the null-array
development, and this is the lowest file that sees both.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **`prop:canonical-gauge`, the gauge and the similarity form `eq:gauge`.**

Reading: `χ` is produced existentially, with the four properties the article uses — it fixes
`0`, is a strictly increasing surjection of `[0,∞)`, intertwines the action with
multiplication, and straightens the accumulated exponent to a dilate of `F := G(1,·)`.
It is also **normalised**, `χ 1 = 1` (fidelity review R17): the gauge is the inverse of the
orbit coordinate `λ ↦ S_λ 1`, which fixes `1`, so the normalisation that
`thm:main-characterization`'s uniqueness clause quantifies over is a property of the gauge this
node builds rather than a hypothesis a reader has to arrange.
`F ∈ LEₛ` and `F ≢ 0` are the last two clauses; the node's further riders (`F` even, continuous,
`F(0) = 0`, with the pair `(a,ν)`) are `nonvanishing_exponent` and the definition of
`IsSymLevyExponent`, and are not restated.

Also stated: `lam ↦ S lam t` is strictly increasing for every `t > 0`, which the node asserts and
which `thm:main-characterization`'s uniqueness clause uses.

`#print axioms` reduces to Lean core: the Lévy clause is `increments_levy`, whose null-array
limit is proved outright, and the trust boundary is spent only by the *infinite-divisibility*
sentence of `thm:increments-levy`, which this node does not use. -/
theorem canonical_gauge (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    (∀ t : ℝ, 0 < t → StrictMonoOn (fun lam => S lam t) (Ioi 0)) ∧
      ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
        χ 1 = 1 ∧
        (∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t) ∧
        (∀ t ω : ℝ, 0 ≤ t → exponent (μ 0 t) ω = exponent (μ 0 1) (χ t * ω)) ∧
        IsSymLevyExponent (exponent (μ 0 1)) ∧
        (∃ ω : ℝ, exponent (μ 0 1) ω ≠ 0) :=
  canonical_gauge_of_levy Fam μ hker hnd S hcov
    (increments_levy Fam μ hker le_rfl zero_le_one)

end SpatialLine
