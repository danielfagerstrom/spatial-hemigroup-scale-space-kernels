/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Exponent
import SpatialLine.TransformBridge
import SpatialLine.CornerDefs
import SpatialLine.VariationDefs
import SpatialLine.MeasurableHull
import ScaleSpaceCore.PolyaFrequencyClass

/-!
# The cited interfaces this development consumes, as Lean axioms

**This file widens the project's trust base, and it is the only file that does.** Every `axiom`
here is admitted on a page-anchored entry of `blueprint/AXIOMS.md` and named in
`blueprint/trust-boundary.txt`; the CI axiom guard refuses any name the ledger does not back. An
axiom is added here only when a proof in this development *consumes* it — never to record that a
node is `[A]`, which the blueprint's `\statusA` line already does.

Wave 2's merge (2026-09-09) collected the three admitted names here. They had been declared in
four separate files — `InterfacesCh2`, `InterfacesCh5`, `InterfacesCh7`, `InterfacesCh10` —
because the parallel proving worktrees must not edit the same file, and two of those files held
*the same axiom under the same name*. All three names belong to one node,
`prop:fourier-toolbox`, and to two ledger entries, **A1** and **A3**, so one file is the honest
arrangement: the trust boundary is readable in a single screen.

## The nine names

Three of `prop:fourier-toolbox`, listed first, and six admitted later, each with its own section
below: `kernel_regularity_law` (**A8**, **A9**) and `bernstein_completely_monotone` (**A11**)
in wave 3, and in wave 4 `moments_tails_criterion` (**A13**), `moments_tails_divergence`
(**A14**, narrowed), `polyaExponent_of_variationDiminishing` and
`variationDiminishing_of_polyaExponent` (**A21** and **A22**, spent only together). The
consumers of all nine are on `blueprint/trust-boundary.txt` and in the guard's module docstring,
which is where the count is checked against `#print axioms` rather than asserted.

* `fourier_toolbox_levy_converse` — `prop:fourier-toolbox`(3), the **converse** direction of the
  symmetric Lévy–Khintchine representation, ledger **A3**: every symmetric Lévy pair defines a
  continuous negative definite function. Spent by `profile_integrability_mem`,
  `increments_levy_infinitely_divisible` and `exists_isSymmetric_of_isSymLevyExponent`.

* `fourier_toolbox_bochner_symm` — `prop:fourier-toolbox`(1), Bochner's theorem in its symmetric
  form, ledger **A1**, **as the forward implication only** (see below). Spent by
  `increments_levy_infinitely_divisible` and by `exists_isSymmetric_of_isSymLevyExponent`, and
  through the latter by `main_construction`.

* `fourier_toolbox_levy_unique` — `prop:fourier-toolbox`(3), the **uniqueness** clause, ledger
  **A3**: two symmetric Lévy pairs with the same exponent have the same Gaussian coefficient and
  the same Lévy measure. Spent by `eqOn_maternProfile_of_exponent`, the backward direction of
  `thm:matern`(1) ⟺ (2) and (1) ⟺ (3).

`blueprint/trust-boundary.txt` predicted that A3 would split into two Lean names, one for the
converse and one for uniqueness, as the causal development's A17/A18 did. It has, and A1 has
supplied the third; `prop:fourier-toolbox` contributed no fourth name, and every later name came
from another node.

## Why the Bochner axiom is an implication and not the equivalence

Both consumers spend Bochner in one direction only: from the three conditions on `φ` to a
symmetric probability measure whose cosine transform is `φ`. The reverse direction — a symmetric
probability law's transform is continuous, positive definite and `1` at the origin — is
elementary and is proved here, from the identification of `fourierCos` with `charFun` on a
symmetric measure and the expansion of the positive-definiteness double sum as the integral of
`‖∑ⱼ cⱼ e^{iωⱼx}‖²`. So the axiom is admitted as the implication actually consumed, and the
equivalence the reviewed skeleton states is available beside it as the theorem
`fourier_toolbox_bochner_symm_iff`, which spends the axiom for one leg and nothing for the
other. This narrows the trust base by exactly the half of A1 the development can prove, and the
merge did it rather than leaving it to a later review (wave 2, 2026-09-09).

The hypotheses are otherwise `Skeleton.fourier_toolbox_bochner_symm`'s verbatim.

## What the citations carry, and what they do not

Ledger **A1** (@sato1999levy Prop. 2.5, pp. 8–9: (i) on p. 8 with the symmetric rider from (ii),
p. 8, and (v), p. 9; corroborated at @feller2009introduction Vol. 2, §XIX.2, p. 622) states the
equivalence for a real `φ`. It does **not** carry the sign convention: the source's
characteristic function is `∫ e^{i⟨z,x⟩} μ(dx)`, opposite to this article's (2.1), which is
immaterial because the measure produced is symmetric and its transform therefore real — the
bridge is `charFun_eq_fourierCos_of_symmetric`. Nor does it carry the reduction of "real" to
"even", which is elementary.

**The anchor is two pages, not one** (fidelity review 2026-09-10, F6-6). Prop. 2.5(**v**),
`\tilde μ̂(z) = μ̂(−z) = conj μ̂(z)`, is printed on p. 9; p. 8 carries (i) and (ii). The symmetric
rider runs through both: a real transform gives `μ̂ = conj μ̂ = \tilde μ̂` by (v), and it takes
(ii), the uniqueness of the transform, to conclude `μ = \tilde μ`. (ii) is the statement the
proving campaign **retired as A5** and proves here from Mathlib's `Measure.ext_of_charFun`, so
this axiom's page reach touches a fact the ledger deliberately stopped charging for — harmless,
but it is why the anchor is pp. 8–9. Note also that the axiom asks `Continuous φ` on all of `ℝ`
where Sato asks continuity **at `z = 0`** only, and asks it of a real `φ` where the source
allows a complex one: the hypotheses are stronger than the source's twice over, which is the
safe direction.

Ledger **A3** (@sato1999levy Thm. 8.1(i)–(iii), pp. 37–38) states existence, the converse and
uniqueness for the Lévy–Khintchine representation. It does **not** carry the folding of a
symmetric Lévy measure on `ℝ ∖ {0}` to a measure on `(0,∞)`; that reduction is the blueprint's
own, written out under "The folding convention", and is built into `SymLevyPair`.

**Where the folding reduction sits, exactly** (fidelity review R37). "Built into `SymLevyPair`"
understates it. Chapter 2's folding convention is prose and not a node, so it is not proved
anywhere; and because the two axioms below *quantify over* `SymLevyPair`, the reduction is
**inside** their statements rather than beside them. Admitting them therefore widens the trust
base by it, not merely by Sato's theorem: what is taken on trust is "every folded pair defines a
continuous negative definite function", where the citation reads "every Lévy pair on the
punctured line does". The reduction is elementary — a symmetric Lévy measure and its image on
the ray carry the same `∫(1 − cos ωx)`, and the two integrability conditions correspond — and
proving it beside the axioms would need the punctured-line representation as a second definition,
with the axioms restated on it. That is the honest alternative and it has not been taken; the
excess is declared here and at **A3** in `blueprint/AXIOMS.md` instead.

Proving campaign: chapter 2 (wave 1), chapters 5, 7 and 10 (wave 2); collected here by wave 2's
merge (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory

/-! ## Ledger A3 — the symmetric Lévy–Khintchine representation -/

/-- **`prop:fourier-toolbox`(3), the converse** — cited interface, ledger **A3**
(@sato1999levy Thm. 8.1(i)–(iii), pp. 37–38).

Every symmetric Lévy pair defines a continuous negative definite function. This is the direction
`thm:increments-levy` and `thm:main-characterization`(⇐) consume, and the direction that has to
be spent to know that a constructed exponent is the exponent of a probability measure at all.

What A3 does **not** carry is the folding of a symmetric Lévy measure on `ℝ ∖ {0}` to a measure
on `(0,∞)`; that reduction is the blueprint's own. It is *not* stated beside this axiom
(fidelity review R37): the axiom quantifies over `SymLevyPair`, whose Lévy measure is already
folded, so the reduction sits **inside** the statement and is part of what admitting the name
takes on trust. See the module docstring for what proving it beside the axiom would cost.

**Only one of the five fields needs the citation** (fidelity review 2026-09-10, F6-5;
note-only — the axiom is *not* changed). `IsSymNegDef` is a five-field structure, and four of
its fields are elementary consequences of the *form* of `SymLevyPair.exponent` rather than of
Sato's theorem. `continuous` is already **proved in this development**, as
`SpatialLine.SymLevyPair.continuous_exponent` (`SpatialLine/ExponentContinuity.lean`), by dominated
convergence against the truncation bound, with `SymLevyPair.exponentL_ne_top`
(`SpatialLine/Growth.lean`) guarding the `.toReal`; and `even`, `nonneg` and `map_zero` follow
from `ω ↦ 1 − cos(ωx)` being even, nonnegative and zero at the origin, together with `a ≥ 0`.
What genuinely needs Sato Thm. 8.1(iii) is `exp_posDef`, and only that: `e^{−τψ}` is the
characteristic function of the law of the triplet `τ·(A, ν, 0)` — which is **Cor. 8.3, p. 38** —
and a characteristic function is positive definite, which is **Prop. 2.5(i), p. 8**, A1's page,
though this development proves that half itself (`isPositiveDefinite_fourierCos`). So the name's
page reach is wider than the pinned pp. 37–38, and the axiom is not minimal: it could be
narrowed to the `exp_posDef` field, as A1 was narrowed to its forward implication and A11 to its
existence equivalence. That narrowing is a separate decision and has not been taken; it would
change the type and every consumer's destructuring, and it buys no page — the boundary would
still carry the name. Recorded at **A3**. -/
axiom fourier_toolbox_levy_converse (P : SymLevyPair) : IsSymNegDef P.exponent

/-- **`prop:fourier-toolbox`(3), uniqueness** — cited interface, ledger **A3**
(@sato1999levy Thm. 8.1(i)–(iii), pp. 37–38).

Two symmetric Lévy pairs with the same exponent have the same Gaussian coefficient and the same
Lévy measure. Equality of the measures is equality on `ℝ`, which is meaningful because both are
`IsFolded` and so determined by their restriction to `(0,∞)`.

This is the direction that turns a *transform* into a *profile*: everything a corner theorem's
backward direction says about `k` comes through it. -/
axiom fourier_toolbox_levy_unique (P Q : SymLevyPair)
    (h : ∀ ω, P.exponent ω = Q.exponent ω) : P.a = Q.a ∧ P.ν = Q.ν

/-! ## Ledger A1 — Bochner's theorem, symmetric form

The axiom is the forward implication; the reverse is proved; the equivalence the reviewed
skeleton states is the bundling theorem at the end of the section. -/

/-- **`prop:fourier-toolbox`(1), the symmetric clause, forward** — cited interface, ledger **A1**
(@sato1999levy Prop. 2.5, pp. 8–9: (i) and (ii) on p. 8, the symmetric rider also using (v),
p. 9; corroborated at @feller2009introduction Vol. 2, §XIX.2, p. 622).

A real function that is continuous, positive definite and takes the value `1` at the origin is
the cosine transform of a symmetric probability measure. This is the whole of A1 that this
development consumes: `increments_levy_infinitely_divisible` and
`exists_isSymmetric_of_isSymLevyExponent` produce a law from an exponent and never read the
other direction, which is `fourier_toolbox_bochner_symm_of_measure` below.

On `blueprint/trust-boundary.txt`; see the module docstring for what A1 carries and what it does
not. -/
axiom fourier_toolbox_bochner_symm (φ : ℝ → ℝ)
    (h : Continuous φ ∧ IsPositiveDefinite (fun ω => (φ ω : ℂ)) ∧ φ 0 = 1) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ fourierCos μ = φ

/-- The cosine transform of a symmetric probability measure is positive definite.

The double sum `∑ⱼ∑ₖ cⱼ conj(cₖ) φ(ωⱼ - ωₖ)` is the integral of `‖∑ⱼ cⱼ e^{iωⱼx}‖²`, once `φ` is
read as the characteristic function — which it is, on a symmetric measure. This is the
elementary half of ledger A1 and it is proved, not cited. -/
theorem isPositiveDefinite_fourierCos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsym : IsSymmetric μ) : IsPositiveDefinite fun ω => ((fourierCos μ ω : ℝ) : ℂ) := by
  intro n ω c
  -- The trigonometric sum whose squared modulus the double sum integrates.
  set g : ℝ → ℂ := fun x => ∑ j, c j * Complex.exp ((ω j : ℂ) * (x : ℂ) * Complex.I) with hg
  -- Each summand of the double sum is a term of the product `g x * conj (g x)`.
  have hterm : ∀ (j k : Fin n) (x : ℝ),
      (c j * Complex.exp ((ω j : ℂ) * (x : ℂ) * Complex.I)) *
        (starRingEnd ℂ) (c k * Complex.exp ((ω k : ℂ) * (x : ℂ) * Complex.I))
        = c j * (starRingEnd ℂ) (c k) *
            Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) := by
    intro j k x
    have hconj : (starRingEnd ℂ) (Complex.exp ((ω k : ℂ) * (x : ℂ) * Complex.I))
        = Complex.exp (-((ω k : ℂ) * (x : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hprod : Complex.exp ((ω j : ℂ) * (x : ℂ) * Complex.I) *
        Complex.exp (-((ω k : ℂ) * (x : ℂ) * Complex.I))
        = Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [map_mul, hconj, ← hprod]
    ring
  -- Hence the double sum of those summands is `‖g x‖²`.
  have hpt : ∀ x : ℝ, ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) *
      Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) = ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have hmul : ((‖g x‖ ^ 2 : ℝ) : ℂ) = g x * (starRingEnd ℂ) (g x) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hmul, hg]
    simp only [map_sum]
    rw [Fintype.sum_mul_sum]
    exact (Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => hterm j k x).symm
  -- Each summand is integrable, being bounded and continuous.
  have hint : ∀ j k : Fin n, Integrable (fun x : ℝ => c j * (starRingEnd ℂ) (c k) *
      Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I)) μ := fun j k =>
    (integrable_charFun_integrand μ (ω j - ω k)).const_mul _
  -- The double sum is the integral of `‖g‖²`, a nonnegative real.
  have hsum : ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * ((fourierCos μ (ω j - ω k) : ℝ) : ℂ)
      = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    calc ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * ((fourierCos μ (ω j - ω k) : ℝ) : ℂ)
        = ∑ j, ∑ k, ∫ x, c j * (starRingEnd ℂ) (c k) *
            Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) ∂μ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, ← charFun_apply_real,
            ← charFun_eq_fourierCos_of_symmetric hsym]
      _ = ∑ j, ∫ x, ∑ k, c j * (starRingEnd ℂ) (c k) *
            Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) ∂μ :=
          Finset.sum_congr rfl fun j _ =>
            (integral_finsetSum _ fun k _ => hint j k).symm
      _ = ∫ x, ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) *
            Complex.exp (((ω j - ω k : ℝ) : ℂ) * (x : ℂ) * Complex.I) ∂μ :=
          (integral_finsetSum _ fun j _ =>
            integrable_finsetSum _ fun k _ => hint j k).symm
      _ = ∫ x, ((‖g x‖ ^ 2 : ℝ) : ℂ) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_complex_ofReal
  rw [hsum]
  exact Complex.zero_le_real.2 (integral_nonneg fun x => by positivity)

/-- **Bochner's theorem, the reverse direction, proved.**

A symmetric probability law's cosine transform is continuous, positive definite and takes the
value `1` at the origin. This is the half of ledger A1 the development does not have to cite,
and separating it is what narrows `fourier_toolbox_bochner_symm` to an implication. -/
theorem fourier_toolbox_bochner_symm_of_measure (φ : ℝ → ℝ)
    (h : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ fourierCos μ = φ) :
    Continuous φ ∧ IsPositiveDefinite (fun ω => (φ ω : ℂ)) ∧ φ 0 = 1 := by
  obtain ⟨μ, hprob, hsym, rfl⟩ := h
  exact ⟨continuous_fourierCos μ, isPositiveDefinite_fourierCos hsym, fourierCos_zero μ⟩

/-- **`prop:fourier-toolbox`(1), the symmetric clause** — the equivalence the reviewed skeleton
states, `Skeleton.fourier_toolbox_bochner_symm`'s type verbatim.

The forward leg is ledger **A1**, admitted as `fourier_toolbox_bochner_symm`; the reverse leg is
`fourier_toolbox_bochner_symm_of_measure` and is proved. Stated so that the blueprint node's
equivalence has a declaration of its own; nothing in this development consumes it. -/
theorem fourier_toolbox_bochner_symm_iff (φ : ℝ → ℝ) :
    (Continuous φ ∧ IsPositiveDefinite (fun ω => (φ ω : ℂ)) ∧ φ 0 = 1)
      ↔ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ fourierCos μ = φ :=
  ⟨fourier_toolbox_bochner_symm φ, fourier_toolbox_bochner_symm_of_measure φ⟩

/-! ## Ledger A8 and A9 — the regularity of a self-decomposable law

Added by wave 3 of the proving campaign (2026-09-09), when `kernel_regularity` first consumed
it. The interface is stated about a *law*, with no scale-space vocabulary in it; the assembly
that checks its hypotheses for the kernels from the origin is
`SpatialLine.kernel_regularity`, and it is `[T]`. -/

/-- **`prop:kernel-regularity`, the interface proper** — cited interfaces, ledger **A8**
(@sato1999levy Thm. 27.13, p. 181: a self-decomposable law that is not a point mass has a
density) and **A9** (@yamazato1978unimodality Thm. 1, p. 523: every law of class L is unimodal).

Unimodality of a *symmetric* law is stated as "the density may be taken even and nonincreasing
on `(0,∞)`", which is the reading the blueprint node fixes; that the mode of a symmetric
unimodal law is the origin is elementary and is part of what the entries do **not** carry.
Evenness together with the monotonicity on the open right ray is the reflection: `p` is
nondecreasing on `(−∞,0)` and nonincreasing on `(0,∞)`, with no value at the origin asserted.

**Narrowed at the origin (fidelity review 2026-09-10, F6-1); this is no longer the reviewed
skeleton's type.** The reviewed statement asked for `AntitoneOn p (Set.Ici 0)`, on the *closed*
half-line. That is not what the entries carry, and it is **false**: `AntitoneOn p (Set.Ici 0)`
forces `p x ≤ p 0` for every `x ≥ 0`, i.e. a density bounded by a real number, whereas Sato's
Thm. 27.13 gives absolute continuity only and Yamazato's Thm. 1 gives convexity left of the mode
and concavity right of it — neither pins a value at the mode, and a concave `F` on `(0,∞)` may
have `F'(0+) = +∞`. The counterexample is inside this development: the Matérn member at
`γ ≤ 1/2`, admitted by `matern_exponent` and built for every `γ > 0` by
`witness_two_members_matern_family`, is a symmetric nondegenerate self-decomposable law whose
density is of order `|x|^{2γ−1}` at the origin, unbounded for `γ < 1/2` and logarithmically
unbounded at `γ = 1/2`. So the statement is narrowed to `AntitoneOn p (Set.Ioi 0)`, which is
this development's own convention for a profile (`SDProfile.k_antitone` in
`SpatialLine/Exponent.lean`), and the blueprint's prose — "its density is unimodal with mode at
the origin" — is unchanged,
being true on either reading. This is the case where prose may leave the reading open and a
formal statement may not.

Range: the two entries speak about a nondegenerate self-decomposable law on `ℝ`, and this
statement says no more. Nothing is claimed about a law that is not self-decomposable, and in
particular nothing about the increments `μ_{s,t}` with `s > 0`, which are infinitely divisible
but not in general self-decomposable. Nothing is claimed about `p 0`.

On `blueprint/trust-boundary.txt`. Consumed by `SpatialLine.kernel_regularity`,
`SpatialLine.polya_frequency` and `SpatialLine.exists_smoothing_law`, the last two at the
absolute-continuity conjunct alone. -/
axiom kernel_regularity_law (μ : Measure ℝ) (hprob : IsProbabilityMeasure μ)
    (hsym : IsSymmetric μ) (hsd : IsSelfDecomposable μ) (hnd : μ ≠ Measure.dirac 0) :
    μ ≪ volume ∧ ∃ p : ℝ → ℝ,
      μ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
        (∀ x : ℝ, p (-x) = p x) ∧ AntitoneOn p (Set.Ioi 0)

/-! ## Ledger A11 — Bernstein's theorem

Added by wave 3 of the proving campaign (2026-09-09), consumed by
`prop:thorin-subclass`(1) iff (2) in both directions.
-/

/-- **Bernstein's theorem** — cited interface, ledger **A11**
(@schilling2012bernstein Thm. 1.4, p. 3, 2nd ed.; corroborated at @feller2009introduction
Vol. 2, §XIII.4, Thm. 1 p. 439 and Thm. 1a p. 440).

A function on the positive half-line is completely monotone if and only if it is the Laplace
transform of a positive measure on `[0,∞)`.

**The uniqueness half of the entry is deliberately not admitted.** Schilling's Thm. 1.4 states
the equivalence *together with* uniqueness of the representing measure, and
`prop:thorin-subclass`'s own uniqueness clause is where the article said that uniqueness would be
spent. It is not: two folded measures with the same finite Laplace transform on a ray are equal
by `laplace_uniqueness_locally_finite`, which this development **proves**
(`prop:laplace-uniqueness-locally-finite`, `SpatialLine/LaplaceUniqueness.lean`). So the axiom is
the existence equivalence alone, and the ledger is charged for less than its citation carries —
the same narrowing wave 2 applied to A1.

**Reading of the Lean statement.** The representing measure lives on `[0,∞)`, which is
`U (Set.Iio 0) = 0` and *not* `IsFolded U`: Bernstein's measure is allowed an atom at the origin,
and excluding it is the article's own step, which the blueprint marks `[T]` in as many words
(`thorin_subclass_representation` does it from the profile's integrability at infinity). The
transform identity is stated as finiteness of the `lintegral` together with the real equality
rather than as an `ℝ≥0∞` identity: `ENNReal.ofReal (f x) = laplaceL U x` would be satisfied by a
negative `f` together with the zero measure, so the `ℝ≥0∞` form of the *equivalence* is false in
its backward direction.

**What the entry does not carry**, and what this development therefore proves beside it: the
elementary integral `∫₀^∞ (1 - cos ωx)e^{-θx}x⁻¹dx = ½log(1 + ω²/θ²)` and the Tonelli that turns
the mixture into `eq:thorin` (`thorin_frullani`); the integrability correspondence
(`thorin_measure_facts`); and the exclusion of an atom of `U` at `θ = 0`.

On `blueprint/trust-boundary.txt`. -/
axiom bernstein_completely_monotone (f : ℝ → ℝ) :
    IsCompletelyMonotone f ↔
      ∃ U : Measure ℝ, U (Set.Iio 0) = 0 ∧
        ∀ x : ℝ, 0 < x → laplaceL U x ≠ ⊤ ∧ f x = (laplaceL U x).toReal

/-! ## Ledger A13 — the moment criterion for infinitely divisible laws

Added by wave 4 of the proving campaign (2026-09-10), when `stable_family_moments` first
consumed it. -/

/-- **`prop:moments-tails`(1), the moment criterion** — cited interface, ledger **A13**
(@sato1999levy Thm. 25.3, p. 159: for an infinitely divisible law with Lévy measure `ν₂` and a
submultiplicative, locally bounded, measurable weight `g`, `E g(X) < ∞` iff
`∫_{|x|>1} g dν₂ < ∞`; used here with `g(x) = (|x| ⊔ 1)^n`).

**Which weight (fidelity review 2026-09-10, F6-3).** This docstring and ledger A13 read
"`g(x) = |x|^n`", and `|x|^n` **is not submultiplicative**: Sato's Def. 25.2 on the same page
asks `g(x + y) ≤ a g(x) g(y)`, which at `y = 0` would need `|x|^n ≤ a·|x|^n·0`. Thm. 25.3 does
not apply to it. The legitimate weight is `(|x| ⊔ 1)^n`, listed as submultiplicative by Prop.
25.4(iii) and (i) on p. 159. The correction is textual: `E (|X| ⊔ 1)^n` and `E |X|^n` are finite
together, since `|x|^n ≤ (|x| ⊔ 1)^n ≤ |x|^n + 1` and the law is a probability measure; and the
two weights agree identically on `{|x| > 1}`, the only region the criterion integrates over. So
both sides of the equivalence below are unchanged. Note that the Lean statement never names the
submultiplicative function: its left-hand side is `Integrable (fun x => |x|^n) (μ t)`, the
*moment* whose finiteness is being characterised, which is the right thing to say. The admitted
type is unchanged by this correction.

`Skeleton.moments_tails_criterion`'s type verbatim. The law is the kernel at canonical scale
`t`, quantified over by its cosine transform as everywhere in this development, and the
criterion is stated *after* the translation into the folded profile, which is the blueprint's
own `[T]` step and is written out in the node's proof: the Lévy measure of `X_t` is the
`t`-dilate of `k(x)x⁻¹dx` folded, so `∫_{|x|>1}|x|^n ν₂(dx)` and `∫₁^∞ x^{n-1}k(x)dx` are
finite together.

Range: `n ≥ 1`, which is the node's own range; nothing is claimed at `n = 0`, where the moment
is the total mass and the criterion is vacuous. The conclusion is about `|x|^n`, hence about the
symmetrisation of `μ t` alone, so the absence of a symmetry hypothesis is not the defect R7
found elsewhere in this chapter.

**What the entry does not carry**: the translation into the folded profile just described, and
the variance formula of the same clause; both are `[T]`.

On `blueprint/trust-boundary.txt`. Consumed by `SpatialLine.stable_family_moments` and
`SpatialLine.matern_moments_integrable`. -/
axiom moments_tails_criterion (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun x : ℝ => |x| ^ n) (μ t) ↔
      ∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (x ^ (n - 1) * P.k x) ≠ ⊤


/-! ## Ledger A14 — the tail floor for a Levy law with bounded jump support

Added by wave 4 of the proving campaign (2026-09-10), when
`moments_tails_completely_monotone` first consumed it. **Narrowed**, and the narrowing was
forced: `Skeleton.moments_tails_bounded`'s divergence conjunct is *false* as it was typed, and
this axiom is the true statement the entry carries. See the docstring below. -/

/-- **`prop:moments-tails`(2), the divergence branch** — cited interface, ledger **A14**
(@sato1999levy Thm. 26.1, p. 168, clause (ii): with
`c = inf{a > 0 : supp ν ⊆ {|x| ≤ a}}`, the moment `E exp(α|X|log|X|)` is infinite for every
`α > 1/c`).

Read here at a **lower bound** for `c`. If the profile is nonzero at some point at or beyond
`τ > 0` then, `k` being nonnegative and nonincreasing, the Levy measure `k(x)x⁻¹dx` has mass
arbitrarily close to that point, so its radius is at least `τ`; the radius of the law at
canonical scale `t` is the `t`-dilate, at least `τt`; and clause (ii) applies at every
`α > (τt)⁻¹`. Nothing is claimed at or below that threshold, and the finiteness branch of the
entry is not admitted, no proof consuming it.

**Why this is narrower than the skeleton's two declarations, and why it had to be.**
`Skeleton.moments_tails_bounded`'s second conjunct reads: if `k` vanishes beyond `τ`, then the
moment is infinite for every `α > (τt)⁻¹`. That is **false** on two counts, and admitting it
would have admitted a false axiom.

* At `k ≡ 0` — the pure Gaussian — every `τ` satisfies the hypothesis, while the law is
  Gaussian and `E exp(α|X|log|X|)` is *finite* for every `α`, `α|x|log|x|` growing more slowly
  than `x²`. Sato's Remark 26.3 treats `ν = 0` separately for exactly this reason, and the
  ledger entry records that.
* At any `τ` strictly larger than the radius — and the hypothesis "`k` vanishes beyond `τ`"
  admits every such `τ` — the true threshold `1/(ct)` is *larger* than `(τt)⁻¹`, so the claim
  asserts divergence on a range where the entry's own clause (i) asserts convergence. The
  ledger's parenthesis "(Sato's `c` is an infimum; the blueprint's `τ` is the same number)" is
  the reading the Lean statement failed to carry.

`Skeleton.moments_tails_bounded` is repaired accordingly (`% CHANGED (proof 2026-09-10)` at
`prop:moments-tails`), and `Skeleton.moments_tails_heavy` is untouched: at unbounded support
`c = ∞`, `1/c = 0`, and every `α > 0` is above the threshold, which is this axiom read along
`τ → ∞`.

**What the entry does not carry**: the finiteness branch; the tail-ratio statement
`P[|X| > r]/e^{-αr log r} → ∞`; and the comparison of the two regimes with the Gaussian rate,
which is `[T]` and is `lintegral_exp_sq_eq_top`.

On `blueprint/trust-boundary.txt`. Consumed by
`SpatialLine.moments_tails_completely_monotone` alone. -/
axiom moments_tails_divergence (P : SDProfile) (μ : ℝ → Measure ℝ)
    (hprob : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hcos : ∀ t ω : ℝ, 0 < t → fourierCos (μ t) ω = Real.exp (-P.exponent (t * ω)))
    {t : ℝ} (ht : 0 < t) {τ : ℝ} (hτ : 0 < τ) (hmass : ∃ x : ℝ, τ ≤ x ∧ P.k x ≠ 0)
    {α : ℝ} (hα : (τ * t)⁻¹ < α) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (α * |x| * Real.log |x|)) ∂(μ t) = ⊤


/-! ## Ledger A21 and A22 — Pólya frequency densities and variation diminution

Added by wave 4 of the proving campaign (2026-09-10), when `prop:polya-frequency`(1) and
`thm:scale-monotone-noncreation`'s converse first consumed them. The two axioms are the two
directions of that node's clause (1), stated **about a single law** rather than about a family:
Karlin's theorems are theorems about one kernel, and the family form is this article's
packaging, so the single-law form is the one closer to the citation. `SpatialLine.polya_frequency`
is the assembly that puts the family back, and it is `[T]`.

## What the two entries carry, and what these axioms carry beyond them

**A22** (@karlin1968total Ch. 5, Thm. 3.1(i), p. 233 for sufficiency; Thm. 4.2, pp. 242–243 for
necessity) is the equivalence of variation diminution with total positivity for a translation
kernel. **A21** (@karlin1968total Ch. 7, Thm. 3.2(**a**), p. 345, with Remark 3.1, p. 346, and
§2 p. 336) is Schoenberg's representation: a density on the line is Pólya frequency exactly when
the reciprocal of its two-sided Laplace transform is `C e^{-γσ² + δσ}∏_i(1 + a_iσ)e^{-a_iσ}` with
`γ ≥ 0`, real `a_i` of either sign and `∑a_i² < ∞`. **Page 336 was added to A21's anchor by the
fidelity review (2026-09-10, F6-4)**: it carries the class `E₂` at (2.2) with that parameter
range verbatim, and — the reason the page is load-bearing — the sentence that *produces* a
density, "φ(s) = 1/ψ(s) for ψ(s) in `E*₂` is the Laplace transform of a PF density, provided
`γ + ∑a_i² > 0`". Thm. 3.2(a) on p. 345 is an *iff about a density function* and read forwards
presupposes one; see the range note on `variationDiminishing_of_polyaExponent` below.

Four things these axioms have carried beyond the two entries. **Two of them still do**; items 2
and 4 were both discharged on 2026-09-11 and are kept here as history, with the declarations that
discharged them named. The current, per-axiom lists are in the two docstrings below, which are
stated at Karlin's letter; what follows is the history of this pair. Each of the two survivors is
deliberate:

1. **The composition.** Neither axiom mentions total positivity: A22 and A21 are spent together,
   the first turning variation diminution into the Pólya frequency property and the second
   turning that into the product form. Total positivity appears in neither statement of this
   development and so is not defined here (`SpatialLine/Variation.lean`, module docstring).

2. **The symmetry reduction and the matching** — **discharged 2026-09-11; this item is history,
   not a live extension.** It is what `prop:polya-frequency`'s printed proof carries out and
   marks `[T]`: `δ = 0` with the `a_i` in `±` pairs, the identification `γ = a` and
   `λ_i = 1/θ_i`, and the passage from the reciprocal Laplace transform to the exponent. From
   wave 4 to 2026-09-11 it sat inside these two axioms, recorded here, at both ledger entries and
   at the node as the deepest of the steps that do, and described in prose as an analytic
   continuation of `Ψ(σ) = \hatφ(iσ)` off the imaginary axis, needing the two-sided Laplace
   transform as an entire function and an identity theorem.

   **It needs neither.** Karlin's own strip (Prop. 1.4, p. 333) contains the imaginary axis *and*
   a real interval, so the symmetry of `μ` makes `ψ` even on that interval with no continuation,
   and evenness there forces `δ = 0` and every odd power sum `∑ a_j^{2k+3}` to vanish
   (`ScaleSpace.polyaE2_even_imp_oddPowerSums`); the atomic measure `∑ a_j² δ_{a_j}` is then
   symmetric, which halves every even quadratically bounded sum
   (`ScaleSpace.tsum_eq_two_mul_tsum_posPart`) and reads the modulus
   `ScaleSpace.norm_polyaE2_mul_I` on the imaginary axis as the Pólya form with `λ_j = a_j⁺`. The
   two matching theorems are `SpatialLine.isPolyaExponent_of_variationDiminishing` and
   `SpatialLine.variationDiminishingOrd_of_polyaExponent` in `SpatialLine/PolyaMatching.lean`,
   both on Lean core plus the axiom of their own direction; the core lemmas are
   `ScaleSpaceCore/PolyaFrequencyClass.lean` and `ScaleSpaceCore/PowerSumSymmetry.lean`
   (ScaleSpaceCore v0.2.0). The axioms below are restated at Karlin's letter accordingly, and
   `hsym` and `hcos` moved out of them onto the theorems. Fidelity review F6-2's finding stands
   otherwise: seven of the eleven names still carry a step beyond their pages, and the per-name
   list is at the head of `blueprint/trust-boundary.txt`.

3. **Integrable test functions.** Karlin states the variation-diminishing conclusion for bounded
   Borel `f`; `IsVariationDiminishingOrd` — following the node, which says "every integrable or
   bounded `g`" — quantifies over integrable `f` as well. The determinant argument is the same
   one, but the extension is ours and is named here rather than left silent. It touches only
   `variationDiminishing_of_polyaExponent`; the other direction has the wider quantifier as a
   *hypothesis*, where a wider range is a narrowing, not a widening. **This is the one extension
   that survives the 2026-09-11 narrowing**, and the reason the name is still on the per-name
   list at the head of `blueprint/trust-boundary.txt`.

4. **The essential sign-change count, and which representatives it ranges over**
   (fidelity review R14) — **discharged 2026-09-11; this item is history, not a live
   extension.** Karlin counts sign changes of a bounded Borel function in the ordinary sense,
   `S⁻(f)`. The development's count is `signChangesAE g` (`SpatialLine/Variation.lean`), the
   infimum of `signChanges h` over **every** `h` with `h =ᵐ[volume] g` — non-measurable
   representatives included, the definition placing no measurability condition on `h`. The two
   directions were never equally exposed, and unlike item 3 this one touched both.
   `polyaExponent_of_variationDiminishing` was and is **safe**: variation diminution is a
   hypothesis there and the essential form of it is the stronger one, because `hac` makes
   `μ * g` continuous, the essential and the ordinary counts agree on a continuous function, and
   on the right the essential count is at most the ordinary one — so the hypothesis implies
   Karlin's. `variationDiminishing_of_polyaExponent` **needed one thing more**: its conclusion
   was an inequality between two infima, Karlin gives it between the two ordinary counts, and
   passing to the essential ones additionally requires that no representative of `g`, in
   particular no non-measurable one, lower the right-hand count below what Karlin's inequality
   controls. From 2026-09-10 to 2026-09-11 that step was recorded, at **A21** and **A22** in
   `blueprint/AXIOMS.md` and here, as *believed and not proved*.

   It is now **proved**: `SpatialLine.exists_measurable_rep_signChanges_le`
   (`SpatialLine/MeasurableHull.lean`) replaces any representative of a measurable `g` by a
   measurable one with no more sign changes and no larger absolute value — delete `g` on a
   measurable null superset of the set where the two differ, and every alternation of the result
   is an alternation of the original at the same points — so the infimum is attained along
   measurable representatives (`SpatialLine.signChangesAE_eq_iInf_measurable`) and
   `SpatialLine.isVariationDiminishing_of_ord` carries Karlin's ordinary-count conclusion to the
   essential-count one. The axiom below is narrowed to `IsVariationDiminishingOrd`, Karlin's
   letter, and `SpatialLine.isVariationDiminishing_of_polyaExponent`, stated beside it, is what
   the four consumers call.

## The hypothesis ranges, against the pages

`polyaExponent_of_variationDiminishing` carries `hac : μ ≪ volume` because **Karlin's Thm. 4.2
is stated for a density**: "Let `k(u)` be a density function on `(-∞,∞)`; i.e. `k(u)` is
nonnegative and has total integral 1" (p. 243). With `IsProbabilityMeasure μ` that hypothesis is
exactly Radon–Nikodym's. This development does not get the density for free: it is ledger **A8**,
already admitted as `kernel_regularity_law`, and the assembly spends it.

`variationDiminishing_of_polyaExponent` carries `hnd : 0 < γ + ∑a_j²` — since 2026-09-11 in
Karlin's own parameters, and before that as `∃ ω, F ω ≠ 0` on this article's — because
**Thm. 3.2(a) requires `γ + ∑a_i² > 0`**, which p. 346 says in as many words is "essential in
order that `f` be a bona fide density function". At `γ = 0` with every `a_i = 0` the law is `δ₀`,
which is not a Pólya frequency density and is outside the theorem; that case is *proved* rather
than cited (`isVariationDiminishing_dirac_zero` — convolution by `δ₀` is the identity), which is
why the axiom may exclude it, and the translation between the two forms of the condition is
`SpatialLine.variationDiminishingOrd_of_polyaExponent`'s first step. Both axioms are on
`blueprint/trust-boundary.txt`.
-/

/-- **`prop:polya-frequency`(1), necessity** — cited interfaces, ledger **A22** into **A21**,
**restated at Karlin's letter on 2026-09-11**.

A probability law with a density whose convolution operator is variation-diminishing is a Pólya
frequency density, so the reciprocal of its bilateral Laplace transform is a function of class
`E₂*` with `γ + ∑a_i² > 0`, on an open strip around the imaginary axis.

**Cite:** @karlin1968total Ch. 5, Thm. 4.2, pp. 242–243 (variation diminution of a translation
kernel is total positivity, hence the Pólya frequency property) composed with Ch. 7, Thm. 3.2(a),
p. 345 (a density is PF exactly when the reciprocal of its Laplace transform is of class `E₂*`
with `γ + ∑a_i² > 0`), Prop. 1.4, p. 333 (the Laplace transform of a PF density exists in an open
strip containing the imaginary axis) and §2, (2.2), p. 336 (the class `E₂`, and `E₂*` as its
`ψ(0) = 1` subclass — no constant, no factor `s^k`).

**The symmetry reduction and the matching are no longer inside this axiom.** Until 2026-09-11 it
concluded `IsPolyaExponent F` for a symmetric law with cosine transform `e^{-F}`, and so carried
`δ = 0`, the pairing of the `a_i`, and the passage from the reciprocal Laplace transform to the
exponent — the step the blueprint marks `[T]`. Those are now proved, on Lean core plus this
axiom, as `SpatialLine.isPolyaExponent_of_variationDiminishing`
(`SpatialLine/PolyaMatching.lean`), which has this axiom's old signature and is what the two
consumers call. The hypotheses `hsym` and `hcos`, which Karlin's pages do not carry, moved to
that theorem with them.

**What this axiom still carries beyond its pages**, each item deliberate:

1. **The composition.** Total positivity appears in neither statement of this development and is
   not defined here: A22 turns variation diminution into the Pólya frequency property and A21
   turns that into the product form, and the two are spent only together.

2. **The essential sign-change count in the hypothesis.** `IsVariationDiminishing` is
   `signChangesAE`, an infimum over every almost-everywhere representative, and quantifies over
   integrable as well as bounded test functions; Karlin's hypothesis is the ordinary count of a
   bounded Borel function. Both differences make the hypothesis *stronger*, so the axiom asks for
   more than the page gives and the direction is safe (`hac` makes `μ * g` continuous, where the
   two counts agree).

3. **A density where Karlin has a density function.** `IsProbabilityMeasure μ` with
   `μ ≪ volume` is Radon–Nikodým's form of Karlin's "nonnegative with total integral 1"
   (Thm. 4.2, p. 243); the choice of a representative of the derivative, and the passage from a
   kernel that is totally positive almost everywhere to Karlin's pointwise density, are ours.

4. **The index set padded to `ℕ`.** Karlin's family `{a_i}` may be finite; here it is a sequence,
   a finite family being padded by zeros, whose factors contribute `log 1 = 0`.

5. **The strip as a two-sided bound on `Re s`, with integrability.** Prop. 1.4's "open strip
   containing the imaginary axis" is read as `∃ α < 0 < β` with absolute convergence of
   `∫ e^{-(Re s)x} dμ` and the identity `φ(s)ψ(s) = 1` at every `s` of that strip.

Consumed by `SpatialLine.isPolyaExponent_of_variationDiminishing` alone, and through it by
`SpatialLine.polya_frequency` and `SpatialLine.scale_monotone_step_one`. On
`blueprint/trust-boundary.txt`. -/
axiom polyaExponent_of_variationDiminishing (μ : Measure ℝ)
    (hprob : IsProbabilityMeasure μ) (hac : μ ≪ volume) (hvd : IsVariationDiminishing μ) :
    ∃ (γ δ : ℝ) (a : ℕ → ℝ), 0 ≤ γ ∧ Summable (fun j => a j ^ 2) ∧ 0 < γ + ∑' j, a j ^ 2 ∧
      ∃ α β : ℝ, α < 0 ∧ 0 < β ∧ ∀ s : ℂ, s.re ∈ Set.Ioo α β →
        Integrable (fun x => Real.exp (-s.re * x)) μ ∧
        ScaleSpace.bilateralLaplace μ s * ScaleSpace.polyaE2 γ δ a s = 1

/-- **`prop:polya-frequency`(1), sufficiency** — cited interfaces, ledger **A21** and **A22**.

A symmetric probability law whose exponent has the Pólya form, and is not identically zero, has
a convolution operator that diminishes the **ordinary** sign-change count of every measurable
integrable or bounded test function. That is Karlin Ch. 5, Thm. 3.1(i) (p. 233) at its own
count and its own class of test functions, widened only by item 3 of the extension list above.

**Narrowed 2026-09-11 (fidelity review row R14, the author's decision).** Until then this axiom
concluded `IsVariationDiminishing μ`, the *essential*-count property, which Karlin's page does
not state: `signChangesAE` is an infimum over every almost-everywhere representative, and the
passage from Karlin's inequality between ordinary counts to an inequality between those infima
was carried inside the axiom and recorded as believed. The passage is now proved —
`SpatialLine.exists_measurable_rep_signChanges_le` with
`SpatialLine.isVariationDiminishing_of_ord`, `SpatialLine/MeasurableHull.lean` — so the axiom is
stated at the letter of the page and the essential form is the theorem
`SpatialLine.isVariationDiminishing_of_polyaExponent` below, which is what every consumer calls.
Nothing on any consumer's `#print axioms` line changed.

Range: `hnd` is Thm. 3.2(a)'s condition `γ + ∑a_i² > 0` (p. 346), read on this article's
parameters; no density is hypothesised because A21's sufficiency leg *produces* one.

**Where the density comes from (fidelity review 2026-09-10, F6-4).** The attribution above was
short by one page. Thm. 3.2(a) on p. 345, the pinned anchor, is an equivalence *about a density
function*: read forwards it presupposes the density rather than yielding it, so on that anchor
alone this axiom's want of a density hypothesis was unsupported. The sentence that produces one
is on **p. 336**, immediately after (2.2): "φ(s) = 1/ψ(s) for ψ(s) in `E*₂` is the Laplace
transform of a PF density, provided `γ + ∑a_i² > 0`" — the same proviso `hnd` carries. That page
is now on A21's `**Cite:**` line, and with it the axiom asks no more than the source gives.

Consumed by `SpatialLine.variationDiminishingOrd_of_polyaExponent` alone, and through it and
`SpatialLine.isVariationDiminishing_of_polyaExponent` by `SpatialLine.polya_frequency`,
`SpatialLine.scale_monotone_converse`, `SpatialLine.exists_smoothing_law` and
`SpatialLine.isVariationDiminishing_gaussianKernel`. On `blueprint/trust-boundary.txt`.

**Restated at Karlin's letter on 2026-09-11, and the matching is no longer inside it.** Until
then it was stated about a symmetric law with cosine transform `e^{-F}` and an exponent of the
Pólya form, and so carried the pairing of the parameters, the reading of `hnd` as
`γ + ∑a_i² > 0`, and the identification of Karlin's produced density with `μ`. Those are now
proved, on Lean core plus this axiom, as
`SpatialLine.variationDiminishingOrd_of_polyaExponent` (`SpatialLine/PolyaMatching.lean`), which
has this axiom's old signature and is what `isVariationDiminishing_of_polyaExponent` calls;
`hsym` and `hcos`, which Karlin's pages do not carry, moved to that theorem with them.

**Cite:** @karlin1968total §2, (2.2) and the sentence after it, p. 336 (`E₂*`, and that
`φ = 1/ψ` for `ψ ∈ E₂*` *is* the Laplace transform of a PF density provided `γ + ∑a_i² > 0`),
Ch. 7, Thm. 3.2(a), p. 345 with Remark 3.1, p. 346, Prop. 1.4, p. 333 (the strip), and Ch. 5,
Thm. 3.1(i), p. 233 (a PF kernel diminishes sign changes).

**What this axiom still carries beyond its pages:**

1. **The composition**, as for the necessity leg: total positivity is named in neither statement.

2. **Integrable test functions.** Karlin states the conclusion for bounded Borel `f`;
   `IsVariationDiminishingOrd` — following the node, which says "every integrable or bounded
   `g`" — quantifies over integrable `f` as well. The determinant argument is the same one, but
   the extension is ours. This is the one extension that survived the 2026-09-11 narrowing of the
   count, and it is why the name is on the per-name list at the head of
   `blueprint/trust-boundary.txt`.

3. **`IsFiniteMeasure ν` with `ν ≪ volume` where the page says density.** The conclusion is the
   measure, not a pointwise density, and asserts neither a representative nor total mass 1
   (`ψ(0) = 1` gives the mass, and the development does not need it). That is weaker than the
   page and therefore safe.

4. **The index set padded to `ℕ`**, and **the strip read as `∃ α < 0 < β` with integrability**,
   exactly as for the necessity leg. -/
axiom variationDiminishing_of_polyaExponent (γ δ : ℝ) (a : ℕ → ℝ)
    (hγ : 0 ≤ γ) (ha : Summable fun j => a j ^ 2) (hnd : 0 < γ + ∑' j, a j ^ 2) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν ≪ volume ∧ IsVariationDiminishingOrd ν ∧
      ∃ α β : ℝ, α < 0 ∧ 0 < β ∧ ∀ s : ℂ, s.re ∈ Set.Ioo α β →
        Integrable (fun x => Real.exp (-s.re * x)) ν ∧
        ScaleSpace.bilateralLaplace ν s * ScaleSpace.polyaE2 γ δ a s = 1

/-! `SpatialLine.isVariationDiminishing_of_polyaExponent`, the essential-count form every
consumer calls, moved to `SpatialLine/PolyaMatching.lean` on 2026-09-11 with its statement
unchanged: it now composes the measurable-hull reduction with the matching theorem
`SpatialLine.variationDiminishingOrd_of_polyaExponent` rather than with the axiom directly. -/

/-! ## Chapter 12: the ordinary-differential input of `thm:joint-locality` (ledger **A19**)

Two names, admitted 2026-09-10 (wave 5), when `SpatialLine.joint_locality_forward` first
consumed them. Both are stated in the form the entry was **restated** into by the statement
review (question **Q13**): A19(b′), the consequence the proof spends, rather than the solution
basis of A19(a). The reason is recorded at the entry and in `Skeleton/Chapter12.lean`: the basis
`z^ν(c₁K_ν + c₂I_ν)(z)` would need `I_ν`, which — unlike `K_ν`, whose DLMF (10.32.9) integral is
definitional for every real order — has no single integral representation valid for every real
`ν`, and the proof discards that branch in one line by boundedness. So what is admitted is the
uniqueness of the bounded normalised solution, which is (b)'s asymptotics.

**What "clause (a) is not admitted" does and does not mean** (fidelity review 2026-09-10, F6-7).
It means the *conclusion* is charged for less than the source states: what the article spends is
the uniqueness of the bounded normalised solution and not the solution basis. It does **not**
mean that the substitution sits outside the trust base. Both names below are stated about the
covariant equation `φ'' + (β/z)φ' − cφ = 0` and conclude in terms of `SpatialLine.besselK`, and
nothing between the two is written down anywhere in this development; so the substitution
`φ(z) = z^ν w(√c z)`, `ν = (1−β)/2`, that reduces the equation to A&S 9.6.1 — clause (a) — is
**inside** both statements, and admitting them takes it on trust. Each name carries one step
more besides: `joint_locality_bounded_solution` the elimination of the `I_ν` branch by
boundedness and the passage from the asymptotics 9.6.7–9.6.9 to a pointwise identity on all of
`(0,∞)` (uniqueness for a second-order linear ODE); `joint_locality_hyperbolic` the transfer of
zeros through `z^ν ≠ 0` on `(0,∞)`, the reduction of a nontrivial real solution to a multiple of
a **general real cylinder function** `C_ν = J_ν cos πt + Y_ν sin πt`, and the infinitude of that
function's positive zeros, which neither source states by name. These are listed by name at the
head of `blueprint/trust-boundary.txt` and at **A19**.

**Read at the DLMF primary (2026-09-11, fidelity row R119).** The stored `@dlmf2026` sections
carry (10.25.1), (10.25.3), (10.32.9) — the integral that *is* `besselK`, for `|ph z| < π/2` and
every real order — and, stored the same day, §10.30's limiting forms at the origin
((10.30.2)–(10.30.3)), which §10.25 does not carry; `K_{−ν} = K_ν` stays on A&S 9.6.6. For the
general cylinder function DLMF §10.21(i) states the infinitude of positive zeros for `J_ν` and
`Y_ν` at real `ν` and the interlacing of any two distinct real cylinder functions of the same
order, from which the general case is a one-line deduction — still a step inside the name,
where A&S p. 370 had only presupposed it. Recorded at A19.

**The `C²` qualifier is load-bearing and is on both names.** A19 speaks of the solutions of an
ordinary differential equation, which are classical solutions; without the hypothesis the
statement would range over `iteratedDeriv`'s junk value as well and would be wider than the
citation (review **R22**). It is not a repair — a nowhere-`C²` `φ` would force `φ = 0` through
the equation, against `hφ0` — but a domain correction, and the article supplies the hypothesis:
`SpatialLine.joint_locality_ode` *concludes* the regularity, from the locality hypothesis and
not from admissibility.

**Hypothesis ranges, against the entry.** `hc : 0 < c` and `hc : c < 0` are the entry's own two
regimes; the entry states (b′) "for `c > 0` and `ν = (1−β)/2`" and (c) for the corresponding
*ordinary* Bessel equation, which is what `c < 0` is. Two edge cases were checked before
admission. At `ν ≤ 0` the first name asserts nothing: its conclusion `0 < (1−β)/2` is exactly the
entry's "there are none when `ν ≤ 0`", so the case is carried as a *conclusion* and not excluded
by a hypothesis. And the constant solution `φ ≡ 1`, which is bounded and normalised, does not
satisfy the equation for any `c > 0` — it gives `−c = 0` — so it is no counterexample to the
uniqueness clause; at `c = 0` it *is* the solution, and that case is proved rather than cited
(`SpatialLine.joint_locality_degenerate`).

**What is not admitted.** Ledger **A20**, the half-plane Dirichlet problem, has no consumer: the
forward direction of `thm:joint-locality` does not reach it, and the backward direction, which
would consume its *existence* clause, is not proved. Its *uniqueness* clause — the part of A20
whose boundedness qualifier the ledger records a caveat about — is not consumed by the node at
all, on either direction. Neither name is added.
-/

/-- **`thm:joint-locality`, the bounded normalised solution of `eq:bessel-ode`** — cited
interface, ledger **A19**(b′).

For `c > 0` and `ν = (1−β)/2`, a solution of `φ'' + (β/z)φ' − cφ = 0` that is `C²` on `(0,∞)`,
bounded on `[0,∞)` and equal to `1` at the origin exists only for `ν > 0`, and is then the
normalised `2^{1−ν}Γ(ν)^{−1}(√c z)^νK_ν(√c z)`. `K_ν` is `SpatialLine.besselK`, the DLMF
(10.32.9) integral.

Consumed by `SpatialLine.joint_locality_forward`, in the case `c > 0`, at both conjuncts. On
`blueprint/trust-boundary.txt`. -/
axiom joint_locality_bounded_solution {c β : ℝ} (hc : 0 < c) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (2 : WithTop ℕ∞) φ (Set.Ioi 0))
    (hode : ∀ z : ℝ, 0 < z →
      iteratedDeriv 2 φ z + β / z * deriv φ z - c * φ z = 0)
    (hbdd : ∃ C : ℝ, ∀ z : ℝ, 0 ≤ z → |φ z| ≤ C) (hφ0 : φ 0 = 1)
    (hcont : ContinuousWithinAt φ (Set.Ici 0) 0) :
    0 < (1 - β) / 2 ∧
      ∀ z : ℝ, 0 < z →
        φ z = 2 ^ (1 - (1 - β) / 2) / Real.Gamma ((1 - β) / 2)
          * (Real.sqrt c * z) ^ ((1 - β) / 2) * besselK ((1 - β) / 2) (Real.sqrt c * z)

/-- **`thm:joint-locality`, the oscillation of the ordinary Bessel equation** — cited interface,
ledger **A19**(c).

For `c < 0` the equation `φ'' + (β/z)φ' − cφ = 0` is the ordinary Bessel equation in disguise,
and every nontrivial `C²` solution has arbitrarily large positive zeros. The exclusion drawn
from it — that an admissible transform is strictly positive, so no admissible family arises — is
this article's, `[T]`, and is in the node's proof rather than here.

Consumed by `SpatialLine.joint_locality_forward`, in the case `c < 0`. On
`blueprint/trust-boundary.txt`. -/
axiom joint_locality_hyperbolic {c β : ℝ} (hc : c < 0) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (2 : WithTop ℕ∞) φ (Set.Ioi 0))
    (hode : ∀ z : ℝ, 0 < z → iteratedDeriv 2 φ z + β / z * deriv φ z - c * φ z = 0)
    (hnt : ∃ z : ℝ, 0 < z ∧ φ z ≠ 0) :
    ∀ R : ℝ, ∃ z : ℝ, R < z ∧ φ z = 0

end SpatialLine
