# Axiom provenance ledger — spatial hemigroup scale space, the line

The project's **trust boundary**. Every `[A]` analytic-interface node in the blueprint is
grounded here, in a named theorem with a page anchor, resolved through the librarian.

Format contract (enforced by `linkage check`, fatal checks 2 and 6):

```
## A<N> — <one-line statement of what is taken on trust>
**Blueprint:** `<label>` · **Lean:** `<decl>`
**Cite:** @<citekey> — <page anchor>

- **Statement as used.** …
- **Primary — <the named theorem>.** …
```

A `[A]` node must also declare, in its status annotation, what the citation carries and what
it does not (`\textbf{Assignment.}`, fatal check 7). Widening this file widens the trust
base; it is a review decision, not a fix. **Every anchor must be read out of a held copy by
the librarian**, never quoted from memory; an entry drafted before that pass says so in its
first line and is not load-bearing until the anchor is verified.

---

## Status of this ledger (2026-09-07, blueprint campaign)

**Every entry below is DRAFTED, NOT VERIFIED.** The page anchors are transcribed from the
draft's own citation apparatus, which records them as checked on 2026-09-05/06 by the author
but not by a librarian pass against a held scan in this repository. Each entry therefore opens
with `ANCHOR UNVERIFIED — librarian pass pending`; the pass of 2026-09-07 verified all 22 (one anchor moved, A21, and caveats recorded at A7, A19, A20), and no entry is load-bearing until that line
is replaced by a verification note naming the pass. The causal article's ledger is the model
for what a verified entry looks like, including the discipline of recording discrepancies
rather than papering over them.

**The `AXX` identifiers are opaque and stable.** They are assigned in order of introduction,
never reused, never renumbered — the manifest projects a `ledger` array to the hub, so
renumbering silently changes what an existing hub note means. Order of first use is a property
of the index below, not of the names.

| Serves | Entries |
|---|---|
| Ch. 2 — the Fourier toolbox and the two transform interfaces | A1–A7 |
| Ch. 7 — regularity of the kernels from the origin | A8–A9 |
| Ch. 8 — the behaviour of an admissible kernel at the origin | A10 |
| Ch. 9 — the subordination bridge | A11–A12 |
| Ch. 10 — moments, tails, and the three corners | A13–A18 |
| Ch. 12 — joint locality | A19–A20 |
| Ch. 13 — the counting axioms | A21–A22 |

## What is deliberately NOT here

Nine facts the draft names as ledger candidates are held `[T]` or rerouted, and the reason is
recorded at the node as well as here. Keeping them out is the point of the exercise: the
boundary should be as narrow as the causal article's principle allows.

| Fact the draft names | Disposition |
|---|---|
| Wendel's theorem (translation-invariant operators on `L¹` are convolutions) | **[T]** — proved from scratch in `lem:convolution-representation`, as in the causal article; `@wendel1952left` is cited in `rem:wendel` for provenance only |
| Prokhorov's theorem, Helly selection, the portmanteau theorem | **[T]** — Mathlib has them; used in `lem:convolution-representation` and `thm:increments-levy` |
| Quadratic growth of a continuous negative definite function (Jacob Vol. I, Lemma 3.6.22) | **rerouted** — `lem:quadratic-growth`, three lines from the truncation split; used by `cor:semigroup-case` and `thm:scale-locality` |
| Nonvanishing of an infinitely divisible characteristic function (Sato Lemma 7.5, p. 32) | **rerouted** — `lem:nonvanishing` proves the stronger fact this article needs from (A6)–(A7), and comes first in the order of dependence |
| The null-array convergence theorem for infinitely divisible laws (Sato Thm. 8.7, p. 42) | **rerouted** — `thm:increments-levy` extracts the representation directly, the truncation inequality being proved inline |
| The composition rule, `f` Bernstein and `ψ` continuous negative definite give `f∘ψ` continuous negative definite (Jacob Vol. I, §3.9) | **rerouted** — `lem:bridge-exponents` obtains the special case it needs from A11 and A12, which Ch. 10 needs anyway |
| Peetre's theorem | **not used** — `def:localities` defines scale-local generation by polynomiality of the symbol; the support formulation is `rem:peetre` |
| Courrège's theorem | **not used** — only the easy direction was ever needed, and `thm:non-enhancement`(2) proves the form this article uses |
| Sato Thm. 14.14 (the symmetric stable laws) | **rerouted** — `cor:semigroup-case` exhibits the profile explicitly, so membership follows from A3's converse; the word "stable" is then nomenclature |

One further fact, the correspondence between self-decomposable laws and self-similar additive
processes (Sato §16), appears only as a reading in `rem:sato-process`, grounds no node, and is
therefore not an entry.

---

## A1 — Bochner: continuous positive definite with value 1 at 0 ⟺ a probability transform
**Blueprint:** `prop:fourier-toolbox` (clause 1) · **Lean:** `SpatialLine.fourier_toolbox_bochner_symm` *(the symmetric leg, in `Formalization/SpatialLine/Interfaces.lean`; **the admitted statement is the forward implication**, not the equivalence — see below; the general complex clause is not stated as an axiom, nothing consumes it)*
**Cite:** @sato1999levy — Prop. 2.5, pp. 8–9: clause (i), p. 8 (Bochner) with clause (ii), p. 8 (uniqueness of the transform) and clause (v), p. 9 (the reflected law's transform is the conjugate), the last two carrying the symmetric rider. Corroboration: @feller2009introduction — Vol. 2, §XIX.2, Theorem (Bochner), p. 622, with the definition (2.7) there

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato p. 8 and Feller p. 622 both state Bochner's theorem as used).
- **Anchor page range corrected 2026-09-10 (fidelity review, F6-6).** The Cite line read "Prop.
  2.5(i), p. 8; the symmetric clause from (ii) and (v)", but **(v) is printed on p. 9**, not on
  p. 8: p. 8 carries (i) and (ii), and p. 9 carries (v), `\tilde μ̂(z) = μ̂(−z) = conj μ̂(z)`. The
  anchor is therefore pp. 8–9. Two further points of the same reading, recorded rather than left
  implicit. First, the symmetric rider runs through **(ii)**, the Fourier-uniqueness statement
  that the proving campaign **retired as A5** and proves here from Mathlib's
  `Measure.ext_of_charFun`: a real transform gives `μ̂ = conj μ̂ = \tilde μ̂` by (v), and it takes
  (ii) to conclude `μ = \tilde μ`. So this entry's page reach touches a fact the ledger
  deliberately stopped charging for — harmless, since the development proves it, but it is why
  the range is two pages. Second, the axiom asks `Continuous φ` on all of `ℝ` where Sato asks
  continuity **at `z = 0`** only, and asks it of a real `φ` where the source allows a complex
  one: the admitted hypotheses are stronger than the source's twice over, which is the safe
  direction.
- **Statement as used.** A function `φ : ℝ → ℂ` is the Fourier transform of a probability
  measure on `ℝ` iff it is continuous, positive definite and `φ(0) = 1`; it is the transform of
  a *symmetric* probability measure iff moreover it is real, equivalently even.
- **Primary — Bochner's theorem.** The symmetric clause is a rider, not a separate theorem: the
  source gives that a measure is symmetric iff its transform is real, and the equivalence of
  "real" with "even" for a transform is elementary. The verification pass should confirm that
  the rider is available at the anchor and not only in a later section.
- **Sign convention.** The source's characteristic function is `∫ e^{i⟨z,x⟩} μ(dx)`, the
  opposite sign to this article's `(2.1)`; immaterial for symmetric laws, and the entry is used
  only for symmetric ones outside the construction direction of the main theorem.
- **Lean, 2026-09-09 (proving campaign, wave 2; narrowed by the merge).** The symmetric leg is
  admitted as the axiom `SpatialLine.fourier_toolbox_bochner_symm`, in
  `Formalization/SpatialLine/Interfaces.lean` and on `blueprint/trust-boundary.txt`.
  **The admitted statement is the forward implication** — continuous, positive definite and
  value `1` at the origin ⇒ the cosine transform of a symmetric probability measure — with
  `Skeleton.fourier_toolbox_bochner_symm`'s hypotheses otherwise verbatim. That is the only
  direction the development spends. The reverse direction is elementary and is **proved**, as
  `SpatialLine.fourier_toolbox_bochner_symm_of_measure`, from
  `SpatialLine.isPositiveDefinite_fourierCos` (the positive-definiteness double sum is the
  integral of the squared modulus of a trigonometric sum, read through `charFun` on a symmetric
  measure); the equivalence the reviewed skeleton states survives beside it as the theorem
  `SpatialLine.fourier_toolbox_bochner_symm_iff`, which spends the axiom for one leg and nothing
  for the other. So this entry is charged for half of what its citation states.
  Consumers: `SpatialLine.increments_levy_infinitely_divisible` — the closing sentence of
  `thm:increments-levy` — and `SpatialLine.exists_isSymmetric_of_isSymLevyExponent`, and through
  the latter `SpatialLine.main_construction`, the construction direction of
  `thm:main-characterization` and the only place in the article where a measure is produced from
  an exponent. The trust-boundary proposal made A1 conditional on Mathlib not supplying Bochner;
  at the pinned version it does not — there is no `IsPositiveDefinite` in `Mathlib.MeasureTheory`
  at all — so unlike A5 and A6 this entry could not be retired. Chapters 5 and 7 admitted the
  same axiom under the same name in two files, `InterfacesCh5.lean` and `InterfacesCh7.lean`;
  wave 2's merge collected all three admitted names in `Interfaces.lean`.

## A2 — Schoenberg: the kernel form of negative definiteness equals the exponential form
**Blueprint:** `prop:fourier-toolbox` (clause 2) · **Lean:** *(not stated yet)*
**Cite:** @schilling2012bernstein — Def. 4.3 and Prop. 4.4, p. 36. Corroboration: @berg1975potential — Thm. 7.8, p. 41; @jacob2001pseudo — Def. 3.6.5, p. 122; Def. 3.6.6, p. 123; Thm. 3.6.11, p. 125

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Schilling–Song–Vondraček Prop. 4.4 p. 36 and Jacob Thm. 3.6.11 p. 125 as used; the Berg–Forst anchor, Thm. 7.8 p. 41, was not independently checked in this pass).
- **Statement as used.** For continuous even `ψ ≥ 0` with `ψ(0) = 0`: `ψ ∈ NDₛ` (that is,
  `e^{−τψ}` positive definite for every `τ > 0`) iff `ψ` is negative definite in the kernel
  sense.
- **What the entry is for.** The blueprint takes the exponential form as the *definition*
  (`def:symmetric-negdef`), so this entry is needed only to import results stated for the kernel
  form — which is how the closure clause A4 and parts of the literature are phrased. It is not
  used in any construction.

## A3 — The symmetric Lévy–Khintchine representation, with a unique pair
**Blueprint:** `prop:fourier-toolbox` (clause 3) · **Lean:** `SpatialLine.fourier_toolbox_levy_converse`, `SpatialLine.fourier_toolbox_levy_unique`, both in `Formalization/SpatialLine/Interfaces.lean` *(the converse and uniqueness clauses; existence is not stated as an axiom — nothing consumes it yet)*
**Cite:** @sato1999levy — Thm. 8.1(i)–(iii), pp. 37–38, with (8.2) for the condition on the Lévy measure

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Thm. 8.1 pp. 37–38, existence is clause (iii)).
- **Statement as used.** Every `ψ ∈ NDₛ` is `a ω² + ∫_{(0,∞)} (1 − cos ωx) ν(dx)` with `a ≥ 0`
  and `∫ (1 ∧ x²) ν(dx) < ∞`; the pair `(a, ν)` is unique; and conversely every such pair
  defines a member of `NDₛ`.
- **Primary.** Existence is clause (iii), not (ii) — the draft records this correction. The
  source states the representation on `ℝ` with a centering term and a Lévy measure on
  `ℝ ∖ {0}`.
- **What the entry does NOT carry.** The *folding* to `(0,∞)`: that a symmetric law has a
  symmetric Lévy measure, that the centering term then vanishes, and that the two halves are
  added under `x ↦ |x|`. That reduction is ours and is written out in the blueprint under
  "The folding convention"; the factor 2 it introduces is the single commonest place for a
  constant to go missing when a statement is carried from a source into this article.
- **How the centering term vanishes, stated correctly (2026-09-14, R157; the external review's
  finding F).** Both this entry and the blueprint's folding paragraph said the term vanishes
  "because `∫ sin(ωx) ν₂(dx) = 0` for symmetric `ν₂`". That integral **need not converge**: for
  `ν₂ ∝ |x|^{−1−α}` with `1 ≤ α < 2` it diverges absolutely near the origin, so the sentence
  cancelled an undefined quantity. The argument runs on the *compensated* integrand of the
  general representation: the odd part of `e^{−iωx} − 1 + iωx·1_{|x|<1}` is
  `−i(sin ωx − ωx·1_{|x|<1})`, which is `O(x³)` at the origin and bounded, hence
  `ν₂`-integrable, and odd, so its integral against a symmetric `ν₂` is `0`. Nothing downstream
  changes: the conclusion, and the folded form the two admitted names quantify over, are the
  same. Both texts now carry the corrected wording.
- **Where the folding reduction sits, in the Lean (fidelity review R37, recorded 2026-09-10).**
  Both admitted names quantify over `SymLevyPair`, whose Lévy measure is folded onto `[0,∞)` by
  construction. So the reduction is **inside** the axioms' statements, not beside them: what
  admitting them takes on trust is "every folded pair defines a continuous negative definite
  function", where the citation reads "every Lévy pair on the punctured line does". The folding
  convention is prose in chapter 2 and not a node, so nothing proves it. The reduction is
  elementary — the two measures give the same `∫(1 − cos ωx)` and their integrability conditions
  correspond — and stating it beside the axioms would mean carrying the punctured-line
  representation as a second definition and restating both axioms on it. That has not been done;
  the excess is *declared* rather than discharged, here and in
  `Formalization/SpatialLine/Interfaces.lean`. It is a widening of the same kind as A21/A22's,
  but a smaller one and of an elementary step, and it does not change the trust-base sentence,
  which names the eleven declarations and the one A21/A22 step.
- **Only one field of the converse's conclusion needs the citation, and the name's page reach is
  wider than the anchor (fidelity review 2026-09-10, F6-5; note-only, nothing changed).**
  `SpatialLine.fourier_toolbox_levy_converse` concludes `IsSymNegDef P.exponent`, a five-field
  structure. Four of the fields are elementary consequences of the *form* of the exponent rather
  than of Thm. 8.1: `continuous` is already **proved here**
  (`SpatialLine.SymLevyPair.continuous_exponent`, by dominated convergence against the truncation
  bound, with `SymLevyPair.exponentL_ne_top` guarding the `.toReal`), and `even`, `nonneg` and
  `map_zero` follow from `ω ↦ 1 − cos ωx` being even, nonnegative and zero at the origin together
  with `a ≥ 0`. What needs the citation is `exp_posDef` alone — and *that* field reaches two pages
  outside the pinned pp. 37–38: `e^{−τψ}` is the characteristic function of the law of the
  triplet `τ·(A, ν, 0)`, which is **Cor. 8.3, p. 38**, and a characteristic function is positive
  definite, which is **Prop. 2.5(i), p. 8** — A1's page, though this development proves that half
  itself (`SpatialLine.isPositiveDefinite_fourierCos`). So the axiom is *not minimal*: it could be
  narrowed to the `exp_posDef` field, as A1 was narrowed to its forward implication and A11 to
  its existence equivalence. **The narrowing has not been taken**: it would change the type and
  every consumer's destructuring, and it buys no page, the name staying on the boundary either
  way. Recorded, not acted on; `SpatialLine/Interfaces.lean` says the same at the axiom.
- **This entry is the workhorse.** It is spent for *uniqueness* in `lem:selfdecomposable-exponents`
  ((1) ⟹ (3)), `prop:choquet-cone`, `thm:matern` and `thm:scale-locality`, and for the
  *converse* direction in `thm:increments-levy` and `thm:main-characterization`(⇐).
- **Lean, 2026-09-09 (proving campaign, chapter 2).** The converse clause is admitted as the
  axiom `SpatialLine.fourier_toolbox_levy_converse`, in `Formalization/SpatialLine/Interfaces.lean`
  and on `blueprint/trust-boundary.txt`. Its only consumer so far is
  `SpatialLine.profile_integrability_mem`, the "consequently" clause of
  `lem:profile-integrability`. The existence and uniqueness clauses have no Lean name yet and
  should get their own when a proof consumes them — the split into two or three names is what
  `trust-boundary.txt` predicted, on the model of the causal A17/A18.
- **Lean, 2026-09-09 (proving campaign, wave 2, chapter 10).** The **uniqueness** clause is now
  admitted too, as `SpatialLine.fourier_toolbox_levy_unique`, in
  `Formalization/SpatialLine/Interfaces.lean` and on `blueprint/trust-boundary.txt`. Its
  only consumer is `SpatialLine.eqOn_maternProfile_of_exponent`, which is the backward
  direction of both equivalence clauses of `thm:matern` — one of the four places this entry's
  own text says uniqueness is spent, so the split is the predicted one and not a widening
  beyond it. Existence still has no Lean name. Note that uniqueness identifies the Lévy
  *measures* and so the profiles only almost everywhere; the passage to the pointwise
  statement `thm:matern` makes is `SpatialLine.eqOn_of_ae_eq_of_antitoneOn`, ours and `[T]`,
  and nothing of it is charged to this entry. Wave 2's merge put the axiom where it belongs,
  beside `fourier_toolbox_levy_converse` in `Interfaces.lean`; the converse direction of the
  main theorem, which chapter 7 proved in the same wave, does **not** spend uniqueness, so this
  entry has exactly two Lean names and existence still has none.
- **Lean, 2026-09-09 (proving campaign, wave 3, chapter 8).** `prop:choquet-cone` — the second
  of the four places this entry's own text names uniqueness — now spends it, through a single
  intermediary, `SpatialLine.sdProfile_unique` ("two profiles with the same exponent have the
  same Gaussian coefficient and the same profile measure"). Its consumers are the node's four
  remaining declarations, `SpatialLine.choquet_cone_injective`,
  `SpatialLine.choquet_cone_extreme_gaussian`, `SpatialLine.choquet_cone_extreme_cin` and
  `SpatialLine.choquet_cone_extreme_only`, in `Formalization/SpatialLine/ChoquetExtreme.lean`.
  **No new axiom was admitted**: this is the same name chapter 10 declared, and the trust
  boundary still holds exactly three. The caveat recorded at chapter 10 applies again and is
  again not charged here: uniqueness identifies the Lévy *measures*, so the tails of the
  Choquet measure are pinned only almost everywhere, and the passage to every positive point
  and thence to the measure itself is `SpatialLine.tail_eq_of_ae_tail_eq` and
  `SpatialLine.measure_eq_of_tail_eq`, ours, `[T]`, and on Lean core.

## A4 — The class is a convex cone, closed under pointwise limits (with the continuity proviso)
**Blueprint:** `prop:fourier-toolbox` (clause 4) · **Lean:** *(not stated yet)*
**Cite:** @jacob2001pseudo — Lemma 3.6.7A, p. 123 (the kernel form, no proviso); @sato1999levy — Prop. 2.5(viii), p. 9 (the proviso: continuity at 0)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Jacob Lemma 3.6.7A p. 123 and Sato Prop. 2.5(viii) p. 9).
- **Statement as used.** `NDₛ` is a convex cone; in the kernel form it is closed under pointwise
  limits with no proviso; and if `ψₙ ∈ NDₛ` with `ψₙ → ψ` pointwise and `ψ` continuous at `0`,
  then `ψ ∈ NDₛ`.
- **Why the proviso is load-bearing.** The causal class is closed under pointwise limits
  outright; the continuity requirement is what the line costs, and it is the same requirement
  that appears in A6. The blueprint's proofs are arranged so that this clause is never spent —
  `thm:increments-levy` extracts the representation directly — but the statement is part of the
  toolbox the article states, so it is grounded.

## A5 — A finite measure on the line is determined by its Fourier transform
**Blueprint:** *(none — retired)* · **Lean:** *(none — the statement is proved)*
**Cite:** @sato1999levy — Prop. 2.5(ii), p. 8

- **RETIRED 2026-09-09 — the statement is proved from Mathlib; the entry is kept for the record
  and grounds no node.** `prop:fourier-uniqueness` is now **[T]**, proved as
  `SpatialLine.fourier_uniqueness` from `MeasureTheory.Measure.ext_of_charFun`, which is this
  statement verbatim for finite measures on a complete second-countable inner product space.
  The entry is kept, with its anchor, because the article's text of record still names the fact
  as classical and a reader may want the citation; no `\ledger{A5}` reference remains in the
  blueprint, and no name enters `trust-boundary.txt` on its account. Author's decision of
  2026-09-09, answering the statement review's Q2.
- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Prop. 2.5(ii) p. 8).
- **Statement as used.** If `μ̂ = ρ̂` pointwise on `ℝ` for finite Borel measures `μ, ρ`, then
  `μ = ρ`.
- **Scope.** Finite measures on `ℝ` only. The corresponding statement for locally finite
  measures on a half-line is `prop:laplace-uniqueness-locally-finite` and is held **[T]**,
  because the causal development proves it and that argument transfers verbatim.
- **The causal twin.** The causal article's A6 is the Laplace analogue; the two entries are the
  same fact on the two transforms, and if the shared Lean core ever carries one it should carry
  both.

## A6 — Lévy's continuity theorem
**Blueprint:** *(none — retired)* · **Lean:** *(none — the consumed clause is proved)*
**Cite:** @sato1999levy — Prop. 2.5(vii), p. 9 (probability measures); Prop. 2.5(viii), p. 9 (the limit function continuous at 0)

- **RETIRED 2026-09-09 — the statement is proved from Mathlib; the entry is kept for the record
  and grounds no node.** `prop:levy-continuity` now states only the clause the article consumes
  — pointwise convergence of the transforms to the transform of a probability measure gives weak
  convergence — and is **[T]**, proved as `SpatialLine.levy_continuity` from
  `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`. Reading the `\uses` edges shows
  that all four consumers (`prop:two-members`(1), `thm:main-characterization`,
  `prop:matern-density`, `prop:thorin-machine`) apply the theorem with the limit law already in
  hand, so the general clause of Prop. 2.5(viii) — the limit function only continuous at `0` —
  has no consumer; it is stated as `rem:levy-continuity-general` and is not a node. The entry is
  kept, with its anchor, for the record; no `\ledger{A6}` reference remains in the blueprint, and
  no name enters `trust-boundary.txt` on its account. Author's decision of 2026-09-09, answering
  the statement review's Q2.
- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Prop. 2.5(vii)–(viii) p. 9).
- **Statement as used.** Pointwise convergence of the transforms of probability measures to the
  transform of a probability measure implies weak convergence; and if the limit function is
  continuous at `0`, it is a transform and the convergence is weak.
- **What the entry does NOT carry.** The passage from weak convergence to convergence of the
  convolution operators in `L¹`, which is the `ε/3` argument in `thm:main-characterization`(⇐)
  and is **[T]**. The causal article's A5 records the same division of labour, and additionally
  records a trap — a boundedness hypothesis in the general measure form — which does not arise
  here because only the probability form is used.

## A7 — The one-dimensional characterization of self-decomposable Lévy measures
**Blueprint:** `prop:sd-exponents` · **Lean:** *(not stated yet)*
**Cite:** @sato1999levy — Cor. 15.11, p. 95 (the one-dimensional `k(x)/x` form), with Thm. 15.10, p. 95 (the polar form on `ℝ^d`) and Def. 15.1, p. 90; Prop. 15.5, p. 93 (self-decomposable ⟹ infinitely divisible)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Cor. 15.11 p. 95, Thm. 15.10 p. 95, Def. 15.1 p. 90, Prop. 15.5 p. 93. Caveat: Cor. 15.11 is the general one-dimensional form with $k$ increasing on $(-\infty,0)$ and decreasing on $(0,\infty)$; the symmetric specialization to a profile on $(0,\infty)$ alone is an immediate consequence, not a verbatim statement at the anchor).
- **Statement as used.** A symmetric infinitely divisible law is self-decomposable iff its Lévy
  measure is `k(x) x^{-1} dx` on `(0,∞)` with `k` nonincreasing; self-decomposability imposes no
  restriction on the Gaussian part.
- **This entry is CITED AND NOT CONSUMED.** `prop:sd-exponents` lies on no proof path: the
  profile form the article needs is proved directly in `lem:selfdecomposable-exponents`, from
  the dilation identity, A3's uniqueness clause, and a convex-tail argument in the
  log-displacement coordinate. This is the one place where the spatial development's trust base
  is *narrower* than its causal twin's, which carries the corresponding statement as its A18 and
  spends it in the analysis direction of the main theorem. The entry is kept because the
  statement is part of the article's text of record and is where a reader meets class `L`.
- **For the verification pass.** Confirm that Cor. 15.11 is the one-dimensional specialisation
  and that Thm. 15.10 is the `ℝ^d` polar form; the draft records this distinction, and the
  causal ledger records that the `ℝ^d` theorem carries no numbered half-line specialisation.

## A8 — A nondegenerate self-decomposable law is absolutely continuous
**Blueprint:** `prop:kernel-regularity` · **Lean:** `SpatialLine.kernel_regularity_law` (with A9; `SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`), consumed by `SpatialLine.kernel_regularity`, `SpatialLine.polya_frequency` and `SpatialLine.exists_smoothing_law`
**Cite:** @sato1999levy — Thm. 27.13, p. 181

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Thm. 27.13 p. 181, stated on $\mathbb{R}^d$, used for $d = 1$).
- **Statement as used.** A self-decomposable law on `ℝ` that is not a point mass has a density.
- **What the entry does NOT carry.** The hypothesis check: that the kernels from the origin are
  self-decomposable is `lem:selfdecomposable-exponents` through `thm:main-characterization`, and
  that they are nondegenerate is `prop:strict-positivity`(2). Both are **[T]**.
- **Scope.** The kernels *from the origin* only. The increments `μ_{s,t}` with `s > 0` are
  infinitely divisible but not in general self-decomposable, and the blueprint claims nothing
  about them. The causal article's A10 is the same theorem in the same role.
- **Narrowed at the origin (fidelity review 2026-09-10, F6-1); the admitted statement changed.**
  `SpatialLine.kernel_regularity_law` concluded, beside absolute continuity, that the density is
  even and `AntitoneOn p (Set.Ici 0)` — nonincreasing on the **closed** half-line. That conjunct
  belongs to A9 rather than to A8, but it is recorded at both entries because the two are spent
  through one Lean name. **It was false, and neither entry carries it.** `AntitoneOn p (Ici 0)`
  gives `p x ≤ p 0` for every `x ≥ 0`, so it asserts that the density is bounded by a real
  number; Thm. 27.13 gives absolute continuity and nothing about the size of the density, and
  Yamazato's Thm. 1 gives convexity left of the mode and concavity right of it, which permits
  `F'(0+) = +∞`. This ledger's own **A10** says the same thing in Sato's vocabulary: at
  `c = k(0+) + k(0−) < 1` the density behaves like `|x|^{c−1}` at the origin. The witness is
  inside the development — the Matérn member at `γ ≤ 1/2`, a symmetric nondegenerate
  self-decomposable law with density of order `|x|^{2γ−1}`, built for every `γ > 0` by
  `SpatialLine.witness_two_members_matern_family`.
  **What is now admitted:** `μ ≪ volume`, an even density, and `AntitoneOn p (Set.Ioi 0)` on the
  **open** ray — this development's own convention for a profile (`SDProfile.k_antitone`).
  Nothing is claimed about `p 0`. The blueprint statement of `prop:kernel-regularity` is
  unchanged, "unimodal with mode at the origin" being a claim about the shape of the density and
  not about its value there; the node carries `% CHANGED (fidelity review 2026-09-10, F6-1)`.
  `SpatialLine.kernel_regularity` re-exports the conjunct and is narrowed with the axiom; the
  other two consumers destructure the absolute-continuity conjunct alone, so no downstream
  content rested on the false clause.

## A9 — A law of class L is unimodal
**Blueprint:** `prop:kernel-regularity` · **Lean:** `SpatialLine.kernel_regularity_law` (with A8; `SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`), consumed by `SpatialLine.kernel_regularity`, `SpatialLine.polya_frequency` and `SpatialLine.exists_smoothing_law`
**Cite:** @yamazato1978unimodality — Thm. 1, p. 523

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Yamazato Thm. 1 p. 523, read from the page image, the copy having no text layer).
- **Statement as used.** Every self-decomposable law on `ℝ` is unimodal; in the symmetric case
  the mode is at the origin. Yamazato's own reading of "unimodal with mode `m`", printed on the
  same page, is that the distribution function is **convex for `x < m` and concave for `x > m`**
  — a statement about the shape of `F` away from `m`, with no value asserted at `m`.
- **What the entry does NOT carry.** The symmetric rider — that a symmetric unimodal law has its
  mode at `0` — which is elementary and **[T]**; and the same hypothesis check as A8. **Nor any
  bound on the density at the mode** (fidelity review 2026-09-10, F6-1): see the narrowing note
  below and at A8.
- **Narrowed at the origin (fidelity review 2026-09-10, F6-1).** The Lean name concluded
  `AntitoneOn p (Set.Ici 0)`, which forces `p x ≤ p 0` for every `x ≥ 0` and so asserts a
  bounded density; that is more than "unimodal with mode at the origin" and is **false** for the
  Matérn members at `γ ≤ 1/2`, whose density is of order `|x|^{2γ−1}` (A10 in Sato's
  vocabulary). What is admitted now is evenness together with `AntitoneOn p (Set.Ioi 0)` on the
  open ray, i.e. nonincreasing on `(0,∞)` and, by evenness, nondecreasing on `(−∞,0)`, with
  nothing asserted at the origin. That is exactly the reflection of Yamazato's convex/concave
  reading under the symmetric rider. The full record is at **A8**.
- **What it buys the article.** "The axioms never produce a multimodal kernel, and no truncation
  of the Gaussian is admissible." That sentence is a claim about the whole cone and rests
  entirely on this entry.

## A10 — The behaviour of a self-decomposable density at the origin
**Blueprint:** `prop:cin-origin-singularity` · **Lean:** *(not admitted — no consumer; `Skeleton.cin_origin_singularity_unbounded`, `_smooth` and `_threshold` are stated in the statement skeleton, `notready`; see the wave-6 note below)*
**Cite:** @sato1999levy — Thm. 28.4, p. 191 (the smooth regime, `N < c ≤ N+1`); Thm. 53.8, pp. 410–411, formulas (53.28) and (53.30) (the singular regime and the threshold `c = 1`)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Thm. 28.4 p. 191 and Thm. 53.8 pp. 410–411 with (53.28)–(53.30). The two open readings are settled from the page image: for $c = 1$, (53.30) reads $f(x) \sim (\kappa/\pi)\cos(c'\pi/2)\,L(x)$ as $x \to 0$ with $\kappa$ the constant of (53.27), an exponential-integral expression and not $1$, $c' = k(0+) - k(0-)$, and $L$ the integral (53.26); the cosine factor is $\cos(c'\pi/2)$).
- **Statement as used.** For a self-decomposable law with no Gaussian part and two-sided
  `k`-function, with `c := k(0+) + k(0−)`: for `c < 1` the density is unbounded with
  `f(x) ≍ |x|^{c−1}`; for `N < c ≤ N+1` it extends continuously with `N − 1` derivatives; at
  `c = 1` it is continuous at no better than logarithmic order, `f(x) ≍ L(x)` with `L` the
  displayed integral.
- **What the entry does NOT carry.** The translation into this article's folding convention: the
  source's `c` on the two-sided profile is exactly the folded `k(0+)` of `(2.3)`, and the
  source's antisymmetric constant `c' = k(0+) − k(0−)` vanishes for a symmetric law. Nor the
  propagation of the singularity to `±nτ`, which is `lem:cin-delay-equation` and is **[T]**.
- **Wave 6 (2026-09-10): the decision not to admit was re-taken, with reasons.** Nothing in
  `SpatialLine` spends any of the three declarations, and the one assembly available — the
  threshold regime instantiated at the `Cin` ray, whose hypotheses
  `SpatialLine.cin_origin_singularity_cin_ray` already verifies — would spend one of the three
  and leave two names unspent. The statements themselves were checked at their edges and hold:
  `c = 0` is excluded from all three and must be (with `a = 0` it forces `k` to vanish on
  `(0,∞)`, hence the law is `δ₀`, which has no density), the Gaussian is excluded by `a = 0`,
  `c = ∞` is excluded by the shape of the hypothesis, and none of the three is vacuous.
  **A second obstacle to admission**, recorded here because it is a property of this entry: the
  Lean statements are in this article's *folded* convention, and the translation from the
  source's two-sided constant is exactly what the bullet above says the entry does not carry.
  The translation is correct for a symmetric law, but admitting these names would place it on
  the trust boundary, which is a review decision rather than a prover's. And the node was
  **never blocked on** `lem:cin-delay-equation`, contrary to the wave-4 and wave-5 inventories:
  the three regimes mention no delay equation, and what did depend on it, the propagation, was
  moved out into `rem:cin-propagation` by review Q8.
- **DELIBERATE NARROWING.** The blueprint node claims the *order* of the singularity and not the
  constant in (53.30). The draft's own check records two unresolved readings: the constant, and
  whether the cosine factor `cos(πc'/2)` is read correctly from the page image. The verification
  pass must settle both before the constant may be asserted anywhere.

## A11 — Bernstein's theorem: completely monotone ⟺ the Laplace transform of a measure
**Blueprint:** `rem:bridge-subordination`, `prop:thorin-subclass` *(`prop:bridge-strictness` dropped its reference on 2026-09-10 — clause (b) below is retired; `lem:bridge-exponents` dropped its delay-law clause the same day, and clause (a) moved with it into the remark, which is prose and carries no `\ledger{}`)* · **Lean:** `SpatialLine.bernstein_completely_monotone` *(in `Formalization/SpatialLine/Interfaces.lean`; **the admitted statement is the existence equivalence only**, not the uniqueness of the representing measure — see below)*
**Cite:** @schilling2012bernstein — Thm. 1.4, p. 3 (2nd ed.), which states the equivalence with uniqueness of the representing measure. Corroboration: @feller2009introduction — Vol. 2, §XIII.4, Theorem 1 and Theorem 1a, pp. 439–440

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Schilling–Song–Vondraček Thm. 1.4 p. 3, Feller Thm. 1 p. 439 and Thm. 1a p. 440, agreeing with the causal ledger's anchors).
- **Statement as used.** `f` is completely monotone iff `f(σ) = ∫ e^{−σu} F(du)` for a positive
  measure `F`, unique; and `f` is the transform of a *probability* measure iff moreover
  `f(0+) = 1`.
- **Three uses, three clauses.** (a) In `rem:bridge-subordination` (until 2026-09-10 in
  `lem:bridge-exponents` itself), the probability form produces the delay `T_1` and so realises
  `e^{−τ g(ω²/2)}` as a positive mixture of Gaussian transforms. (b) In
  `prop:bridge-strictness`(2), analyticity of a Laplace transform gives that a completely
  monotone function vanishing at one interior point vanishes identically — the Fourier-side
  substitute for the causal vanishing lemma, here applied on the *causal* side. (c) In
  `prop:thorin-subclass`, uniqueness of the representing measure is what makes the Thorin
  measure well defined.
- **Agreement with the sibling.** The causal ledger pins the same theorem as its A1 at Feller
  §XIII.4, Thm. 1/1a, pp. 439–440; the two ledgers should agree, and the verification pass
  should say so explicitly.
- **Lean, 2026-09-09 (proving campaign, wave 3).** Admitted as the axiom
  `SpatialLine.bernstein_completely_monotone`, in `Formalization/SpatialLine/Interfaces.lean` and
  on `blueprint/trust-boundary.txt`, spent by `SpatialLine.thorin_subclass_representation` alone.
  **The admitted statement is the existence equivalence only** — completely monotone on `(0,∞)`
  iff the Laplace transform of a measure carried by `[0,∞)`, with the transform finite there.
  Clause (c) above predicted that uniqueness of the representing measure would be spent in
  `prop:thorin-subclass`; **it is not**. That node's uniqueness clause is discharged by
  `SpatialLine.laplace_uniqueness_locally_finite`, which this development proves
  (`prop:laplace-uniqueness-locally-finite`, `[T]`), so the ledger is charged for less than the
  citation carries — the same narrowing wave 2 applied to A1. Clauses (a) and (b), the two uses
  in the bridge chapter, have no Lean and no consumer.
- **Lean, 2026-09-10 (proving campaign, wave 4): clause (b) is retired.**
  `prop:bridge-strictness` is proved entire to Lean core and no longer references this entry.
  Clause (b) mistook the argument for the obligation: `def:causal-admissible` *gives* the
  representing measure `b₀δ₀ + k_I(u)du`, so `F_I'(σ) = b₀ + ∫₀^∞ e^{−σu}k_I(u)du` is a Laplace
  transform by construction and the step needed is only that this is strictly positive unless
  the data vanish — an integral of a positive integrand, `[T]` in
  `Formalization/SpatialLine/CausalExponent.lean` (`CausalAdmissible.deriv_integral_pos`).
  Bernstein's theorem produces a measure; here there was one already. Clause (a),
  in `lem:bridge-exponents`, is unaffected and still has no Lean: there the measure is what is
  wanted and nothing hands it over.
- **Author's decision, 2026-09-10: clause (a) is unadmitted, no consumer, and its blueprint home
  is now a remark.** `lem:bridge-exponents` was narrowed by dropping its delay-law clause —
  `SpatialLine.bridge_exponents` had been proved without reading that hypothesis, so the clause
  stood on two interfaces (this entry's clause (a) and A12) that nothing spent, and the
  statement-skeleton declaration `Skeleton.bridge_delay_law` that typed it is deleted. The node's
  mixture clause now *quantifies over* a delay law rather than asserting one, which loses nothing
  (a law on `[0,∞)` is determined by its Laplace transform) and strengthens the admissibility
  clause by one hypothesis. The existence is `rem:bridge-subordination`, prose, cited to this
  entry and to A12 and marked as not machine-checked. So clause (a) has no Lean name, no consumer
  and no `[A]` node; the entry stays on the trust boundary for the existence equivalence spent in
  `prop:thorin-subclass` alone.
- **What the entry does not carry, and what is proved beside it.** The elementary integral
  `∫₀^∞ (1 − cos ωx)e^{−θx}x^{−1}dx = ½log(1 + ω²/θ²)` and the Tonelli that turns the mixture
  into `eq:thorin`; the integrability correspondence, which turns out to follow from finiteness
  of the Thorin integral at the single frequency `ω = 1`; and the exclusion of an atom of `U` at
  `θ = 0`, which follows from `∫₁^∞ k(x)x^{−1}dx < ∞`. All three are `[T]` in
  `Formalization/SpatialLine/Thorin.lean`.

## A12 — The exponential of a Bernstein function is completely monotone
**Blueprint:** `rem:bridge-subordination` · **Lean:** *(unadmitted, no consumer — see the 2026-09-10 note below)*
**Cite:** @schilling2012bernstein — Thm. 3.7, p. 27 (2nd ed.), clause (iii)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Schilling–Song–Vondraček Thm. 3.7(iii) p. 27).
- **Statement as used.** For `g` a Bernstein function, `e^{−τg}` is completely monotone for every
  `τ > 0`.
- **What it replaces.** Together with A11 it supplies exactly the special case of the
  Bernstein/negative-definite composition rule that the bridge needs, so Jacob Vol. I §3.9 is
  not an entry. Two small cited facts, both needed in Ch. 10 anyway, in place of one large one.
- **Agreement with the sibling.** This is the causal ledger's A2, same anchor.
- **Author's decision, 2026-09-10: unadmitted, no consumer.** This entry served exactly one step,
  the delay law of `lem:bridge-exponents`, jointly with A11 clause (a);
  `SpatialLine.bridge_exponents` turned out to prove the admissibility clause without reading
  that hypothesis, so the step had no consumer. Rather than admit two names nothing spends, the
  node was narrowed: it now quantifies over a delay law, the statement-skeleton declaration
  `Skeleton.bridge_delay_law` is deleted, and the existence is the prose remark
  `rem:bridge-subordination`, which cites this entry and A11(a) and is marked as not
  machine-checked. Nothing in `Formalization/` reaches this entry, and no name of it is on
  `blueprint/trust-boundary.txt`.

## A13 — The moment criterion for infinitely divisible laws
**Blueprint:** `prop:moments-tails` (clause 1) · **Lean:** `SpatialLine.moments_tails_criterion` (`SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`), consumed by `SpatialLine.stable_family_moments` and `SpatialLine.matern_moments_integrable`
**Cite:** @sato1999levy — Thm. 25.3, p. 159 (the `g`-moment theorem for submultiplicative `g`)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Thm. 25.3 p. 159).
- **Statement as used.** For an infinitely divisible law with Lévy measure `ν₂` and a
  submultiplicative, locally bounded, measurable weight `g`, `E g(X) < ∞` iff
  `∫_{|x|>1} g dν₂ < ∞`; used with `g(x) = (|x| ∨ 1)^n`.
- **The weight, corrected (fidelity review 2026-09-10, F6-3).** This entry and the Lean
  docstring both read "used with `g(x) = |x|^n`". **`|x|^n` is not submultiplicative** in Sato's
  Def. 25.2 (p. 159), which asks for `g(x + y) ≤ a g(x) g(y)`: at `y = 0` that would need
  `|x|^n ≤ a |x|^n · 0`. Thm. 25.3 therefore does not apply to it, and the legitimate weight is
  `g(x) = (|x| ∨ 1)^n`, which **Prop. 25.4(iii) and (i) on the same page** list as
  submultiplicative (`|x| ∨ 1` is, and a positive power of a submultiplicative function is). The
  correction is textual, not mathematical: `E (|X| ∨ 1)^n` and `E |X|^n` are finite together
  (they differ by at most the total mass, `|x|^n ≤ (|x| ∨ 1)^n ≤ |x|^n + 1`), and on the Lévy
  side the two weights agree identically on `{|x| > 1}`, which is the only region the criterion
  integrates over. So both sides of the admitted equivalence are unchanged and the name is not
  narrowed; what changes is which theorem of p. 159 the entry is entitled to invoke. The Lean
  statement never named the submultiplicative function: its left-hand side is
  `Integrable (fun x => |x|^n) (μ t)`, the *moment* whose finiteness is being characterised,
  which is the right thing to say.
- **What the entry does NOT carry.** The translation into the folded profile, and the variance
  formula `E X_t² = t² F''(0)` with `F''(0) = 2a + ∫ x² ν(dx)`; both **[T]** and written out in
  the blueprint. Nor the three translation steps the *axiom* carries inside its statement —
  reading the Lévy measure off the transform (which is A3's uniqueness clause), the fold with
  its factor 2, and the dilation invariance in `t`; those are listed by name at the head of
  `blueprint/trust-boundary.txt` (fidelity review F6-2).
- **Agreement with the sibling.** This is the causal ledger's A7, same anchor.

## A14 — The tail floor for a Lévy law with bounded jump support
**Blueprint:** `prop:moments-tails` (clause 2) · **Lean:** `SpatialLine.moments_tails_divergence` (`SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`; the divergence branch alone, **narrowed** -- see the note below), consumed by `SpatialLine.moments_tails_completely_monotone`; `Skeleton.moments_tails_bounded` and `Skeleton.moments_tails_heavy` remain in the statement skeleton, `notready`
**Cite:** @sato1999levy — Thm. 26.1, p. 168

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Sato Thm. 26.1 p. 168 states **both directions on the same page**: clause (i), for $0 < a < 1/c$, finiteness of $\mathbb{E}\,e^{a|X_t|\log|X_t|}$ and $P[|X_t| > r] = o(e^{-ar\log r})$; clause (ii), for $a > 1/c$, the moment is infinite and $P[|X_t| > r]/e^{-ar\log r} \to \infty$. The converse the blueprint's tail dichotomy rests on is clause (ii); the draft's note that the converse was still to read is out of date).
- **Statement as used.** If the Lévy measure is carried by `{|x| ≤ τ}` (a Gaussian part being
  allowed), then `E exp(α|X| log|X|) < ∞` for every `α < 1/τ` and for no `α > 1/τ`.
  **Unbounded-support branch (added 2026-09-09).** If the Lévy measure has unbounded support,
  then `E exp(α|X| log|X|) = ∞` for every `α > 0`, and `P[|X| > r] / e^{-αr log r} → ∞` as
  `r → ∞`. This is clause (ii) of the same theorem read at `c = ∞`: Sato defines
  `c = inf{a > 0 : supp ν ⊂ {|x| ≤ a}}`, sets `c = ∞` for unbounded support and `1/∞ = 0`
  explicitly in the statement (p. 168, (26.1) and the sentence after it), so the branch is a
  direct instance of the printed dichotomy, not a remark or a proof-only fact. The Gaussian part
  is unrestricted (Remark 26.3 treats the pure-Gaussian case `ν = 0` separately). Librarian read
  from the page image 2026-09-09, on the skeleton review's finding R21; the Lean declaration
  `Skeleton.moments_tails_heavy` asserts exactly this branch. (Sato's `c` is an infimum; the
  blueprint's `τ` is the same number.)
- **Fidelity note (2026-09-10, wave 4).** `Skeleton.moments_tails_bounded`'s divergence conjunct
  did not carry the parenthesis above -- that Sato's `c` is an *infimum*. As typed it asserted
  divergence for every `α > 1/(τt)` whenever `k` vanishes beyond `τ`, which is false at `k ≡ 0`
  (the pure Gaussian; Sato's Remark 26.3 treats `ν = 0` separately) and false at any `τ` strictly
  larger than the radius, where it contradicts clause (i) of this same theorem. The declaration is
  repaired -- the divergence conjunct now quantifies over a `τ'` at or beyond which the profile is
  nonzero, which is a lower bound for `c` and is what the entry supports -- and the Lean axiom
  admitted on the trust boundary is that narrowed form, `SpatialLine.moments_tails_divergence`.
  The finiteness branch and the tail-ratio statement are not admitted, nothing consuming them.
- **Verification note.** The draft records the first clause as verified and the converse clause
  as still to read. The blueprint asserts BOTH directions, since the dichotomy is what the
  chapter's conclusion rests on ("no admissible kernel other than the Gaussians has a Gaussian
  tail"). If the converse is not at this anchor, the blueprint statement must be narrowed to the
  finiteness clause and `rem:cone-shape` rewritten.

## A15 — The variance-gamma density and its characteristic function
**Blueprint:** `prop:matern-density` · **Lean:** *(unadmitted, no consumer — the density sentence of `prop:matern-density` is `Skeleton.matern_density`, `notready`, and nothing in `SpatialLine` reaches it: the two clauses of that node that do have Lean, `SpatialLine.matern_density_special` and `SpatialLine.matern_density_gaussian_limit`, print Lean core, the special values being computations on the *definition* of `besselK` and the limit a transform argument. Admitting the entry would put a name on the trust boundary that no proof spends, which is the campaign's rule against. Wording aligned with A10, A16, A18 and A20 on 2026-09-10; it read "not stated yet", which was true of the Lean and silent about the reason)*
**Cite:** @fischer2025variance — the density (1.1) and the characteristic function (2.12); self-decomposability §2.3, p. 6

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Fischer et al. density (1.1) p. 1, characteristic function (2.12) p. 5, self-decomposability §2.3 p. 6).
- **Statement as used.** The symmetric variance-gamma law `VG(2γ, 0, t, 0)` has density
  `(√π Γ(γ) t)^{-1} (|x|/2t)^{γ−1/2} K_{γ−1/2}(|x|/t)` and characteristic function
  `(1 + t²ω²)^{−γ}`; equivalently, the Matérn kernel of smoothness `γ − ½` and range `t`
  normalised to unit mass is that Fourier pair.
- **What the entry does NOT carry.** The identification of the Matérn correlation function with
  the same function normalised to `1` at the origin instead of to unit mass; the two special
  values `γ = 1` and `γ = ½`; and the Gaussian limit. All **[T]**.
- **The Matérn *name* holds only for `γ > ½` (2026-09-14, R156; the external review's finding
  C).** The displayed function is a probability density for every `γ > 0`, and the
  variance-gamma identification is what this entry carries and what the article reads; but a
  Matérn *covariance function* of smoothness `ν = γ − ½` is bounded at the origin, which needs
  `ν > 0`. At `γ = ½` it is `K_0`, logarithmically divergent there. The sentence identifying the
  kernel as the Matérn kernel has left `prop:two-members`(2) altogether and carries the
  restriction at `prop:matern-density`, which is the only place it is now stated.
- **Note on the source's route.** The source argues self-decomposability through Sato Cor. 15.11
  — that is A7 — which the blueprint does not consume. Admissibility of the Matérn exponent is
  obtained instead from `lem:selfdecomposable-exponents` on the explicit profile
  `k(x) = 2γ e^{−x}`, so this entry is needed for the *density*, not for membership of the class.

## A16 — Asymptotics of the modified Bessel function of the second kind
**Blueprint:** `prop:matern-density` · **Lean:** *(not admitted, and after wave 7 it has no second route either. The clause the campaign wanted from this entry — `prop:student-t`(2), the Student-t transform at a general Bessel order — is **proved**, on Lean core, as `SpatialLine.student_transform` (2026-09-10), and it uses **no asymptotic**: `besselK` is defined here by its DLMF integral, and the transform is that integral reached by a change of variables. So chapter 12 never waited on this entry, and the asymptotic itself is still neither proved nor admitted. What remains unformalised is the Matérn tail, which is this entry's own consequence and has no consumer — the wave-6 note below, whose second paragraph, on chapter 12's indirect route, is superseded)*
**Cite:** @dlmf2026 — §10.25(ii), (10.25.3) (`K_ν(z) ∼ √(π/2z) e^{−z}` as `z → ∞`). Corroboration: @abramowitz1964handbook — §9.7

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Abramowitz–Stegun 9.7.2 p. 378, read from the page image; the DLMF record has no stored artifact and is cited by section only).
- **Statement as used** *(narrowed 2026-09-11, R119)*. `K_ν(z) ∼ √(π/2z) e^{−z}` as `z → +∞`,
  for fixed real `ν`, which converts the closed form of A15, at `ν = γ − ½`, into the tail
  `φ_t(x) ∼ c_γ t^{−γ}|x|^{γ−1} e^{−|x|/t}`.
- **Read at the primary (2026-09-11, R119).** The stored DLMF §10.25 carries (10.25.3) verbatim:
  `K_ν(z) ∼ √(π/(2z)) e^{−z}` as `z → ∞` in `|ph z| ≤ 3π/2 − δ`, with **no uniformity in `ν`**.
  The statement as used read "uniformly for `ν` in a compact set", which is not on the page and
  which nothing uses: the tail is taken at one `γ` at a time. The clause is dropped, the safe
  direction, and the entry now asks exactly what (10.25.3) states at real `z > 0`. **Verdict:
  the anchor holds at the primary**, for fixed `ν`. The entry is unadmitted, so no trust-boundary
  name is affected.
- **Note.** `@dlmf2026` is a library record without a stored artifact and is cited by section;
  `@abramowitz1964handbook` is held as page images and is the anchor the verification pass
  should read.
- **DLMF artifact stored (2026-09-11, post-sync follow-up, fidelity row R53).** The note above is
  superseded as to the artifact: the librarian stored DLMF §§ 10.21, 10.25 and 10.32 as markdown
  converted from the live pages (Release 1.2.7, 2026-06-15; retrieved 2026-09-11), attached to
  the `@dlmf2026` Zotero item as `Mathematics/dlmf2026-ch10-secs10.21-10.25-10.32.md`, and
  `library resolve dlmf2026 --json` reports md `stored`. §10.25 is now readable at the primary;
  the anchor has **not** been re-judged against it, and the verification above still rests on
  Abramowitz–Stegun 9.7.2.
- **Corrected 2026-09-09 (statement review, R20).** The power of `t` in the tail read `t^{−γ−½}`
  and is `t^{−γ}`: substituting the asymptotic into the closed form of A15 gives
  `(√π Γ(γ) t)^{−1}(|x|/2t)^{γ−½}√(πt/2|x|)e^{−|x|/t} = c_γ t^{−γ}|x|^{γ−1}e^{−|x|/t}`, the
  scaling `φ_t = t^{−1}φ_1(·/t)` says the same, and the Laplace kernel `e^{−|x|/t}/(2t)` at
  `γ = 1` confirms it. The anchor and the cited asymptotic are untouched; what was wrong was
  this entry's arithmetic in converting it, and the same correction is made at
  `prop:matern-density` and in the draft's §10.
- **Note on the formal `K_ν` (2026-09-09, statement review, Q10).** Mathlib has no Bessel
  function, so `SpatialLine.besselK ν z` is *defined* by DLMF (10.32.9),
  `K_ν(z) = ∫₀^∞ e^{−z cosh u} cosh(νu) du` for `z > 0`, which is the representation this entry's
  own sources work from. The entry is therefore a statement about that integral: a prover
  discharging it has no Mathlib API behind the name and argues from the representation. Nothing
  is claimed at `z ≤ 0`, where the integral diverges and the Bochner integral returns junk, and
  no node of the article is stated there.
- **Unadmitted at the close of the proving phase (2026-09-10, wave 6), and it has no consumer.**
  Its blueprint node `prop:matern-density` is `[A]` and unproved, and the two declarations that
  would spend the entry — the Matérn tail and its asymptotic — are `notready` in the statement
  skeleton. The entry is also what a second, indirect route runs into: chapter 12's *backward*
  direction of `thm:joint-locality` needs `prop:student-t`(2), the Student-t transform, which is
  `|ω|^a K_a(|ω|)` at a **general real order**, and this development has the defining integral of
  `besselK` and no asymptotic for it (F15). So the obstacle is not an argument but a missing
  asymptotic theory, and admitting the entry would put the shape of a statement about an object
  the development cannot compute with on the trust boundary. Not admitted, by the campaign's
  rule that a name joins the boundary only when a proof consumes it.
- **The indirect route was never a route (2026-09-10, wave 7).** The paragraph above named this
  entry as the obstruction to `prop:student-t`(2), and three consecutive inventories repeated it.
  It is wrong, and precisely so: an asymptotic of `K_a` at large argument is what the *Matérn
  tail* needs, while what the Student-t transform needs is the value of one integral, and in this
  development that integral **is** the definition of `K_a`. The Laplace transform of the
  inverse-gamma delay law, `∫₀^∞ u^{-a-1}e^{-1/(2u)-σu}du`, goes to
  `2c^{-a}∫₀^∞ cosh(av)e^{-2√(AB)cosh v}dv` under `u = c e^v` with `A = 1/2`, `B = σ`,
  `c = √(A/B)` — the substitution wave 5 wrote for the first-passage transform, at a general
  order instead of `-3/2`, and *cheaper* there, because at the half-integer order the cosh
  integral additionally has to be evaluated. The declaration is
  `SpatialLine.lintegral_Ioi_rpow_exp_besselKernel`, generalising
  `SpatialLine.lintegral_Ioi_firstPassage`. The entry's own statement, the large-argument
  asymptotic, is untouched by this and stays unadmitted with no consumer; what changed is that
  nothing but the Matérn tail wants it.

## A17 — Thorin: the extended generalized gamma convolutions
**Blueprint:** `lem:thorin-ggc` · **Lean:** *(not admitted — no consumer, and none is scheduled; see the wave-6 note below)*
**Cite:** @bondesson1992generalized — Ch. 7, Definition p. 105, formula (7.1.1) with the integrability condition (7.1.2); the GGC class is Thm. 3.1.1, §3.1, p. 30

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Bondesson Def. and (7.1.1)–(7.1.2) p. 105, Thm. 3.1.1 p. 30).
- **Statement as used.** The extended generalized gamma convolutions are the laws with moment
  generating function `exp{bσ + cσ²/2 + ∫ (log(θ/(θ−σ)) − σθ/(1+θ²)) U(dθ)}`, `U ≥ 0` on
  `ℝ ∖ {0}`; the symmetric members are those with `b = 0` and `U` symmetric.
- **What the entry does NOT carry.** The pairing of `±θ` at `σ = iω`, which gives
  `−log(1 + ω²/θ²)` and hence `(10.1)` with `a = c/2` and `U` folded; the comparison of the two
  integrability conditions; and clauses (4) and (5) of `prop:thorin-subclass` entirely. All
  **[T]**.
- **Open reading (draft check, §10 item 4).** The Lévy-density form of the class — `|x|` times
  the two-sided Lévy density completely monotone on each half-line — still wants its page in the
  source's §7.1. The blueprint does not use that form; `prop:thorin-subclass`(1) is its folded
  statement, obtained from A11 instead.
- **The blueprint binding moved 2026-09-10 (wave 6).** The entry grounded clause (3) of
  `prop:thorin-subclass`; that clause is now the node `lem:thorin-ggc`, and this line names it.
  `prop:thorin-subclass` keeps its original clause numbering — (1), (2), (4), (5) — and its
  `\statusA` line no longer cites this entry, resting on A11 alone.
- **Unadmitted at the close of the proving phase (2026-09-10, wave 6), and no Lean is
  scheduled.** Nothing consumes `lem:thorin-ggc`, and the obstacle to a declaration is the
  entry's own reading rather than the difficulty of a proof: the statement-as-used is a *moment
  generating* function on real `σ`, and the laws the lemma classifies have no exponential moment
  at any `σ ≠ 0`, so a Lean definition of the class by that formula would be empty at the members
  of the family. The reading that does apply is the same formula at `σ = iω` — whose `±θ` pairing
  this entry says in as many words that it does not carry, that pairing being
  `prop:thorin-subclass`(1) ⟺ (2), which the article proves. A definition taken *after* the
  pairing would make the lemma a tautology, which is what the withdrawn
  `Skeleton.thorin_subclass_ggc` was (statement review, R19). Should the clause ever need a
  declaration, what is missing is a formal statement of Bondesson's definition at imaginary
  argument: a librarian read of §7.1 and a new ledger entry, not a Lean exercise.
- **Agreement with the sibling.** The causal ledger's A21 pins Thorin's characterization at
  Bondesson Thm. 3.1.1, p. 30, together with SSV Thm. 8.2, p. 109; the anchors overlap and the
  verification pass should reconcile them.

## A18 — The generalized inverse Gaussian laws are generalized gamma convolutions
**Blueprint:** `prop:student-t`, `lem:student-subordinated` *(the second added 2026-09-11 by the R121 split, replacing `lem:subordinated-members`, which the R44 split had added the same day)* · **Lean:** *(not admitted — no consumer; see the wave-6 note below)*
**Cite:** @halgreen1979self — §2 "The GIGDs are Generalized Γ-Convolutions", pp. 14–15. Corroboration: @grosswald1976student — the infinite divisibility of the Student-t law

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Halgreen §2 pp. 14–15, an unnumbered prose section as the draft expected).
- **Statement as used.** The inverse-gamma laws, being generalized inverse Gaussian, are
  generalized gamma convolutions and hence self-decomposable; so the causal Bessel family is
  causally admissible in the sense of `def:causal-admissible`.
- **What the entry does NOT carry.** Everything spatial: the density computation
  `prop:student-t`(1), the transform (2), the bridge image (3) and the moment count (4) are all
  **[T]**.
- **Note.** The source has no numbered statements, which the causal ledger records for its A8;
  the verification pass should record the same and quote the section heading.
- **Unadmitted at the close of the proving phase (2026-09-10, wave 6), and it has no consumer.**
  What the entry grounds is the *causal* admissibility of the Bessel family, and every clause of
  `prop:student-t` that this article uses is spatial and **[T]**. The spatial clauses are
  unproved for a reason that is not this entry's: clauses (1), (2) and (4) are computations with
  `|ω|^a K_a(|ω|)` at a general real order, and the development has `besselK`'s defining integral
  and no asymptotic for it (F15, and A16's wave-6 note). So admitting A18 would buy nothing —
  it would not close the one place its family is wanted, chapter 12's backward direction, which
  waits on clause (2) and not on causal admissibility.
- **Still unadmitted, and the paragraph above is corrected (2026-09-10, wave 7).** Clauses (1) and
  (2) are now proved, on Lean core, as `SpatialLine.bridge_families_bessel` with
  `SpatialLine.student_density` and as `SpatialLine.student_transform`; no asymptotic was needed
  (see A16). Chapter 12's backward direction is proved and this entry is not on its path: what the
  checked route takes from `prop:student-t` is clause (2) alone, and clause (2)'s proof forms no
  causal exponent. The entry is unadmitted with no consumer, and what still rests on it is the
  *causal* admissibility asserted by `Skeleton.student_causal`, which stays `notready`, and
  clause (3), whose `Skeleton.student_thorin` quantifies over exactly that causal datum. Clause
  (4) does not: `Skeleton.student_moments` carries no causal hypothesis and is open on its own.
- **A second blueprint consumer, and still unadmitted (2026-09-11, the R44 split).** The
  membership sentence of `prop:bridge-strictness`(4) is now the node `lem:subordinated-members`,
  `[A]` on this entry: of its four family memberships the Student-t one asks for exactly what this
  entry grounds, the Lévy data of the inverse-gamma delay law, while the Gaussian, Matérn and
  stable ones are `[T]` and elementary. Nothing changes on the Lean side — the entry is still
  unadmitted, `Skeleton.subordinated_members` is `sorry`, and `Skeleton.student_causal` is the
  declaration that would carry it — but the entry now grounds a *statement of record* and not only
  a skeleton target, which is the form its own wave-6 note said it lacked. Admitting it would close
  one quarter of a node, not a node: the other three data would still have to be written.
- **The other three data are written, and the Student-t membership is its own node (2026-09-11,
  R121, split under the safe-direction delegation; still unadmitted).** The Gaussian, Matérn and
  stable memberships are `SpatialLine.subordinated_members`, on Lean core, from three causally
  admissible data built in `SpatialLine/CausalData.lean` (the drift, the Gamma profile `γe^{-u}`
  and the stable profile `α u^{-α}/Γ(1-α)`); `lem:subordinated-members` is narrowed to those three
  families and is `[T]` and `\leanok`, and no longer cites this entry. The Student-t membership is
  the new node `lem:student-subordinated`, `[A]` on this entry and `notready`, typed as
  `Skeleton.student_subordinated` (`sorry`). So the paragraph above now reads at a whole node:
  admitting this entry, with `Skeleton.student_causal` as its declaration, is what that node waits
  on. Nothing on the Lean side of the entry changes.

## A19 — The modified Bessel equation: solution basis, behaviour at 0, and oscillation
**Blueprint:** `thm:joint-locality` · **Lean:** `SpatialLine.joint_locality_bounded_solution` (clause b′), `SpatialLine.joint_locality_hyperbolic` (clause c) *(in `Formalization/SpatialLine/Interfaces.lean`; clause (a), the solution basis, is **not** admitted — see the wave-5 note below)*
**Cite:** @dlmf2026 — §10.25(i)–(ii), (10.25.1) (the modified Bessel equation) and (10.25.3) (`K_ν` at infinity); §10.30, (10.30.2)–(10.30.3) (`K_ν` at the origin) and (10.30.4) (`I_ν` at infinity); §10.21(i) (the zeros of real cylinder functions); (10.32.9) (the integral representation). Corroboration: @abramowitz1964handbook — §9.6 (in particular 9.6.6, `K_{−ν} = K_ν`, which the stored DLMF sections do not carry) and §9.5 *(Cite line restated 2026-09-11, R119: §10.25 does not carry the behaviour at the origin)*

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Abramowitz–Stegun 9.6.1, 9.6.6–9.6.9 pp. 374–377 and §9.5 p. 370, read from the page image; the DLMF record has no stored artifact. Caveat: clause (a), the transformed equation, is not a table entry and is verifiable only by direct substitution from 9.6.1; candidate to demote to [T]).
- **Statement as used (restated 2026-09-09, statement review, Q13).** (b′) For `c > 0` and
  `ν = (1−β)/2`, the solutions of `φ'' + (β/z) φ' − c φ = 0` that are `C²` on `(0,∞)`, bounded on
  `[0,∞)` and tend to `1` at the origin are exactly the normalised
  `2^{1−ν} Γ(ν)^{−1} (√c z)^ν K_ν(√c z)` when `ν > 0`, and there are none when `ν ≤ 0`.
  (c) Every nontrivial solution of the corresponding *ordinary* Bessel equation has infinitely
  many positive zeros.
- **As the source states it.** (a) The general solution of `w'' + ((1−2ν)/z) w' − w = 0` on
  `(0,∞)` is `z^ν (c₁ K_ν + c₂ I_ν)(z)`. (b) `z^ν K_ν(z) → 2^{ν−1} Γ(ν)` as `z → 0` for `ν > 0`,
  while `z^ν K_ν(z) ≍ z^{−2|ν|}` for `ν < 0` and `z^0 K_0(z)` diverges logarithmically;
  `z^ν I_ν` is unbounded at infinity. (b′) is (a) and (b) combined into the consequence the
  article consumes: the `I_ν` branch is discarded in one line by boundedness, the normalisation
  is (b)'s limit, and the non-existence for `ν ≤ 0` is (b)'s two behaviours at the origin. The
  restatement was made because the entry should say what the proof spends, and because it makes
  the `C²` qualifier visible — an admissible `F` is only `C¹` off the origin, and the regularity
  of `φ` comes from the locality hypothesis of `def:localities`, not from admissibility.
- **What the entry does NOT carry.** The reduction of the covariant second-order equation to
  that ordinary differential equation, and the exclusions — the hyperbolic case through
  `lem:nonvanishing`, the degenerate case through (ND). Both **[T]** and written out. Nor the
  `C²` regularity of `φ`, which is **[T]** and is derived in the node's proof.
- **Substitution check.** Clause (a) is verifiable by direct substitution from
  `K_ν'' + K_ν'/z − (1 + ν²/z²) K_ν = 0`; the verification pass may prefer to record that
  computation rather than a table anchor, in which case the clause can be demoted to **[T]**.
  Note (2026-09-09) that demoting (a) would *not* discharge what the article spends: the
  consumed statement (b′) rests on the asymptotics (b), not on the substitution.
- **The caveat above, restated (fidelity review 2026-09-10, F6-7). Clause (a) is unadmitted as a
  *name*, but the substitution it records is carried *inside* both names, so the entry is not
  charged for less on that account.** The two axioms are stated about the covariant equation
  `φ'' + (β/z)φ' − cφ = 0` and conclude in terms of `SpatialLine.besselK`; nothing between the
  two is written down anywhere in this development. What admitting them takes on trust is
  therefore the whole passage, of which the substitution `φ(z) = z^ν w(√c z)`, `ν = (1−β)/2`,
  reducing the equation to A&S 9.6.1 (respectively to the ordinary Bessel equation for `c < 0`)
  is the first step. Beyond it each name carries one step more: `joint_locality_bounded_solution`
  carries the elimination of the `I_ν` branch by boundedness and the passage from the
  asymptotics 9.6.7–9.6.9 to a *pointwise identity on all of* `(0,∞)`, which is uniqueness for a
  second-order linear ODE; `joint_locality_hyperbolic` carries the transfer of zeros through
  `z^ν ≠ 0` on `(0,∞)` and the reading of §9.5 at a **general real cylinder function**
  `C_ν = J_ν cos πt + Y_ν sin πt` rather than at `J_ν` and `Y_ν` separately — p. 370 states the
  infinitude of real zeros for `J_ν, J'_ν, Y_ν, Y'_ν` and asserts interlacing "for any real
  cylinder function", which presupposes the general case without stating it, so at the readable
  anchor that case is *implicit*. The earlier sentence "the entry is charged for less than the
  source states" is true of the **conclusion** — what the article spends is the uniqueness of the
  bounded normalised solution, not the solution basis — and it should not be read as saying the
  substitution sits outside the trust base. It does not. These steps are listed by name at the
  head of `blueprint/trust-boundary.txt` (fidelity review F6-2).
- **The primary anchor is still unreadable (fidelity review 2026-09-10).** `@dlmf2026` has no
  stored artifact — `library resolve dlmf2026 --json` reports pdf, md and latex all `absent` —
  so §10.25, §10.21 and (10.32.9) could not be read in this pass either, and the judgements above
  are made on the Abramowitz–Stegun corroboration, read as page images (pp. 370, 374–377). A&S
  carries every formula clause (b′) needs: 9.6.1 (the equation), 9.6.6 (`K_{−ν} = K_ν`), 9.6.7,
  9.6.8 (`K_0 ∼ −ln z`) and 9.6.9 (`K_ν(z) ∼ ½Γ(ν)(z/2)^{−ν}` for `Re ν > 0`), and 9.6.24, which
  is `SpatialLine.besselK`'s defining integral **with no restriction on `ν`**. The one place it
  is thinner than the axiom is clause (c)'s general cylinder function, as just described. Either
  acquire a DLMF artifact or restate the Cite line on the A&S anchor; until then the corroboration
  is doing the work of the primary.
- **The DLMF artifact is stored (2026-09-11, post-sync follow-up, fidelity row R53).** The first
  of those two directions is taken: the librarian stored DLMF §§ 10.21, 10.25 and 10.32 as
  markdown converted from the live pages (Release 1.2.7, 2026-06-15; retrieved 2026-09-11), with
  (10.32.9) in the third part, attached to the `@dlmf2026` Zotero item as
  `Mathematics/dlmf2026-ch10-secs10.21-10.25-10.32.md`; `library resolve dlmf2026 --json` reports
  md `stored`, pdf and latex `absent`. The anchors have **not** been re-judged against it: the
  judgements above still rest on the A&S page images, and reading §10.25, §10.21 and (10.32.9) at
  the primary, clause (c)'s general cylinder function first, is owed to a later pass.
- **Read at the primary (2026-09-11, R119).** The librarian returned the stored passages verbatim
  and, because §10.25 turned out not to carry the limiting forms at the origin, fetched and
  stored §10.30 from the same release (Release 1.2.7) on the same Zotero item
  (`Mathematics/dlmf2026-ch10-sec10.30.md`). Judged clause by clause:
  - **(10.32.9)** is `K_ν(z) = ∫₀^∞ e^{−z cosh t} cosh(νt) dt` for `|ph z| < π/2`, with no
    restriction on `ν`: `SpatialLine.besselK`'s definition at `z > 0` and every real `ν` is at
    the letter. **Holds.**
  - **(b′).** §10.25 carries the equation (10.25.1) and the behaviour at infinity (10.25.3), and
    **not** the behaviour at the origin; DLMF's own note at §10.25(iii) sends the reader to §10.30
    for it. So the Cite line's "§10.25 (… behaviour at 0 and ∞)" **failed as to 0**. At §10.30:
    (10.30.2) `K_ν(z) ∼ ½Γ(ν)(½z)^{−ν}` for `Re ν > 0` and (10.30.3) `K_0(z) ∼ −ln z` as `z → 0`
    are A&S 9.6.8–9.6.9 at the letter, and (10.30.4) gives the growth of `I_ν` at infinity. The
    Cite line is restated to name §10.30 (delegated, the source's letter). The `ν < 0` branch also
    needs `K_{−ν} = K_ν` (DLMF (10.27.3), not stored), which stays on A&S 9.6.6. With that,
    **(b′)'s formulas hold at the primary**; what `joint_locality_bounded_solution` carries beyond
    them is unchanged (the substitution, the elimination of `I_ν`, ODE uniqueness).
  - **(c), the general cylinder function.** DLMF §10.21(i) does **not** state the infinitude of
    positive zeros for a general real cylinder function by name either. It states it for
    `J_ν, Y_ν, J′_ν, Y′_ν` at real `ν`, and it states that "the positive zeros of any two real
    distinct cylinder functions of the same order are interlaced"; with (10.21.4),
    `C_ν = J_ν cos πt + Y_ν sin πt`, the general case follows in one line — a `C_ν` not
    proportional to `J_ν` has a zero between any two consecutive positive zeros of `J_ν` — and
    (10.21.19)'s closing sentence, the large-`t` expansion of the zero `ρ_ν(t)`, presupposes it.
    **So the primary is better than A&S p. 370 but the step does not vanish**: an implicit
    presupposition becomes a one-line deduction from two stated sentences, and
    `joint_locality_hyperbolic` still carries it. Also carried, and not at the stored sections:
    that a nontrivial real solution of Bessel's equation is a real multiple of some `C_ν` (the
    fundamental pair `J_ν, Y_ν`, DLMF §10.2(ii), not stored and not read here). The per-name list
    at the head of `blueprint/trust-boundary.txt` is restated to match; no status changed and no
    name was added or removed.
- **Admitted 2026-09-10 (wave 5), at clauses (b′) and (c) only.** The two Lean names above are
  declared in `Formalization/SpatialLine/Interfaces.lean` and on
  `blueprint/trust-boundary.txt`; their one consumer is
  `SpatialLine.joint_locality_forward`, the forward direction of `thm:joint-locality`, in the
  cases `c > 0` and `c < 0`. Clause (a) is not admitted, and the entry is therefore charged for
  less than the source states: what the article spends is the *uniqueness* of the bounded
  normalised solution, which is (b)'s asymptotics, and the substitution check on (a) is not what
  anything rests on. Both names carry the `C²` qualifier explicitly (review R22), and the
  article *proves* the qualifier rather than assuming it —
  `SpatialLine.joint_locality_ode` concludes the regularity of `φ` from the locality hypothesis,
  which is why that node was proved before either axiom was admitted.
- **Edge cases checked against the entry before admission (2026-09-10).** At `ν ≤ 0` the first
  name asserts nothing: its conclusion `0 < (1−β)/2` *is* the entry's "there are none when
  `ν ≤ 0`", carried as a conclusion rather than excluded by a hypothesis. The constant `φ ≡ 1`,
  which is bounded and normalised, does not solve the equation for any `c > 0` (it would give
  `−c = 0`), so it is no counterexample to the uniqueness clause; at `c = 0` it *is* the
  solution, and that case is **proved** (`SpatialLine.joint_locality_degenerate`), not cited.
- **Note on the formal `K_ν` (2026-09-09, statement review, Q10).** As at A16: Mathlib has no
  Bessel function, so `SpatialLine.besselK ν z` is defined by DLMF (10.32.9),
  `∫₀^∞ e^{−z cosh u} cosh(νu) du` for `z > 0`, and this entry is a statement about that
  integral. `I_ν` is not defined anywhere in the development — it has no single integral
  representation valid for every real `ν` — which is the other reason the entry is stated in the
  form (b′) rather than as the solution basis.

## A20 — The half-plane Dirichlet problem of generalized axially symmetric potential theory
**Blueprint:** `rem:gaspt-uniqueness` (alone since 2026-09-10; the fidelity review took the reference off `thm:joint-locality`’s status line, row R33) · **Lean:** *(not admitted, and neither clause has a consumer. The **existence** clause is **proved**, not axiomatized: `SpatialLine.student_scaleSpace_gaspt` (wave 7, 2026-09-10; with `SpatialLine.integral_student_gaspt_kernel` and `SpatialLine.hasDerivAt_studentWeight` under it), on Lean core. The **uniqueness** clause is cited and not proved, and after wave 7 its only assertion in the blueprint is `rem:gaspt-uniqueness`; no declaration spends it, which is why this entry is not on the trust boundary. The wave-5 and wave-6 notes below record the decision not to admit; what has changed is that the existence clause is no longer an open obligation)*
**Cite:** @weinstein1953generalized — §10, p. 34, eq. (43) (the Poisson integral for `k < 1`, and the non-existence of Green's function for `k ≥ 1`); @huber1954uniqueness — Thm. 2, p. 356 (uniqueness among bounded solutions)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Weinstein §10 eq. (43) and the non-existence of the Green's function for $k \ge 1$, p. 34; Huber Thm. 2 p. 356. Caveat: Huber's Theorem 2 as displayed carries no explicit boundedness qualifier for the uniqueness clause, the $k \ge 1$ case reading $u \equiv 0$ unconditionally; the "bounded solutions" language may be a standing hypothesis of his §§1–2, to be reread before the entry is called settled).
- **Statement as used.** For `k = β < 1` the Dirichlet problem for
  `z_xx + z_yy + (k/y) z_y = 0` on the half-plane is solved by
  `A y^{1−k} ∫ f(ξ) ((x−ξ)² + y²)^{−(2−k)/2} dξ`, which with `k = 1 − 2ν` is the Student-t
  kernel `∝ t^{2ν}(t² + x²)^{−ν−½}`; and the bounded solution is unique, unbounded null
  solutions `y^{1−k} v` existing.
- **What the entry does NOT carry.** That the scale space is bounded — `|u| ≤ ‖f‖_∞` from
  positivity and unit mass — which is what places it in the class the uniqueness clause speaks
  about, and is **[T]**.
- **The boundary of the range is exactly the boundary of admissibility.** Weinstein's
  non-existence of Green's function at `k ≥ 1` is `ν ≤ 0`, which the blueprint excludes by the
  behaviour of `z^ν K_ν` at the origin. That the two exclusions coincide is a consistency check
  the verification pass should record, not a claim the entry carries.
- **Not admitted 2026-09-10 (wave 5), and the reason is the campaign's rule.** An axiom is
  added only when a proof consumes it. The forward direction of `thm:joint-locality`
  (`SpatialLine.joint_locality_forward`) does not reach the Dirichlet problem at all: it runs
  through the ordinary-differential input A19 and the exclusions, and stops at the
  classification of the exponent. The backward direction, which *would* consume the entry's
  **existence** clause — the regularity and the equation of the Student-t scale space, which is
  what the `⇐` half of the node has to exhibit — is not proved, being blocked on
  `prop:student-t`(2), itself an unadmitted `[A]`. The entry's **uniqueness** clause, the part
  whose boundedness qualifier the caveat above is about, is consumed by *neither* direction.
- **Open (draft check, §12 item 7).** The normalisation constant `A` against
  `prop:student-t`(1). Weinstein fixes it by `f ≡ 1`, which is unit mass; the blueprint does not
  assert the constant.
- **The decision not to admit was re-taken at the close of the proving phase (2026-09-10, wave
  6), and the block was re-read rather than inherited.** Chapter 12's backward direction is the
  only consumer there would be, and it is blocked on two things, of which this entry is neither:
  `prop:student-t`(2), an unadmitted `[A]` waiting on a Bessel asymptotic (A16, A18), and the
  `C²` regularity of the Student-t scale space, which the `⇐` half has to exhibit. The second of
  those is no longer general: wave 6 proved the joint regularity of *any* dilation family's scale
  space (`SpatialLine.contDiffOn_uncurry_mconv_dilate`), so what remains at the Student-t member
  is the identification of its kernels as the dilates of one law, which is clause (1), and the
  transform, which is clause (2). The uniqueness clause, whose boundedness qualifier the
  caveat above is about, is still consumed by neither direction, so that caveat is still not
  load-bearing.
- **The existence clause is proved, and the uniqueness clause is all that is left cited (2026-09-10, wave 7).**
  Chapter 12's backward direction was written and neither obstruction survived contact with the
  Lean statement. `prop:student-t`(2) is proved (see A16 below), and the existence clause of this
  entry — that the Poisson integral against the Student-t kernel is a `C²` solution of the GASPT
  equation — is `SpatialLine.student_scaleSpace_gaspt`, on Lean core. The regularity half is the
  dilation-structure lemma wave 6 proved; the equation half is the density identity
  `((1+w²)φ)'(w) = β w φ(w)` read under one integration by parts, with a *constant* dominating
  function because the compact support of the test function confines the dilation variable. What
  the source carries that this article does not prove is therefore now exactly one thing: the
  **uniqueness** of the bounded solution, which `rem:gaspt-uniqueness` states and cites and which
  no direction of `thm:joint-locality` evaluates. The recorded caveat about Huber's boundedness
  qualifier is still not load-bearing, and remains a thing to reread only if some later node
  spends the uniqueness clause. **Left for the fidelity review:** `thm:joint-locality`'s status
  line still carries `\ledger{A20}` beside `\ledger{A19}`, with the annotation explaining that
  the entry grounds nothing the theorem asserts and pointing at the remark. Under LINKAGE rule 7
  — `\ledger{}` is for an entry carrying part of *this* node's statement — that reference should
  probably move to the remark alone, as A11 and A12 moved to `rem:bridge-subordination` on
  2026-09-10. It is a decision about a statement of record and is not taken at a merge.

## A21 — Schoenberg's representation of Pólya frequency densities on the line
**Blueprint:** `prop:polya-frequency`, `thm:scale-monotone-noncreation` · **Lean:** `SpatialLine.polyaExponent_of_variationDiminishing`, `SpatialLine.variationDiminishing_of_polyaExponent` (`SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`), consumed together by `SpatialLine.polya_frequency`; the sufficiency leg since 2026-09-11 only through the theorem `SpatialLine.isVariationDiminishing_of_polyaExponent`, and through it by `SpatialLine.polya_frequency`, `SpatialLine.scale_monotone_converse`, `SpatialLine.exists_smoothing_law` and `SpatialLine.isVariationDiminishing_gaussianKernel`; the necessity leg also by `SpatialLine.scale_monotone_step_one`
**Cite:** @karlin1968total — Ch. 7, Thm. 3.2(a), p. 345, with Remark 3.1, p. 346; and Ch. 7 §2, the class `E₂` at (2.2) and the sentence following it, p. 336 (the parameter range `γ ≥ 0`, real `a_i`, `∑a_i² < ∞`, and that `1/ψ` for `ψ ∈ E*₂` with `γ + ∑a_i² > 0` **is the Laplace transform of a PF density**); and Ch. 7 §1, Prop. 1.4, p. 333, **"if `f` is a PF density, then its Laplace transform exists in an open strip containing the imaginary axis"** — the domain on which Thm. 3.2(a)'s identity holds, added 2026-09-12 with the restatement at the letter (rows R150, R151), since the Lean statements now assert that strip

- **Page 336 added 2026-09-10 (fidelity review, F6-4).** The sufficiency direction of this
  article needs a *density* to exist, and the Lean name
  `SpatialLine.variationDiminishing_of_polyaExponent` hypothesises none — the docstring said
  "no density is hypothesised because A21's sufficiency leg *produces* one". That is right, but
  **the sentence that produces one is not at the pinned anchor**: Thm. 3.2(a) on p. 345 is an
  *iff about a density function*, and read forwards it presupposes the density rather than
  yielding it. The producing sentence is on **p. 336**, immediately after (2.2): "φ(s) = 1/ψ(s)
  for ψ(s) in `E*₂` is the Laplace transform of a PF density, provided `γ + ∑a_i² > 0`". On the
  old anchor alone the step was unsupported; with p. 336 the axiom is `≤ source`. The same page
  carries verbatim the parameter range this entry's "Statement as used" quotes, so the addition
  costs nothing and closes two gaps at once.
- **Anchor moved 2026-09-07** (librarian, read from the held copy): clause (b) of Karlin's Thm. 3.2 is the **one-sided** representation (class $\mathcal{E}_1$, $\lambda_i \ge 0$, PF functions vanishing on a half-line, p. 336); the two-sided form on the whole line with real $a_i$ of either sign and $\sum a_i^2 < \infty$ (class $\mathcal{E}_2$) is **clause (a)** of the same theorem, same page 345. The citation below is corrected accordingly; the causal ledger's pin at (b) is right for its one-sided use.
- **Statement as used.** `φ` is a Pólya frequency density iff the reciprocal of its two-sided
  Laplace transform is `e^{−γσ² + δσ} ∏_i (1 + λ_i σ) e^{−λ_i σ}` with `γ ≥ 0`, real `λ_i`,
  `∑ λ_i² < ∞`, the identity holding at complex `σ` on an open strip containing the imaginary
  axis (Prop. 1.4, p. 333).
  **No constant, corrected 2026-09-12 (phase C1c).** This bullet read `C e^{−γσ² + δσ}∏…` until
  then. Karlin's (2.2), p. 336, carries a factor `s^k` and no constant, and `E₂*` is the subclass
  with `ψ(0) = 1`, which forces `k = 0` and leaves no constant to name — which is also why the
  Lean `ScaleSpace.polyaE2` has none. The `C` was this ledger's, not the page's; dropping it
  removes a disagreement with the node, whose annotation was rewritten to the letter the same
  day, and changes nothing that was proved.
- **THE TWO-SIDED FORM IS THE ONE NEEDED HERE.** The causal ledger's A20 pins the *one-sided*
  representation at the same theorem; the verification pass must confirm that clause (b) at
  p. 345 is the two-sided statement and that the `λ_i` are real of either sign, since the
  symmetry reduction (`δ = 0`, `λ_i` in `±` pairs, `∏(1 − λ_i²σ²)`) is what produces the
  Gaussian-plus-Thorin-atoms form of `prop:polya-frequency`(1). If the two-sided form lives
  elsewhere in Ch. 7, the anchor must move.
- **What the entry does NOT carry.** The symmetry reduction itself, the identification
  `γ = a`, `λ_i = 1/θ_i`, the variance reading of the summability condition, and the three
  exclusions (non-integer Matérn, Student-t and stable, `Cin` rays). All **[T]** and written out.
- **Admitted 2026-09-10 (wave 4), jointly with A22**, as the two directions of
  `prop:polya-frequency`(1) *about a single law*: A21 and A22 are never spent apart, and Karlin's
  theorems are about one kernel, so the single-law form is closer to the citation than the
  family form. The family is put back by the `[T]` assembly `SpatialLine.polya_frequency`.
- **The one place a `[T]` step sat inside an axiom, from 2026-09-10 to 2026-09-12.** The
  symmetry reduction and the matching named above were not proved beside the axioms: the record
  read the passage from A21's reciprocal Laplace transform to this article's exponent as an
  analytic continuation of `Ψ(σ) = φ̂(iσ)` off the imaginary axis, needing the two-sided Laplace
  transform as an entire function together with an identity theorem, and the axioms were
  therefore stated in the article's own vocabulary with the matching inside them. **Both halves
  of that reading were wrong, and the step is now machine-checked** — see the discharge bullet
  below (rows R150 and R151). A fidelity review of chapter 13 should start at that bullet.
- **"Every other admitted name carries only what its pages carry" is withdrawn (fidelity review
  2026-09-10, F6-2).** The sentence stood at this entry, at A22, at the head of
  `blueprint/trust-boundary.txt`, in `README.md` and in `CLAUDE.md`. The interface pass read all
  eleven names against the page images and found it inaccurate: **eight of the eleven carry a
  step beyond their pages** — the folding convention inside `fourier_toolbox_levy_converse`, the
  symmetric rider and the choice of representative inside `kernel_regularity_law`, three
  translation steps inside `moments_tails_criterion`, the radius bound and the dilation inside
  `moments_tails_divergence`, the sign-change reconciliation and the a.e.-to-density step inside
  this entry's necessity leg, integrable test functions and the representative choice inside its
  sufficiency leg, and the substitution to the Bessel equation inside both A19 names. The
  **per-name list is at the head of `blueprint/trust-boundary.txt`**, which is the canonical
  place; this entry, A22, `README.md` and `CLAUDE.md` point there rather than repeating it.
  What survives of the withdrawn sentence is that this pair's step is the **deepest** — the only
  one that is an analytic continuation rather than an elementary translation, and the only one
  the author has recorded a decision about. Nothing below is new work taken on trust and no
  status changed; what changed is the resolution at which the trust base is stated.
- **Author's decision, 2026-09-10: the debt is accepted, and the claim is qualified to match.**
  The two admitted compositions carry, beyond their citations, the symmetry reduction and the
  parameter matching between Karlin's two-sided Laplace representation and this article's
  exponent — an analytic-continuation step the blueprint marks `[T]` and proves in prose, not
  machine-checked, and queued for the shared core (`ScaleSpaceCore`: the two-sided Laplace
  transform as an entire function, with an identity theorem). Until that lands, the honest
  statement of this article's trust base is *Lean core, plus the eleven names of
  `blueprint/trust-boundary.txt`, plus the steps that file's per-name list records inside eight
  of them, of which this one is the deepest*; it is said in the same words at A22, at the head
  of `blueprint/trust-boundary.txt`, in `README.md` and in `CLAUDE.md`. (The clause about the
  other seven replaces "plus this one step inside A21 and A22", which fidelity review F6-2
  corrected on 2026-09-10.) No status changes: the node stays `[A]` and the theorems that spend
  the pair stay `\leanok`.
- **DISCHARGED, 2026-09-12 (phase C1c; rows R150 and R151). The debt is paid, not accepted, and
  the reason it was thought unpayable was a misreading of this entry's own pages.** Read from the
  held copy: Karlin's Thm. 3.2(a) (p. 345) is stated at *complex* `s`, and Prop. 1.4 (p. 333)
  puts the Laplace transform of a Pólya frequency density on an **open strip containing the
  imaginary axis**. So `s = iω` lies inside the region where `1/φ = ψ` already holds and nothing
  is continued anywhere; the "analytic continuation" of the bullets above was never part of the
  argument. What the matching actually consumes is (i) evenness of `ψ` on a real interval of that
  strip, which the symmetry of the law gives outright, (ii) the consequence `δ = 0` with every
  odd power sum `∑_j a_j^{2k+3}` vanishing, and (iii) the modulus of `ψ` on the imaginary axis,
  with the reflection invariance of the finite atomic measure `∑_j a_j² δ_{a_j}` turning
  `½∑_j log(1 + a_j²ω²)` into `∑_j log(1 + (a_j⁺)²ω²)` — so the integer weights come from a
  halving identity and not from pairing the parameters index by index, and `λ_j = a_j⁺`. Items
  (ii) and (iii) are `ScaleSpace.polyaE2_even_imp_oddPowerSums`,
  `ScaleSpace.tsum_eq_two_mul_tsum_posPart` and `ScaleSpace.norm_polyaE2_mul_I` in
  `ScaleSpaceCore` v0.2.0, all on Lean core; the assemblies are
  `SpatialLine.isPolyaExponent_of_variationDiminishing` and
  `SpatialLine.variationDiminishingOrd_of_polyaExponent`
  (`SpatialLine/PolyaMatching.lean`), each on Lean core plus the axiom of its own direction.
  **Both axioms are restated at this entry's letter** (the author's decision of 2026-09-11): they
  no longer mention `F`, and the article's `hsym` and `hcos` move to the two theorems, which keep
  the old signatures so that no consumer statement changes. Dropping `hsym` widens what the
  necessity axiom asserts — it now speaks about asymmetric Pólya frequency densities too, as
  Karlin's page does — which is why it was the author's decision and not a delegated one. No
  status changed, the trust boundary still holds exactly eleven names, and the headline
  `#print axioms` lines are byte-identical across the change. What the two names still carry
  beyond their pages is the per-name list at the head of `blueprint/trust-boundary.txt`; the
  symmetry reduction and the matching are no longer on it.
- **The essential sign-change count (fidelity review R14, recorded 2026-09-10).** The counting
  in this development is `signChangesAE`, an infimum over every a.e. representative including
  non-measurable ones, where the cited theorems count on bounded Borel functions. The necessity
  leg is safe and the sufficiency leg needs one further step; the two cases are set out at
  **A22**, and `SpatialLine/Interfaces.lean` says the same there.
- **The sufficiency step is proved, and the sufficiency leg is narrowed to the letter
  (author's decision (b) of the fidelity review, 2026-09-11).** The further step the bullet above
  left believed is now machine-checked on Lean core:
  `SpatialLine.exists_measurable_rep_signChanges_le` (`SpatialLine/MeasurableHull.lean`) replaces
  any representative of a measurable `g` by a measurable one with no more sign changes and no
  larger absolute value, so the infimum defining `signChangesAE` is attained along measurable
  representatives (`SpatialLine.signChangesAE_eq_iInf_measurable`). In consequence
  `SpatialLine.variationDiminishing_of_polyaExponent` now concludes
  `SpatialLine.IsVariationDiminishingOrd` — Karlin's own ordinary count, on measurable test
  functions — and the essential form is the theorem
  `SpatialLine.isVariationDiminishing_of_polyaExponent`, which adds only the proved reduction
  `SpatialLine.isVariationDiminishing_of_ord`. What this pair carries beyond its pages is
  therefore one item shorter: the integrable test functions of A22 remain, and the symmetry
  reduction and the matching remain; the choice of representative does not. No status changed and
  no `#print axioms` line changed. Set out in full at **A22**.
- **Hypothesis range, checked against the page (2026-09-10).** Thm. 3.2(a) carries
  `γ + ∑a_i² > 0`, which p. 346 states is "essential in order that `f` be a bona fide density
  function". `SpatialLine.variationDiminishing_of_polyaExponent` carries it as
  `hnd : ∃ ω, F ω ≠ 0`; the excluded case is the point mass at the origin, whose convolution
  operator is the identity and is variation-diminishing for elementary reasons, so it is
  **proved** (`SpatialLine.isVariationDiminishing_dirac_zero`) rather than cited.

## A22 — Variation diminution and total positivity coincide for translation kernels
**Blueprint:** `prop:polya-frequency`, `thm:scale-monotone-noncreation` · **Lean:** `SpatialLine.polyaExponent_of_variationDiminishing`, `SpatialLine.variationDiminishing_of_polyaExponent` (`SpatialLine/Interfaces.lean`, on `blueprint/trust-boundary.txt`), consumed together by `SpatialLine.polya_frequency`; the sufficiency leg since 2026-09-11 only through the theorem `SpatialLine.isVariationDiminishing_of_polyaExponent`, and through it by `SpatialLine.polya_frequency`, `SpatialLine.scale_monotone_converse`, `SpatialLine.exists_smoothing_law` and `SpatialLine.isVariationDiminishing_gaussianKernel`; the necessity leg also by `SpatialLine.scale_monotone_step_one`
**Cite:** @karlin1968total — Ch. 5, Thm. 4.2 (with Thm. 3.1(i) for the direction from total positivity to variation diminution)

- **Anchor verified 2026-09-07** (librarian, read from the held copy; Karlin Thm. 3.1(i) p. 233 for sufficiency and Thm. 4.2 pp. 242–243 for necessity, the two-sided translation-kernel setting as stated).
- **Statement as used.** Convolution by a kernel is variation-diminishing iff the kernel is
  totally positive, that is a Pólya frequency density. Both directions are used: the necessity
  leg converts the hypothesis of `thm:scale-monotone-noncreation` into a Pólya frequency
  property, the sufficiency leg gives the counting clauses of `prop:polya-frequency`(2).
- **Page.** The causal ledger pins the pair at Ch. 5, Thm. 3.1(i), p. 233 and Thm. 4.2,
  pp. 242–243; the verification pass should confirm those pages serve the two-sided setting
  here as well.
- **What the entry does NOT carry.** The composition step — that the convolution of a
  variation-diminishing operator with a Laplace kernel is variation-diminishing — which is
  immediate from the definition and is **[T]**.
- **Admitted 2026-09-10 (wave 4), jointly with A21**; see A21 for the shape of the two Lean
  names and for the one `[T]` step they carried between 2026-09-10 and 2026-09-12, when it was
  machine-checked and both axioms were restated at Karlin's letter (rows R150, R151).
- **Author's decision, 2026-09-10: the debt is accepted, and the claim is qualified to match.**
  The two admitted compositions carry, beyond their citations, the symmetry reduction and the
  parameter matching between Karlin's two-sided Laplace representation and this article's
  exponent — an analytic-continuation step the blueprint marks `[T]` and proves in prose, not
  machine-checked, and queued for the shared core (`ScaleSpaceCore`: the two-sided Laplace
  transform as an entire function, with an identity theorem). Until that lands, the honest
  statement of this article's trust base is *Lean core, plus the eleven names of
  `blueprint/trust-boundary.txt`, plus the steps that file's per-name list records inside eight
  of them, of which this one is the deepest*. No status changes.
- **DISCHARGED, 2026-09-12 (phase C1c; rows R150 and R151), and the full account is at A21.** The
  symmetry reduction and the parameter matching are machine-checked: Karlin's identity holds at
  complex `s` on an open strip containing the imaginary axis (Prop. 1.4, p. 333), so no
  continuation is involved, and what the matching consumes is proved in `ScaleSpaceCore` v0.2.0
  and assembled in `SpatialLine.isPolyaExponent_of_variationDiminishing` and
  `SpatialLine.variationDiminishingOrd_of_polyaExponent`. Both axioms are restated at their
  letter, dropping this article's `hsym` and `hcos`. This entry's own items on the per-name list
  are unaffected: integrable test functions on the sufficiency leg, the essential-versus-ordinary
  reconciliation and the passage to an honest density on the necessity leg, plus the composition,
  the padding of the index set to `ℕ` and the reading of the strip, which the restatement makes
  explicit. No status changed; no `#print axioms` line changed.
- **"Every other admitted name carries only what its pages carry" is withdrawn (fidelity review
  2026-09-10, F6-2); see A21 for the finding.** Eight of the eleven admitted names carry a step
  beyond their pages, and the **per-name list is at the head of
  `blueprint/trust-boundary.txt`**, the canonical place; this entry points there rather than
  repeating it. This pair's two entries appear on that list twice over: the necessity leg for
  the essential-versus-ordinary sign-change reconciliation and the passage from Thm. 4.2's
  a.e. total positivity to an honest Pólya frequency density, the sufficiency leg for integrable
  test functions and the choice of representative in the essential count — all four already
  recorded below and at A21 — and both, jointly, for the symmetry reduction and the matching.
  Two of those six items have since left the list by being proved: the choice of representative
  (2026-09-11, R14) and the pair's symmetry reduction with the matching (2026-09-12, the
  discharge bullet above). The count of names carrying a step is still eight of eleven.
- **Hypothesis range, checked against the page (2026-09-10).** Thm. 4.2 is stated for a
  **density**: "Let `k(u)` be a density function on `(-∞,∞)`; i.e. `k(u)` is nonnegative and has
  total integral 1" (p. 243). `SpatialLine.polyaExponent_of_variationDiminishing` therefore
  carries `hac : μ ≪ volume`, and the assembly has to supply it — which it does from **A8**
  (`kernel_regularity_law`), whose own hypothesis check is a change of scale
  (`SpatialLine.isSelfDecomposable_of_fourierCos`). Nothing is claimed here about a law without
  a density, and in particular nothing about a lattice law.
- **One extension beyond the letter, named rather than left silent.** Thm. 3.1(i) states the
  variation-diminishing conclusion for *bounded* Borel `f` (p. 233: "The function `f` will
  represent a bounded Borel-measurable function unless stated explicitly to the contrary");
  `IsVariationDiminishingOrd` (`IsVariationDiminishing` before the 2026-09-11 narrowing) follows
  the node, which says "every integrable or bounded `g`", and so admits integrable `f` as well.
  The determinant argument is the same one. This touches only the sufficiency direction; in the
  necessity direction the wider quantifier is a *hypothesis*, where wider is narrower. **Since
  2026-09-11 it is the only extension this leg carries beyond Karlin's page**, the second one
  below having been proved.
- **A second extension beyond the letter (fidelity review R14, recorded 2026-09-10).** Karlin
  counts sign changes of a bounded Borel function in the ordinary sense, `S^-(f)`. This
  development counts them in the *essential* sense, `signChangesAE g`, which is defined as the
  infimum of `S^-(h)` over **every** function `h` equal to `g` almost everywhere — non-measurable
  representatives included, the definition placing no measurability condition on `h`. The two
  directions are not equally exposed.
  - **Necessity is safe**, and in one line. There the variation-diminishing property is a
    *hypothesis*, and it is stronger than Karlin's: the kernel is absolutely continuous
    (`hac`), so `k * g` is continuous, and for a continuous function the essential and the
    ordinary counts agree, while on the right-hand side the essential count is at most the
    ordinary one. So `S^-_{ae}(k*g) ≤ S^-_{ae}(g)` implies `S^-(k*g) ≤ S^-(g)`.
  - **Sufficiency needs one thing more.** There the property is the *conclusion*, an inequality
    between two infima. Karlin's theorem gives `S^-(k*g) ≤ S^-(g)`, and passing to the essential
    counts additionally requires that no representative of `g` — in particular no non-measurable
    one — lower the right-hand count below what that inequality controls. That step was believed
    and not proved from 2026-09-10 to 2026-09-11; it was the second respect in which this pair
    carried more than its pages, and it was stated in the same words in
    `SpatialLine/Interfaces.lean`.
  - **Proved, and the leg narrowed to the letter (2026-09-11, the author's decision (b) of the
    fidelity review).** The missing step is a two-line construction once the obligation is read
    rather than the classical argument: given a measurable `g` and any `h` equal to it almost
    everywhere, take a measurable null superset `N` of the set where they differ and delete `g`
    on it. The result `h' = 1_{N^c} g` is measurable, is again a representative of `g`, satisfies
    `|h'| ≤ |g|` pointwise — so it inherits whichever of integrability or boundedness `g` has —
    and, wherever it is nonzero, equals `h`; hence **every alternation of `h'` is an alternation
    of `h` at the same points and with the same signs**, and `S^-(h') ≤ S^-(h)`. No sign-interval
    geometry is needed. That is `SpatialLine.exists_measurable_rep_signChanges_le`, its corollary
    `SpatialLine.signChangesAE_eq_iInf_measurable` (the infimum is attained along measurable
    representatives), and the reduction `SpatialLine.isVariationDiminishing_of_ord`, all in
    `SpatialLine/MeasurableHull.lean` and all on Lean core.

    In consequence `SpatialLine.variationDiminishing_of_polyaExponent` is **restated at Karlin's
    letter**: it now concludes `SpatialLine.IsVariationDiminishingOrd`, the ordinary count on
    measurable integrable-or-bounded test functions, and the essential-count form the development
    consumes is the theorem `SpatialLine.isVariationDiminishing_of_polyaExponent`, stated beside
    it, which is what all four consumers call. Note the direction: the ordinary-count conclusion
    is the *stronger* statement, and stating the axiom at it is a narrowing in the sense this
    ledger tracks — what the axiom asserts is now what the page asserts, with nothing believed in
    between. The first extension above, integrable test functions, is untouched and is now the
    only one this name carries. No status changed, no printed statement changed, and the
    `#print axioms` lines of `SpatialLine.polya_frequency` and
    `SpatialLine.scale_monotone_noncreation` are unchanged.
