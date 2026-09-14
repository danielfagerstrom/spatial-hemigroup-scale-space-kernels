/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter2
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The target types of Chapter 3 — the axioms

**This file carries `sorry`s and is not part of the `SpatialLine` library.**

`def:cascade-family` itself is a definition, and it lives in `SpatialLine/Family.lean` with
`\leanok`. What is stated here is the chapter's two theorems: the two members the theory has to
fit between, and the article's thesis in negative form.

## What writing this chapter down found

**1. `CascadeCore` cannot be the vehicle for the negative result, because it bundles (A4).**
`prop:no-positivity-no-classification` exhibits a family satisfying (A1)–(A3), (A5)–(A8) and (ND)
and *asks* whether (A4) holds. Stating that against a structure with a positivity field is
impossible, and stating it as a bare conjunction of seven clauses would drift from
`def:cascade-family` silently. So `SpatialLine/Family.lean` now splits `PreCascadeCore` —
(A1)–(A3) and (A5)–(A7) — from the predicates `IsPositive` (A4) and `IsNondegenerate` (ND), with
`CascadeCore extends PreCascadeCore`. Two things fell out of the same split: every node can now
carry *exactly* the axiom list the blueprint gives it, and `lem:nonvanishing`'s hypothesis list
"(A1)–(A3), (A5)–(A7)" is literally `PreCascadeCore`. Paper I did not need the split; the
`ScaleSpaceCore` lift should adopt it. This is a change to the shared vocabulary and phase B
depends on it.

**2. `prop:no-positivity-no-classification`'s example needs `∫ q = 0`, and the blueprint did not
say so.** The proposition's setting asks `φ ∈ A(ℝ)`, the Wiener algebra, whose members vanish at
infinity by Riemann–Lebesgue. For the exhibited
`φ_ε(ω) = ε ∫ (1 - cos ωx) q(x) dx = ε ∫ q - ε q̂(ω)` that forces `∫ q = 0`; without it `φ_ε`
tends to `ε ∫ q ≠ 0` and is not in `A(ℝ)`, so "the family is one of those described" fails. The
hypothesis is added below and to the blueprint statement (`% CHANGED (skeleton 2026-09-08)`); it
costs the example nothing, since `q = 1_{[1,2]∪[-2,-1]} - 1_{[3,4]∪[-4,-3]}` still witnesses it.

**PROVING CAMPAIGN (2026-09-09).** Both clauses of `prop:two-members` are proved and moved; see
the pointer below. Two things the statement phase had not seen came out of proving them, and
both are recorded at the declarations that now carry them:

* **(ND) is about the operator, not the kernel.** The blueprint discharges (ND) by exhibiting a
  frequency at which the kernel's transform is not `1`; the axiom asks that the *operator* is not
  the identity, and the passage between the two is the identification of the kernel of the
  identity — `SpatialLine.eq_dirac_of_mconvL1_eq_id`, proved by testing at a bump with a strict
  maximum at the origin. It is what `lem:convolution-representation`'s uniqueness clause should
  start from, and neither member could be finished without it.
* **(A7) is cheaper than R30 priced it, and the reason is structural.** A convolution semigroup
  in one parameter makes a difference of operators factor through a single increment, so the
  `ε/3` argument is not needed at all; for the *hemigroup* the two endpoints have to be moved
  separately, and the second move needs `Θ` to decrease under convolution. The reusable estimate
  is `SpatialLine.norm_mconvL1_sub_le`, and `prop:levy-continuity`'s first clause was proved from
  Mathlib rather than taken as ledger interface A6.

**3. The Matérn member is quantified over its specification, the Gaussian one is not.** Mathlib
has `ProbabilityTheory.gaussianReal` and `charFun_gaussianReal`, so clause (1) can name its
kernels and is a genuine existence statement. Mathlib has no Matérn law, and constructing one is
`prop:matern-density`'s job in Chapter 10; so clause (2) hypothesises a kernel family with the
stated transform and concludes that it satisfies the axioms. That loses nothing — the transform
determines the law by `prop:fourier-uniqueness` — and it keeps a Chapter 10 construction out of
Chapter 3. It does mean clause (2) is **conditional on Chapter 10 for non-vacuity**, which is
exactly what the node's own forward `\uses` edges already say.
-/

namespace Skeleton

open MeasureTheory Set Filter SpatialLine
open scoped ENNReal Topology

/-! ## `prop:two-members` (draft, the two members of §3) — [T] -/

/-! ### Moved to `SpatialLine` (proving campaign, 2026-09-09)

`two_members_gaussian` is `SpatialLine.two_members_gaussian` (`SpatialLine/Gaussian.lean`) and
`two_members_matern` is `SpatialLine.two_members_matern` (`SpatialLine/Matern.lean`), both with
the reviewed statement verbatim. What is left of the node here is the moment clause below, and
`Skeleton.matern_density` in Chapter 10.

The two families are built through `SpatialLine/Transport.lean` (a kernel becomes an operator
family) and `SpatialLine/L1Continuity.lean` ((A7)); the design record of what the proofs cost
against the estimates, and of the two facts the skeleton had not anticipated needing, is in
those files' module docstrings. -/

/-! ### `prop:two-members`(2), the kernel's moments — **PROVED AND MOVED (wave 5, 2026-09-10)**

`SpatialLine.two_members_matern_moments`, in `SpatialLine/MaternMixture.lean` (it was written in
`MaternMoments.lean` and moved on 2026-09-14, see below), with the
statement verbatim (the review's R7 hypothesis `hsym` included). Priced **L** and paid **S**
once chapter 10's variance was in hand — the estimate was made against a route the statement
does not need.

**Both reasons the wave-2 note gave for the block were upper bounds on the obligation, not the
obligation.** That note said clause (1) would need either "all moments finite iff the
characteristic function is `C^∞` at the origin", which Mathlib does not carry, or the
exponential tail of the Bessel-K density, which is ledger A15/A16. Neither is spent. Clause (1)
is `SpatialLine.matern_moments_integrable` — the moment criterion (ledger **A13**) on an
exponentially decaying profile, wave 4's — and clauses (2) and (3) are
`SpatialLine.matern_mean_variance`, which is `moments_tails_variance` at the witness
`maternDatum γ 1` and is **Lean core**. The catalogue's first moment is `∫₀^∞ x·2γe^{-x}dx =
2γΓ(2) = 2γ`, one Gamma evaluation, so the variance is `2γt²`.

**The one thing that had to be written was the endpoint identification.** The node states the
family by its transfer function `((1+s²ω²)/(1+t²ω²))^γ` and the chapter-10 declarations want
`exp(-F(tω))`; at `s = 0` these are the same function, which is
`SpatialLine.maternTransform_zero`, six lines. That identification is all that stood between
this node and chapter 10, and it is why the node was never blocked on
`prop:matern-density`'s Bessel-K route: the *density* sentence is, the *moment* sentence is not.

What remained of `prop:two-members` was `Skeleton.matern_density` in Chapter 10 — the density
identification, ledger **A15**, unadmitted because no proof consumes it — which kept the node
`\notready`.

**The node is `\leanok` and Lean core (2026-09-14, R156).** The density sentence was narrowed
out of clause (2): the closed form is a valid *density* for every `γ > 0` but a Matérn
*covariance function* only for smoothness `γ − 1/2 > 0`, so the identification was false on the
part of the node's own hypothesis range `0 < γ ≤ 1/2`. `Skeleton.matern_density` leaves the
`\lean` tag (it remains Chapter 10's own node), and with the sentence gone the only remaining
axiom on the node's path, `moments_tails_criterion` (A13) inside `matern_moments_integrable`,
was replaced by `matern_moments` — the same conjunct from the Gamma mixture's even moments, on
Lean core. `two_members_matern_moments` moved to `SpatialLine/MaternMixture.lean` for that
reason: `matern_moments` is proved there, and that file imports `MaternMoments.lean`.
-/

/-! ## `prop:no-positivity-no-classification` (draft Proposition 3.6) — [T] -/

/-- **`prop:no-positivity-no-classification`**: without (A4) there is no classification.

Reading, clause by clause.

* `φ ∈ A(ℝ)` real and even with `φ(0) = 0` is rendered as: `φ` is the cosine transform of an
  integrable `h`, with `φ 0 = 0`. Writing `φ ω = ∫ cos(ωx) h(x) dx` builds evenness and realness
  in, and for an *even* `h` it is exactly `ĥ`; for a general `h` it is the transform of the even
  part, which is the same subspace of `A(ℝ)`. So the hypothesis is the blueprint's, with the
  "real and even" riders discharged by the form rather than assumed.
* "each `μ_{s,t}` is a finite symmetric signed measure, an integrable function when `s < t`" is
  stated through what the article uses of it: off the diagonal there is an **even integrable
  function** `k` with the prescribed cosine transform, and `Φ_{s,t}` is convolution by it; on the
  diagonal `Φ_{t,t} = id` is `PreCascadeCore.diag`. A `SignedMeasure` layer would add vocabulary
  that nothing downstream consumes.
* "(A4) if and only if `F` is of the form (2.5)" is `IsPositive Fam.Φ ↔ IsAdmissibleExponent F`,
  and it is bundled into the same statement because it is a statement about *the family just
  constructed*.

Class (c) — the article's thesis in negative form; nothing corresponds on the causal side.

Cost **L**. Obligation, in three unequal parts. (i) The family: `A(ℝ)` is a Banach algebra under
pointwise multiplication and `b ↦ φ(b ·)` is continuous into it — Mathlib has the Fourier
transform on `L¹` and the Riemann–Lebesgue lemma, but not the Wiener algebra as a Banach algebra,
so this is the expensive part and may want a small development of its own. (ii) The axioms: each
is one line from the kernel form, as in `two_members_gaussian`. (iii) The equivalence: `⟸` is
`lem:selfdecomposable-exponents`((3) ⟹ (1)) and `⟹` is `thm:main-characterization`, so this
clause is *downstream of Chapter 7* and cannot be proved before it.

**Not attempted (proving campaign, 2026-09-09).** Confirmed blocked, and the block is the
*bundling*: part (iii) waits on `Skeleton.main_analysis` with `Skeleton.main_uniqueness` for
`⟹` and on `Skeleton.sd_exponents_three_implies_one` for `⟸` (Chapter 7), and because the
equivalence is one conjunct
of a single existential, nothing else in the statement can land either — the family of part (i)
and the axioms of part (ii) are independent of Chapter 7 and would be provable now.

**Recommendation (a statement change, not made here).** Split this node the way
`prop:kernel-regularity` was split at R27: one declaration producing the family and its axioms
(A1)-(A3), (A5)-(A8), (ND) with the kernel form, and one taking that family and asserting
`IsPositive Fam.Φ ↔ IsAdmissibleExponent F`. Priced at the split, the first half is **M** given
`SpatialLine/Transport.lean` and `SpatialLine/L1Continuity.lean`, which now exist and supply
(A1)-(A6), (A8) and (A7) for any kernel family — what remains is the Wiener-algebra construction
of `h_{s,t}` and its norm continuity, which is the genuine work and has no Mathlib support; the
second half stays **M** and stays downstream of Chapter 7. Leaving it bundled means the whole
node stays `notready` until Chapter 7 closes, for no mathematical reason. -/
theorem no_positivity_no_classification {h : ℝ → ℝ} (hh : Integrable h) (φ F : ℝ → ℝ)
    (hφ : ∀ ω, φ ω = ∫ x, Real.cos (ω * x) * h x) (hφ0 : φ 0 = 0)
    (hF : ∀ ω, F ω = ω ^ 2 + φ ω) :
    ∃ Fam : PreCascadeCore, ∃ S : ℝ → ℝ → ℝ,
      S = (fun lam t => lam * t) ∧
        IsScaleCovariant Fam.Φ (Ioi 0) S ∧
        IsNondegenerate Fam.Φ ∧
        (∀ s t : ℝ, 0 ≤ s → s < t → ∃ k : ℝ → ℝ, Integrable k ∧ (∀ x, k (-x) = k x) ∧
          (∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = Real.exp (-(F (t * ω) - F (s * ω)))) ∧
          (∀ f : X, ((Fam.Φ s t f : X) : ℝ → ℝ)
            =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y))) ∧
        (IsPositive Fam.Φ ↔ IsAdmissibleExponent F) := by
  sorry

/-- **`prop:no-positivity-no-classification`, the family and its axioms** — the first half of
the R27-style split recommended by wave 1 and written here (wave 2, 2026-09-09) as a `sorry`'d
target.

Reading: exactly the conjuncts of `no_positivity_no_classification` that do **not** mention
positivity. The bundled declaration is unchanged and stays the node's statement of record; this
one is what a prover can attack today, and the bundle follows from the two halves in one line
once both land (apply `no_positivity_classification` to the family this produces).

Cost **M**, and the M is one thing: the Wiener-algebra construction of `h_{s,t}` with its norm
continuity in `(s,t)`. Everything else is now supplied — `SpatialLine/Transport.lean` gives
(A1)-(A6) and (A8) for any kernel family and `SpatialLine/L1Continuity.lean` gives (A7) through
`norm_mconvL1_sub_le`, which is the estimate wave 1 found in place of the epsilon-over-three
argument; (ND) is `eq_dirac_of_mconvL1_eq_id`. Mathlib has the Fourier transform on `L¹` and
Riemann-Lebesgue but not `A(ℝ)` as a Banach algebra, so the exponential series
`e^{-φ_{s,t}} = 1 + hat h_{s,t}` has to be summed by hand; that is the piece with no upstream
support and it may deserve a development of its own. -/
theorem no_positivity_family {h : ℝ → ℝ} (hh : Integrable h) (φ F : ℝ → ℝ)
    (hφ : ∀ ω, φ ω = ∫ x, Real.cos (ω * x) * h x) (hφ0 : φ 0 = 0)
    (hF : ∀ ω, F ω = ω ^ 2 + φ ω) :
    ∃ Fam : PreCascadeCore, ∃ S : ℝ → ℝ → ℝ,
      S = (fun lam t => lam * t) ∧
        IsScaleCovariant Fam.Φ (Ioi 0) S ∧
        IsNondegenerate Fam.Φ ∧
        ∀ s t : ℝ, 0 ≤ s → s < t → ∃ k : ℝ → ℝ, Integrable k ∧ (∀ x, k (-x) = k x) ∧
          (∀ ω : ℝ, ∫ x, Real.cos (ω * x) * k x = Real.exp (-(F (t * ω) - F (s * ω)))) ∧
          (∀ f : X, ((Fam.Φ s t f : X) : ℝ → ℝ)
            =ᵐ[volume] fun x => ∫ y, k y * (f : ℝ → ℝ) (x - y)) := by
  sorry

/-! ### `prop:no-positivity-no-classification`, positivity iff admissibility — **PROVED AND
MOVED (wave 6, 2026-09-10)**

`SpatialLine.no_positivity_classification`, in `SpatialLine/NoPositivityClassification.lean`,
with the statement verbatim, together with its two directions
`no_positivity_admissible_of_positive` and `no_positivity_positive_of_admissible`. **Re-priced
L in both directions by wave 5; paid M in both**, and the difference is four facts that were
already in the development or one lemma away from it.

**`⇐` reads three of the five hypotheses and none of the three the estimate named.** It uses
`hker` and `IsAdmissibleExponent F` and nothing else — not `hcov`, not `hnd`, and *not* `hF0`,
the normalisation wave 5 had to add to make the split half true. The reason is worth recording,
because it explains the asymmetry: the `⇐` direction never evaluates `F` at a point, only at
differences `F(tω) - F(sω)`, and that is exactly the invariance under `F ↦ F + c` which made
the *other* direction false without the normalisation. Judgement point 7 in its usual form.

**The signed-uniqueness step is a lemma with its own file and is `S–M`.**
`SpatialLine/SignedUniqueness.lean`'s `ae_nonneg_of_fourierCos_eq` is the strict generalisation
of `ae_eq_zero_of_even_of_integral_cos_eq_zero` the wave-5 annotation named, and the extra
content over that lemma — the *nonnegativity* — is one test of the Jordan identity on the set
where a measurable version of `k` is negative. Mutual singularity, which the annotation
expected to spend, is not used.

**`s = 0` is not a separate case.** The estimate for `⇐` assumed the increment exponent would
have to be produced at `0 < s` and at `s = 0` by different means.
`sd_increment_isSymLevyExponent` (wave 2's, for `lem:selfdecomposable-exponents`) covers
`0 ≤ c ≤ d` uniformly, and this is its second consumer.

**`⇒`'s expensive-looking step is three lines because the `L¹` positive cone is closed.** The
route is the annotation's — read (A4) at an approximate identity — and what makes it cheap is
Mathlib's `OrderClosedTopology (Lp E p μ)` instance: `ρ_ε * k ≥ 0` for every `ε > 0` passes to
the limit `k` with no subsequence and no almost-everywhere convergence argument.
`tendsto_bconv_approxId` is wave 1's, proved for `lem:convolution-representation`, and this is
its second consumer.

**`SDProfile.dilate` is thirty lines and both halves were in place**, exactly as the wave-5
annotation said (`profileJumpL_comp_div` and `lintegral_min_profileMeasure_comp_div_ne_top`,
with `antitoneOn_comp_div` beside them). It is the only new definition either direction needs,
and it is what lets `⇒` absorb the gauge constant instead of proving the gauge is the identity
— see the blueprint's `% CHANGED (proof of record 2026-09-10, wave 6)`.

`#print axioms` on the bundle is Lean core plus **A1** (`fourier_toolbox_bochner_symm`) and
**A3** at both its admitted clauses; each direction spends less, `⇒` only A3's uniqueness and
`⇐` only A1 with A3's converse. No name is added to the trust boundary.

What remains of the node is `no_positivity_family` alone, the Wiener-algebra construction, which
is unchanged and still has no Mathlib support.
-/

/-! ### `prop:no-positivity-no-classification`, the example: moved to `SpatialLine`
(proving campaign, wave 5, 2026-09-10)

`no_positivity_example` is `SpatialLine.no_positivity_example`
(`SpatialLine/NoPositivity.lean`), with the reviewed statement verbatim, and it rests on Lean
core. The Cesàro identity the route needs is
`SpatialLine.SymLevyPair.intervalIntegral_exponent` (`SpatialLine/SincAverage.lean`), stated
for an arbitrary symmetric Lévy pair rather than for this example.

What the three rounds of estimate cost, measured against what was written:

* Wave 2 priced the node **M-L** on "uniqueness of the signed Lévy-Khintchine representation"
  and named the printed proof's averaging identity as the obligation. **That uniqueness is
  never stated.** The two Cesàro readings identify the Gaussian coefficient and the Lévy
  measure of a candidate profile directly, so the only uniqueness spent is the one wave 3 had
  already proved for the cosine transform of an `L¹` function. This is the survey-versus-attempt
  gap in its usual direction: the survey named an obstruction the written proof walks past.
* Wave 3 re-priced the node **L** on the Tonelli identity plus three dominated convergences,
  and that estimate held. Its step (B) — proving the Lévy measure finite before letting `T`
  grow — turned out not to be needed: **Fatou** bounds the total mass by the liminf of
  integrals that are already finite for each `T`, so the tail estimate and its monotone
  exhaustion are never written, and two of the three limits collapse into one.
* The support hypothesis `hqsupp` is confirmed unused, and now the compiler says so.

The design record is the module docstrings of `SpatialLine/SincAverage.lean` and
`SpatialLine/NoPositivity.lean`. -/

end Skeleton
