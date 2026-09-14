# PLAN — response to the external reviews (2026-09-14)

Working plan for revising the article in response to two external reviews of the build at
revision `09602a3` (48 pages), both archived verbatim in `reviews/`:

- **the content review** (`reviews/line-review-content-GPT-Astra-Ultra.md`, "the review"
  below), a referee report with the verdict *major revision*: the characterization and its
  carrying arguments (Theorem 5.2, Lemma 6.4, Proposition 6.6, Lemma 7.1, Theorem 7.3,
  Proposition 7.8) check out; seven definite errors (A–G) and a list of smaller gaps; the
  headline claims, the trust-base account, the Pauwels comparison and the Iijima summary
  overstate or contradict the body; fourteen required changes, nine suggestions;
- **the presentation review** (`reviews/line-review-presentation-GPT-6-Astra-Extra-High.md`),
  twenty ranked located items on the opening, the register, the figures and tables, the
  notation and the section structure.

Assessment session 2026-09-14 (the article session, Fable): every finding verified
independently against the text, the blueprint and, where it applies, the Lean; the verdicts
below are the session's, and the decisions marked **D** are the author's. Conventions: each
batch is one commit through the gates (`tectonic`, `linkage check` at 33 verbatim,
`check-control-chars.py`); statements shared with the blueprint are not changed here (the
blueprint is the formalization session's, and every change it should mirror is listed in
§ "Owed to the blueprint"); page references ("p. 20") are to the reviewed build.

## Verification of the substantive findings (R0, done 2026-09-14)

| finding | verdict | evidence |
|---|---|---|
| **A** Proposition 3.5's construction uses the Gaussian of variance $t^2 - s^2$ where the transform $e^{-(t^2-s^2)\omega^2}$ needs variance $2(t^2 - s^2)$ (pp. 19–20) | **confirmed** | `03-axioms.tex:419–437`: $g_{t^2-s^2}$ with $\hat g_v = e^{-v\omega^2/2}$ fixed at Prop. 3.4. Printed-proof error in the one construction that is not machine-checked; the machine-checked clauses (the positivity equivalence, the example) are unaffected. Fix: $g_{2(t^2-s^2)}$ throughout the proof; blueprint mirror. |
| **B** Lemma 4.2 concludes $g \ge 0$ without positivity (p. 23) | **confirmed as a prose error, not a statement error** | The statement's hypothesis "the representation of Lemma 4.1" is a family of *probability* measures, and the Lean (`SpatialLine.nonvanishing`, `IsKernelFamily` with `isProbability`) assumes exactly that. My lead paragraph ("positivity is not among its hypotheses … needs no (A4)") and `rem:modulation-transfer`'s "(A1)–(A3), (A5)–(A7)" overclaim. Fix the prose: the lemma is about probability kernels, which (A4) supplies; the signed counterexample the review gives is correct and shows why. |
| **C** The Matérn covariance identification is wrong for $0 < \gamma \le \tfrac12$ (pp. 2, 6, 17–19) | **confirmed** | The density $\propto (|x|/2t)^{\gamma-1/2} K_{\gamma-1/2}(|x|/t)$ is a valid density for every $\gamma > 0$ but a Matérn *covariance function* (bounded, $C(0) < \infty$) only for smoothness $\gamma - \tfrac12 > 0$; at $\gamma = \tfrac12$ it is $K_0$, log-divergent. The shared statement `prop:two-members`(2) carries the sentence; its narrowing (drop the density sentence) is already requested of the formalization session and is now required. Paper-side: call the family variance-gamma (Bessel) throughout and restrict the Matérn identification to $\gamma > \tfrac12$; the figure's $\gamma = \tfrac12$ curve is the unbounded case and is labelled so. |
| **D** Absolute continuity and unimodality asserted for all kernels; they hold for $\mu_{0,t}$ only (pp. 1, 3, 17, 21, 36, 40–41) | **confirmed** | The variance-gamma increment at $\gamma = 1$ has transform $(1+s^2\omega^2)/(1+t^2\omega^2) = s^2/t^2 + (1 - s^2/t^2)(1+t^2\omega^2)^{-1}$: an atom of mass $s^2/t^2$ at $0$. Proposition 7.9 says "from the origin" and the text after it says so; the abstract, § 1, § 8 and the § 7 lead drop the qualification. Fix every summary: "the kernels from the origin". |
| **E** "Unimodal, so no truncated Gaussian is admissible" is a non sequitur (pp. 3, 40–41) | **confirmed** | A truncated Gaussian is even and unimodal. The exclusion is true for another reason: its transform changes sign (integration by parts, leading term $2p(R)\sin(R\omega)/\omega$), which Lemma 4.2 forbids. Fix the reason in § 1, § 7, § 8. |
| **F** The folding argument cancels $\int \sin(\omega x)\,\nu_2(dx)$, which need not converge (pp. 8–9) | **confirmed** | For $\nu_2 \propto |x|^{-1-\alpha}$, $1 \le \alpha < 2$, the sine integral diverges absolutely near $0$. The correct sentence: the odd part of the compensated integrand, $\sin\omega x - \omega x\,\mathbf 1_{|x|<1}$, is integrable and odd, so its integral against a symmetric $\nu_2$ is $0$. Paper-side prose in § 2's folding paragraph; the same reduction sits inside admitted interface A3 per § 1.1, and the ledger's wording should be checked (formalization session). |
| **G** § 1.1's Bochner statement omits "real" (pp. 4, 9) | **confirmed as a description error** | The admitted declaration `fourier_toolbox_bochner_symm` takes `φ : ℝ → ℝ`; Prop. 2.3(1) says "real, equivalently even"; § 1.1 and § 2's vocabulary paragraph say "a continuous positive definite function with value 1 at the origin". Fix both to "a real-valued continuous positive definite function". |
| Theorem 5.2: "Prokhorov after normalising the masses" needs the zero-mass case | **confirmed, routine** | Add: pass to a subsequence of the masses; if the limit is $0$ the weighted measures vanish and the pair is $(0,0)$; otherwise normalise. Proof of record: blueprint mirror. |
| Lemma 6.4 lead: "clause (4) is the one place in this section where (ND) is used" | **confirmed false** | Clause (1) uses (ND) (the identity increment), clause (3) uses it through the strict monotonicity of $\Theta$, and Lemma 6.2 uses it. My sentence from the § 6 review batch. Fix. |
| Lemma 7.1: $B(0)$ undefined when $F'(0)$ does not exist; the difference-quotient supremum is extended-valued at first | **confirmed, routine** | Define $B(0) := 0$; say the supremum is finite by its interval integrals. Proof of record: mirror. |
| Proposition 7.9: "a second mode at $-m$" is no contradiction (a modal interval is allowed) | **confirmed** | My sentence from the § 7 review batch. Fix: the set of modes of a unimodal law is an interval; by symmetry it is symmetric about $0$, so it contains $0$. |
| Proposition 2.7's proof: Stone–Weierstrass on compacts to equality on the line skips a step | **confirmed, routine** | The proof is a prose account of Mathlib's `ext_of_charFun`; add "with approximants uniformly bounded" or point at the Mathlib argument as the record. Mirror. |
| Lemma 4.1's proof: $y \mapsto f(y)\,T_y g$ is not continuous for $f \in L^1$ | **confirmed** | It is strongly measurable; continuity belongs to $y \mapsto T_y g$. Wording fix in the proof; mirror. |
| Prop. 3.4's Matérn clause is called a "direct" check but uses Theorem 7.3 | **confirmed** | The proof's (2) goes through Prop. A.3 and Theorem 7.3 (the blueprint's `\uses` says so); not circular, since the theorem does not use the example, but "before the general theory" is false for that member. Fix the lead of § 3.7 and § 1's sentence; the review's suggested direct increment profile $2\gamma(e^{-x/t} - e^{-x/s})$ is the blueprint's business. |
| Figure 3 caption: variance 4 decays as $e^{-x^2/8}$, not $e^{-x^2/4}$ | **confirmed** | The script plots $\exp(-x^2/8)/\sqrt{8\pi}$; the caption is wrong. Fix. |
| Remark 7.2: "not stationary increments" should be "not necessarily"; $a$ is not the variance rate | **confirmed** | The Cauchy member has stationary increments in the canonical gauge; the continuous part has variance $2at^2$. Fix (copied remark; mirror). |
| Remark 7.5: Gaussian displacement of variance $2at^2$ "to every kernel" | **confirmed** | For an increment it is $2a(t^2-s^2)$; "to the kernel at scale $t$". Fix. |
| Lemma 7.6: the class of Theorem 7.3 excludes $F = 0$, so "cone" needs the zero adjoined | **confirmed** | My lead sentence; add "with the zero exponent adjoined". |
| Lemma A.1's Tonelli remark confuses infinite mass with non-σ-finiteness | **confirmed** | The tail measure is σ-finite (finite away from $0$). Wording; mirror. |
| The half-line closure comparison (pp. 10, 12–13) | **confirmed, needs a qualification** | Bernstein functions on $(0,\infty)$ are closed under pointwise limits; the normalized subclass on $[0,\infty)$ is not ($1 - e^{-ns} \to \mathbf 1_{s>0}$). Qualify the two sentences. |
| "Reflection excludes … the spatial theory has none [degenerate member]" (pp. 14–15, 17) | **confirmed** | The identity family is excluded by (ND), not by (A3); and calling the Gaussian "the degenerate member" (copied `rem:provenance-causal`) conflicts with "nondegenerate". Fix both. |
| The Iijima summary (p. 3) lists conditions the Poisson semigroup satisfies | **confirmed as stated** | Linearity, translation and scale invariance, the semigroup and positivity admit $e^{-t|\omega|}$; the Gaussian needs a regularity assumption the classical derivations leave implicit. The librarian verified that the *source* lists those five (DIKU report pp. 4–5); the paper must not present them as sufficient. Fix the sentence and cite the Poisson counterexample discussion (librarian: which Felsberg–Sommer paper carries it). |

## Standing decisions (the session's, under the repo's rules)

- **Statements shared with the blueprint are not touched here.** Two findings land on shared
  statements: `prop:two-members`(2)'s density sentence (C; the narrowing was requested on
  2026-09-12 and is now required) and the title of `prop:no-positivity-no-classification`
  ("without positivity there is no classification", which the review reads as an impossibility
  claim). Both go to the formalization session; the paper-side prose is corrected now.
- **Proofs of record are the blueprint's.** The small proof repairs (A, the Prokhorov
  normalisation, $B(0)$, the strongly measurable integrand, the Tonelli remark) are applied in
  the paper's copy so that the released text is right, and each is listed for the mirror.
- **The proof of record follows the machine-checked route** (author's decision 2026-09-09), so
  the review's shorter route for the orientation of the action (suggestion 4) is not adopted
  in the text; it is recorded for the formalization session as a candidate rewrite.
- **The reference policy toward the causal article stands** (ADR-0003: introduction, one
  remark per section) unless the author decides otherwise at D2.

## Decision points — for the author

*Decided 2026-09-14: the author follows the recommendations on D1, D2, D3, D4, D6 and D7 (all
applied the same day). D5, decided later the same day against the recommendation and with
both reviews: the disclosure becomes a short contributor section (roles, verification and
review, the record in short form, responsibility), and the chronology, the figures with their
caveats and the detailed review account move to `notes/PROCESS.md`, which the section cites;
the note is the material for a possible later blog post.*

- **D1 — Figure 5, the admissible cone.** Both reviews object: the drawing gives geometric
  positions (a "far boundary") to objects whose geometry the paper declares out of scope, and
  "corners" suggests extreme rays for families that are mixtures. Options: (a) keep the figure
  with the boundary claim removed and the unit-step rays labelled as the generating rays of
  the superposition; (b) replace it with a table of named members and their $(a,k)$; (c) drop
  it. *Recommendation: (a).*
- **D2 — the causal comparisons.** Both reviews ask to consolidate the per-section
  relation-to-the-causal-theory remarks (2.16, 3.3, 4.4, 5.5, 6.8, 7.11) into one subsection
  or table, and to make them optional reading. ADR-0003 chose one remark per section.
  *Recommendation: keep ADR-0003, but move each remark to the end of its section and shorten;
  the reviews' real complaint is interruption, not existence.*
- **D3 — § 1.1's length.** The presentation review would keep Table 1 and a short coverage
  statement in the introduction and move the dependency discussion to an appendix; the
  content review wants *more* precision there (a fixed revision, the declarations, the axiom
  output, a claim-to-declaration mapping). The standard makes § 1.1 the trust base's one home.
  *Recommendation: keep § 1.1 where it is, tighten it (one consistent count of what is not
  verified), add the `#print axioms` output for the main theorem and the revision, and drop
  the repeated verification narratives from the body.*
- **D4 — the appendix's placement.** The review wants Lemma A.1's tail-measure facts before
  Lemma 7.1. The appendix exists to keep chapter-8 material out of v0.1's body.
  *Recommendation: keep; add one sentence before Lemma 7.1 saying what it takes from the
  appendix.*
- **D5 — the disclosure's length.** Both reviews would move the chronology and the figures to
  supplementary material. The statement is on Paper I's model and the standard's § 6.
  *Recommendation: keep; the author decided its form on 2026-09-14.*
- **D6 — Figure 3.** Caption-only fix (the $e^{-x^2/8}$, the clipped $\gamma = \tfrac12$
  curve, the variance-gamma name), or re-render with variances standardised so that shape is
  compared at equal width. *Recommendation: caption only now.*
- **D7 — the new figure.** The presentation review's one missing figure is the displacement
  profile: a nonincreasing $k$, two dilates $k(\cdot/s)$, $k(\cdot/t)$ and their nonnegative
  difference, which is what Lemma 7.1's condition means. *Recommendation: add it (numpy, next
  to `fig-members`), in § 7 before Lemma 7.1.*

## Batches

### R1 — the mathematical corrections (paper-side; each also listed for the mirror)   [DONE 2026-09-14]
A (the Gaussian factor in Prop. 3.5's proof), B (the prose around Lemma 4.2 and
`rem:modulation-transfer`), E (the truncated-Gaussian reason), F (the folding sentence),
G (the Bochner wording in § 1.1 and § 2), the Prokhorov normalisation, the (ND) sentence in
§ 6, the mode-interval argument in Prop. 7.9, $B(0)$ and the finite supremum in Lemma 7.1's
proof, the strongly measurable integrand in Lemma 4.1's proof, the Tonelli remark in
Lemma A.1's proof, Remark 7.2's two sentences, Remark 7.5's variance, the zero exponent at
Lemma 7.6, the half-line closure qualification, the identity family and "degenerate" in § 3.

### R2 — the headline claims and the scope   [DONE 2026-09-14, except the § 3.7 direct profile (blueprint)]
"Kernels from the origin" in every summary (D); "no classification in the form of Theorem 7.3"
for "cannot be classified" (abstract, § 1, § 3.8's subsection title, § 8); the
variance-gamma name with the Matérn identification restricted to $\gamma > \tfrac12$ (C);
"with one axiom weakened and two smaller changes, Remark 3.2" for "every other axiom is
retained"; "interchangeability" defined at first use as dependence of an increment on the
scale difference alone (stationary increments in the scale parameter), with commutativity
named as what survives; "unique up to normalization" wherever uniqueness is claimed; the
non-creation limitation stated next to the first claim; "corners" replaced by "the named
families"; Remark 7.10 marked as observations outside the paper's proofs; the § 3.7 lead no
longer claims the Matérn check is independent of the general theory.

### R3 — terminology   [DONE 2026-09-14 for the paper-side items; "increment kernel" sweep pending]
"Kernel from the origin" and "increment kernel" used consistently; "admissible" given a
standalone sentence in § 2 (after `lem:profile-integrability`): the pairs $(a,k)$ with $k$
nonincreasing and the criterion satisfied, the exponent they define, the zero exponent
admissible as an exponent and excluded as a family by (ND); "degenerate" reserved for the
excluded identity and "jump-free" for the Gaussian; the Brownian motion in the appendix
glossed as $W$ independent of $T$ in the prose (the shared statement keeps its letter).

### R4 — the trust-base account   [DONE 2026-09-14, subject to D3]
One consistent count: two parts not machine-checked (the signed construction; the closed-form
identification), stated identically in the abstract's neighbourhood, § 1.1, § 3 and § 8.
Table 1's caption corrected ("every result not listed uses no cited fact *directly*") and a
line added for the facts cited for orientation only (Schoenberg's clause (2), the existence
half of (3), closure (4), Prop. 2.13, the variance-gamma closed form). The `#print axioms`
output for `main_characterization` and the repository revision printed in § 1.1. The appendix's
"machine-checked on Lean core" reconciled with § 1.1's A13 sentence (the mixture route is
Lean core; the moment clause of Prop. 3.4 uses the criterion).

### R5 — related work (librarian first)   [DONE 2026-09-14; `lamperti1962semistable`'s PDF is to be filed by the author from a browser, the librarian's acquisition note has the URL]
Sato 1991 (self-similar processes with independent increments) as the original source of the
correspondence; Lamperti 1962 for self-similarity beside the 1972 paper; Jurek–Vervaat 1983
for the background driving Lévy process behind $B = \omega F'$; Maejima's
semi-selfdecomposability for the discrete-covariance open question; the Poisson
counterexample and the implicit regularity assumption in the Gaussian-uniqueness derivations
(Felsberg–Sommer) beside the Iijima sentence; Burgeth et al. § 2.4's scaled Bessel family
named where the range cascade is claimed as new; Porcu et al.'s $\nu > 0$ requirement at the
Matérn identification; a citation for "a nondegenerate infinitely divisible law has unbounded
support" if E is argued that way rather than by the sign change.

### R6 — presentation   [DONE 2026-09-14 except D1, D6, D7 and the Figure 1 placement]
The abstract's main-result sentence split in three; the contribution and its limits in the
first two pages; the "four steps" announcement cut; the Matérn/Bessel sentence untangled;
Figure 2 moved to § 1 beside the hemigroup display; Figures 1 and 4 at paragraph boundaries,
captions tightened; Table 2 gains the central symbols ($\chi$, $g_{s,t}$, $G$, $\Theta$, $\nu$,
$\varpi$, $B$) with defining equations, the correspondence column kept (release rule 3);
the "reserved letters" sentence cut; the optical medium wording in §§ 5–6 reduced to the
transfer function averaged against a Gaussian window; § 3.7's closing sentence stated as a
result; the scale coordinate's unit named in § 2 (a length in the canonical gauge, the
Gaussian's diffusion parameter $\propto t^2$); D7's figure.

### R7 — declined or deferred, with reasons
The shorter orientation proof (proof of record follows the checked route; recorded for the
formalization session); the appendix's placement (D4); § 1.1's relocation (D3); the
consolidation of the causal remarks (D2); the disclosure's chronology (D5); "the principal
classification is classical" — already said in § 1 and § 8, the wording sharpened in R2
rather than the claim withdrawn; the review's remark that extremality of the step rays is an
elementary consequence — not established here, and the text says so; adding it is module B's.

## Second round — the Grok presentation review of the second build (2026-09-14)

`reviews/line-review-presentation-768625d-Grok46-ExtraHigh.md`, part B on revision `768625d`.
Twenty located items; the dispositions, with the author's earlier decisions respected where
the second reviewer disagrees with them:

| item | disposition |
|---|---|
| 1 limits in the first two pages | **applied**: one sentence at the end of the abstract names the contribution and what is outside the paper |
| 2 "the causal article below" is false; comparisons address the other paper | **applied** the wording ("called the causal article in what follows"); the consolidation is D2, decided (kept per section, at section ends) |
| 3 cut § 1.1 to Table 1, move the build recipe and axiom dump to an appendix | **declined**: D3, decided; the first referee asked for exactly that material |
| 4 split the abstract further; Lean to a final clause | **applied** in part by item 1; the Lean sentence is already last |
| 5 rename "interchangeability" to stationarity of increments | **applied** (the author's decision G5, 2026-09-14, all three reviewers having asked): "the stationarity of the increments in the scale parameter" throughout the paper-side prose, including the copied provenance remark (mirror item); no shared statement carries the old word |
| 6 untangle Bessel / Matérn / variance-gamma | **applied**, the reviewer's wording |
| 7 § 2 is a second paper; move Props. 2.7–2.8's proofs and Remark 2.4 to an appendix | **applied** the opening sentence; **declined** the moves (the remark was the author's request, the proofs are short and are the two toolbox facts proved rather than cited) |
| 8 tell § 7 what it is for | **applied** |
| 9 end sections on the fact obtained, collect the twins | **declined**: D2, decided |
| 10 Figure 4 out of the proof; caption | **applied**: the float placement `[!htb]` so that it sits at the paragraph where it is input; the caption sentence |
| 11 Figure 6 replace or cut | **declined**: D1, decided (kept, relabelled); the table of named pairs is a good idea for module B |
| 12 Figure 3 caption: describe the plot | **applied**: the caption describes the four densities and the Gaussian, states that the variances differ, marks the clipped curve, and drops the moral |
| 13 Figure 1 splits a sentence | **applied**: `[!htb]` placement after its paragraph |
| 14 one name for the exponent class | **declined with reason**: both names are in shared statements ($\NDs$ in the definition and the toolbox, $\LEs$ in the chapter 5–7 statements), so the paper cannot unify them alone; the vocabulary paragraph says which is which |
| 15 "two ends"; "Matern" in the heading | **applied** the sentence; the heading is a shared statement, and the accent is the blueprint's render-allowlist question (a `\Matern` macro like `\Levy`): owed to the blueprint |
| 16 stop the optical metaphor after MTF | **applied**: "optical density" and "the medium" are gone from the copied remark (mirror item) |
| 17 Student-$t$ among the named families | **applied** |
| 18 telegram headings | **applied** at the one the reviewer quotes ("Positivity does."); the run-in labels are kept, being the introduction's structure |
| 19 the statement: cut ratios, dates, the spare-time sentence | **declined**: D5, decided the same day (the short form keeps the ratio and the eight days as the record in one sentence); noted for the author |
| 20 § 8 closes on a claim about method | **applied** in part: the two-sentence flourish is cut; the open questions already end the section |
| Table 2 retitle | **applied**; the causal column stays (release rule 3) |

### The Grok referee report (partial) on the second build

`reviews/line-review-content-768625d-Grok46-partial.md`: verdict *major revision*, the run
unfinished. Assessed point by point against revision `bb97240`:

| point | disposition |
|---|---|
| "kernels at scale" conflates the kernels from the origin with the increments | **applied**: the abstract says "the admissible kernels from the origin" |
| "reimposing interchangeability" needs a reparametrization (the Gaussian is one-parameter in the variance gauge, not in the canonical one) | **applied**: "in whichever scale parametrization the family has it"; `cor:semigroup-case` assumes stationarity in the family's own labels, and the Gaussian at $\alpha = 2$ has it in the variance gauge |
| the regularity is presented as part of the machine-checked result | **applied** in the abstract ("the regularity of the kernels rests on two more"); the claim that its application is "not machine-checked" is wrong: `prop:kernel-regularity` is `\leanok` on the admitted interface, Table 1 |
| Prop. 3.5's construction and the closed form are not machine-checked; the abstract does not say | **already stated** at the point of claim (§ 1, § 3, § 8) and in § 1.1; the abstract's sentence is about the characterization theorem, which is machine-checked; no change |
| Props. 7.8–7.9 rely on external results with unverified hypotheses | **wrong**: 7.8 uses none, 7.9's proof does the hypothesis check |
| Lemma 4.2's statement should list (A4) or "kernels of Lemma 4.1" | **it does**: "the representation of Lemma 4.1" is its hypothesis; shared statement, and the prose after the first review explains; no change |
| Theorem 5.2's proof incomplete | **declined**: no gap named; the first referee checked it |
| Lemma 6.4 and Prop. 6.6 depend on Theorem 7.3 | **wrong**: the proofs do not; the lead mentions § 7 as what uses the form |
| Lemma 7.1 not machine-checked | **wrong**: `\leanok`, and listed in Table 1 |
| $A(\RR)$ used as bounded without saying it is the Wiener algebra | **wrong**: the statement defines it so |
| the Jordan decomposition step does not say the parts are finite and positive | **already there**: "two finite measures", the Jordan parts of a finite signed measure; no change |
| $T^2/3$ should be $T^3/3$ | **wrong**: the identity averages over $[0,T]$, and the average of $\omega^2$ is $T^2/3$ |
| "hemigroup" in probability (convolution hemigroups) not discussed | **applied** (2026-09-14): two sentences after the hemigroup display in § 1 place the term in the probability literature on groups (Siebert 1982, the earliest attestation the librarian found; Heyer 1977; Hazod–Siebert 2001) and beside Sato's "system of probability measures" (Thm. 9.7, p. 51, read from the held copy). The three group-literature sources were gated at first; **the author filed them the same day** and the librarian read the anchors from the held copies: Heyer Def. 4.6.1, p. 308 (the earliest use of the word of the three; Siebert's introduction points to Heyer's § 4.6), Siebert p. 365, Hazod–Siebert Def. 2.14.16, p. 380, all three using "hemigroup" for the composition law with the identity at $s = t$ and weak continuity. The paper prints those anchors. Paper I cites nothing for the term either, so the gap is real there too. The Lamperti 1962 and Jurek–Vervaat 1983 anchors, now held, were verified at the same time (no mismatch) |
| whether the hemigroup axioms are strictly weaker than the Gaussian axioms; whether the Matérn member was known | **answered in the text**: § 8's placement paragraph, and the Bessel scale space sentence in § 1 |
| "gauge" used in Lemma 6.4 before it is defined; Remark 6.7 repeats the abstract | **wrong** on both: § 6's second sentence defines the gauge; Remark 6.7 (the variance gauge) is not in the abstract |
| Prop. 7.8's "$k(\kappa\varepsilon)$ must vanish" needs a.e. | **declined**: $k$ is nonincreasing, so $k \ge k(\kappa\varepsilon)$ on $[\varepsilon, \kappa\varepsilon]$ pointwise and the value vanishes |
| the ten suggestions | 1, 2, 3, 6, 7 are already in the text (the closed form named, § 1.1's exceptions, the uniqueness clause in the paragraph after Lemma 7.1, the smoothness qualification, the orientation-only line of Table 1); 4, 5, 8 are declined above; 9, 10 name no defect |

## Owed to the blueprint (the formalization session) — **DONE 2026-09-14**

*All of the list below is in the blueprint (`Formalization/SKELETON.md` § 21, ledger rows
R156–R157). `prop:two-members`(2) is narrowed and `\leanok` on Lean core; the paper's copy of
that statement and of `prop:no-positivity-no-classification`'s title are updated verbatim.
Three items were deliberately not applied, with reasons in § 21: the causal clause inside
`thm:increments-levy`'s proof, which the paper kept; `B(0)`, which the proof already answers;
and the direct increment profile, which is new mathematics with a Lean cost. The paper's prose
followed the narrowing the same day: one step not machine-checked (§ 1, § 1.1, § 3, § 8), Table 1
without the moment-criterion row, § 3's closed form cited and not claimed.*
`prop:two-members`(2): drop the density sentence (required by C, requested 2026-09-12).
`prop:no-positivity-no-classification`: retitle. Proof-of-record repairs: A (Gaussian factor),
the Prokhorov normalisation in `thm:increments-levy`, $B(0)$ and the finite supremum in
`lem:selfdecomposable-exponents`, the strongly measurable integrand in
`lem:convolution-representation`, the Tonelli remark in `lem:cin-rays`, the mode-interval
argument at `prop:kernel-regularity` (which also gets a proof environment), Prop. 2.7's
approximation step. Copied remarks: `rem:provenance-causal` ("degenerate member"),
`rem:modulation-transfer` (probability kernels), the Sato-process remark's two sentences,
`rem:boundary`'s variance, `rem:displacement-profile-log`'s "extreme rays". The folding
reduction's wording inside ledger A3. The direct increment profile for the Matérn member in
`prop:two-members`'s proof if independence from `thm:main-characterization` is wanted.
