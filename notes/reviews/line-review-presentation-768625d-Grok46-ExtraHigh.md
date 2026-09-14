# Part B — presentation review

Manuscript: *Spatial scale space from hemigroup axioms: characterization of the kernels on the line* (working draft, 49 pages). Presentation only; not a referee report on the mathematics. Page numbers are the printed pages. Quoted phrases are from the text.

**After two pages.** A mathematical-imaging reader can see the theorem: the cascade is weakened from a semigroup to a hemigroup, and with positivity the kernels at scale are the symmetric self-decomposable laws, written as a Gaussian coefficient plus a nonincreasing profile (p. 2). The Gaussian is one ray, not the class. Why that matters for the field is only partly in view: the non-creation property is correctly parked (p. 1), but the rest of the scope — no claim on locality, extrema, filters, dimension, or signals — waits until p. 4. What the paper does *not* claim is therefore not yet in the first two pages. The companion paper is already treated as the reader’s other hand (“the causal article below”, p. 2).

**Register.** The prose is controlled and specific, but it often addresses the author’s twin development and the Lean artefact rather than a JMIV reader. Coined labels (`interchangeability`, `smoothed transmittance`, `optical density`, `displacement profile`) are defined, yet several are kept in play after the definition has done its work. A few openings announce a heading instead of stating a claim.

**Figures and tables.** Six figures, two tables. Figure 1 now sits in the introduction and earns that place. Figure 5 (the dilated profile and its increment) is the right picture for the main condition and should stay. Figure 3 earns its place as a kernel plot; its caption argues a moral the axes do not isolate. Figure 4 earns its content and loses it by splitting a proof. Figure 6 draws a cone whose extreme-ray geometry the paper declines to prove. Table 1 is the right compact account of the trust base; Table 2 is still titled as a dictionary for the other paper.

**Notation.** Table 2 now lists the symbols this paper actually uses (`gs,t`, `Θ`, `χ`, `ϖ`, `B`). The collision of `B` with Brownian motion is flagged in the appendix, which is enough. The body still runs two names, `NDs` and `LEs`, for one class. The local reuse of `a` and `c` is announced and is the lesser problem.

**Section structure.** §§3–6 open with a job. §2 opens with “Letters.” §7 opens inside the argument. Almost every technical section ends on a remark about the causal paper rather than on the fact the next section needs. §1.1 and the author-contribution note are process documents placed where a field reader is still trying to learn the result.

Ranked items follow. Twenty located notes; plainer wording where it is cheap.

---

1. **Put the limits in the same two pages as the theorem.**
   P. 1: “We characterize the spatial scale spaces on the line.”
   P. 1: “whether an aperture creates structure across scale … is outside this paper.”
   P. 4: “no empirical claims about natural signals are made,” together with locality, extrema, filters, and dimension `d`.
   The first two pages now carry the result and one exclusion. They do not yet say that this is an axiomatic derivation of a known probability class on the line, and that implementation and higher dimension are not treated.
   Prefer, in the abstract or at the end of paragraph 1: **“The contribution is the derivation from measurement axioms on the line. Locality, non-creation of extrema, recursive filters, and dimension d are outside the paper.”**

2. **Write the opening for a reader who has not read the companion paper.**
   P. 2: “the companion article on temporal scale space [8], the causal article below”
   P. 3: “Each section records in one remark how its argument relates to the causal one.”
   P. 7, Table 2 title: “The letters, with the correspondence to the causal article.”
   “Below” is false: [8] is not in this file. The running comparison tells a reader they are holding the wrong half of a pair.
   Prefer: **cite [8] once as a companion result under causality; collect the section-by-section twins in one optional remark or appendix.** Drop “below.”

3. **Cut §1.1 back to Table 1.**
   Pp. 4–6: “What is proved,” “What it rests on,” “Why these and not more,” “What is not formalized,” then the `lake` commands and
   P. 6: `"'SpatialLine.main_characterization' depends on axioms: [propext, …]"`
   The disclosure belongs in the paper. The build log does not. An imaging reader is still in the introduction.
   Prefer: **one short paragraph of coverage and two exceptions, plus Table 1. Move the toolchain, axiom dump, and repository recipe to a formalization appendix.**

4. **Split the abstract’s result.**
   P. 1: “With positivity the admissible kernels at scale are exactly the symmetric self-decomposable laws. Each family is determined by a Gaussian coefficient and a nonincreasing function … The Gaussian families form the one ray with a Gaussian coefficient alone, an extreme ray of the cone rather than the whole of it.”
   This is clearer than a single packed sentence, but the cone, the ray, interchangeability, variance-gamma, Matérn, unimodality, and Lean still share one paragraph.
   Prefer three jobs in three sentences: **what is classified; what the two parameters are; what is not claimed (structure across scale, dimension, signals).** Move Lean to a final clause or to §1.1.

5. **Name the dropped assumption as stationarity of increments, not as interchangeability.**
   P. 1: “measurement stages are interchangeable.”
   P. 2: “We call this second assumption the interchangeability of the measurement stages; in the language of processes it is stationarity of the increments in the scale parameter, and it is not commutativity, which every family of convolutions has.”
   The disclaimer is necessary because the chosen name is the wrong one. “Interchangeable” still suggests that operators may be reordered.
   Prefer the name you already gloss: **“stationarity of increments in the scale parameter.”** Then: **“The semigroup makes an increment depend only on t − s. The hemigroup lets it depend on both endpoints.”**

6. **Untangle Bessel / Matérn / variance-gamma on p. 3.**
   P. 3: “The same kernels are the Bessel scale space of [5], where the operators are composed by varying the smoothness at fixed range; their scaled family (§ 2.4 there) adds a dilation parameter but is still composed along the smoothness. Here the range is the cascade parameter, at fixed smoothness.”
   A reader of [5] can parse this; a reader of the field who has not must hold three names, two parameters, and a pointer into another paper’s subsection.
   Prefer: **“These kernels are the variance-gamma laws. For γ > 1/2 they are Matérn covariances. Burgeth, Didas and Weickert compose the same transforms by varying smoothness at fixed range; here the cascade parameter is the range, at fixed smoothness.”**

7. **§2 is still a second paper placed before the axioms.**
   P. 7: “Letters. Space runs over R with coordinate x.”
   Pp. 7–13 then give two names for one class, a cone sermon (Remark 2.4), uniqueness and Lévy-continuity proofs, and a dictionary for [8].
   The axioms that motivate the symbols begin on p. 14.
   Prefer: **open §2 with what it is for (“Fourier facts and the profile representation used later”). Keep Definitions 2.1–2.2, (2.2)–(2.3), and Lemma 2.15. Move the proofs of Propositions 2.7–2.8 and Remark 2.4 to an appendix.**

8. **Tell §7 what it is for before using it.**
   P. 33: “By Lemma 5.1 the exponent of a kernel is a difference of accumulated exponents, and by Proposition 6.6 the accumulated exponent is a dilate of one function.”
   The characterization section starts in the middle of the derivation. The reader who came here from the introduction has to reconstruct the job.
   Prefer: **“This section turns the similarity form into a condition on one function F, solves it, and states the classification (Theorem 7.3).”** Then the two sentences above.

9. **End sections on the fact just obtained.**
   Closing remarks 2.16, 3.6, 4.4, 5.5, 6.8, 7.11 each land on the causal twin.
   Example, p. 13: “At that point the trust base of this article is the narrower of the two.”
   That is a note about another manuscript. The next section needs the profile (2.3), not a comparison of trust bases.
   Prefer: **end §2 on (2.3); end §4 on the exponent gs,t; end §6 on G(t, ω) = F(χ(t)ω).** Move the twins to one collected remark.

10. **Do not put Figure 4 inside a proof.**
    Pp. 30–31: Figure 4 sits between the dominated-convergence sentence of Lemma 6.4(3) and “Under (ND), Θ is continuous…”.
    The figure is the right picture of the gauge. The placement makes the proof unreadable.
    Prefer: **place Figure 4 at the statement of Proposition 6.6, or at a paragraph break before the proof.** Caption, instead of “equal ratios of λ, unequal steps on the axis”: **“The given scale labels need not preserve dilation ratios; the canonical coordinate does.”**

11. **Figure 6 still draws a geometry the paper does not claim.**
    P. 40: “They are drawn along the far side only to keep them apart; whether they are extreme, which the superposition alone does not show, is outside this paper, and the drawing places nothing.”
    A figure that must cancel itself in the caption is not earning its place.
    Prefer: **a small table of named pairs (a, k): Gaussian (a, 0), stable (0, Cα x^{−α}), Matérn (0, 2γ e^{−x}).** If a cone sketch is kept, draw only the Gaussian ray and the stable slice, which the text does prove.

12. **Figure 3: describe the plot, not the moral.**
    P. 20: “The exponential rate is the price of the jumps, and the Gaussian, with no jumps, is the one member without that rate.”
    The Matérn curves are not variance-matched to one another; the Gaussian is one variance among them. Peak shape and width move together.
    Prefer: **“Left: Matérn densities at γ = 1/2, 1, 2, 4, and a Gaussian of variance 4. At γ = 1/2 the origin is unbounded; at γ = 1 the plot is the Laplace density. Right: the same curves on a log scale.”** If the comparison is Gaussian approximation, say that the variances differ.

13. **Do not split a sentence across Figure 1.**
    Pp. 1–2: “the composite depends only on the total amount” / Figure 1 / “of scale crossed”.
    Figure 1 is the one figure a field reader needs in the introduction. The interrupt is layout, not content.
    Prefer: **finish the paragraph, then place the figure.** Keep the caption’s best sentence: **“Increments of equal span at different positions need not coincide.”**

14. **Use one name for the exponent class in the body.**
    P. 10: “Which vocabulary does the work.” Then LEs is “the name the later sections use,” while NDs remains in play through Lemma 7.1.
    Two official names for one set, plus the remark that only one is used, is a cost with no return for an imaging reader.
    Prefer: **define the class once (the form (2.2), or the exponential form of Definition 2.2) and keep that name.** Put the NDs/LEs dictionary in a footnote.

15. **“Two ends” and “Matern”.**
    P. 18: “Two members are exhibited, at the two ends of what the axioms admit”
    P. 18: “2. (The Matern family.)”
    Gaussian and Matérn are two members the axioms must contain, not the two ends of the cone (the stable rays are another boundary the paper itself draws). The accent is missing in the proposition title, not in the surrounding text.
    Prefer: **“Two members are checked before the general theory: no jumps, and jumps of every size.”** Write **Matérn** in the heading.

16. **Stop the optical metaphor after MTF.**
    P. 24: “the exponent is its optical density.”
    P. 24: “the medium is self-similar (§6).”
    Modulation transfer (same remark) is the imaging word. “Optical density” and “medium” invent a layered object the axioms do not contain.
    Prefer: **keep “modulation transfer function.”** For Θ (p. 28): **“the transfer function averaged against a Gaussian window; it is strictly monotone in scale and is the coordinate used in §6.”**

17. **Do not name Student-t among the exclusions.**
    P. 4: “the named families inside it (Matérn, Student-t, symmetric stable)”
    Student-t never appears again. Listing it as a “named family inside” a cone whose geometry is outside the paper is a forward reference with no payoff.
    Prefer: **“named families (Gaussian, Matérn, symmetric stable)”** — the three the text actually exhibits.

18. **Replace the telegram headings in the introduction.**
    P. 3: “Which assumption narrows. Positivity.”
    The other labels (“The assumption.”, “What the class is.”, “The route.”) do the same: they announce a file divider.
    Prefer a sentence: **“Positivity is what makes a classification possible: without it the remaining axioms already admit an infinite-dimensional family through the Gaussian.”**

19. **The author-contribution note is a process memoir.**
    P. 46: “the agents’ words outnumber mine by about twenty-two to one”
    P. 46: “the sustained work took eight days”
    Roles, verification, and responsibility are the parts a journal reader needs. Word counts, calendar, and the archive of another review are not.
    Prefer: **keep Roles, Verification, Responsibility. Cut the ratios, the dates, and the sentence about spare time.**

20. **Do not close the mathematics on a claim about writing method.**
    P. 43: “Verification is usually described as a check on a finished argument. Here it shortened the argument.”
    The four open questions just above that paragraph already end the paper on content. The flourish restates §1.1 in a higher register.
    Prefer: **delete the paragraph, or reduce it to one sentence in the formalization appendix.** The open questions should be the last word of §8.

---

**Figures, one line each.** Fig. 1: keep, in the introduction, after the paragraph. Fig. 2: keep; it is the covariance square. Fig. 3: keep the plot, rewrite the caption (item 12). Fig. 4: keep, move out of the proof (item 10). Fig. 5: keep; it is the figure the characterization needs. Fig. 6: replace or cut (item 11). Nothing else is missing once Fig. 5 is present; a plot of transfer functions would be optional, not required.

**Table 2.** Retitle as a table for this paper: symbol / meaning / defining location. Keep the causal column only if it is moved out of the main notation table.

**Section openings that already work.** §3, “This section assembles the axiom system”; §4, “This section derives the form of the measurement operators”; §6, “Covariance turns the free relabelling Sλ of (A8) into a coordinate.” Match §2 and §7 to that pattern.
