**After two pages, a field reader can identify the main result, but its significance takes work and its limits remain too implicit.** The strongest message is that the weaker composition requirement admits non-Gaussian, scale-covariant families with finite moments. That deserves more prominence. The section openings generally give useful direction; repeated commentary about formalization and the companion paper interrupts that direction.

I read all 48 pages, including the five figures and two tables. These are presentation comments, ranked by their effect on the reader. Page numbers are the printed numbers. :codex-file-citation{path="C:/Users/DAHT/Downloads/spatial-hemigroup-line-09602a3.pdf" purpose="source"}

1. **Bring the contribution and its limits into the first two pages.**  
   P. 1: “We characterize the spatial scale spaces on the line”; p. 3: “The class this paper arrives at is classical in probability theory”; p. 4: “no empirical claims about natural signals are made.” The latter two qualifications arrive late. State early that the contribution is an axiomatic derivation of a known probability class, and that locality, non-creation of extrema, higher dimensions, and filtering performance are not established here.

2. **Replace “interchangeability” with the property actually described.**  
   P. 1: “measurement stages are interchangeable”; p. 15: “increments … determined by the difference \(t-s\).” “Interchangeable” suggests changing the order of operators. Your explanation concerns dependence on position along the scale axis. Prefer: **“The semigroup assumption makes an increment depend only on the scale difference. We allow it to depend on both endpoints.”** Use “stationary increments in the scale parameter” if a short technical name is needed.

3. **Narrow the wording of the no-positivity claim.**  
   P. 1: “Without positivity the class cannot be classified”; p. 19: “Without positivity there is no classification.” These read as unrestricted impossibility claims. The nearby qualification, “no classification in the style of Theorem 7.3,” is substantially narrower. Prefer: **“Without positivity, the remaining axioms admit an infinite-dimensional family of signed kernels; the positive-profile characterization no longer applies.”**

4. **Make the “one changed axiom” account consistent with the later explanation.**  
   P. 2: “Every other axiom … is retained”; p. 17: “Positivity … is an axiom here,” alongside the explanation that continuous kernel functions are no longer assumed. The reader has to reconcile these descriptions. Prefer: **“The central change is the replacement of semigroup recursivity by a hemigroup. Remark 3.2 details the accompanying operator formulation and treatment of positivity and regularity.”**

5. **Distinguish kernels at scale from transition kernels in every summary.**  
   P. 1: “The kernels are absolutely continuous and unimodal”; p. 40: the proposition concerns “the kernels from the origin only.” The abstract’s unqualified wording invites the broader reading. Prefer: **“The kernels \(\mu_{0,t}\), for \(t>0\), have unimodal densities.”** Apply the same distinction to “the axioms never produce a multimodal kernel” on pp. 3 and 40.

6. **Explain the scale coordinate before using the Gaussian example.**  
   P. 6 calls \(t\) “the evolution variable of the diffusion equation”; p. 32 explains that it is a length, whereas the familiar diffusion parameter is a variance. That clarification comes too late for p. 17’s \(g_{t^2-s^2}\). Add on p. 6: **“Initially \(t\) is an ordered scale label. In the canonical parametrization it has units of length; the Gaussian diffusion parameter is proportional to \(t^2\).”**

7. **Split the abstract’s main-result sentence.**  
   P. 1: “With positivity the admissible families are exactly … rather than the whole answer.” This sentence combines the classification, parameter interpretation, cone structure, and Gaussian’s position. Prefer three sentences: **“With positivity, the admissible kernels at scale are the symmetric self-decomposable laws. Each family is specified by a Gaussian coefficient and an admissible nonincreasing displacement profile. The Gaussian families form the ray with zero displacement profile.”**

8. **Condense §1.1 and retain Table 1 as the compact account.**  
   Pp. 4–6: “What is proved,” “What it rests on,” “Why these and not more,” and “What is not formalized.” The disclosure is useful, but occupies much of the introduction and recurs throughout the proofs. Table 1, “The cited facts and their direct uses” (p. 5), earns its place. Keep a short statement of coverage and limitations near the introduction; move the detailed dependency discussion and build instructions to a formalization appendix.

9. **Make the companion-paper comparison optional reading.**  
   P. 3: “The derivation runs in the order of the causal article”; p. 32: “Everything else … ports verbatim.” These passages address someone following both developments. Consolidate the recurring comparisons into one subsection or appendix. Likewise, delete p. 6’s reservation of letters “for the later modules”: it explains the author’s programme without helping the reader interpret this paper.

10. **Turn Table 2 into a reference for this manuscript.**  
    P. 6: “The letters, with the correspondence to the causal article.” The correspondence column consumes space while central symbols—\(\chi\), \(g_{s,t}\), \(\Theta\), \(\nu\), \(\varpi\), and \(B\)—are absent. Use columns **symbol / meaning / defining equation or section**. Separate transition quantities from quantities accumulated from scale zero. Move the cross-paper correspondence elsewhere; the resulting table could also use larger type.

11. **Move Figure 2 into the introduction.**  
    P. 16: “The two readings of the cascade property.” This is the most useful diagram: it directly explains the changed assumption. It is first invoked on p. 2 but appears fourteen pages later. Place it beside that first explanation and shorten the caption around its strongest sentence: **“Increments of equal span at different positions need not coincide.”**

12. **Keep Figure 3, but clarify what its comparison shows.**  
    P. 19: “flattens toward the Gaussian as \(\gamma\) grows.” The plotted Matérn curves have different variances, while the Gaussian has variance 4, so shape and width change together. For a Gaussian-approximation comparison, standardize the variances; otherwise describe only the displayed changes in peak and tails. Mark the clipped singularity at \(\gamma=\tfrac12\), reconcile the Gaussian legend with the caption’s tail formula, and replace “the price of the jumps” with a description limited to these Matérn curves.

13. **Replace or substantially simplify Figure 5.**  
    P. 39: “The admissible cone,” with Cin rays on “the far boundary.” The drawing gives geometric positions to objects whose geometric classification is expressly outside scope on p. 38. The final “schematic” qualification does not fully undo that impression. A family map or a small table of \((a,k)\) examples would communicate the established relationships more clearly. Also reconcile p. 12’s assertion “The extreme rays … are” with p. 38’s statement that their extremality is outside the paper.

14. **The missing figure is the displacement profile.**  
    P. 2: “the whole catalogue stretches with the scale”; p. 33, equation (7.1): \(k(u/t)-k(u/s)\). This function is central to both the interpretation and the characterization, yet never pictured. Plot a simple decreasing profile, two dilates, and their nonnegative difference. That would explain what the monotonicity requirement does more directly than another cone schematic.

15. **Use “degenerate” consistently.**  
    P. 14: “the class has no degenerate member”; p. 17: “the degenerate member is … the Gaussian scale space itself”; p. 39: “not a degenerate boundary.” Whatever distinction is intended, the terminology currently reverses itself. Use **“jump-free member”** for the Gaussian and reserve “degenerate” for the precise excluded case.

16. **Introduce the Brownian notation and avoid the collision with \(B\).**  
    P. 43: “\(X_t\overset d=B_T\)” appears without defining the process or its independence from \(T\). Earlier, \(B\) denotes the symbol \(\omega F'(\omega)\). Prefer: **“Let \(W\) be standard Brownian motion, independent of \(T\). Then \(X_t\overset d=W_T\).”** This is a more consequential collision than the explicitly announced local reuse of \(a\) and \(c\).

17. **Stop extending the optical analogy beyond its explanatory use.**  
    P. 28: “the transmittance of the medium to depth \(t\)” and “a self-similar medium has no marked layer.” The modulation-transfer interpretation on p. 23 helps an imaging reader; the invented medium and its layers introduce another object to interpret. Prefer: **“\(\Theta(t)\) is the transfer function averaged against a Gaussian window. Its strict monotonicity provides a coordinate on the scale axis.”**

18. **Cut announcements and untangle the Matérn introduction.**  
    P. 1: “The introduction takes the derivation in four steps” repeats the paragraph labels that follow. Delete it. P. 2’s sentence ending “composed there along the smoothness index at fixed range where here it is composed along the range” is genuinely hard to parse. Prefer: **“These are Matérn kernels, also used in Bessel scale space [5]. That construction composes operators by varying smoothness at fixed range. Here we vary range at fixed smoothness.”**

19. **Keep Figures 1 and 4, but tighten their captions and placement.**  
    P. 15: “Scale covariance”; p. 30: “The orbit coordinate.” They earn their places by showing different things: commuting operations and a change of scale coordinate. Figure 1 interrupts the cascade discussion rather than accompanying §3.3. Figure 4 interrupts a proof mid-sentence. Move each to a paragraph boundary. In Figure 4, replace “equal ratios … unequal steps” with **“The original coordinate need not preserve dilation ratios; the canonical coordinate does.”**

20. **Let sections end on results, and shorten the project history.**  
    P. 18: “Between the two the theory has to fit, and Theorem 7.3 says what fits” adds a flourish without specifying a relationship. Prefer: **“Theorem 7.3 characterizes all families satisfying these axioms.”** Several major sections instead finish with another causal-paper comparison; end them with the result now available to the next section. The concluding questions on p. 42 already do this well. For the disclosure on pp. 44–46, retain roles, review status, and responsibility; move chronology and phrases such as “the constellation’s writing standard” (p. 45) to a supplementary process account.

- Revise the opening
- Revise the captions
- Rebuild the notation table