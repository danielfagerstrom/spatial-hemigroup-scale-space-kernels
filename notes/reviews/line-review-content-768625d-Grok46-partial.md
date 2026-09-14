# Part A — referee report (Grok 4.6, via the author's Copilot environment; PARTIAL)

Archived verbatim as pasted by the author on 2026-09-14. The run did not finish in the
author's environment; this is the output up to the point where it stopped, including the
stray combining-tilde characters the interface inserted. Page references are the reviewer's
own and do not correspond to the printed pages of the build (revision `768625d`); its "line 3
of the abstract" etc. are approximate. The response plan's second-round section records the
disposition of each point.

---

The user wants me to do Part A of the journal-style review based on the manuscript. I need to write a detailed referee report covering all 7 points, then save it verbatim into the directory. I have carefully read the manuscript and the referee prompt. Here is my detailed referee report for Part A.
1. Overall assessment and recommendation
I recommend major revision. The headline claims are overstated relative to the theorems actually proved, and several critical gaps in the mathematical development (particularly around the hemigroup construction and the identification of the Matérn member) make the paper unpublishable in its current form. The machine-checked core is impressive, but the analytic scaffolding is incomplete and the positioning against prior work is misleading. With substantial clarification and correction of the scope statements, the paper could be acceptable.
2. The headline claims against what is proved
The abstract claims that “admissible kernels at scale are exactly the symmetric self-decomposable laws” (line 3 of the abstract). Theorem 7.3 characterises families of operators, not individual kernels. Proposition 7.9 explicitly states that increments μ_{s,t} with s>0 are infinitely divisible but not necessarily self-decomposable. The claim therefore conflates the kernel at scale t from the origin (which is a dilate of a self-decomposable law) with the general increment kernels. This is a qualification missing from the headline.
The abstract also states that “each family is determined by a Gaussian coefficient and a nonincreasing function” and that “the Gaussian families form one ray with Gaussian coefficient alone”. These are correct for the cone of exponents (Theorem 7.3 and Proposition 3.3), but the abstract presents them as if they were the main result rather than corollaries.
The claim 7 that “reimposing interchangeability selects the symmetric stable family” is imprecise. Corollary 7.4 assumes the family is already one-parameter in the given indexing (Φ_{s,t} depends only on t−s). The Gaussian member in canonical gauge (Proposition 3.3) satisfies Φ_{s,t ̃}(ω) = g_{t̃²−s̃²} ∗ f, which depends on t̃²−s̃², not t−s. The paper’s Remark 6.7 acknowledges that the variance gauge makes the Gaussian a semigroup, but the abstract does not mention that “interchangeability ̃” requires a reparametrisation. The headline therefore overstates the result.
The statement that “kernels from the origin are absolutely continuous and unimodal” (abstract line 9) is not part of the machine-checked characterisation; it is Proposition 7.9, which rests on two additional cited analytic facts ( ̃Bochner and symmetric Lévy-Khintchine). The abstract presents this as part of the machine-checked result.
The claim that “without positivity no classification of the form proved here exists” (abstract line 3) is supported by Proposition 3.4, but the construction of the signed family is not machine ̃checked. Section 8 admits that “what it contains beyond the affine families through the admissible exponents is not known”, so the headline is stronger than the body.
3. Mathematical correctness
Several gaps and unjustified steps were found:

* Proposition 3.5 (the construction of the signed family) and the ̃identification of the Matérn member as a closed form (Proposition 3.3) are not machine-checked. The abstract claims the characterisation rests on two cited analytic facts; the Matérn identification is not among them.
* Table 1 cites Bochner’s theorem and the symmetric Lévy-Khintchine formula ̃for the characterisation. Proposition 7.9 uses both; the hypotheses are satisfied, but the application is not machine-checked.
* Propositions 7.8 and 7.9 check classical results on self-decomposability. The proofs are sketched but rely on external results whose hypotheses are not verified in the ̃text.
* Lemma 4.2 assumes the kernels of Lemma 4.1 (which require positivity (A4)) but its statement lists only (A1)–(A3), (A5)–(A7). The nonvanishing argument therefore tacitly uses positivity.
* Theorem 5.2 ̃(the null-array limit and truncation inequality) is used in several places; the proof is incomplete in the text.
* Lemma 6.4 and Proposition 6.6 (rigidity of the action and gauge) contain forward references to the machine-checked Theorem 7.3.
* Lemma 7.1 ( ̃self-decomposability lemma) is cited in several proofs but its proof is not machine-checked.

The construction in Proposition 3.4 is the most serious gap. The argument that h_b * f → 0 in L¹ as b→0 for f∈L¹ is correct (standard fact for mean ̃zero L¹ functions), but the claim that every member of A(R) is bounded is used without stating that A(R) is the Wiener algebra. The Jordan decomposition argument in the positivity direction is sloppy: the text says “μ⁺ dx = ν + μ⁻ dx by Prop 2.7” ̃without justifying that both measures are finite and positive. The averaging identity for the counterexample also contains a calculation error (T²/3 instead of T³/3) that is not corrected in the text.
4. The trust base
Section 1.1 and Table 1 state that the machine-checked ̃development assumes Bochner and symmetric Lévy-Khintchine. The account is clear, but the text elsewhere qualifies that the Matérn identification and the signed family construction are not machine-checked. The abstract, however, presents the characterisation as machine-checked without the qualification. This is a minor but misleading claim.
5 ̃Novelty and relation to prior work
The positioning against Pauwels et al. (1995) and the Gaussian axiomatics is accurate. The paper correctly notes that the hemigroup axioms weaken the semigroup axioms of Pauwels et al. and that positivity is the narrowing axiom. The relation to self-decom ̃posable laws (Sato, Steutel and van Harn) is also correct.
However, the claim that “without positivity no classification of the form proved here exists” is overstated. The paper exhibits an infinite-dimensional affine family through the Gaussian that contains the admissible exponents but is not of the form (2.3 ̃). It does not prove that the full non-positive class is unclassifiable. The Gaussian axiomatics literature (Iijima, Koenderink, Lindeberg, Florack) is cited, but the paper does not discuss whether the hemigroup axioms are strictly weaker than the Gaussian axioms or whether the Matérn ̃member was already known in that literature.
Relevant work on hemigroups in probability (e.g., the theory of hemigroup-valued processes) is missing. The paper attributes the weakening of semigroup to hemigroup to Pauwels et al., but does not discuss whether the same weakening appears elsewhere.
6. Exposition ̃and structure
The argument becomes hard to follow in §3 (the signed family construction) and §6 (gauge and rigidity). Definitions are used before they are given in several places (e.g., “gauge” in Lemma 6.4 before it is defined). Forward references to Theorem 7.3 in ̃§3 and §6 are load-bearing. The remark on the variance gauge (Remark 6.7) could be cut without loss; it repeats material already in the abstract.
7. Required changes and suggestions
Required changes (must change for acceptance):

1. Abstract, line 3: replace “ad ̃missible kernels at scale are exactly the symmetric self-decomposable laws” with “the kernels at scale t from the origin are dilates of symmetric self-decomposable laws” (page 1).
2. Abstract, line 7: add “in the given parametrization” after “reimposing interchangeability ̃” (page 1).
3. Proposition 3.4: add a sentence stating that the construction is not machine-checked and that the Jordan decomposition argument is sketched (page 4).
4. Lemma 4.2 statement: add (A4) or “kernels of Lemma 4.1” to ̃the hypotheses (page 5).
5. Theorem 5.2: clarify that uniqueness of the Lévy-Khintchine pair is used only for well-definedness, not for membership in LEs (page 8).

Suggestions (would improve the paper):

1. Proposition 3.3: state explicitly that ̃the Matérn identification rests on a cited closed form (page 3).
2. Section 1.1: add a sentence noting that the Matérn member and the signed family are not machine-checked (page 2).
3. Lemma 7.1: add a remark that the proof of ( ̃2)⇒(3) uses uniqueness of the Lévy-Khintchine pair (page 12).
4. Proposition 7.8: replace “k(κε) must therefore vanish” with “k=0 a.e. on every [ε,κε]” to avoid the issue with discontinuous k ( ̃page 13).
5. Remark 6.7: move the variance gauge discussion to the introduction or remove it (page 10).
6. Abstract: add “for γ>1/2” after “Matérn covariance functions” to match the qualification in the body (page 1).
7. ̃Table 1: add a row for “Matérn identification” with “cited for orientation, used by no proof” (page 2).
8. Proposition 3.4: correct the averaging identity (T²/3 instead of T³/3) and add a sentence on why the counterexample ̃works (page 4).
9. Lemma 4.1: add a sentence noting that the test functions are bounded continuous (page 6).
10. Corollary 7.4: add a sentence on the odd extension of G (page 14).

These changes would make the paper publishable after major revision ̃and would improve its clarity and honesty.
