# Referee report

*Spatial scale space from hemigroup axioms: characterization of the kernels on the line*

Page references refer to the supplied PDF’s printed pagination, pp. 1–48. This report assesses the printed arguments and their relationship to the cited literature; it does not certify a successful build of the Lean development.

## 1. Overall assessment and recommendation

**Recommendation: major revision.** The central characterization appears mathematically sound, and the nonvanishing, null-array, action-rigidity and self-decomposability arguments contain worthwhile work. I found no substantive defect in the principal arguments of Theorem 5.2, Proposition 6.6 or Lemma 7.1. However, the manuscript contains definite errors: the signed construction has a Gaussian normalization error; Lemma 4.2 claims nonnegative exponents without the positivity hypothesis needed for that conclusion; the identification with Matérn covariance functions is wrong over part of the stated parameter range; and regularity established only for kernels from scale zero is repeatedly asserted for all kernels, for which it is false. The claims about impossibility of classification, preservation of the earlier axiom system, and the formal trust boundary also exceed or contradict the qualifications in the body. These are not matters of polishing. A corrected manuscript could merit publication, but the present version does not support its headline claims with sufficient accuracy.

## 2. Headline claims against what is proved

| Claim and location | Assessment against the supporting result |
|---|---|
| The axioms are those of Pauwels et al., with one weakened — abstract, pp. 1–2; conclusion, p. 41. | **Inaccurate as stated.** Remark 3.2, pp. 16–17, acknowledges that continuous kernels are no longer assumed and positivity is made an axiom. These changes matter: some admitted origin kernels are unbounded, and some increments have atoms. |
| The admissible families are exactly the symmetric self-decomposable laws — pp. 1–3, 41. | **Supported with qualifications.** Theorem 7.3, pp. 35–37, classifies families, up to a scale gauge, through a **nondegenerate symmetric self-decomposable origin law**. The increment laws need not themselves be self-decomposable. “Exactly the laws” also suppresses the exclusion of the trivial law. |
| The exponent and gauge are unique — pp. 2–4, 41. | **Supported after normalization.** Theorem 7.3 establishes uniqueness after \(\chi(1)=1\); otherwise \((\chi,F)\) and \((c\chi,F(c^{-1}\,\cdot))\) describe the same family. The unqualified uniqueness language on p. 2 should match this. |
| Without positivity the class cannot be classified — abstract; §3.8 and Proposition 3.5, p. 19. | **Not proved.** Proposition 3.5 constructs an infinite-dimensional signed family and excludes the positive Lévy-profile representation for certain members. Neither fact proves impossibility of classification. The positive class is itself infinite-dimensional. |
| Reimposing “interchangeability” selects the symmetric stable family, with \(0<\alpha\le2\) — pp. 1–3, 41. | **Supported if “interchangeability” means dependence only on the scale difference in an additive parameter.** This is the actual assumption of Corollary 7.4, p. 37. It must not mean commutativity: all the convolution operators already commute. |
| The Gaussian is an extreme ray and the unique jump-free type — pp. 1–3. | **Supported**, after adjoining zero to form the cone and distinguishing a ray from one normalized member. This is also an immediate consequence of the classical representation, not a new probability-theoretic phenomenon. |
| The class contains all-moment examples, including the Matérn family — pp. 1–2. | The all-moment assertion is **correct** for the variance-gamma/Bessel family. The unrestricted identification as Matérn **covariance functions** is **wrong for \(0<\gamma\le\tfrac12\)**. |
| The kernels are absolutely continuous and unimodal — abstract, p. 3, conclusion p. 41. | **False if “kernels” includes the stage kernels \(\mu_{s,t}\).** Proposition 7.9, p. 40, establishes this only for \(\mu_{0,t}\), \(t>0\), and expressly disclaims the general increment statement. |
| The characterization and everything it uses are machine-checked using two cited analytic facts — contribution list and §1.1, p. 4. | This may accurately describe the principal formal declaration, but the PDF alone does not establish it. It must be distinguished from verification of every printed statement, the regularity conclusions, the moment clause, and the two substantive exceptions identified on pp. 5–6. |
| The Fourier-side route is a contribution — pp. 3–4. | **Substantiated by the proofs**, particularly the Gaussian-window coordinate and direct extraction of the increment representation. Its novelty should be described as an operator-axiomatic derivation and formal proof architecture, rather than a new classification of self-decomposable laws. |

Several scope statements also need correction.

**“Outside this paper” does not exempt assertions made inside it.** The text excludes cone geometry and extreme rays on pp. 4, 38–43, but repeatedly describes their geometry and supplies the superposition that makes the remaining extremality argument short. It is legitimate to omit that argument; it is misleading to present an elementary consequence as a substantial unresolved question. Calling the Matérn, Student-\(t\), and stable families “corners” on p. 4 is particularly unfortunate: the non-Gaussian stable and Matérn profiles are mixtures of step profiles, not extreme rays.

Likewise, locality and generator evolution are called outside scope, but Remark 7.10, p. 40, states the evolution equation and asserts the polynomial-symbol implication. These should either be proved as short corollaries or identified precisely as observations requiring further functional-analytic formulation.

Finally, deferring non-creation of extrema is a material limitation of the imaging interpretation. Positivity and unimodality of an aperture do not establish the classical non-creation-of-structure property. That limitation belongs near the first claim to characterize “spatial scale spaces,” not only in the exclusions on pp. 4 and 41.

## 3. Mathematical correctness

### 3.1. Definite errors and invalid inferences

**A. Proposition 3.5 constructs the wrong Gaussian factor — pp. 19–20.**

The proposition defines
\[
F(\omega)=\omega^2+\phi(\omega),
\qquad
\widehat\mu_{s,t}(\omega)
=e^{-(t^2-s^2)\omega^2}
 e^{-[\phi(t\omega)-\phi(s\omega)]}.
\]
But p. 20 realizes this using \(g_{t^2-s^2}\), explicitly described as the Gaussian of variance \(t^2-s^2\). With the convention fixed in Proposition 3.4,
\[
\widehat g_v(\omega)=e^{-v\omega^2/2}.
\]
The constructed measure therefore has half the intended Gaussian exponent.

Both the kernel formula and the operator-exponential formula on p. 20 must use
\[
g_{\,2(t^2-s^2)}.
\]
This is a repairable normalization error, not a counterexample to the proposition’s intended statement. It is nevertheless an error in precisely the construction for which the printed proof is the sole verification.

The treatment of continuity at \(s=0\) is otherwise appropriate. The author correctly recognizes that dilation is not norm-continuous there in the Fourier algebra and instead uses strong continuity of the convolution operators.

**B. Lemma 4.2 claims more than its hypotheses imply — p. 23.**

The nonvanishing argument is valid without positivity, provided the finite signed convolution representation is available. The additional conclusion
\[
g_{s,t}=-\log\widehat\mu_{s,t}\ge0
\]
is false without positivity.

The final paragraph uses
\[
|\widehat\mu|\le\|\mu\|=1.
\]
For a signed measure, total mass one does not imply total variation one.

An explicit counterexample is obtained by setting
\[
\sigma=\tfrac12(\delta_{-1}+\delta_1),\qquad h=t-s,
\]
and
\[
\mu_{s,t}
=e^h\sum_{n=0}^{\infty}\frac{(-h)^n}{n!}\sigma^{*n}.
\]
These are finite symmetric signed measures of mass one forming a norm-continuous convolution semigroup. They satisfy the lemma’s advertised assumptions, but
\[
\widehat\mu_{s,t}(\omega)=e^{h(1-\cos\omega)},\qquad
g_{s,t}(\omega)=-h(1-\cos\omega).
\]
Thus the transform exceeds one and the exponent is negative away from \(2\pi\mathbb Z\).

The “none amplifies” assertion in Remark 4.3 is consequently also false under the stated positivity-free assumptions. If “the representation of Lemma 4.1” is intended to import a probability measure, positivity has been assumed implicitly, contrary to the surrounding explanation. Split the result into a signed nonvanishing lemma and a probability-kernel corollary.

This error does **not** invalidate Theorem 5.2: that theorem explicitly assumes (A4).

**C. The Matérn covariance identification has the wrong parameter range — pp. 2, 6, 17–19.**

For \(t>0\), the inverse transform of \((1+t^2\omega^2)^{-\gamma}\) is, for \(x\ne0\),
\[
p_{\gamma,t}(x)
=
\frac{1}{t\sqrt{\pi}\,\Gamma(\gamma)}
\left(\frac{|x|}{2t}\right)^{\gamma-\frac12}
K_{\gamma-\frac12}\!\left(\frac{|x|}{t}\right).
\]
This is a valid probability density for every \(\gamma>0\). It is proportional to a conventional Matérn covariance function of smoothness
\(\nu=\gamma-\tfrac12\) only when \(\gamma>\tfrac12\).

At \(\gamma=\tfrac12\), the density is \(K_0(|x|/t)/(\pi t)\), which diverges logarithmically at zero. For \(0<\gamma<\tfrac12\), it has a power singularity there. Such functions cannot be ordinary finite-variance covariance functions: a stationary covariance satisfies \(|C(x)|\le C(0)<\infty\). The manuscript’s cited Matérn survey explicitly requires positive smoothness. [Porcu et al., §2, equation (9)](https://num.math.uni-goettingen.de/schaback/research/papers/TMM.pdf)

The family should be called variance-gamma or Bessel over the full range, with the Matérn covariance correspondence restricted and normalized explicitly. The density’s “smoothness index” should also be distinguished from differentiability of sample paths of a random field having it as covariance.

The variance \(2\gamma t^2\) and the even-moment formula in Proposition A.3, pp. 43–44, are correct.

**D. Absolute continuity and unimodality fail for general increments — pp. 1, 3, 17, 21, 36, 40–41.**

The qualification following Proposition 7.9 is essential, but the manuscript repeatedly drops it. Its own examples disprove the broader assertion.

For the variance-gamma member with \(\gamma=1\),
\[
\widehat\mu_{s,t}(\omega)
=\frac{1+s^2\omega^2}{1+t^2\omega^2}
=\frac{s^2}{t^2}
+\left(1-\frac{s^2}{t^2}\right)\frac1{1+t^2\omega^2}.
\]
For \(0<s<t\), this increment has an atom of mass \(s^2/t^2\) at zero. It is not absolutely continuous.

The manuscript also supplies a counterexample to unimodality. Take
\[
F(\omega)=\operatorname{Cin}(\omega),\qquad k(x)=\mathbf1_{(0,1)}(x).
\]
Then the increment from \(s\) to \(t\), \(0<s<t\), has folded Lévy measure
\[
\nu_{s,t}(dx)=\mathbf1_{(s,t)}(x)\frac{dx}{x}.
\]
It is compound Poisson, of intensity \(\log(t/s)\), with atom \(s/t\) at zero. Its one-jump density has an upward jump at \(x=s\); the density contributed by two or more jumps is continuous, so that upward jump persists in the complete density off zero. The law cannot be unimodal about zero. Its symmetry and sole atom at zero also preclude a different mode in the distribution-function definition used on p. 40.

Thus “the axioms never produce a multimodal kernel” on p. 40 is wrong for stage kernels. This is not merely terminological: §4 explicitly calls \(\mu_{s,t}\) the kernel of a stage.

**E. Unimodality does not exclude truncated Gaussians — pp. 3, 40–41.**

A normalized Gaussian restricted to a symmetric bounded interval is even and unimodal. Consequently, the repeated inference “unimodal, so no truncation of the Gaussian is admissible” is invalid.

The exclusion itself is correct, but needs a different argument. For a hard truncation at \(\pm R\), integration by parts gives a cosine transform with leading term
\[
\frac{2p(R)\sin(R\omega)}{\omega},
\]
and remainder \(O(\omega^{-2})\); it changes sign infinitely often, contradicting Lemma 4.2. Alternatively, prove or cite the impossibility of a nondegenerate infinitely divisible law with bounded support.

**F. The folding argument cancels an integral that may not exist — pp. 8–9.**

The statement
\[
\int \sin(\omega x)\,\nu_2(dx)=0
\]
does not follow simply from symmetry of a Lévy measure. For
\[
\nu_2(dx)=c|x|^{-1-\alpha}\,dx,\qquad 1\le\alpha<2,
\]
the positive and negative parts of the sine integral diverge near zero.

Use the compensated odd integrand, or symmetric truncations followed by a justified limit, and identify the vanishing drift by symmetry and uniqueness. The folded representation is correct; its printed justification is not. This matters particularly because p. 5 places the folding reduction inside an admitted interface.

**G. The stated Bochner interface omits a necessary hypothesis — pp. 4 and 9.**

A continuous positive definite function with value one at zero need not be the cosine transform of a symmetric probability measure. For example, \(e^{-i\omega}\) is the transform of \(\delta_1\).

The real-valued/even hypothesis must be included. Proposition 2.3(1), p. 7, states this correctly; §1.1’s allegedly self-contained account does not. If the Lean interface has a real-valued function type, print that restriction. I cannot determine from the PDF whether this is only an error in the description or a mismatch with the actual admitted declaration.

### 3.2. Examination of the arguments carrying the characterization

**Theorem 5.2 — pp. 25–26: the principal argument checks out.**

The null-array estimate
\[
0\le \sum_i g_i-\sum_i(1-e^{-g_i})
\le \bigl(\max_i g_i\bigr)g_{s,t}
\]
is valid. Uniform continuity in scale makes the right-hand side tend to zero at each fixed frequency.

The stated truncation inequality
\[
1-\frac{\sin u}{u}
\ge \frac{2}{3\pi^2}(1\wedge u^2)
\]
is valid, including the treatment of \(u>\pi\). It supplies both bounded weighted mass and uniform control of the tails. The limiting test function
\[
x\longmapsto\frac{1-\cos(\omega x)}{1\wedge x^2},
\qquad k_\omega(0)=\omega^2/2,
\]
is bounded and continuous on \([0,\infty)\). One weakly convergent subsequence of weighted measures therefore works for all frequencies; no missing diagonal extraction is needed.

The phrase “Prokhorov after normalising the masses” should be completed: first pass to a subsequence of total masses, handle a zero limit directly, and normalize only when the limit is positive. Blind normalization of measures whose masses tend to zero need not preserve tightness. This is a routine omitted detail, not a substantive failure of the argument.

**Lemma 6.4 and Proposition 6.6 — pp. 29–31: the principal arguments check out.**

The proof correctly obtains injectivity in scale, the action law, continuity through the inverse of the strictly monotone transmittance, and absence of nonzero fixed points. The infimum and supremum arguments in Proposition 6.6 correctly use the inverse action as well as monotonicity; they do not require an unproved continuity assertion.

The explanatory statement on p. 29 that clause (4) is the only use of (ND) in the section is nevertheless **false**. Clause (1) expressly invokes it; clause (3) uses it through strict transmittance; Lemma 6.2 uses it too.

**Lemma 7.1 — pp. 32–35: all three directions are supportable.**

The forward dilation calculation includes the necessary Lévy-integrability domination. In the reverse direction, uniqueness is applied to two **positive** Lévy representations, so signed uniqueness is not being smuggled in. The log-coordinate difference-quotient construction successfully produces the monotone density.

The proof also addresses the logarithmic-moment condition needed for the background measure. In particular, the direction from \(B=\omega F'\) uses finiteness of \(F(1)\) and the logarithmic growth of \(\operatorname{Cin}\); it does not incorrectly assume that the Lévy condition alone supplies the logarithmic moment.

Two details should be made explicit. First, the difference-quotient supremum is initially extended-valued; its interval integrals and monotonicity show it is finite everywhere. Second, define \(B(0)=0\) separately. Writing \(0F'(0)\) is not a mathematical definition when \(F'(0)\) may not exist, as the Cauchy example shows.

**Theorem 7.3 and Corollary 7.4 — pp. 35–37: no substantive defect found.**

The construction has the required Lévy data before Bochner is applied. Nondegeneracy follows from the dilation-invariance lemma. The collapsing-increment estimate is sufficient for strong operator continuity; the endpoint comparison is compressed but repairable by writing the short contraction estimate. Gauge uniqueness uses precisely the nontriviality needed to rule out a nontrivial dilation fixing \(F\).

The semigroup reduction and quadratic-growth proof of \(\alpha\le2\) are valid. The normalization used there should be explained as a choice of units, not as an additional property of every original parametrization.

**Proposition 7.8 — pp. 38–39: the hypotheses and proof check out.**

Monotonicity is correctly obtained by evaluating a Lévy increment at frequency one. The strictness argument handles \(s=0\) separately and, for \(s>0\), uses a finite tail integral to eliminate a dilation-invariant nonzero profile. The almost-everywhere equality is used legitimately. Neither absolute continuity nor Yamazato’s theorem is needed here.

**Proposition 7.9 — p. 40: the classical hypotheses are satisfied, but the final sentence of its proof is inadequate.**

The factor law required for self-decomposability is indeed \(\mu_{t',t}\), where \(\chi(t')=\chi(t)/b\), \(b>1\). Surjectivity and monotonicity of the gauge give \(0<t'<t\). Nontriviality together with symmetry excludes every point mass, which is the relevant nondegeneracy condition in dimension one. The applications of absolute continuity and class-\(L\) unimodality are therefore legitimate. Sato’s own account corroborates these regularity results. [Sato, *Selfdecomposable distributions and related topics*](https://ksato.jp/pdf/kenitisato.pdf)

However, “a second mode at \(-m\)” is not a contradiction to unimodality: a flat modal interval is permitted. Conclude that zero is a mode by symmetry and the convex/concave distribution-function characterization, or explicitly choose an even unimodal density version. The proposition’s conclusion remains true.

### 3.3. Further errors and smaller gaps

- **Page 9, Proposition 2.7:** the passage from compact Stone–Weierstrass approximation to equality of integrals over the whole line skips control of approximants outside the compact set. Add a uniform boundedness argument or use a measure-determining/monotone-class theorem. The uniqueness result itself is correct.

- **Page 22, Lemma 4.1:** \(y\mapsto f(y)T_yg\) is not generally continuous when \(f\in L^1\); it is strongly measurable and integrable. Continuity belongs to \(y\mapsto T_yg\). The representation proof otherwise works.

- **Pages 17–18 and 43–44:** the advertised “direct” preliminary verification of the second example invokes Theorem 7.3, and Proposition A.3(2) invokes it again. This is not necessarily a logical circle, since the main theorem does not require the example, but the claimed independence is absent. Give the increment profile
  \[
  2\gamma\bigl(e^{-x/t}-e^{-x/s}\bigr)
  \]
  directly, with the evident convention at \(s=0\).

- **Page 19, Figure 3 caption:** the plotted Gaussian is described as having variance four, but its decay is written \(e^{-x^2/4}\). The correct exponential factor is \(e^{-x^2/8}\).

- **Page 35, Remark 7.2:** “not stationary increments” must be “not necessarily stationary increments”; the Cauchy member \(F(\omega)=|\omega|\) has stationary increments in the canonical gauge.

- **Page 35, Remark 7.2:** \(a\) is not the variance rate in canonical scale. The continuous Gaussian component has variance \(2at^2\), hence variance rate \(4at\).

- **Pages 37–38, Remark 7.5:** the Gaussian contribution to an increment has variance \(2a(t^2-s^2)\), not \(2at^2\) for “every kernel.”

- **Page 38, Lemma 7.6:** the nondegenerate admissible class in Theorem 7.3 excludes \(F=0\), so it is not literally closed under multiplication by zero. State that adjoining the zero exponent produces the convex cone.

- **Page 43, Lemma A.1:** the explanation that Tonelli “needs no \(\sigma\)-finiteness” because the tail measure can have infinite mass near zero confuses infinite mass with failure of \(\sigma\)-finiteness. The actual measure is \(\sigma\)-finite: its tails away from zero are finite. Invoke that fact.

- **Pages 10 and 12–13:** the contrast claiming unrestricted pointwise closure on the half-line needs qualification. For example, \(e^{-ns}\) converges to zero for \(s>0\), retaining value one at zero, and does not converge to a probability Laplace transform. Likewise \(1-e^{-ns}\) leaves the normalized class vanishing continuously at zero. Closure on \((0,\infty)\) is not the same assertion as closure of normalized exponents on \([0,\infty)\).

- **Pages 14–15 and 17:** reflection alone does not exclude the identity family; (ND) does. Calling the Gaussian “the degenerate member” on p. 17 also conflicts with the probabilistic use of “nondegenerate” and with Figure 5. A jump-free Gaussian is nondegenerate when its variance is positive.

## 4. The trust base

The detailed disclosures on pp. 4–6 are useful: they identify admitted analytic interfaces, acknowledge that folding is included in an admitted statement, describe the extra density-version assertions accompanying regularity, and name the unformalized signed construction and closed-form identification. I see no basis for alleging deliberate concealment. Nevertheless, the account is **not consistently clear, complete or accurate**.

The five rows of Table 1 require the following assessment:

| Cited fact | Assessment of its use |
|---|---|
| Bochner’s theorem | The construction uses continuous, normalized, real/even positive definite functions, so the intended applications are legitimate. The abbreviated interface on pp. 4 and 9 omits the symmetry hypothesis and is false as written. |
| Symmetric Lévy–Khintchine converse and uniqueness | The main applications have nonnegative Gaussian coefficients and positive measures satisfying the Lévy condition. Lemma 7.1’s uniqueness argument is legitimate. The folding explanation, however, uses an undefined uncompensated sine integral. |
| Absolute continuity of nondegenerate class-\(L\) laws | Correctly applied to \(\mu_{0,t}\), \(t>0\), in dimension one. It does not establish absolute continuity of general increments. |
| Yamazato’s unimodality theorem | Correctly applied to the origin laws. The symmetric density-version conclusion needs the short argument discussed above; its inclusion in the admitted interface is disclosed. |
| Moment criterion for infinitely divisible laws | Applicable to the variance-gamma member: the Lévy density has exponential tails, so every required polynomial tail integral is finite. No missing moment hypothesis was found. |

**Table 1’s caption is wrong literally.** It says every other result of §§2–7 and the appendix rests on Lean core alone. Results using the listed interfaces indirectly do not. Moreover, the table is not a list of “every cited fact of the paper”: Schoenberg’s equivalence, the existence and closure clauses of the toolbox, Proposition 2.13, and the variance-gamma closed form are cited but absent. Some are orientation-only and need not be admitted into the formal development; that distinction needs its own column or separate list.

**The number of unverified parts changes between sections.** Pages 5–6 identify two substantive exceptions, while pp. 3 and 41 call the signed construction “the one step” not machine-checked. Page 21 additionally discusses an unformalized signed-uniqueness argument, and p. 26 labels sharper estimates unverified. Distinguish substantive results from ancillary remarks, and use one consistent account.

**The appendix’s coverage is ambiguous.** Page 42 says both computations are machine-checked on Lean core, while pp. 5 and 17 describe the all-moment verification as using an admitted criterion. Page 44 distinguishes another route and its inability to reach the general even-moment formula. A declaration-by-declaration account should identify exactly which moment statements and which proofs are covered.

**Verification of a formal statement does not certify the surrounding English or its identification with that statement.** The discrepancies in Lemma 4.2 and the unrestricted regularity claims demonstrate why this distinction matters. The statement on p. 41 that the printed proofs are the verified ones needs qualification wherever the PDF itself identifies a different route or an unformalized argument.

For acceptance, supply a fixed repository revision corresponding to this PDF, the exact admitted declarations with all types and hypotheses, the axiom output for the principal theorem, and a mapping between printed claims and formal declarations. Existing Mathlib theorems such as Prokhorov need not be counted as additional admitted analytic assumptions merely because they are classical results.

## 5. Novelty and relation to prior work

**Pauwels et al. are partly represented accurately, but the “one changed axiom” narrative is not.** Their extended family and the exclusion of positivity for indices above two are correctly identified. Their original assumptions also include integrable, continuous kernels, and their discussion of recursivity expressly motivates an additive amount of blurring. Describing that assumption as “tacit” overstates what has been uncovered. The precise change here is from scale-homogeneous increments to an evolution family. [Pauwels et al., §§II.B–D and the remarks following Proposition 1](https://dev.ipol.im/~reyotero/bib/bib_all/1995_Pauwels_VanGool_extended_scale_space_PAMI.pdf)

“Interchangeability” should be replaced or defined immediately. Commutativity survives the proposed weakening:
\[
(\mu_{s,t}*\cdot)(\mu_{u,v}*\cdot)
=(\mu_{u,v}*\cdot)(\mu_{s,t}*\cdot).
\]
What is dropped is invariance under translating both scale endpoints, in a selected additive coordinate.

**The Iijima summary on p. 3 is mathematically inadequate.** Linearity, translation invariance, scale covariance, a semigroup and positivity do not by themselves force a Gaussian; the Cauchy/Poisson semigroup is a counterexample. The missing regularity or other restrictive assumptions must be identified rather than compressed out of the historical summary. Felsberg and Sommer explicitly discuss the Poisson counterexample and an implicit regularity assumption in the Gaussian uniqueness argument. That directly relevant discussion is missing. [Felsberg and Sommer, §2.1, author manuscript p. 7](https://citeseerx.ist.psu.edu/document?doi=fd52bf1ef33b150de7cd38abb9014d050c27056c&repid=rep1&type=pdf)

The broad attribution of non-creation and non-enhancement approaches to Koenderink and Lindeberg is reasonable. However, p. 41 should not merge all Gaussian axiomatics into one scheme in which the semigroup is retained and a structure condition added. The systems have different hypotheses and regularity assumptions. [Lindeberg’s account of the distinct derivations](https://link.springer.com/article/10.1007/s00422-013-0569-z)

**The principal probability classification is classical.** The manuscript acknowledges this on p. 3, but it should give the closest original source directly: Sato’s 1991 paper establishes the correspondence between self-decomposable laws and self-similar processes with independent increments, including the converse construction, in \(\mathbb R^d\). The present contribution must be located in deriving that setting from the measurement operators and in the formal treatment, rather than in discovering the class or its process interpretation. [Sato, *Self-similar processes with independent increments*](https://link.springer.com/article/10.1007/BF01198788)

Sato and Steutel–van Harn are appropriate general references for the monotone Lévy-density characterization. Proving that characterization afresh, as Lemma 7.1 does, is useful for controlling the formal trust base; it does not make the characterization new.

The Gaussian/jump interpretation of the Lévy pair is also standard. Its interpretation as aperture displacement is an imaging interpretation, not a new probabilistic decomposition. Likewise, the symbol \(B=\omega F'\) and its logarithmic-moment condition belong to the background-driving Lévy-process theory. The Jurek–Vervaat representation is relevant to §§7 and the generator discussion. [Jurek and Vervaat, 1983](https://link.springer.com/article/10.1007/BF00538800)

**The Bessel comparison needs more precision.** The distinction between composition in the shape parameter and the present range-indexed hemigroup is useful. However, Burgeth, Didas and Weickert already introduce a scaled Bessel family with a separate spatial scale parameter. The new claim should therefore concern the range cascade and its axiomatic placement, not the existence of the scaled kernels. [Burgeth et al., §2.4, p. 89](https://www.mia.uni-saarland.de/Publications/burgeth-dsscv05.pdf)

**The future-work claims need a literature boundary.** Higher-dimensional self-similar additive processes and discrete-scale analogues are not unexplored probability classes. The unresolved task may be the corresponding operator-axiomatic derivation or its formalization. The discrete discussion should acknowledge semi-selfdecomposable laws and semi-selfsimilar processes. [Maejima, *Semi-selfdecomposability and semi-selfsimilarity*](https://www.maphysto.dk/publications/MPS-misc/1999/11.pdf)

Finally, the general self-similarity attribution on p. 3 should distinguish Lamperti’s 1962 *Semi-stable stochastic processes* from the 1972 Markov-process paper currently cited as [18]; Sato’s 1991 paper cites the former for this background.

## 6. Exposition and structure

The paper is substantially longer than the argument requires. Its principal obstacle is repeated explanation of its own architecture, often with changing qualifications.

The most consequential structural problems are these:

- **Load-bearing forward references — pp. 17–21.** The examples are announced as direct checks before the general theory, but use Theorem 7.3. Proposition 3.5’s positivity equivalence also depends on that theorem. Put the signed result after the characterization, or separate its independent construction from its later classification consequence.

- **An undefined operative term — pp. 12, 17–19, 38 and 42.** “Admissible” is used repeatedly without an early standalone definition specifying whether zero is included and whether profiles are identified almost everywhere. This causes the cone/nondegeneracy conflict.

- **Ambiguous kernel terminology — throughout, especially pp. 17, 21, 36 and 40.** Use “origin kernel” for \(\mu_{0,t}\) and “increment kernel” for \(\mu_{s,t}\). This distinction carries mathematical content.

- **An avoidable proof detour — pp. 29–31.** The orbit direction follows immediately from
  \[
  \beta(S_\lambda t)
  =\int e^{-\lambda^2x^2/2}\,\mu_{0,t}(dx).
  \]
  Under (ND), this is strictly decreasing in \(\lambda\); since \(\beta\) is strictly decreasing, \(S_\lambda t\) is strictly increasing. This can replace Lemma 6.5 and the longer orientation contradiction.

- **An appendix containing structural prerequisites — pp. 34–35 and 42–43.** Lemma A.1 supplies the tail measure and asymptotics used in Lemma 7.1. Present the needed facts before that lemma, or split them from the optional discussion of rays.

Material that could be cut or condensed includes the repeated comparisons with the causal article in Remarks 2.16, 3.3, 4.4, 5.5, 6.8 and 7.11; repeated trust-base explanations outside §1.1; the repeated declarations that extremality is outside scope; and much of the methodological narrative on p. 41. A single comparison table and a precise verification ledger would be more effective.

The AI disclosure, pp. 44–46, is unusually detailed. Its essential information—nature of assistance, verification procedure and author responsibility—should remain. Session chronology, word ratios and campaign statistics could move to supplementary material; they do not resolve any mathematical question in the report.

## 7. Required changes

1. **Pp. 19–20:** correct the Gaussian variance in Proposition 3.5’s construction, because the displayed measure does not have the stipulated transform.

2. **P. 23:** separate positivity-free nonvanishing from nonnegative exponents and non-amplification, because the latter conclusions require positive probability kernels.

3. **Pp. 1–3, 17, 21, 36 and 40–41:** restrict density and unimodality claims to origin kernels, because admissible increments can have atoms and fail unimodality.

4. **Pp. 3 and 40–41:** replace the unimodality-based exclusion of truncated Gaussians with a valid nonvanishing or infinite-divisibility argument.

5. **Pp. 2, 6 and 17–19:** state the variance-gamma/Bessel density and restrict the conventional Matérn covariance identification to \(\gamma>\tfrac12\), because the claimed covariance is unbounded at zero otherwise.

6. **Pp. 4 and 8–9:** correct the Bochner hypothesis and the Lévy folding argument, because the former omits symmetry and the latter cancels a potentially undefined integral.

7. **Pp. 1–4, 19 and 41–42:** withdraw the claim that classification without positivity is impossible, because Proposition 3.5 proves no such impossibility.

8. **Pp. 1–2, 13–17 and 41:** rewrite the comparison with Pauwels et al. and define “interchangeability” as scale homogeneity, because commutativity is retained and additional assumptions have changed.

9. **Pp. 3 and 41:** correct the Gaussian-axiomatics summary and address the Poisson counterexample, because the listed assumptions do not select the Gaussian.

10. **Pp. 4–6, 21, 26 and 41–44:** reconcile Table 1, the verification claims and all stated exceptions against a fixed formal-development revision, because the current trust account is internally inconsistent.

11. **Pp. 9, 22, 26, 34–36 and 40:** complete the smaller analytic details identified above, including bounded approximation, strong measurability, finite-mass normalization, profile finiteness, \(B(0)\), endpoint continuity and the modal-interval argument.

12. **Pp. 19, 29, 35 and 37–38:** correct the Gaussian caption, the claimed uses of (ND), stationarity wording, variance factors and the cone’s zero case, because these are false statements even though they do not overturn the main theorem.

13. **Pp. 3–4 and 38–43:** distinguish the new operator/formalization contribution from known probability results and elementary consequences, because the present novelty and scope language gives a misleading impression.

14. **Pp. 10 and 12–13:** qualify the half-line closure comparison, because pointwise convergence need not preserve normalization and continuity at zero.

## Suggestions

1. **Pp. 12 and 17:** introduce a standalone definition of admissible data, including the zero case and the convention for profile representatives, to prevent later ambiguity.

2. **Pp. 17–21:** move Proposition 3.5’s classification-dependent clauses after Theorem 7.3, so readers encounter their prerequisites first.

3. **Pp. 19–21:** strengthen the Gaussian perturbation observation to “positivity forces \(\phi=0\)” for \(\phi\in A(\mathbb R)_{\mathrm{even},0}\), since the existing averaging argument already gives this and makes the special example unnecessary.

4. **Pp. 29–31:** use the spatial Gaussian-window formula to orient the scale action directly, reducing the proof substantially.

5. **Pp. 34–35 and 42–43:** place the required tail-measure and Cin facts before Lemma 7.1, separating them from optional geometric interpretation.

6. **Pp. 38–43:** either add the short step-ray extremality argument or remove repeated references to its being outside scope, since the present repetition obscures its elementary status.

7. **Pp. 12–13, 17, 24, 27, 32 and 40:** consolidate comparisons with the causal article into one table, preserving the substantive distinctions without interrupting each proof.

8. **Pp. 4–6 and 41:** replace repeated verification narratives with one precise claim-to-declaration ledger, which would make the trust boundary easier to audit.

9. **Pp. 44–46:** move the extended production history to supplementary material while retaining the substantive disclosure and responsibility statement.

Reviewed source: :codex-file-citation{path="C:/Users/DAHT/Downloads/spatial-hemigroup-line-09602a3.pdf" purpose="source"}