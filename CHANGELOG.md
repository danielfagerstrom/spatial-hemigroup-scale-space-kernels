# Changelog

All releases of this module are recorded here, newest first, with what changed and why, and in
particular which statements were renumbered, strengthened, weakened or withdrawn (hub `RELEASES.md`,
rule 2).

## v0.1 — 2026-09-14 — first release: the characterization on the line

The article *Spatial scale space from hemigroup axioms: characterization of the kernels on the
line*, sections 1–8 with Appendix A, 49 pages, on the model of the causal article. What it
contains: the axioms of Pauwels et al. 1995 with the semigroup weakened to a two-parameter
hemigroup, that is, with the stationarity of the increments in the scale parameter dropped; the
convolution representation, the cascade (each increment infinitely divisible, the kernels from the
origin self-decomposable), scale covariance in similarity form with the canonical gauge, and the
characterization theorem: the admissible families are exactly the symmetric self-decomposable
laws, each determined by a Gaussian coefficient and a nonincreasing displacement profile, with the
gauge and the exponent unique up to one normalization. The semigroup case is recovered as the
symmetric stable family with α ≤ 2; positivity is shown to be the narrowing axiom; the kernels
from the origin are absolutely continuous and unimodal. Thirty-three numbered statements are the
blueprint's verbatim; every one of them is machine-checked in Lean 4 except the signed
construction of Proposition 3.6's first clause, and the characterization rests on Lean core plus
two cited analytic facts (Bochner's theorem forward, the symmetric Lévy–Khintchine representation
at its converse and uniqueness clauses), the regularity of the kernels on two more.

What is deferred, stated as open in section 8 and promised nowhere: the geometry of the admissible
cone, the subordination bridge and the corner families (module B), and the selection of the
Gaussian by locality and non-creation (module C), both in the development repository (ADR-0004).

The release form (ADR-0005): the development repository, `spatial-hemigroup-scale-space`, stays
private while it holds modules B and C; the release is the verification export at
`https://github.com/danielfagerstrom/spatial-hemigroup-scale-space-kernels`, written by the
development repository's `scripts/export-release.py` — the Lean modules the statements rest on
(76 of 149), the trust boundary and the ledger, blueprint chapters 2–7, the paper and the PDF, the
process account, both external review rounds verbatim and the response plan. The export builds
from scratch and its guard reproduces the `#print axioms` block printed in section 1.1.

Release commit: *to be filled at tagging*. Version DOI: *to be recorded at the Zenodo deposit*.
The development log of everything before this release follows.
