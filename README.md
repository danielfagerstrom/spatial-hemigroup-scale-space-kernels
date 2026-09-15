# Spatial scale space from hemigroup axioms: characterization of the kernels on the line — release v0.1

This repository is the verification artifact of the article of the same name (the PDF is at the
root). It is an export of the development repository at revision `3f89ab6`, restricted to what
the article's statements rest on; the development repository also holds the material of two
further modules and stays private until they are released.

## What is here

- `Formalization/` — the Lean 4 development: the transitive import closure of every module that a
  numbered statement of the article names (76 modules), with the toolchain pinned in-tree
  (`lean-toolchain`, `lake-manifest.json`). `SpatialLine/` is sorry-free; `Skeleton/` holds the
  typed statements of the nodes the article marks as not machine-checked.
- `Formalization/CIAxiomGuard.lean` — prints the axiom usage of every named declaration.
- `blueprint/trust-boundary.txt`, `blueprint/AXIOMS.md` — the eleven interface names of the full
  development, each with the page-verified citation it rests on and the step it carries beyond its
  source. The article's theorems rest on four of them (section 1.1 of the paper).
- `blueprint/src/parts/` — the statements and proofs of record of the article's sections 2–7, with
  the `\lean{}` tag naming the declaration behind each statement.
- `paper/`, `figures/` — the article's sources.
- `notes/` — the process account, the external reviews verbatim, and the response plan.

## Verifying

    cd Formalization
    lake exe cache get        # Mathlib's prebuilt oleans
    lake build
    lake env lean CIAxiomGuard.lean

The last command prints, for `SpatialLine.main_characterization`, Lean's three logical axioms and
`SpatialLine.fourier_toolbox_bochner_symm`, `SpatialLine.fourier_toolbox_levy_converse`,
`SpatialLine.fourier_toolbox_levy_unique`, and nothing else (the block printed in section 1.1).

## Statements and declarations

| blueprint node (chapter) | declarations |
|---|---|
| `def:positive-definite (02)` | `SpatialLine.IsPositiveDefinite` |
| `def:symmetric-negdef (02)` | `SpatialLine.IsSymNegDef` |
| `prop:fourier-toolbox (02)` | `Skeleton.fourier_toolbox_bochner`, `Skeleton.fourier_toolbox_bochner_symm`, `Skeleton.fourier_toolbox_schoenberg`, `Skeleton.fourier_toolbox_levy_exists`, `Skeleton.fourier_toolbox_levy_converse`, `Skeleton.fourier_toolbox_levy_unique`, `Skeleton.fourier_toolbox_cone`, `Skeleton.fourier_toolbox_kernel_closed`, `Skeleton.fourier_toolbox_closure` |
| `def:levy-exponents (02)` | `SpatialLine.IsSymLevyExponent` |
| `prop:fourier-uniqueness (02)` | `SpatialLine.fourier_uniqueness` |
| `prop:levy-continuity (02)` | `SpatialLine.levy_continuity` |
| `prop:laplace-uniqueness-locally-finite (02)` | `SpatialLine.laplace_uniqueness_locally_finite` |
| `lem:quadratic-growth (02)` | `SpatialLine.SymLevyPair.quadratic_growth`, `SpatialLine.SymLevyPair.quadratic_growth_isBigO` |
| `lem:lattice-zero (02)` | `SpatialLine.lattice_zero_isClosedSubgroup`, `SpatialLine.lattice_zero_trichotomy`, `SpatialLine.lattice_zero_eq_univ_iff`, `SpatialLine.lattice_zero_mem_iff`, `SpatialLine.lattice_zero_exponent`, `SpatialLine.lattice_zero_example_mem`, `SpatialLine.lattice_zero_example_lattice` |
| `def:self-decomposable (02)` | `SpatialLine.IsSelfDecomposable` |
| `prop:sd-exponents (02)` | `Skeleton.sd_exponents` |
| `lem:profile-integrability (02)` | `SpatialLine.profile_integrability`, `SpatialLine.profile_integrability_mem` |
| `def:cascade-family (03)` | `SpatialLine.PreCascadeCore`, `SpatialLine.IsPositive`, `SpatialLine.IsNondegenerate`, `SpatialLine.CascadeCore`, `SpatialLine.IsScaleCovariant`, `SpatialLine.CascadeFamily` |
| `prop:two-members (03)` | `SpatialLine.two_members_gaussian`, `SpatialLine.two_members_matern`, `SpatialLine.two_members_matern_moments` |
| `prop:no-positivity-no-classification (03)` | `Skeleton.no_positivity_no_classification`, `Skeleton.no_positivity_family`, `SpatialLine.no_positivity_classification`, `SpatialLine.no_positivity_example` |
| `lem:convolution-representation (04)` | `SpatialLine.representation_existsUnique`, `SpatialLine.representation_symmetric`, `SpatialLine.representation_converse` |
| `lem:nonvanishing (04)` | `SpatialLine.nonvanishing`, `SpatialLine.nonvanishing_exponent` |
| `lem:additivity (05)` | `SpatialLine.additivity` |
| `thm:increments-levy (05)` | `SpatialLine.increments_levy`, `SpatialLine.increments_levy_id_measure`, `SpatialLine.increments_levy_infinitely_divisible` |
| `cor:monotonicity (05)` | `SpatialLine.monotonicity_zero_set`, `SpatialLine.monotonicity_strict` |
| `cor:smoothed-transmittance (05)` | `SpatialLine.smoothed_transmittance`, `SpatialLine.smoothed_transmittance_strictAnti` |
| `lem:covariance-fourier (06)` | `SpatialLine.covariance_fourier`, `SpatialLine.covariance_similarity` |
| `lem:no-lattice (06)` | `SpatialLine.no_lattice` |
| `lem:dilation-invariance (06)` | `SpatialLine.dilation_invariance` |
| `lem:action-rigidity (06)` | `SpatialLine.action_rigidity_injective`, `SpatialLine.action_rigidity_group`, `SpatialLine.action_rigidity_continuous`, `SpatialLine.action_rigidity_no_fixed_point` |
| `lem:dilation-atom (06)` | `SpatialLine.dilation_atom` |
| `prop:canonical-gauge (06)` | `SpatialLine.canonical_gauge_orbit`, `SpatialLine.canonical_gauge` |
| `lem:selfdecomposable-exponents (07)` | `SpatialLine.sd_exponents_three_implies_one`, `SpatialLine.sd_exponents_one_implies_three`, `SpatialLine.sd_exponents_three_implies_two`, `SpatialLine.sd_exponents_two_implies_three`, `SpatialLine.sd_exponents_profile_measure`, `SpatialLine.sd_exponents_symbol` |
| `thm:main-characterization (07)` | `SpatialLine.main_characterization`, `SpatialLine.main_construction`, `SpatialLine.main_analysis_exists`, `SpatialLine.main_analysis`, `SpatialLine.main_uniqueness` |
| `cor:semigroup-case (07)` | `SpatialLine.semigroup_case`, `SpatialLine.semigroup_case_profile`, `SpatialLine.semigroup_case_gaussian` |
| `lem:admissible-cone (07)` | `SpatialLine.admissible_cone` |
| `prop:strict-positivity (07)` | `SpatialLine.strict_positivity_monotone`, `SpatialLine.strict_positivity_strict`, `SpatialLine.strict_positivity_consequences` |
| `prop:kernel-regularity (07)` | `SpatialLine.kernel_regularity_law`, `SpatialLine.kernel_regularity` |
| `lem:cin-rays (08)` | `SpatialLine.cin_ray`, `SpatialLine.cin_elementary`, `SpatialLine.cin_expansion_zero`, `SpatialLine.cin_expansion_top`, `SpatialLine.cin_superposition`, `SpatialLine.cin_superposition_exists` |
| `prop:matern-exponent (10)` | `SpatialLine.matern_exponent`, `SpatialLine.matern_transforms`, `SpatialLine.matern_moments`, `SpatialLine.matern_gamma_mixture` |

## Licence

Lean sources under Apache 2.0, text under CC BY 4.0 (`LICENSES/`).
