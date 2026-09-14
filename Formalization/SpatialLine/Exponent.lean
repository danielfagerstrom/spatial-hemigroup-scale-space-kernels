/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Transform

/-!
# The function classes: positive definiteness, `NDₛ`, `LEₛ`, and the self-decomposable profile

Blueprint: `blueprint/src/parts/02-preliminaries.tex` — `def:positive-definite` (2.1),
`def:symmetric-negdef` (2.2), the representation (2.2)/`eq:levy-khintchine`, and the profile
form (2.5)/`eq:sd-profile`.

## Representation first

`prop:fourier-toolbox`'s status annotation says it: "The classes `NDₛ` and `LEₛ` are the same
class, named by the definition and by the representation respectively; this article's proofs
manipulate the representation, and the machine-checked development is expected to define `LEₛ`
alone." Both are defined here, because `def:positive-definite` and `def:symmetric-negdef` are
blueprint nodes and a node needs a faithful Lean twin; but `SymLevyPair` is the object every
later chapter works with, and `prop:fourier-toolbox`(3) is the only place the two meet.

This is Paper I's rule (`def:bernstein-function` ⇄ `Hemigroup.levyExponent`) with the Laplace
side replaced by the Fourier side.

## Two `ℝ≥0∞`-first definitions

`SymLevyPair.exponentL` and `SDProfile.exponentL` are `lintegral`s, so they need no
integrability side condition and the elementary facts about them are unconditional; the
real-valued versions are `.toReal` of those. Finiteness is not a field of either structure: it
is `lem:quadratic-growth`, a node, and stating it that way is what keeps the structures free of
a condition whose proof the blueprint owns.

twin: `Hemigroup.levyExponent` / `Hemigroup.levyExponentD` (the same design, opposite transform).

## The profile structure and the bridge

`SDProfile`'s fields are laid out to be field-for-field parallel with Paper I's
`Hemigroup.SelfDecomposableExponent` — `b₀ ↦ a`, then `k`, `b₀_nonneg ↦ a_nonneg`, `k_nonneg`,
`k_antitone`, `k_zero` — so that the bridge map of `lem:bridge-exponents` (blueprint (9.1)–(9.2),
phase B) is a function between two structures with parallel fields and no reshaping. The one
deliberate divergence is the last field: Paper I carries a single finiteness condition
`ne_top`, this structure carries the *two* integrability conditions the blueprint states in
`lem:profile-integrability`, because those are what every family in this article is tested
against. `lem:profile-integrability` is the node that relates the two.

`k_zero` is a normalisation, not a constraint, exactly as in Paper I: `k` is a density against
`dx/x` on `(0,∞)` and every other field leaves `k 0` free.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal ComplexOrder

/-! ## `def:positive-definite` and `def:symmetric-negdef` -/

/-- **`def:positive-definite`.** `∑_{j,k} c_j conj(c_k) φ(ω_j - ω_k) ≥ 0` for every finite
family.

Reading: the double sum is asserted to be a *nonnegative real*, which is what `0 ≤ z` means for
`z : ℂ` under `ComplexOrder` (`0 ≤ z.re` and `z.im = 0`). The blueprint writes `≥ 0` of a
complex expression and means exactly that; Hermitian symmetry of `φ` is thereby part of the
assertion rather than a separate consequence, which is the standard convention. Finite families
are indexed by `Fin n`, which loses nothing. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * φ (ω j - ω k)

/-- Negative definiteness **in the kernel sense**, the right-hand side of
`prop:fourier-toolbox`(2).

Not a blueprint node of its own: it is the vocabulary clause (2) is stated in, and the only
place this article ever mentions it. Note that no constraint `∑ c_j = 0` appears — the blueprint
writes the kernel form with the compensating terms `ψ(ω_j) + ψ(ω_k)`, which is the
unconstrained form of the definition. -/
def IsNegDefKernel (ψ : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ j, ∑ k, ((ψ (ω j) + ψ (ω k) - ψ (ω j - ω k) : ℝ) : ℂ) * (c j * (starRingEnd ℂ) (c k))

/-- **`def:symmetric-negdef`**, the class `NDₛ`: continuous, even, nonnegative, vanishing at the
origin, with `e^{-τψ}` positive definite for every `τ > 0`.

The exponential form is primitive, as the blueprint's status annotation insists, so that the
class is defined with no derivative and Schoenberg's theorem (`prop:fourier-toolbox`(2)) is
needed only to import results stated for the kernel form.

twin: `Hemigroup.levyExponent`'s defining node `def:bernstein-function` — same structural role,
opposite defining device. -/
structure IsSymNegDef (ψ : ℝ → ℝ) : Prop where
  /-- `ψ` is continuous. -/
  continuous : Continuous ψ
  /-- `ψ` is even. -/
  even : ∀ ω, ψ (-ω) = ψ ω
  /-- `ψ` takes values in `[0,∞)`. -/
  nonneg : ∀ ω, 0 ≤ ψ ω
  /-- `ψ(0) = 0`. -/
  map_zero : ψ 0 = 0
  /-- `e^{-τψ}` is positive definite for every `τ > 0`. -/
  exp_posDef : ∀ τ : ℝ, 0 < τ → IsPositiveDefinite fun ω => (Real.exp (-(τ * ψ ω)) : ℂ)

/-! ## `LEₛ`: the symmetric Lévy–Khintchine form (2.2) -/

/-- **The data of the symmetric Lévy–Khintchine representation `eq:levy-khintchine`**: a Gaussian
coefficient `a ≥ 0` and a folded Lévy measure `ν` on `(0,∞)` with `∫ (1 ∧ x²) ν(dx) < ∞`.

The blueprint's `ν` lives on `(0,∞)`; here it is a measure on `ℝ` carrying `IsFolded`, so that
dilation (pushforward along `x ↦ c x`) and the folding convention stay expressible in the
ambient space. `σ`-finiteness of `ν` on `(0,∞)` is a consequence of `ν_integrable`, not a
field. -/
structure SymLevyPair where
  /-- The Gaussian coefficient `a`. -/
  a : ℝ
  /-- The folded Lévy measure `ν`, carried by `(0,∞)`. -/
  ν : Measure ℝ
  a_nonneg : 0 ≤ a
  ν_folded : IsFolded ν
  ν_integrable : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν ≠ ⊤

namespace SymLevyPair

/-- **`eq:levy-khintchine`**, `ℝ≥0∞`-valued: `a ω² + ∫ (1 - cos ωx) ν(dx)`. -/
noncomputable def exponentL (P : SymLevyPair) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.a * ω ^ 2) + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν

/-- The real-valued exponent. Equal to `exponentL` under `lem:quadratic-growth`, which is the
only regime this article uses. -/
noncomputable def exponent (P : SymLevyPair) (ω : ℝ) : ℝ := (P.exponentL ω).toReal

end SymLevyPair

/-- **The class `LEₛ`**: the functions of the form `eq:levy-khintchine`.

`prop:fourier-toolbox`(3) is the statement that `LEₛ = NDₛ`; this article's proofs manipulate
`LEₛ`, and `NDₛ` appears only where the blueprint's text does. -/
def IsSymLevyExponent (ψ : ℝ → ℝ) : Prop := ∃ P : SymLevyPair, ∀ ω, ψ ω = P.exponent ω

/-! ## Self-decomposability and the profile form (2.5) -/

/-- **`def:self-decomposable`.** For every `b > 1` the law factors as `μ̂(ω) = μ̂(ω/b) ρ̂_b(ω)`.

Reading: the transform form is the one formalised. The blueprint's "equivalently `X =d cX + R_c`
with `R_c` independent of `X`" is the same statement read through the transform of a sum of
independent variables, and formalising the random-variable form would add a probability space
this development never otherwise needs. `charFun` is Mathlib's complex transform, with the
opposite sign convention to (2.1); the factorisation is insensitive to it.

The class is defined for an arbitrary probability measure on `ℝ`, not only a symmetric one, as
the blueprint defines it. -/
def IsSelfDecomposable (μ : Measure ℝ) : Prop :=
  ∀ b : ℝ, 1 < b → ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
    ∀ ω : ℝ, charFun μ ω = charFun μ (ω / b) * charFun ρ ω

/-- The Lévy measure of a profile: density `k(x)/x` against Lebesgue measure on `(0,∞)`.

twin: `Hemigroup.levyMeasureOfDensity`, verbatim. -/
noncomputable def profileMeasure (k : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal (k x / x)

/-- **The data of `eq:sd-profile`**: a Gaussian coefficient `a ≥ 0` and a nonincreasing profile
`k ≥ 0` on `(0,∞)` satisfying the two integrability conditions of `lem:profile-integrability`.

The pair `(a, k)` is what `thm:main-characterization` says the axioms leave free: a jitter
variance and a nonincreasing displacement profile.

twin: `Hemigroup.SelfDecomposableExponent`, field for field — see the module docstring for the
one deliberate divergence in the last field. -/
structure SDProfile where
  /-- The Gaussian coefficient `a`; the slot the causal drift `b₀` occupies. -/
  a : ℝ
  /-- The folded profile `k`, a density against `dx/x` on `(0,∞)`. -/
  k : ℝ → ℝ
  a_nonneg : 0 ≤ a
  k_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  /-- A normalisation, not a constraint (Paper I's `k_zero`): every other field leaves `k 0`
  free, and fixing it to `0` makes the lower endpoint `s = 0` a special case of the general
  formula rather than a separate definition. -/
  k_zero : k 0 = 0
  /-- `∫₀¹ x k(x) dx < ∞`, the first half of `lem:profile-integrability`. -/
  integrable_near_zero : ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x) ≠ ⊤
  /-- `∫₁^∞ k(x)/x dx < ∞`, the second half. -/
  integrable_at_top : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x) ≠ ⊤

namespace SDProfile

/-- **`eq:sd-profile`**, `ℝ≥0∞`-valued: `a ω² + ∫₀^∞ (1 - cos ωx) k(x) dx/x`. -/
noncomputable def exponentL (P : SDProfile) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.a * ω ^ 2)
    + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)

/-- The real-valued exponent of `eq:sd-profile`. -/
noncomputable def exponent (P : SDProfile) (ω : ℝ) : ℝ := (P.exponentL ω).toReal

/-- The Lévy measure attached to the profile. -/
noncomputable def levyMeasure (P : SDProfile) : Measure ℝ := profileMeasure P.k

end SDProfile

/-- **The admissible exponents** of `thm:main-characterization`: the functions of the form
`eq:sd-profile`.

This is the class the main theorem's `F` ranges over, the cone of `lem:admissible-cone`, and
the hypothesis of `prop:strict-positivity`. -/
def IsAdmissibleExponent (F : ℝ → ℝ) : Prop := ∃ P : SDProfile, ∀ ω, F ω = P.exponent ω

end SpatialLine
