/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Family

/-!
# The cone's coordinates, defined: `Cin`, the Choquet measure, and the symbol

Blueprint: `blueprint/src/parts/08-cone.tex` — `lem:cin-rays`, `prop:choquet-cone` — and
`eq:symbol` in Chapter 7, whose right-hand side is `symbolL` below. Nothing here is a blueprint
node; these are the objects Chapters 7, 8 and 11–13 quantify over.

**Definitions only.** The file carries no theorem, and it is the lowest module of the cone's
material on purpose: Chapter 7's `lem:selfdecomposable-exponents` reads `symbolL`,
`HasProfileTail` and `incrementProfile`, so the release export of the characterization theorem
(ADR-0005) reaches this file and must not, through it, reach the proofs of Chapters 8–13. It was
called `SpatialLine.Cone` until 2026-09-14.

## `cin`

`Cin(z) = ∫₀^z (1 - cos v)\,dv/v`, the Fourier-side twin of Paper I's `Ein`. It is written as an
`intervalIntegral` for the same reason `Hemigroup.ein` is: the integrand is continuous off the
origin and extends continuously by `0`, so no measure-theoretic side condition is needed and the
substitution `u = τ z` is `intervalIntegral.integral_comp_mul_left`.

**The even extension is automatic**, which the blueprint's "extended evenly to `ℝ`" reads as a
separate stipulation. The integrand `v ↦ (1 - cos v)/v` is *odd*, and for an odd integrand
`∫₀^{-a} = ∫₀^{a}`; so `cin` as written is already even and `lem:cin-rays`(1)'s evenness clause
is a lemma about this definition rather than part of it.

twin: `Hemigroup.ein`, with `1 - e^{-u}` replaced by `1 - cos u`. The two differ in one way that
matters downstream: `einIntegrand` is bounded by `1` and `cin`'s integrand is not monotone, so
the growth clauses of `lem:cin-rays`(1) have no causal counterpart.

## The Choquet measure as a specification

`HasProfileTail k ϖ` is `lem:cin-rays`(2)'s `ϖ` — a measure carried by `(0,∞)` whose tails are
the profile — as a **specification**, exactly as Paper I's `HasLevyTail` is, and for the same
two reasons. A profile that is only `AntitoneOn (Ioi 0)` has no right-continuous representative
this development can name, so the tail identity holds at the continuity points of `k`, which is
almost every `x`; and `lem:cin-rays`(2) itself says "for almost every `x > 0`", so the
almost-everywhere reading is the blueprint's own. Every use of a tail below sits under an
integral in `x`.

Phase A diverged from this at first — `Skeleton.sd_exponents_symbol` and
`Skeleton.sd_exponents_profile_measure` stated the tail identity **everywhere**, and
`x ↦ ϖ((x,∞))` is right-continuous while an `SDProfile`'s `k` need not be, so the everywhere
form was a genuinely stronger hypothesis that some admissible profiles cannot meet. The review of
2026-09-09 removed the divergence (R2, R24): `sd_exponents_symbol` takes `HasProfileTail`, and
`sd_exponents_profile_measure` produces its right-continuous `k` with the tail identity in the
`ENNReal.ofReal` form used here. See SKELETON.md, finding F11 and § 5.

## The symbol

`symbolL a ϖ` is `B(ω) = 2a\omega^2 + ∫(1 - \cos\omega v)\,\varpi(dv)`, the right-hand side of
`eq:symbol` — a symmetric Lévy exponent with Gaussian coefficient `2a` and Lévy measure `ϖ`. It
is `ℝ≥0∞`-valued first, as `SymLevyPair.exponentL` is, so that the identity of `eq:symbol` needs
no finiteness side condition; the real-valued `symbol` is its `toReal`. Chapters 11, 12 and 13
are stated in terms of it, which is what keeps `deriv F` out of their hypotheses.
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## `Cin` -/

/-- The integrand of `cin`: `v ↦ (1 - cos v)/v`, odd, and continuous off the origin.

twin: `Hemigroup.einIntegrand`. -/
noncomputable def cinIntegrand (v : ℝ) : ℝ := (1 - Real.cos v) / v

/-- **`Cin(z) = ∫₀^z (1 - cos v)\,dv/v`.**

Even without stipulation, the integrand being odd; see the module docstring.

twin: `Hemigroup.ein`. -/
noncomputable def cin (z : ℝ) : ℝ := ∫ v in (0 : ℝ)..z, cinIntegrand v

lemma cin_apply (z : ℝ) : cin z = ∫ v in (0 : ℝ)..z, cinIntegrand v := rfl

/-- The profile of the `Cin` ray of step `τ`: `k = 1_{(0,τ)}`.

Written as an indicator of the *open* interval so that `k 0 = 0` — `SDProfile`'s normalisation —
holds on the nose. -/
noncomputable def cinProfile (τ : ℝ) : ℝ → ℝ := Set.indicator (Ioo (0 : ℝ) τ) 1

/-! ## The Choquet measure -/

/-- **`ϖ = -dk`**, as a specification: a measure carried by `(0,∞)` whose tails are the profile
`k` at almost every positive point.

twin: `Hemigroup.SelfDecomposableExponent.HasLevyTail`, with the `ae` reading and its reasons
unchanged. -/
def HasProfileTail (k : ℝ → ℝ) (ϖ : Measure ℝ) : Prop :=
  IsFolded ϖ ∧ ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ϖ (Ioi x) = ENNReal.ofReal (k x)

/-- **`eq:cone-superposition`'s right-hand side**, `ℝ≥0∞`-valued: the superposition map
`(a,ϖ) ↦ aω² + ∫ Cin(τω)ϖ(dτ)` of `prop:choquet-cone`.

Naming the map is what lets `prop:choquet-cone`'s bijectivity, linearity and domain clauses be
stated about one object instead of five copies of one display. -/
noncomputable def cinSuperpositionL (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (a * ω ^ 2) + ∫⁻ τ, ENNReal.ofReal (cin (τ * ω)) ∂ϖ

/-- The real-valued superposition map. -/
noncomputable def cinSuperposition (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : ℝ :=
  (cinSuperpositionL a ϖ ω).toReal

/-- The folded profile of a dilation increment, `h_{s,t}(x) = k(x/t) - k(x/s)`
(`eq:dilation-difference`). Nonnegative because `k` is nonincreasing, and **not** itself
nonincreasing --- the trap `lem:profile-integrability` is stated to avoid.

twin: `Hemigroup.SelfDecomposableExponent.incrementDensity`, verbatim. -/
noncomputable def incrementProfile (k : ℝ → ℝ) (s t : ℝ) : ℝ → ℝ :=
  fun x => k (x / t) - k (x / s)

/-! ## The symbol `B = ω F'(ω)` -/

/-- **`eq:symbol`'s right-hand side**, `ℝ≥0∞`-valued:
`B(ω) = 2a\omega^2 + ∫(1 - \cos\omega v)\,\varpi(dv)`.

This is `SymLevyPair.exponentL` of the pair `(2a, ϖ)` written out, and it is deliberately not
*defined* as that pair: `SymLevyPair` carries the integrability field, which is a conclusion of
`lem:selfdecomposable-exponents` here and not something a definition may assume. -/
noncomputable def symbolL (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * a * ω ^ 2) + ∫⁻ v, ENNReal.ofReal (1 - Real.cos (ω * v)) ∂ϖ

/-- The real-valued symbol. -/
noncomputable def symbol (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : ℝ := (symbolL a ϖ ω).toReal

lemma symbol_apply (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) :
    symbol a ϖ ω = (symbolL a ϖ ω).toReal := rfl

end SpatialLine
