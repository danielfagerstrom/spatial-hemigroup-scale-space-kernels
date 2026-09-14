/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.ConvolutionVariation

/-!
# The measurable hull of a representative, and the ordinary-count reduction

Blueprint: `blueprint/src/parts/13-noncreation.tex`, `prop:polya-frequency`(1). Nothing here is
a blueprint node; the file exists to discharge one step that used to sit *inside* an admitted
axiom.

## What was owed

`signChangesAE g` is the infimum of `signChanges h` over **every** `h =ᵐ[volume] g`, the
definition placing no measurability condition on `h`, so non-measurable representatives compete
in the infimum. Karlin Ch. 5, Thm. 3.1(i) (p. 233) gives `S^-(k * f) \le S^-(f)` for a bounded
Borel `f` and the **ordinary** count. Passing from the second to the first needs that no
representative — in particular no non-measurable one — lowers the right-hand infimum below what
Karlin's inequality controls. Fidelity review row **R14** (2026-09-10) named that step and
recorded it, at ledger **A21** and **A22** and in `SpatialLine/Interfaces.lean`, as believed and
not proved. It is proved here (2026-09-11), and the axiom is narrowed to Karlin's letter in
consequence.

## The lemma, and why it is short

The step reads like a construction of sign intervals for `h`, and it is not one.
`exists_measurable_rep_signChanges_le` takes the *measurable* function `g` and deletes it on a
measurable null superset `N` of the disagreement set:

  `h' := Nᶜ.indicator g`.

Then `h'` is measurable, `h' =ᵐ[volume] g`, and `|h'| \le |g|` pointwise, so `h'` inherits
whichever of integrability or boundedness `g` has. The count is the one line that matters: at
every point where `h'` is nonzero, `h'` agrees with `g`, which off `N` agrees with `h` — so every
alternation of `h'` is an alternation of `h` *at the same points and with the same sign pattern*,
whence `signChanges h' \le signChanges h`. Nothing about the geometry of the sign intervals of
`h` is needed; the useful move is to zero `g` on the bad set rather than to preserve values
there.

What comes out is that the infimum defining `signChangesAE` is already attained along measurable
representatives (`signChangesAE_eq_iInf_measurable`), which is the statement the two counts are
reconciled by.

## The reduction

`isVariationDiminishing_of_ord` turns `IsVariationDiminishingOrd μ` — Karlin's own conclusion,
ordinary counts and measurable test functions — into `IsVariationDiminishing μ`, the
essential-count property the development consumes. The direction is not monotonicity:
`signChangesAE \le signChanges` points the wrong way on the left of the inequality. The chain is

  `S^-_ae(μ * g) = S^-_ae(μ * h') \le S^-(μ * h') \le S^-(h') \le S^-(h)`,

taken at each representative `h` of a measurable `g₀ =ᵐ g` with `h'` its measurable hull, and
then an infimum over `h`. The only hypothesis it needs of `μ` is `SFinite`, which is what
`mconv_congr_ae` asks; the interface supplies a probability measure.

Proving campaign, chapter 13, the author's decision (b) of the fidelity review (2026-09-11).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## How the two counts are bounded -/

/-- The sign-change count is monotone in the alternation relation: a function whose alternations
are all alternations of another has at most its count. -/
theorem signChanges_mono {f g : ℝ → ℝ}
    (h : ∀ n : ℕ, HasAlternations f n → HasAlternations g n) :
    signChanges f ≤ signChanges g := by
  refine iSup₂_le fun n hn => ?_
  exact le_iSup₂ (f := fun (m : ℕ) (_ : m ∈ {m : ℕ | HasAlternations g m}) => (m : ℕ∞)) n (h n hn)

/-- The essential count is at most the ordinary count of any representative. -/
theorem signChangesAE_le_of_ae {f h : ℝ → ℝ} (hh : h =ᵐ[volume] f) :
    signChangesAE f ≤ signChanges h :=
  iInf₂_le (f := fun (u : ℝ → ℝ) (_ : u ∈ {u : ℝ → ℝ | u =ᵐ[volume] f}) => signChanges u) h hh

/-- The essential count is at most the ordinary count. -/
theorem signChangesAE_le (f : ℝ → ℝ) : signChangesAE f ≤ signChanges f :=
  signChangesAE_le_of_ae (Filter.EventuallyEq.refl _ _)

/-! ## The measurable hull -/

/-- **The measurable hull of a representative** (fidelity review **R14**). Every representative
`h` of a measurable `g` is dominated, in sign changes, by a *measurable* representative that is
also dominated by `g` in absolute value — so it carries `g`'s integrability and `g`'s bound.

The witness is `g` deleted on a measurable null superset of the set where `h` and `g` differ.
Where the witness is nonzero it equals `h`, so its alternations are alternations of `h` at the
very same points. -/
theorem exists_measurable_rep_signChanges_le {g h : ℝ → ℝ} (hg : Measurable g)
    (hh : h =ᵐ[volume] g) :
    ∃ h' : ℝ → ℝ, Measurable h' ∧ h' =ᵐ[volume] g ∧ signChanges h' ≤ signChanges h ∧
      ∀ x, |h' x| ≤ |g x| := by
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hh)
  have hNae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ N := by
    rw [ae_iff]
    simpa using hN0
  refine ⟨Nᶜ.indicator g, hg.indicator hNmeas.compl, ?_, ?_, fun x => ?_⟩
  · filter_upwards [hNae] with x hx
    exact Set.indicator_of_mem hx g
  · refine signChanges_mono fun n hn => ?_
    obtain ⟨x, ε, hε, hmono, hpos⟩ := hn
    refine ⟨x, ε, hε, hmono, fun i => ?_⟩
    have hi := hpos i
    have hxi : x i ∈ Nᶜ := by
      refine Set.mem_of_indicator_ne_zero (f := g) fun hz => ?_
      rw [hz] at hi
      simp at hi
    have hhg : h (x i) = g (x i) := by
      by_contra hcon
      exact hxi (hsub hcon)
    rwa [Set.indicator_of_mem hxi g, ← hhg] at hi
  · by_cases hx : x ∈ N
    · rw [Set.indicator_of_notMem (by simpa using hx) g]
      simp
    · rw [Set.indicator_of_mem hx g]

/-- **The essential count is an infimum over measurable representatives.** The corollary of the
hull lemma that reconciles `signChangesAE` with Karlin's ordinary count: no representative, in
particular no non-measurable one, lowers the infimum. -/
theorem signChangesAE_eq_iInf_measurable {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume) :
    signChangesAE g = ⨅ h ∈ {h : ℝ → ℝ | Measurable h ∧ h =ᵐ[volume] g}, signChanges h := by
  refine le_antisymm (le_iInf₂ fun h hh => signChangesAE_le_of_ae hh.2) ?_
  refine le_iInf₂ fun h hh => ?_
  have hh' : h =ᵐ[volume] g := hh
  obtain ⟨h', hm, hae, hle, -⟩ :=
    exists_measurable_rep_signChanges_le hg.stronglyMeasurable_mk.measurable
      (hh'.trans hg.ae_eq_mk)
  exact le_trans (iInf₂_le h' ⟨hm, hae.trans hg.ae_eq_mk.symm⟩) hle

/-! ## From the ordinary count to the essential one -/

/-- **Karlin's conclusion implies the one this development consumes.** A law whose convolution
operator diminishes the *ordinary* sign-change count of every measurable integrable or bounded
test function diminishes the *essential* count of every almost-everywhere strongly measurable
one.

This is the step fidelity review **R14** found sitting inside
`variationDiminishing_of_polyaExponent` as a belief; with it proved, the axiom is stated at
Karlin's letter and this theorem carries it the rest of the way. `SFinite` is all it asks of `μ`,
being what `mconv_congr_ae` asks. -/
theorem isVariationDiminishing_of_ord {μ : Measure ℝ} [SFinite μ]
    (h : IsVariationDiminishingOrd μ) : IsVariationDiminishing μ := by
  intro g hg hgb
  obtain ⟨g₀, hg₀meas, hg₀ae, hg₀b⟩ := exists_good_representative hg hgb
  rw [signChangesAE_congr (mconv_congr_ae μ hg₀ae), signChangesAE_congr hg₀ae, signChangesAE]
  refine le_iInf₂ fun k hk => ?_
  obtain ⟨k', hk'meas, hk'ae, hk'le, hk'abs⟩ := exists_measurable_rep_signChanges_le hg₀meas hk
  have hk'b : Integrable k' volume ∨ ∃ C : ℝ, ∀ x, |k' x| ≤ C := by
    rcases hg₀b with hint | ⟨C, hC⟩
    · exact Or.inl (hint.abs.mono' hk'meas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hk'abs x))
    · exact Or.inr ⟨C, fun x => (hk'abs x).trans (hC x)⟩
  calc signChangesAE (mconv μ g₀)
      = signChangesAE (mconv μ k') := signChangesAE_congr (mconv_congr_ae μ hk'ae.symm)
    _ ≤ signChanges (mconv μ k') := signChangesAE_le _
    _ ≤ signChanges k' := h k' hk'meas hk'b
    _ ≤ signChanges k := hk'le

end SpatialLine
