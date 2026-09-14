/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Growth
import SpatialLine.Interfaces

/-!
# The integrability criterion for a profile

Blueprint: `lem:profile-integrability` (`blueprint/src/parts/02-preliminaries.tex`). A change of
variables and nothing else: for `ν(dx) = k(x) x⁻¹ dx` on `(0,∞)`,

`∫ (1 ∧ x²) ν(dx) < ∞ ⟺ ∫₀¹ x k(x) dx < ∞ and ∫₁^∞ k(x)/x dx < ∞`.

**Hypothesis archaeology.** `k` is asked to be nonnegative and a.e. measurable on `(0,∞)` and
nothing else — in particular *not* monotone. `SDProfile.k_antitone` is not consumed here and must
not be assumed, because `lem:cin-rays` and `prop:choquet-cone` apply the criterion to increment
densities `k(u/t) - k(u/s)`, which are not monotone. Paper I documents the same trap.

The "consequently" clause of the node — that the two conditions make `eq:sd-profile` a member of
`NDₛ` — is split in two here, and deliberately: `profile_integrability_pair` produces the Lévy
pair and rests on Lean core alone, while `profile_integrability_mem` adds the class membership
and is the only declaration of the chapter that spends a ledger interface
(`fourier_toolbox_levy_converse`, ledger **A3**). Keeping them apart is what makes the two
`#print axioms` lines say which half of the node the trust boundary pays for.

Proving campaign, chapter 2 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set
open scoped ENNReal

/-! ## The change of variables -/

/-- **`lem:profile-integrability`.** The Lévy condition `∫ (1 ∧ x²) ν < ∞` on the profile measure
`ν(dx) = k(x) x⁻¹ dx` is the conjunction of the two conditions of `eq:sd-profile`. -/
theorem profile_integrability {k : ℝ → ℝ} (hk : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    (hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k)) ≠ ⊤
      ↔ ((∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x)) ≠ ⊤
          ∧ (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x)) ≠ ⊤) := by
  have hdens : AEMeasurable (fun x : ℝ => ENNReal.ofReal (k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := (hkm.div aemeasurable_id).ennreal_ofReal
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hkey : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k))
      = (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x))
        + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x) := by
    rw [profileMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop),
      hsplit, lintegral_union measurableSet_Ioi hdisj]
    congr 1
    · -- Below the truncation `1 ∧ x² = x²`, and `(k(x)/x)·x² = x·k(x)`.
      rw [setLIntegral_congr (μ := volume) (f := fun x => ENNReal.ofReal (x * k x))
        Ioo_ae_eq_Ioc]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have hkx : 0 ≤ k x := hk x hx0
      simp only [Pi.mul_apply, min_eq_right hx1]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    · -- Above it `1 ∧ x² = 1`.
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx' : (1 : ℝ) < x := hx
      have hx1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith [hx']
      rw [Pi.mul_apply, min_eq_left hx1, ENNReal.ofReal_one, mul_one]
  rw [hkey, ENNReal.add_ne_top]

/-! ## Two facts about the profile measure, and a finiteness helper

Wave 3's merge collected these here. `sFinite_profileMeasure` had been written beside
`prop:thorin-subclass` in chapter 10 and `lintegral_ofReal_ne_top_of_integrableOn` beside the
Frullani integral, from where three chapters imported the file for that one lemma; both are
facts about the vocabulary this node is *about*, so they belong beside
`isFolded_profileMeasure`. -/

/-- A nonnegative integrable function has a finite `lintegral` of its `ofReal`. -/
theorem lintegral_ofReal_ne_top_of_integrableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hf : IntegrableOn f s) (hnn : ∀ᵐ x ∂(volume.restrict s), 0 ≤ f x) :
    (∫⁻ x in s, ENNReal.ofReal (f x)) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnn]
  exact ENNReal.ofReal_ne_top

instance sFinite_profileMeasure (k : ℝ → ℝ) : SFinite (profileMeasure k) := by
  unfold profileMeasure
  infer_instance

/-! ## The "consequently" clause -/

/-- **A folded measure is carried by the open positive half-line.** `IsFolded m` says
`m (Iic 0) = 0`, and `Iic 0` is the complement of `{θ | 0 < θ}`, so the two readings are one
fact; chapters 8 to 13 want the almost-everywhere one, under an integral sign. It lives here,
beside `isFolded_profileMeasure`, because `Transform.lean` — where `IsFolded` is defined — is
vocabulary and carries no proofs. -/
theorem ae_pos_of_isFolded {m : Measure ℝ} (hm : IsFolded m) : ∀ᵐ θ ∂m, (0 : ℝ) < θ := by
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hm
  simpa using not_lt.mp (by simpa using hθ)

/-- The profile measure of an `SDProfile` is carried by `(0,∞)`. -/
theorem isFolded_profileMeasure (k : ℝ → ℝ) : IsFolded (profileMeasure k) := by
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply measurableSet_Iic]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h => h

/-- A symmetric Lévy pair carrying a profile's data has the profile's exponent. The two are the
same `lintegral` once `withDensity` is unfolded: `(k(x)/x)·(1 - cos ωx)` is the integrand of
`eq:sd-profile`. -/
theorem exponentL_eq_of_profileMeasure (P : SDProfile) (Q : SymLevyPair) (ha : Q.a = P.a)
    (hν : Q.ν = profileMeasure P.k) (ω : ℝ) : P.exponentL ω = Q.exponentL ω := by
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone
  have hdens : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := (hkm.div aemeasurable_id).ennreal_ofReal
  rw [SDProfile.exponentL, SymLevyPair.exponentL, ha, hν, profileMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop)]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hkx : 0 ≤ P.k x := P.k_nonneg x hx
  have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- **`lem:profile-integrability`, the pair.** The data of `eq:sd-profile` is a symmetric Lévy
pair with the same Gaussian coefficient and the same exponent.

This is the half of the node's "consequently" clause that rests on Lean core alone: the Lévy
condition is `profile_integrability` read right to left from the structure's two integrability
fields. -/
theorem profile_integrability_pair (P : SDProfile) :
    ∃ Q : SymLevyPair, Q.a = P.a ∧ Q.ν = profileMeasure P.k ∧ ∀ ω, P.exponent ω = Q.exponent ω := by
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone
  have hint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
    (profile_integrability P.k_nonneg hkm).mpr ⟨P.integrable_near_zero, P.integrable_at_top⟩
  set Q : SymLevyPair :=
    ⟨P.a, profileMeasure P.k, P.a_nonneg, isFolded_profileMeasure P.k, hint⟩ with hQ
  have hQa : Q.a = P.a := rfl
  have hQν : Q.ν = profileMeasure P.k := rfl
  refine ⟨Q, hQa, hQν, fun ω => ?_⟩
  rw [SDProfile.exponent, SymLevyPair.exponent,
    exponentL_eq_of_profileMeasure P Q hQa hQν ω]

/-- **`lem:profile-integrability`, the "consequently" clause.** The two conditions of
`eq:sd-profile` make its exponent a member of `LEₛ`, hence of `NDₛ`.

Sufficiency only: `SDProfile` *bundles* the two conditions, and the necessity half is
`profile_integrability` read right to left, so there is nothing else to state. The conclusion is
given in both namings of the class, `prop:fourier-toolbox`(3) being what relates them.

**Spends ledger A3** through `fourier_toolbox_levy_converse`, for the second conjunct only; the
first is `profile_integrability_pair` and rests on Lean core. -/
theorem profile_integrability_mem (P : SDProfile) :
    IsSymLevyExponent P.exponent ∧ IsSymNegDef P.exponent := by
  obtain ⟨Q, -, -, hQ⟩ := profile_integrability_pair P
  refine ⟨⟨Q, hQ⟩, ?_⟩
  have : P.exponent = Q.exponent := funext hQ
  rw [this]
  exact fourier_toolbox_levy_converse Q

end SpatialLine
