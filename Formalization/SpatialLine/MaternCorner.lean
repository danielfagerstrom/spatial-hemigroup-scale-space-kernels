/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CornerDefs
import SpatialLine.Frullani
import SpatialLine.ProfileIntegrability
import Mathlib.Tactic.ComputeDegree

/-!
# `prop:matern-exponent`: the Matérn exponent, its transforms and its gauge

Blueprint: `blueprint/src/parts/10-corners.tex`, `prop:matern-exponent` clauses (1) and (2), and
`thm:matern`'s gauge and rational-increment clauses.

twin: Paper I's `prop:gamma-family` / `prop:gamma-kernels`
(`Hemigroup.SelfDecomposableExponent.gammaExponent_toRealExponent`,
`...gammaExponent_laplace_increment`). The causal profile is `γe^{-u}` and the spatial one
`2γe^{-x/θ}`, the factor `2` being the folding.

## The witness, and why it is built here and not in `Corners.lean`

`Corners.lean` holds `maternProfile` as a **plain function** and this node states admissibility
existentially (SKELETON.md, finding F12): building the profile as an `SDProfile` *value* in the
vocabulary file would prove `lem:profile-integrability` for the Matérn corner inside the
`sorry`-free library, leaving `prop:matern-exponent`(1) with nothing to assert. `maternDatum`
below is that node's **witness**, constructed in the file that proves the node; its two
integrability fields are the node's own content and are discharged here.

## The route

The exponent identity is `integral_frullani` at `p = θ⁻¹`, twice the half-logarithm because the
folded profile carries the factor `2`. Everything else in this file is algebra on the transform:
`matern_transforms` reads the exponent through `exp` and `Real.log`, `matern_gauge` is the
dilation, and `matern_rational` is the ratio of the endpoint transforms.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The profile as a function -/

theorem maternProfile_of_pos {x : ℝ} (hx : 0 < x) (γ θ : ℝ) :
    maternProfile γ θ x = 2 * γ * Real.exp (-(x / θ)) :=
  Set.indicator_of_mem hx _

theorem measurable_maternProfile (γ θ : ℝ) : Measurable (maternProfile γ θ) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

theorem maternProfile_nonneg {γ : ℝ} (hγ : 0 < γ) (θ x : ℝ) : 0 ≤ maternProfile γ θ x := by
  unfold maternProfile
  rw [Set.indicator_apply]
  split_ifs with h
  · positivity
  · exact le_rfl

theorem maternProfile_zero (γ θ : ℝ) : maternProfile γ θ 0 = 0 := by
  simp [maternProfile]

theorem maternProfile_antitoneOn {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) :
    AntitoneOn (maternProfile γ θ) (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  rw [maternProfile_of_pos hx, maternProfile_of_pos hy]
  have hd : x / θ ≤ y / θ := by gcongr
  have hle : -(y / θ) ≤ -(x / θ) := by linarith
  have hexp := Real.exp_le_exp.mpr hle
  nlinarith [Real.exp_pos (-(x / θ)), Real.exp_pos (-(y / θ))]

/-- On `(0,∞)` the profile is `2γ` times the exponential the Frullani identity is stated with,
at rate `p = θ⁻¹`. -/
theorem maternProfile_eq_exp {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) (γ : ℝ) :
    maternProfile γ θ x = 2 * γ * Real.exp (-(θ⁻¹ * x)) := by
  rw [maternProfile_of_pos hx]
  congr 2
  field_simp

/-! ## The two integrability conditions -/

theorem integrableOn_id_mul_maternProfile {γ θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => x * maternProfile γ θ x) (Ioo (0:ℝ) 1) := by
  have hp : (0:ℝ) < θ⁻¹ := by positivity
  have hbase : IntegrableOn (fun x : ℝ => 2 * γ * (x * Real.exp (-(θ⁻¹ * x)))) (Ioo (0:ℝ) 1) :=
    IntegrableOn.mono_set ((integrableOn_id_mul_exp_neg hp).const_mul (2 * γ))
      Ioo_subset_Ioi_self
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioo
  rw [maternProfile_eq_exp hθ hx.1]
  ring

theorem integrableOn_maternProfile_div {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => maternProfile γ θ x / x) (Ioi (1:ℝ)) := by
  have hp : (0:ℝ) < θ⁻¹ := by positivity
  have hbase : IntegrableOn (fun x : ℝ => 2 * γ * Real.exp (-(θ⁻¹ * x))) (Ioi (1:ℝ)) :=
    IntegrableOn.mono_set ((integrableOn_exp_neg_Ioi_zero hp).const_mul (2 * γ))
      (Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hbase
    ((measurable_maternProfile γ θ).div measurable_id).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
  have hx1 : (1:ℝ) < x := hx
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx1
  rw [maternProfile_eq_exp hθ hx0, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_le_iff₀ hx0]
  have hc : (0:ℝ) < 2 * γ * Real.exp (-(θ⁻¹ * x)) := by positivity
  nlinarith [hc, hx1]

/-! ## The witness of `prop:matern-exponent`(1) -/

/-- The `SDProfile` that `prop:matern-exponent`(1) asserts to exist: Gaussian coefficient `0`
and profile `2γe^{-x/θ}`. Its two integrability fields are the node's content. -/
noncomputable def maternDatum (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) : SDProfile where
  a := 0
  k := maternProfile γ θ
  a_nonneg := le_rfl
  k_nonneg := fun x _ => maternProfile_nonneg hγ θ x
  k_antitone := maternProfile_antitoneOn hγ hθ
  k_zero := maternProfile_zero γ θ
  integrable_near_zero :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_id_mul_maternProfile hθ)
      ((ae_restrict_iff' measurableSet_Ioo).mpr
        (.of_forall fun x hx => mul_nonneg hx.1.le (maternProfile_nonneg hγ θ x)))
  integrable_at_top :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_maternProfile_div hγ hθ)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (.of_forall fun x hx =>
          div_nonneg (maternProfile_nonneg hγ θ x) (lt_trans zero_lt_one hx).le))

@[simp]
theorem maternDatum_a (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) : (maternDatum γ θ hγ hθ).a = 0 := rfl

@[simp]
theorem maternDatum_k (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) :
    (maternDatum γ θ hγ hθ).k = maternProfile γ θ := rfl

/-! ## The exponent -/

/-- The Lévy integral of any profile agreeing with `maternProfile γ θ` on `(0,∞)`: the Frullani
identity at rate `θ⁻¹`, doubled by the folding factor. -/
theorem lintegral_maternProfile {γ θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) {k : ℝ → ℝ}
    (hk : Set.EqOn k (maternProfile γ θ) (Ioi 0)) (ω : ℝ) :
    (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * k x / x))
      = ENNReal.ofReal (maternExponent γ θ ω) := by
  have hp : (0:ℝ) < θ⁻¹ := by positivity
  have hpt : ∀ x ∈ Ioi (0:ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * k x / x)
      = ENNReal.ofReal (2 * γ * ((1 - Real.cos (ω * x)) * Real.exp (-(θ⁻¹ * x)) / x)) := by
    intro x hx
    congr 1
    rw [hk hx, maternProfile_eq_exp hθ hx]
    ring
  have hint : IntegrableOn
      (fun x : ℝ => 2 * γ * ((1 - Real.cos (ω * x)) * Real.exp (-(θ⁻¹ * x)) / x)) (Ioi 0) :=
    (integrableOn_frullani hp ω).const_mul _
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))),
      0 ≤ 2 * γ * ((1 - Real.cos (ω * x)) * Real.exp (-(θ⁻¹ * x)) / x) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    positivity
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_frullani hp ω]
  congr 1
  rw [maternExponent]
  have hbase : (1:ℝ) + ω ^ 2 / (θ⁻¹) ^ 2 = 1 + θ ^ 2 * ω ^ 2 := by
    field_simp
  rw [hbase]
  ring

/-- **`prop:matern-exponent`(1) at the witness**: the exponent of `maternDatum` is
`γ log(1 + θ²ω²)`. -/
theorem maternDatum_exponent (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) (ω : ℝ) :
    (maternDatum γ θ hγ hθ).exponent ω = maternExponent γ θ ω := by
  have hnn : 0 ≤ maternExponent γ θ ω := by
    have hlog : 0 ≤ Real.log (1 + θ ^ 2 * ω ^ 2) :=
      Real.log_nonneg (by nlinarith [sq_nonneg (θ * ω)])
    rw [maternExponent]
    positivity
  rw [SDProfile.exponent, SDProfile.exponentL, maternDatum_a, maternDatum_k]
  rw [lintegral_maternProfile hγ hθ (fun x _ => rfl) ω]
  simp [ENNReal.toReal_ofReal hnn]

/-! ## The node -/

/-- **`prop:matern-exponent`(1), the exponent.** `γ log(1 + θ²ω²)` is admissible with `a = 0` and
folded profile `2γ exp(-x/θ)`.

**Priced M; paid M.** The obligation is one integral, `∫₀^∞ (1 - cos ωx)e^{-x/θ}x⁻¹dx =
½log(1 + θ²ω²)`, proved in `Frullani.lean` by differentiating under the integral sign; the two
integrability conditions are the dominating functions of that proof read on `(0,1)` and
`(1,∞)`. -/
theorem matern_exponent (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ Q : SDProfile, Q.a = 0 ∧ Q.k = maternProfile γ θ ∧
      ∀ ω : ℝ, Q.exponent ω = maternExponent γ θ ω :=
  ⟨maternDatum γ θ hγ hθ, rfl, rfl, maternDatum_exponent γ θ hγ hθ⟩

/-- **`thm:matern`, the gauge freedom, at the frequency side.** The exponent at range `θ` is
the exponent at range `1` read at the dilated frequency.

This identity is definitional — both sides unfold to `γ log(1 + θ²ω²)` and `ring_nf` closes it,
with neither positivity hypothesis consumed — so it says nothing about the *family*
(fidelity review R23). It is kept because it is the frequency-side half of the change of gauge
and is what the transform computations read; the half that carries the theorem's closing
sentence is `matern_gauge_profile` below. -/
theorem matern_gauge (γ θ : ℝ) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∀ ω : ℝ, maternExponent γ θ ω = maternExponent γ 1 (θ * ω) := by
  intro ω
  simp only [maternExponent]
  ring_nf

/-- **`thm:matern`, the gauge freedom, at the profile.** The Matérn profile of range `θ` is the
profile of range `1` read in the rescaled displacement `x/θ`.

This is the theorem's closing sentence — "the parameter `θ` is a change of gauge and may be
normalised to `1`" — as a statement about the *data* rather than about the exponent
(fidelity review R23): the `(γ,θ)` member of the family is the `(γ,1)` member with the
displacement axis rescaled, so nothing is lost by normalising. Unlike the frequency-side
identity it is false without `0 < θ`, and the range positivity is genuinely consumed.

Stated on `(0,∞)`, where `maternProfile` is its exponential and outside which the indicator
makes both sides `0` for a different reason. -/
theorem matern_gauge_profile {θ : ℝ} (hθ : 0 < θ) (γ : ℝ) :
    Set.EqOn (maternProfile γ θ) (fun x => maternProfile γ 1 (x / θ)) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  show maternProfile γ θ x = maternProfile γ 1 (x / θ)
  rw [maternProfile_of_pos hx0 γ θ, maternProfile_of_pos (div_pos hx0 hθ) γ 1]
  simp

/-- **`prop:matern-exponent`(2), the transforms.** The kernel transform is `(1 + t²ω²)^{-γ}` and
the increment transfer function is the ratio of the endpoint transforms. -/
theorem matern_transforms (γ : ℝ) (hγ : 0 < γ) (μ : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hcos : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω
        = Real.exp (-(maternExponent γ 1 (t * ω) - maternExponent γ 1 (s * ω)))) :
    (∀ t ω : ℝ, 0 < t → fourierCos (μ 0 t) ω = (1 + t ^ 2 * ω ^ 2) ^ (-γ)) ∧
      ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
        fourierCos (μ s t) ω
          = ((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ := by
  have key : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω = ((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ := by
    intro s t ω hs hst
    have hps : (0:ℝ) < 1 + s ^ 2 * ω ^ 2 := by positivity
    have hpt : (0:ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
    rw [hcos s t ω hs hst, Real.rpow_def_of_pos (div_pos hps hpt),
      Real.log_div hps.ne' hpt.ne']
    simp only [maternExponent]
    congr 1
    ring_nf
  refine ⟨fun t ω ht => ?_, key⟩
  have hpt : (0:ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
  rw [key 0 t ω le_rfl ht.le,
    show (1:ℝ) + 0 ^ 2 * ω ^ 2 = 1 by ring, one_div, Real.inv_rpow hpt.le,
    ← Real.rpow_neg hpt.le]

/-- **`thm:matern`, (3) ⟺ (4)** for integer `γ`: the single-pole-pair rational stage transfer
functions.

The one step that is not algebra is the transform at the collapsed pair `(0,0)`: the cascade
relation at `(s,t) = (0,1)` reads `Φ̂_{0,1} = Φ̂_{0,1}·Φ̂_{0,0}`, and the left factor is a positive
power, so `Φ̂_{0,0} = 1`. No continuity of the transform is needed for it. -/
theorem matern_rational (m : ℕ) (hm : 0 < m) (θ : ℝ) (hθ : 0 < θ) (μ : ℝ → ℝ → Measure ℝ)
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t))
    (hcas : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ 0 t) ω = fourierCos (μ s t) ω * fourierCos (μ 0 s) ω) :
    (∀ t ω : ℝ, 0 < t → fourierCos (μ 0 t) ω = (1 + θ ^ 2 * t ^ 2 * ω ^ 2) ^ (-(m : ℝ))) ↔
      ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
        fourierCos (μ s t) ω
          = ((1 + θ ^ 2 * s ^ 2 * ω ^ 2) / (1 + θ ^ 2 * t ^ 2 * ω ^ 2)) ^ (m : ℝ) := by
  have base : ∀ u ω : ℝ, (0:ℝ) < 1 + θ ^ 2 * u ^ 2 * ω ^ 2 := by intro u ω; positivity
  constructor
  · intro h0 s t ω hs hst
    have hzero : fourierCos (μ 0 0) ω = 1 := by
      have h := hcas 0 1 ω le_rfl zero_le_one
      rw [h0 1 ω one_pos] at h
      have hne : ((1 : ℝ) + θ ^ 2 * 1 ^ 2 * ω ^ 2) ^ (-(m : ℝ)) ≠ 0 :=
        (Real.rpow_pos_of_pos (base 1 ω) _).ne'
      field_simp at h
      exact h.symm
    have h0' : ∀ u : ℝ, 0 ≤ u →
        fourierCos (μ 0 u) ω = (1 + θ ^ 2 * u ^ 2 * ω ^ 2) ^ (-(m : ℝ)) := by
      intro u hu
      rcases eq_or_lt_of_le hu with h | h
      · rw [← h, hzero]
        norm_num
      · exact h0 u ω h
    have hcast := hcas s t ω hs hst
    rw [h0' t (hs.trans hst), h0' s hs] at hcast
    rw [Real.div_rpow (base s ω).le (base t ω).le,
      eq_div_iff (Real.rpow_pos_of_pos (base t ω) _).ne']
    rw [Real.rpow_neg (base s ω).le, Real.rpow_neg (base t ω).le] at hcast
    have hsp : (0:ℝ) < (1 + θ ^ 2 * s ^ 2 * ω ^ 2) ^ ((m : ℝ)) :=
      Real.rpow_pos_of_pos (base s ω) _
    have htp : (0:ℝ) < (1 + θ ^ 2 * t ^ 2 * ω ^ 2) ^ ((m : ℝ)) :=
      Real.rpow_pos_of_pos (base t ω) _
    field_simp at hcast
    have hrw : (1 + θ ^ 2 * ω ^ 2 * s ^ 2) = (1 + θ ^ 2 * s ^ 2 * ω ^ 2) := by ring
    rw [hrw] at hcast
    linarith [hcast]
  · intro h1 t ω ht
    rw [h1 0 t ω le_rfl ht.le, show (1:ℝ) + θ ^ 2 * 0 ^ 2 * ω ^ 2 = 1 by ring, one_div,
      Real.inv_rpow (base t ω).le, ← Real.rpow_neg (base t ω).le]

/-- **`thm:matern`(4), the rationality made visible.** At an integer exponent the stage transfer
function of a Matérn family *is* a rational function of `ω`, and its denominator is a power of a
single quadratic without real roots --- a single pole pair, of multiplicity `m`.

This is what `matern_rational` leaves implicit (fidelity review R24). That declaration states
the closed form `((1 + θ²s²ω²)/(1 + θ²t²ω²))^m` and nothing else, and it re-proves verbatim with
`m` replaced by an arbitrary real, so a reader of it cannot see the restriction the blueprint
deliberately narrowed clause (4) to. Here `m : ℕ` is load-bearing in the type: at a
non-integer exponent there is no ratio of polynomials at all, and the conclusion could not be
stated.

The pole pair is `q`, of degree `2` and strictly positive on the whole line, so its two roots
are a single conjugate pair off the real axis; the transfer function is `p^m/q^m`. Both degree
clauses need `0 < s`: at `s = 0` the numerator is the constant `1`, which is clause (4) at the
endpoint kernels and is `matern_kernels`' business, not this one. Nothing needs `0 < m` --- at
`m = 0` both powers are `1` and the family is trivial --- so it is not assumed. -/
theorem matern_rational_polynomial (m : ℕ) (θ : ℝ) (hθ : 0 < θ) (μ : ℝ → ℝ → Measure ℝ)
    (hinc : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      fourierCos (μ s t) ω
        = ((1 + θ ^ 2 * s ^ 2 * ω ^ 2) / (1 + θ ^ 2 * t ^ 2 * ω ^ 2)) ^ (m : ℝ))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ∃ p q : Polynomial ℝ,
      p.natDegree = 2 ∧ q.natDegree = 2 ∧ (∀ ω : ℝ, 0 < q.eval ω) ∧
        ∀ ω : ℝ, fourierCos (μ s t) ω = (p ^ m).eval ω / (q ^ m).eval ω := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  refine ⟨Polynomial.C 1 + Polynomial.C (θ ^ 2 * s ^ 2) * Polynomial.X ^ 2,
    Polynomial.C 1 + Polynomial.C (θ ^ 2 * t ^ 2) * Polynomial.X ^ 2, ?_, ?_, ?_, ?_⟩
  · compute_degree!
    exact ⟨hθ.ne', hs.ne'⟩
  · compute_degree!
    exact ⟨hθ.ne', ht.ne'⟩
  · intro ω
    simp
    positivity
  · intro ω
    have hps : (0:ℝ) < 1 + θ ^ 2 * s ^ 2 * ω ^ 2 := by positivity
    have hpt : (0:ℝ) < 1 + θ ^ 2 * t ^ 2 * ω ^ 2 := by positivity
    rw [hinc s t ω hs.le hst, Real.rpow_natCast, div_pow]
    simp

end SpatialLine
