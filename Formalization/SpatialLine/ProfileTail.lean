/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.CinRays

/-!
# The Choquet measure's own integrability, and the right-continuous profile

Blueprint: the trailing paragraph of `lem:selfdecomposable-exponents` --- "the profile `k` may be
taken right-continuous with `k(infty) = 0`, and then `varpi := -dk` is a positive measure with
`k(x) = varpi((x,infty))`, `int (1 wedge u^2) varpi < infty` and `int log_+ u varpi < infty`".

## The two Tonelli identities, with a continuous weight

The blueprint reads the two integrability conditions on `varpi` off the two on `k` by Tonelli:
`int_0^1 x k(x) dx = int (u wedge 1)^2/2 varpi(du)` and
`int_1^infty k(x) x^{-1} dx = int log_+ u varpi(du)`. Both are instances of the layer cake
formula against `varpi`, whose tails are `k`.

The formalisation makes one change, and it is a simplification rather than a divergence: the
weights `(u wedge 1)^2` and `log_+ u` are the primitives of the **discontinuous** densities
`2t 1_{t<1}` and `t^{-1} 1_{t>1}`, and the layer cake formula wants a density that is interval
integrable on every `(0,t)`. Rather than carry the two indicator functions, the identities are
proved for the primitives of the **continuous** densities `2t(1+t^2)^{-2}` and `t(1+t^2)^{-1}`,
namely `u^2/(1+u^2)` and `log(1+u^2)/2`; each dominates the blueprint's weight up to a factor of
`2`, and each is dominated by the same two conditions on `k`. Nothing is lost, because both
conditions are finiteness assertions.

## The right-continuous modification

`sd_exponents_profile_measure` asks for a modification of the profile that is right-continuous
with limit `0` at infinity, together with a measure whose tails are that modification **at every
positive point**. The construction is one line once the Choquet measure exists
(`cin_superposition_exists`, chapter 8): take `k'(x) := varpi((x,infty)).toReal`. Right
continuity is then continuity of a measure from below and needs no property of the profile;
`k' = k` almost everywhere is the specification `HasProfileTail` itself; and the finiteness that
makes `toReal` faithful comes from the a.e. identity at any point below `x`.

That is finding F6 answered, and answered in the negative: the node was priced as downstream of
a Stieltjes construction, and the construction it is downstream of --- the quantile transform of
`CinRays.lean` --- was already written for `lem:cin-rays`. See SKELETON.md.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## The layer cake against a Choquet measure -/

/-- **The layer cake formula against a measure whose tails are `k`.** For a continuous weight `g`,
nonnegative on the positive half-line, the `ϖ`-integral of the primitive `u ↦ ∫₀^u g` is the
`k`-weighted integral of `g` over `(0,∞)`.

This is the Tonelli step of the blueprint's `ϖ` paragraph, with the weight left free. -/
theorem lintegral_intervalIntegral_of_hasProfileTail {k : ℝ → ℝ} {ϖ : Measure ℝ}
    (hϖ : HasProfileTail k ϖ) (hk : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    {g : ℝ → ℝ} (hg : Continuous g) (hgnn : ∀ t : ℝ, 0 < t → 0 ≤ g t) :
    ∫⁻ u, ENNReal.ofReal (∫ t in (0 : ℝ)..u, g t) ∂ϖ
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (k t * g t) := by
  obtain ⟨hfold, htail⟩ := hϖ
  have hnn : 0 ≤ᵐ[ϖ] (id : ℝ → ℝ) := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun t ht => ?_) hfold
    simp only [Pi.zero_apply, id_eq, not_le, mem_setOf_eq] at ht
    exact mem_Iic.mpr ht.le
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := ϖ) (f := (id : ℝ → ℝ)) (g := g)
    hnn aemeasurable_id (fun t _ => (hg.intervalIntegrable _ _))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => hgnn t ht))
  simp only [id_eq] at hlayer
  rw [hlayer]
  refine lintegral_congr_ae ?_
  filter_upwards [htail, self_mem_ae_restrict measurableSet_Ioi] with t ht ht0
  rw [show {a : ℝ | t < a} = Ioi t from rfl, ht,
    ← ENNReal.ofReal_mul (hk t ht0)]


/-- The continuous density behind the truncation weight `u²/(1+u²)`. -/
theorem continuous_weight_sq : Continuous fun t : ℝ => 2 * t / (1 + t ^ 2) ^ 2 :=
  (continuous_const.mul continuous_id).div (by fun_prop) (fun x => by positivity)

/-- The continuous density behind the logarithmic weight `½log(1+u²)`. -/
theorem continuous_weight_log : Continuous fun t : ℝ => t / (1 + t ^ 2) :=
  continuous_id.div (by fun_prop) (fun x => by positivity)

/-! ## The two weights, and the finiteness they carry -/

/-- The primitive of `t ↦ 2t(1+t²)^{-2}` is `u ↦ u²/(1+u²)`. -/
theorem intervalIntegral_weight_sq (u : ℝ) :
    (∫ t in (0 : ℝ)..u, 2 * t / (1 + t ^ 2) ^ 2) = u ^ 2 / (1 + u ^ 2) := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) u,
      HasDerivAt (fun y : ℝ => y ^ 2 / (1 + y ^ 2)) (2 * x / (1 + x ^ 2) ^ 2) x := by
    intro x _
    have hne : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h2 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using h1.const_add 1
    have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / (1 + y ^ 2))
        ((2 * x * (1 + x ^ 2) - x ^ 2 * (2 * x)) / (1 + x ^ 2) ^ 2) x := h1.div h2 hne
    have heq : (2 * x * (1 + x ^ 2) - x ^ 2 * (2 * x)) / (1 + x ^ 2) ^ 2
        = 2 * x / (1 + x ^ 2) ^ 2 := by ring
    rwa [heq] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable continuous_weight_sq _ _)]
  norm_num

/-- The primitive of `t ↦ t(1+t²)^{-1}` is `u ↦ ½log(1+u²)`. -/
theorem intervalIntegral_weight_log (u : ℝ) :
    (∫ t in (0 : ℝ)..u, t / (1 + t ^ 2)) = Real.log (1 + u ^ 2) / 2 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) u,
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2) / 2) (x / (1 + x ^ 2)) x := by
    intro x _
    have hne : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) (2 * x / (1 + x ^ 2)) x := h1.log hne
    have h3 := h2.div_const 2
    have heq : 2 * x / (1 + x ^ 2) / 2 = x / (1 + x ^ 2) := by ring
    rwa [heq] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable continuous_weight_log _ _)]
  norm_num

/-- Splitting the positive half-line at `1`, in the form the two profile conditions use. -/
theorem lintegral_Ioi_split (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), f t
      = (∫⁻ t in Ioo (0 : ℝ) 1, f t) + ∫⁻ t in Ioi (1 : ℝ), f t := by
  have hsplit : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, -⟩ | hx)
      · exact hx
      · exact lt_of_lt_of_le zero_lt_one (mem_Ici.mp hx)
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx
    exact absurd (mem_Ici.mp hx) (not_le.mpr hx1)
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  congr 1
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm


/-! ## The Choquet measure's two integrability conditions -/

/-- **`∫ (1 ∧ u²)\,ϖ(du) < ∞`** — the first condition of the blueprint's `ϖ` paragraph, read off
the two conditions on the profile.

The weight integrated is `u²/(1+u²)`, which dominates `½(1 ∧ u²)`; its density `2t(1+t²)^{-2}` is
continuous, at most `2t` near the origin and at most `2/t` at infinity, so the layer cake sends it
to the two profile conditions with a factor of `2`. -/
theorem lintegral_min_one_sq_ne_top {P : SDProfile} {ϖ : Measure ℝ}
    (hϖ : HasProfileTail P.k ϖ) :
    (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤ := by
  have hkey := lintegral_intervalIntegral_of_hasProfileTail hϖ P.k_nonneg
    continuous_weight_sq (fun t ht => by positivity)
  have hbound : ∀ u : ℝ, ENNReal.ofReal (min 1 (u ^ 2))
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (∫ t in (0 : ℝ)..u, 2 * t / (1 + t ^ 2) ^ 2) := by
    intro u
    rw [intervalIntegral_weight_sq, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
    rcases le_or_gt (u ^ 2) 1 with h | h
    · rw [min_eq_right h, show 2 * (u ^ 2 / (1 + u ^ 2)) = 2 * u ^ 2 / (1 + u ^ 2) by ring,
        le_div_iff₀ hpos]
      nlinarith
    · rw [min_eq_left h.le, show 2 * (u ^ 2 / (1 + u ^ 2)) = 2 * u ^ 2 / (1 + u ^ 2) by ring,
        le_div_iff₀ hpos]
      nlinarith
  have hle : (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ)
      ≤ ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (P.k t * (2 * t / (1 + t ^ 2) ^ 2)) := by
    calc (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ)
        ≤ ∫⁻ u, ENNReal.ofReal 2
            * ENNReal.ofReal (∫ t in (0 : ℝ)..u, 2 * t / (1 + t ^ 2) ^ 2) ∂ϖ :=
          lintegral_mono hbound
      _ = ENNReal.ofReal 2 * ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (P.k t * (2 * t / (1 + t ^ 2) ^ 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hkey]
  refine ne_top_of_le_ne_top ?_ hle
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  rw [lintegral_Ioi_split]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal 2) ENNReal.ofReal_ne_top P.integrable_near_zero) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo (fun t ht => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have ht0 : (0 : ℝ) < t := ht.1
    have hk : 0 ≤ P.k t := P.k_nonneg t (mem_Ioi.mpr ht0)
    have hw : 2 * t / (1 + t ^ 2) ^ 2 ≤ 2 * t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
    nlinarith
  · refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal 2) ENNReal.ofReal_ne_top P.integrable_at_top) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hk : 0 ≤ P.k t := P.k_nonneg t (mem_Ioi.mpr ht0)
    have hw : 2 * t / (1 + t ^ 2) ^ 2 ≤ 2 * (1 / t) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + t ^ 2) ^ 2),
        show 2 * (1 / t) * (1 + t ^ 2) ^ 2 = 2 * (1 + t ^ 2) ^ 2 / t by ring,
        le_div_iff₀ ht0]
      nlinarith [sq_nonneg t, sq_nonneg (t ^ 2 - 1)]
    have hmul := mul_le_mul_of_nonneg_left hw hk
    rw [show P.k t / t = P.k t * (1 / t) by ring]
    nlinarith

/-- **`∫ log₊ u\,ϖ(du) < ∞`** — the second condition. Same route, with the weight `½log(1+u²)`,
which dominates `log₊ u` and whose density `t(1+t²)^{-1}` is at most `t` near the origin and at
most `1/t` at infinity. -/
theorem lintegral_log_max_one_ne_top {P : SDProfile} {ϖ : Measure ℝ}
    (hϖ : HasProfileTail P.k ϖ) :
    (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ) ≠ ⊤ := by
  have hkey := lintegral_intervalIntegral_of_hasProfileTail hϖ P.k_nonneg
    continuous_weight_log (fun t ht => by positivity)
  have hbound : ∀ u : ℝ, ENNReal.ofReal (Real.log (max 1 u))
      ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..u, t / (1 + t ^ 2)) := by
    intro u
    rw [intervalIntegral_weight_log]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt u 1 with h | h
    · rw [max_eq_left h, Real.log_one]
      have hlog : (0 : ℝ) ≤ Real.log (1 + u ^ 2) :=
        Real.log_nonneg (by nlinarith [sq_nonneg u])
      linarith
    · rw [max_eq_right h.le, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hu : (0 : ℝ) < u := lt_trans zero_lt_one h
      have hle : Real.log (u ^ 2) ≤ Real.log (1 + u ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at hle
      push_cast at hle
      linarith
  have hle : (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (P.k t * (t / (1 + t ^ 2))) := by
    calc (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ)
        ≤ ∫⁻ u, ENNReal.ofReal (∫ t in (0 : ℝ)..u, t / (1 + t ^ 2)) ∂ϖ :=
          lintegral_mono hbound
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (P.k t * (t / (1 + t ^ 2))) := hkey
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_Ioi_split]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top P.integrable_near_zero ?_
    refine setLIntegral_mono' measurableSet_Ioo (fun t ht => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have ht0 : (0 : ℝ) < t := ht.1
    have hk : 0 ≤ P.k t := P.k_nonneg t (mem_Ioi.mpr ht0)
    have hw : t / (1 + t ^ 2) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg t]
    nlinarith
  · refine ne_top_of_le_ne_top P.integrable_at_top ?_
    refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hk : 0 ≤ P.k t := P.k_nonneg t (mem_Ioi.mpr ht0)
    have hw : t / (1 + t ^ 2) ≤ 1 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      nlinarith [sq_nonneg t]
    have hmul := mul_le_mul_of_nonneg_left hw hk
    rw [show P.k t / t = P.k t * (1 / t) by ring]
    exact hmul


/-! ## The right-continuous modification, and the everywhere tail identity

Three general facts about a measure whose tails are a profile almost everywhere, then the node.
-/

section Modification

variable {k : ℝ → ℝ} {ϖ : Measure ℝ}

/-- **A point of `(a,b)` at which the tail identity holds.** `HasProfileTail` asserts the
identity almost everywhere on the positive half-line, so every interval of positive length inside
it contains a point where it holds; this is the only way the specification is ever used
pointwise. -/
theorem exists_tail_eq_mem_Ioo (hϖ : HasProfileTail k ϖ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ r ∈ Ioo a b, ϖ (Ioi r) = ENNReal.ofReal (k r) := by
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt ha hx.1
  have hne : volume.restrict (Ioo a b) ≠ 0 := by
    intro h
    have h1 : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ, h]
      rfl
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h1
    linarith
  haveI : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hne
  have h2 : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ϖ (Ioi x) = ENNReal.ofReal (k x) :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hϖ.2
  obtain ⟨r, hr1, hr2⟩ := (h2.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact ⟨r, hr2, hr1⟩

/-- **The tails of a Choquet measure are finite** at every positive point. Not a hypothesis: a
point of the a.e. identity below `x` bounds `ϖ((x,∞))` by a value of the profile. -/
theorem measure_Ioi_ne_top (hϖ : HasProfileTail k ϖ) {x : ℝ} (hx : 0 < x) : ϖ (Ioi x) ≠ ⊤ := by
  obtain ⟨r, hr, heq⟩ := exists_tail_eq_mem_Ioo hϖ le_rfl hx
  refine ne_top_of_le_ne_top ?_ (measure_mono (Ioi_subset_Ioi hr.2.le))
  rw [heq]
  exact ENNReal.ofReal_ne_top

/-- **`x ↦ μ((x,∞))` is right-continuous**, for an arbitrary measure on the line and with no
finiteness hypothesis: continuity of a measure from below along `(x,∞) = ⋃ₙ (x + (n+1)⁻¹, ∞)`,
transported from the sequence to the filter `𝓝[>] x` by monotonicity. -/
theorem tendsto_measure_Ioi_nhdsGT (μ : Measure ℝ) (x : ℝ) :
    Tendsto (fun y => μ (Ioi y)) (𝓝[>] x) (𝓝 (μ (Ioi x))) := by
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hmono : Monotone (fun n : ℕ => Ioi (x + 1 / (n + 1 : ℝ))) := by
      intro m n hmn
      refine Ioi_subset_Ioi ?_
      have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      have : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      linarith
    have hunion : (⋃ n : ℕ, Ioi (x + 1 / (n + 1 : ℝ))) = Ioi x := by
      ext y
      simp only [mem_iUnion, mem_Ioi]
      constructor
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y - x by linarith)
        exact ⟨n, by linarith⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds ha)).exists
    filter_upwards [Ioo_mem_nhdsGT (show x < x + 1 / (n + 1 : ℝ) by
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith)] with y hy
    exact lt_of_lt_of_le hn (measure_mono (Ioi_subset_Ioi hy.2.le))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact lt_of_le_of_lt (measure_mono (Ioi_subset_Ioi (le_of_lt hy))) ha

/-- **`lem:selfdecomposable-exponents`, the Choquet measure `ϖ`** — the trailing paragraph of
the node: the profile may be taken right-continuous with limit `0` at infinity, and then a
measure with those tails exists and satisfies the two integrability conditions.

Proved by taking the Choquet measure of `lem:cin-rays` (the quantile transform of
`CinRays.lean`) and reading the modification off it: `k'(x) := ϖ((x,∞)).toReal`. The tail
identity then holds at **every** positive point by construction rather than almost everywhere,
right continuity is continuity of `ϖ` from below, `k' = k` almost everywhere is the
specification, and the two integrability conditions are the layer cake identities above.

Finding F6 priced this node as downstream of an unwritten Stieltjes construction. It is not: the
construction it needs was written for `lem:cin-rays` in chapter 8, and no Stieltjes function
appears. Priced **M**, paid **S**. -/
theorem sd_exponents_profile_measure (Q : SDProfile) :
    ∃ (k : ℝ → ℝ) (ϖ : Measure ℝ),
      profileMeasure k = profileMeasure Q.k ∧
        AntitoneOn k (Ioi 0) ∧
        (∀ x : ℝ, 0 < x → ContinuousWithinAt k (Ioi x) x) ∧
        Tendsto k atTop (𝓝 0) ∧
        IsFolded ϖ ∧
        (∀ x : ℝ, 0 < x → ϖ (Ioi x) = ENNReal.ofReal (k x)) ∧
        (∫⁻ u, ENNReal.ofReal (min 1 (u ^ 2)) ∂ϖ) ≠ ⊤ ∧
        (∫⁻ u, ENNReal.ofReal (Real.log (max 1 u)) ∂ϖ) ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := cin_superposition_exists Q
  set k' : ℝ → ℝ := fun x => (ϖ (Ioi x)).toReal with hk'
  have hfin : ∀ x : ℝ, 0 < x → ϖ (Ioi x) ≠ ⊤ := fun x hx => measure_Ioi_ne_top hϖ hx
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), k' x = Q.k x := by
    filter_upwards [hϖ.2, self_mem_ae_restrict measurableSet_Ioi] with x hx hx0
    rw [hk']
    simp only
    rw [hx, ENNReal.toReal_ofReal (Q.k_nonneg x hx0)]
  refine ⟨k', ϖ, ?_, ?_, ?_, ?_, hϖ.1, ?_, lintegral_min_one_sq_ne_top hϖ,
    lintegral_log_max_one_ne_top hϖ⟩
  · rw [profileMeasure, profileMeasure]
    refine withDensity_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  · intro x hx y hy hxy
    exact (ENNReal.toReal_le_toReal (hfin y hy) (hfin x hx)).mpr
      (measure_mono (Ioi_subset_Ioi hxy))
  · intro x hx
    exact (ENNReal.tendsto_toReal (hfin x hx)).comp (tendsto_measure_Ioi_nhdsGT ϖ x)
  · refine tendsto_order.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards with y using lt_of_lt_of_le ha ENNReal.toReal_nonneg
      
    · obtain ⟨R, hR⟩ := eventually_atTop.mp (Q.tendsto_k_atTop.eventually (gt_mem_nhds ha))
      have hS0 : (0 : ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right R 1)
      obtain ⟨r, hr, heq⟩ := exists_tail_eq_mem_Ioo hϖ hS0 (lt_add_one (max R 1))
      have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hS0 hr.1
      have hrR : R ≤ r := le_trans (le_max_left R 1) hr.1.le
      filter_upwards [eventually_gt_atTop r] with y hy
      have hy0 : (0 : ℝ) < y := lt_trans hr0 hy
      have hle : k' y ≤ k' r :=
        (ENNReal.toReal_le_toReal (hfin y hy0) (hfin r hr0)).mpr
          (measure_mono (Ioi_subset_Ioi hy.le))
      have hkr : k' r = Q.k r := by
        rw [hk']
        simp only
        rw [heq, ENNReal.toReal_ofReal (Q.k_nonneg r (mem_Ioi.mpr hr0))]
      rw [hkr] at hle
      exact lt_of_le_of_lt hle (hR r hrR)
  · intro x hx
    exact (ENNReal.ofReal_toReal (hfin x hx)).symm


end Modification

end SpatialLine
