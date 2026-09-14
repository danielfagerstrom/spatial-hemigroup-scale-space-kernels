/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.DilationDecrease
import Mathlib.MeasureTheory.Measure.Prod

/-!
# A translation-decreasing measure has a nonincreasing density

Blueprint: the second half of `lem:selfdecomposable-exponents`(1) implies (3),
`blueprint/src/parts/07-characterization.tex` --- the paragraph that passes to the
log-displacement coordinate and calls the tail function convex. This file is that paragraph, and
it contains no analysis of exponents: after `SpatialLine.dilate_le_of_increments` the obligation
is about measures alone.

**Statement.** A measure `m` on the line, finite on every ray `(theta, infty)` and satisfying
`m(A + h) <= m(A)` for every `h > 0`, is `Lebesgue.withDensity f` for a **nonincreasing**
`f : R -> [0, infty]`.

## The route, and why it is not the blueprint's

The printed proof argues that `M(theta) := m((theta,infty))` is convex --- its increments over
intervals of fixed length are nonincreasing --- and takes `f = -M'`, the right derivative, which
a convex function has, which is monotone, and which integrates back to `M`. Every step of that
is in Mathlib (`ConvexOn.monotoneOn_rightDeriv`,
`ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`,
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`) **except the first**: what the shift
property gives directly is `M(theta) + M(theta + 2 delta) >= 2 M(theta + delta)`, midpoint
convexity, and Mathlib has no "midpoint convex plus continuous implies convex"
(`convexOn_of_slope_mono_adjacent` wants the adjacent-slope inequality at arbitrary triples).
Supplying it means the classical dyadic induction and a continuity passage, and the continuity of
`M` is itself a small argument --- an atom of mass `alpha` would force uncountably many atoms of
mass `alpha` to its left and make `M` infinite.

The route taken here avoids convexity altogether. Put

  `f(theta) := sup_n 2^n * m((theta, theta + 2^{-n}])`.

Each term is nonincreasing in `theta` by the shift property and nondecreasing in `n` because
`m((theta, theta + 2 delta]) <= 2 m((theta, theta + delta])` --- the shift property again --- so
`f` is **antitone by construction**: no modification, no almost-everywhere reasoning and no
Radon-Nikodym derivative appear, and the antitone function is the one the caller wants rather
than a representative of it. That `m((a,b]) = int_a^b f` is then monotone convergence and one
Tonelli:

  `int_{(a,b]} 2^n m((theta, theta + eps]) d theta = 2^n int |(a,b] cap [x - eps, x)| m(dx)`,

whose integrand is `eps` for `x` in `(a + eps, b]`, at most `eps` always, and `0` outside
`(a, b + eps]`. So the left-hand side is squeezed between `m((a + eps, b])` and `m((a, b + eps])`,
and both converge to `m((a,b])` --- from below by continuity of `m` from below, from above by
continuity from above, which is where the finiteness of the rays is spent.

The two measures then agree on every `(a,b]`, hence everywhere (`Measure.ext_of_Ioc'`).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {m : Measure ℝ}

/-! ## The shift property, in the two forms the construction uses -/

theorem measure_Ioc_shift_le (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m)
    {θ₁ θ₂ ε : ℝ} (h12 : θ₁ ≤ θ₂) :
    m (Ioc θ₂ (θ₂ + ε)) ≤ m (Ioc θ₁ (θ₁ + ε)) := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · exact le_rfl
  · have hh : 0 < θ₂ - θ₁ := by linarith
    have hmeas : Measurable fun θ : ℝ => θ - (θ₂ - θ₁) := by fun_prop
    have hpre : (fun θ : ℝ => θ - (θ₂ - θ₁)) ⁻¹' Ioc θ₁ (θ₁ + ε) = Ioc θ₂ (θ₂ + ε) := by
      ext y
      simp only [mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    have := hshift (θ₂ - θ₁) hh (Ioc θ₁ (θ₁ + ε))
    rwa [Measure.map_apply hmeas measurableSet_Ioc, hpre] at this

theorem measure_Ioc_double_le (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m)
    {θ ε : ℝ} (hε : 0 < ε) :
    m (Ioc θ (θ + 2 * ε)) ≤ 2 * m (Ioc θ (θ + ε)) := by
  have hdisj : Disjoint (Ioc θ (θ + ε)) (Ioc (θ + ε) (θ + 2 * ε)) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2)
  have hsplit : m (Ioc θ (θ + 2 * ε))
      = m (Ioc θ (θ + ε)) + m (Ioc (θ + ε) (θ + 2 * ε)) := by
    rw [← measure_union hdisj measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  have hle : m (Ioc (θ + ε) (θ + 2 * ε)) ≤ m (Ioc θ (θ + ε)) := by
    have h0 := measure_Ioc_shift_le hshift (θ₁ := θ) (θ₂ := θ + ε) (ε := ε) (by linarith)
    rwa [show θ + ε + ε = θ + 2 * ε by ring] at h0
  rw [hsplit]
  calc m (Ioc θ (θ + ε)) + m (Ioc (θ + ε) (θ + 2 * ε))
      ≤ m (Ioc θ (θ + ε)) + m (Ioc θ (θ + ε)) := add_le_add le_rfl hle
    _ = 2 * m (Ioc θ (θ + ε)) := (two_mul _).symm


theorem tonelli_window (m : Measure ℝ) [SFinite m] (a b ε : ℝ) :
    (∫⁻ θ in Ioc a b, m (Ioc θ (θ + ε)))
      = ∫⁻ x, volume (Ioc a b ∩ Ico (x - ε) x) ∂m := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ p.1 + ε} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const ε))
  have hfun : Measurable (S.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_one.indicator hS
  have hslice1 : ∀ θ x : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (θ, x)
      = (Ioc θ (θ + ε)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro θ x
    simp only [Set.indicator_apply, hSdef, mem_setOf_eq, mem_Ioc]
  have hslice2 : ∀ θ x : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (θ, x)
      = (Ico (x - ε) x).indicator (fun _ => (1 : ℝ≥0∞)) θ := by
    intro θ x
    simp only [Set.indicator_apply, hSdef, mem_setOf_eq, mem_Ico]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linarith⟩
  have hswap := lintegral_lintegral_swap
    (μ := volume.restrict (Ioc a b)) (ν := m)
    (f := fun θ x => S.indicator (fun _ => (1 : ℝ≥0∞)) (θ, x)) hfun.aemeasurable
  have hL : ∀ θ : ℝ, (∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) (θ, x) ∂m)
      = m (Ioc θ (θ + ε)) := by
    intro θ
    simp only [hslice1 θ]
    rw [lintegral_indicator measurableSet_Ioc, setLIntegral_one]
  have hR : ∀ x : ℝ, (∫⁻ θ in Ioc a b, S.indicator (fun _ => (1 : ℝ≥0∞)) (θ, x))
      = volume (Ioc a b ∩ Ico (x - ε) x) := by
    intro x
    simp only [hslice2 _ x]
    rw [lintegral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
      setLIntegral_one, Set.inter_comm]
  simp only [hL, hR] at hswap
  exact hswap


theorem two_pow_mul_ofReal_half_pow (n : ℕ) :
    (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = 1 := by
  have h2 : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h1 : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), h2]
    simp [ENNReal.inv_pow]
  rw [h1, ENNReal.mul_inv_cancel (by positivity) (by finiteness)]

theorem sandwich_upper (m : Measure ℝ) [SFinite m] (a b ε : ℝ) :
    (∫⁻ x, volume (Ioc a b ∩ Ico (x - ε) x) ∂m)
      ≤ ENNReal.ofReal ε * m (Ioc a (b + ε)) := by
  have hle : ∀ x : ℝ, volume (Ioc a b ∩ Ico (x - ε) x)
      ≤ (Ioc a (b + ε)).indicator (fun _ => ENNReal.ofReal ε) x := by
    intro x
    by_cases hx : x ∈ Ioc a (b + ε)
    · rw [Set.indicator_of_mem hx]
      refine le_trans (measure_mono Set.inter_subset_right) ?_
      rw [Real.volume_Ico]
      exact le_of_eq (by ring_nf)
    · rw [Set.indicator_of_notMem hx]
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
      have hempty : Ioc a b ∩ Ico (x - ε) x = ∅ := by
        ext θ
        simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, h2⟩, h3, h4⟩
        rcases hx with hx | hx
        · linarith
        · linarith
      rw [hempty, measure_empty]
  calc (∫⁻ x, volume (Ioc a b ∩ Ico (x - ε) x) ∂m)
      ≤ ∫⁻ x, (Ioc a (b + ε)).indicator (fun _ => ENNReal.ofReal ε) x ∂m := lintegral_mono hle
    _ = ENNReal.ofReal ε * m (Ioc a (b + ε)) := by
        rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, mul_comm]

theorem sandwich_lower (m : Measure ℝ) [SFinite m] (a b ε : ℝ) :
    ENNReal.ofReal ε * m (Ioc (a + ε) b)
      ≤ ∫⁻ x, volume (Ioc a b ∩ Ico (x - ε) x) ∂m := by
  have hge : ∀ x : ℝ, (Ioc (a + ε) b).indicator (fun _ => ENNReal.ofReal ε) x
      ≤ volume (Ioc a b ∩ Ico (x - ε) x) := by
    intro x
    by_cases hx : x ∈ Ioc (a + ε) b
    · rw [Set.indicator_of_mem hx]
      have hsub : Ico (x - ε) x ⊆ Ioc a b := by
        rintro θ ⟨h1, h2⟩
        obtain ⟨hx1, hx2⟩ := hx
        exact ⟨by linarith, by linarith⟩
      rw [Set.inter_eq_self_of_subset_right hsub, Real.volume_Ico]
      exact le_of_eq (by ring_nf)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc ENNReal.ofReal ε * m (Ioc (a + ε) b)
      = ∫⁻ x, (Ioc (a + ε) b).indicator (fun _ => ENNReal.ofReal ε) x ∂m := by
        rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x, volume (Ioc a b ∩ Ico (x - ε) x) ∂m := lintegral_mono hge


/-! ## The dyadic difference quotients -/

/-- `m` is σ-finite as soon as its rays are finite: `ℝ = ⋃ₙ (-n, ∞)`. -/
theorem sigmaFinite_of_measure_Ioi_ne_top (hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤) : SigmaFinite m := by
  refine ⟨⟨⟨fun n : ℕ => Ioi (-(n : ℝ)), fun n => trivial, fun n => ?_, ?_⟩⟩⟩
  · exact lt_top_iff_ne_top.mpr (hfin _)
  · ext x
    simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by linarith⟩

/-- The `n`-th dyadic difference quotient of the tail, `2ⁿ m((θ, θ+2⁻ⁿ])`. -/
noncomputable def dyadicTerm (m : Measure ℝ) (n : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ n * m (Ioc θ (θ + (1 / 2 : ℝ) ^ n))

/-- **The density**, defined as the supremum of the dyadic difference quotients. Antitone by
construction, being a supremum of antitone functions. -/
noncomputable def dyadicDensity (m : Measure ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, dyadicTerm m n θ

theorem antitone_dyadicTerm
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) (n : ℕ) :
    Antitone (dyadicTerm m n) := fun _ _ h12 =>
  mul_le_mul_left' (measure_Ioc_shift_le hshift h12) _

theorem measurable_dyadicTerm
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) (n : ℕ) :
    Measurable (dyadicTerm m n) := (antitone_dyadicTerm hshift n).measurable

/-- Halving the window at least doubles the quotient — the shift property again, and what makes
the supremum a limit of a monotone sequence, so that monotone convergence applies. -/
theorem monotone_dyadicTerm
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) :
    Monotone (dyadicTerm m) := by
  refine monotone_nat_of_le_succ fun n => ?_
  intro θ
  have hd := measure_Ioc_double_le hshift (θ := θ) (ε := (1 / 2 : ℝ) ^ (n + 1)) (by positivity)
  rw [show 2 * (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n by rw [pow_succ]; ring] at hd
  calc dyadicTerm m n θ ≤ (2 : ℝ≥0∞) ^ n * (2 * m (Ioc θ (θ + (1 / 2 : ℝ) ^ (n + 1)))) := by
        rw [dyadicTerm]
        exact mul_le_mul_left' hd _
    _ = dyadicTerm m (n + 1) θ := by rw [dyadicTerm, pow_succ (2 : ℝ≥0∞) n, mul_assoc]

theorem antitone_dyadicDensity
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) :
    Antitone (dyadicDensity m) := fun _ _ h12 =>
  iSup_mono fun n => antitone_dyadicTerm hshift n h12

/-! ## The integral identity -/

theorem setLIntegral_dyadicTerm (m : Measure ℝ) [SFinite m] (n : ℕ) (a b : ℝ) :
    (∫⁻ θ in Ioc a b, dyadicTerm m n θ)
      = (2 : ℝ≥0∞) ^ n * ∫⁻ x, volume (Ioc a b ∩ Ico (x - (1 / 2 : ℝ) ^ n) x) ∂m := by
  simp only [dyadicTerm]
  rw [lintegral_const_mul' _ _ (by finiteness), tonelli_window]

theorem dyadicTerm_integral_lower (m : Measure ℝ) [SFinite m] (n : ℕ) (a b : ℝ) :
    m (Ioc (a + (1 / 2 : ℝ) ^ n) b) ≤ ∫⁻ θ in Ioc a b, dyadicTerm m n θ := by
  rw [setLIntegral_dyadicTerm]
  calc m (Ioc (a + (1 / 2 : ℝ) ^ n) b)
      = (2 : ℝ≥0∞) ^ n * (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)
          * m (Ioc (a + (1 / 2 : ℝ) ^ n) b)) := by
        rw [← mul_assoc, two_pow_mul_ofReal_half_pow, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ n * ∫⁻ x, volume (Ioc a b ∩ Ico (x - (1 / 2 : ℝ) ^ n) x) ∂m :=
        mul_le_mul_left' (sandwich_lower m a b _) _

theorem dyadicTerm_integral_upper (m : Measure ℝ) [SFinite m] (n : ℕ) (a b : ℝ) :
    (∫⁻ θ in Ioc a b, dyadicTerm m n θ) ≤ m (Ioc a (b + (1 / 2 : ℝ) ^ n)) := by
  rw [setLIntegral_dyadicTerm]
  calc (2 : ℝ≥0∞) ^ n * ∫⁻ x, volume (Ioc a b ∩ Ico (x - (1 / 2 : ℝ) ^ n) x) ∂m
      ≤ (2 : ℝ≥0∞) ^ n * (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)
          * m (Ioc a (b + (1 / 2 : ℝ) ^ n))) := mul_le_mul_left' (sandwich_upper m a b _) _
    _ = m (Ioc a (b + (1 / 2 : ℝ) ^ n)) := by
        rw [← mul_assoc, two_pow_mul_ofReal_half_pow, one_mul]

theorem tendsto_half_pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem antitone_half_pow : Antitone fun n : ℕ => (1 / 2 : ℝ) ^ n := fun _ _ hpq =>
  pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq

/-- **The integral identity.** The density integrates back to the measure on every `(a,b]`. -/
theorem setLIntegral_dyadicDensity (hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤)
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) (a b : ℝ) :
    (∫⁻ θ in Ioc a b, dyadicDensity m θ) = m (Ioc a b) := by
  haveI : SigmaFinite m := sigmaFinite_of_measure_Ioi_ne_top hfin
  have hsup : (∫⁻ θ in Ioc a b, dyadicDensity m θ)
      = ⨆ n : ℕ, ∫⁻ θ in Ioc a b, dyadicTerm m n θ := by
    simp only [dyadicDensity]
    exact lintegral_iSup (fun n => measurable_dyadicTerm hshift n) (monotone_dyadicTerm hshift)
  rw [hsup]
  refine le_antisymm ?_ ?_
  · have hanti : Antitone fun n : ℕ => Ioc a (b + (1 / 2 : ℝ) ^ n) := by
      intro p q hpq
      exact Ioc_subset_Ioc le_rfl (by linarith [antitone_half_pow hpq])
    have hinter : (⋂ n : ℕ, Ioc a (b + (1 / 2 : ℝ) ^ n)) = Ioc a b := by
      ext x
      simp only [mem_iInter, mem_Ioc]
      constructor
      · intro hx
        refine ⟨(hx 0).1, ?_⟩
        have htb : Tendsto (fun n : ℕ => b + (1 / 2 : ℝ) ^ n) atTop (𝓝 b) := by
          simpa using tendsto_const_nhds.add tendsto_half_pow
        exact ge_of_tendsto htb (Eventually.of_forall fun n => (hx n).2)
      · rintro ⟨h1, h2⟩ n
        exact ⟨h1, by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]⟩
    have htend := tendsto_measure_iInter_atTop (μ := m)
      (fun n => (measurableSet_Ioc).nullMeasurableSet) hanti
      ⟨0, ne_top_of_le_ne_top (hfin a) (measure_mono Ioc_subset_Ioi_self)⟩
    rw [hinter] at htend
    refine iSup_le fun n => ge_of_tendsto htend (eventually_atTop.mpr ⟨n, fun k hk => ?_⟩)
    exact le_trans (lintegral_mono (monotone_dyadicTerm hshift hk))
      (dyadicTerm_integral_upper m k a b)
  · have hmono : Monotone fun n : ℕ => Ioc (a + (1 / 2 : ℝ) ^ n) b := by
      intro p q hpq
      exact Ioc_subset_Ioc (by linarith [antitone_half_pow hpq]) le_rfl
    have hunion : (⋃ n : ℕ, Ioc (a + (1 / 2 : ℝ) ^ n) b) = Ioc a b := by
      ext x
      simp only [mem_iUnion, mem_Ioc]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨by linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n], h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := (tendsto_half_pow.eventually (gt_mem_nhds (by linarith : (0:ℝ) < x - a))).exists
        exact ⟨n, by linarith, h2⟩
    have htend := tendsto_measure_iUnion_atTop (μ := m) hmono
    rw [hunion] at htend
    refine le_of_tendsto htend (Eventually.of_forall fun n => ?_)
    exact le_trans (dyadicTerm_integral_lower m n a b)
      (le_iSup (fun k : ℕ => ∫⁻ θ in Ioc a b, dyadicTerm m k θ) n)

/-! ## The density -/

/-- **A translation-decreasing measure is `Lebesgue.withDensity` of its dyadic density.** -/
theorem eq_withDensity_dyadicDensity (hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤)
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) :
    m = volume.withDensity (dyadicDensity m) := by
  refine Measure.ext_of_Ioc' m _ (fun a b _ => ?_) (fun a b _ => ?_)
  · exact ne_top_of_le_ne_top (hfin a) (measure_mono Ioc_subset_Ioi_self)
  · rw [withDensity_apply _ measurableSet_Ioc, setLIntegral_dyadicDensity hfin hshift a b]

/-- **The second half of `lem:selfdecomposable-exponents`(1) ⟹ (3), as a statement about
measures.** A measure on the line, finite on every ray and decreasing under every right
translation, has a nonincreasing density against Lebesgue measure.

The density is `dyadicDensity`, antitone by construction rather than by modification; see the
module docstring for why the route is not the blueprint's convexity argument. -/
theorem exists_antitone_density (hfin : ∀ θ : ℝ, m (Ioi θ) ≠ ⊤)
    (hshift : ∀ h : ℝ, 0 < h → Measure.map (fun θ : ℝ => θ - h) m ≤ m) :
    ∃ f : ℝ → ℝ≥0∞, Antitone f ∧ m = volume.withDensity f :=
  ⟨dyadicDensity m, antitone_dyadicDensity hshift, eq_withDensity_dyadicDensity hfin hshift⟩

end SpatialLine
