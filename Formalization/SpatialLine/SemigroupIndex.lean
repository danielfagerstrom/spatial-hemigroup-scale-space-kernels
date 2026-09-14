/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.StableProfile
import SpatialLine.NoLattice
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# `cor:semigroup-case`: a one-parameter family is a symmetric stable family

Blueprint: `cor:semigroup-case`, the index clause.

## The two functional equations, and where Mathlib does the work

The proof runs two Cauchy equations, and both are reduced to one Mathlib theorem,
`map_real_smul`: a *continuous* additive map between real vector spaces is `ℝ`-linear.

1. **In the scale.** One-parametricity makes `μ_{0,t}` and `μ_{s,s+t}` the kernels of the same
   operator, hence equal (`mconvL1_injective`), so `t ↦ g_{0,t}(ω)` is additive on `[0,∞)`; it
   is continuous there by `lem:additivity`. `eq_mul_of_addOn_of_continuousOn` extends such a
   function to an additive continuous function on all of `ℝ` — the odd extension — and reads
   off `G(t) = t\,G(1)`.

2. **In the frequency.** `eq:similarity` with (1) gives `S_λ(1)\,g(ω) = g(λω)`, and at `ω = 1`
   the normalisation makes `S_λ(1) = g(λ)`, so `g` is multiplicative on `(0,∞)`. Conjugating by
   `exp`/`log` — legitimate because `lem:no-lattice` makes `g` strictly positive off the origin
   — turns that into the additive equation again, and `map_real_smul` gives `g(x) = x^α`.

Evenness of the exponent extends the formula to `ω < 0`, and `g(0) = 0` covers the origin once
`α ≠ 0` is known.

## The two bounds on the index

`α > 0` is continuity at the origin: for `α ≤ 0` the value `x^α` is at least `1` on `(0,1]`,
which no function continuous at `0` with value `0` there can do.

`α ≤ 2` is `lem:quadratic-growth`, and this is the one reroute in the chapter — the printed
proof cites a growth estimate for continuous negative definite functions. The comparison is
made explicit rather than asymptotically: the normalisation `g(1) = 1` forces the growth
constant `C ≥ 1/2`, and `ω = (2C+1)^{1/(α-2)}` is a frequency at which `|ω|^α > C(1+ω^2)` if
`α > 2`.

**Against the estimate.** The skeleton priced the node **M** and named "the Cauchy-equation step
assembled with `covariance_similarity`, which is bookkeeping rather than analysis". The
bookkeeping is right, but the estimate did not price the *first* Cauchy equation, in the scale
variable, which the printed proof hides inside the phrase "homogeneity gives
`g_{s,t} = (t-s)g`". That step needs the odd extension and is the longest part of the file.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Cauchy's equation on the half-line -/

/-- **An additive function, continuous on `[0,∞)`, is linear there.**

The odd extension is additive and continuous on all of `ℝ`, and a continuous additive map of
real vector spaces is `ℝ`-linear (`map_real_smul`). -/
theorem eq_mul_of_addOn_of_continuousOn {G : ℝ → ℝ}
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → G (s + t) = G s + G t)
    (hcont : ContinuousOn G (Ici 0)) : ∀ t : ℝ, 0 ≤ t → G t = t * G 1 := by
  have hG0 : G 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    simp only [add_zero] at h
    linarith
  -- `G'` is `G` restricted to the half-line, continuous everywhere
  set G' : ℝ → ℝ := fun x => G (max x 0) with hG'def
  have hG'cont : Continuous G' :=
    hcont.comp_continuous (by fun_prop) fun x => le_max_right x 0
  have hG'eq : ∀ x : ℝ, 0 ≤ x → G' x = G x := fun x hx => by
    rw [hG'def]
    simp only
    rw [max_eq_left hx]
  have hG'0 : G' 0 = 0 := by rw [hG'eq 0 le_rfl, hG0]
  -- the odd extension
  set H : ℝ → ℝ := fun x => if 0 ≤ x then G' x else -G' (-x) with hHdef
  have hHpos : ∀ x : ℝ, 0 ≤ x → H x = G x := by
    intro x hx
    rw [hHdef]
    simp only [if_pos hx]
    exact hG'eq x hx
  have hHneg : ∀ x : ℝ, x < 0 → H x = -G (-x) := by
    intro x hx
    rw [hHdef]
    simp only [if_neg (not_le.mpr hx)]
    rw [hG'eq (-x) (by linarith)]
  have hHcont : Continuous H := by
    have h1 : Continuous fun x : ℝ => -G' (-x) := (hG'cont.comp continuous_neg).neg
    exact Continuous.if_le (f := fun _ : ℝ => (0 : ℝ)) (g := fun x : ℝ => x)
      hG'cont h1 continuous_const continuous_id
      (fun x hx => by simp [← hx, hG'0])
  -- additivity of the extension
  have hsub : ∀ a b : ℝ, 0 ≤ b → 0 ≤ a - b → G a = G b + G (a - b) := by
    intro a b hb hab
    have h := hadd b (a - b) hb hab
    rwa [show b + (a - b) = a by ring] at h
  have hkey : ∀ x y : ℝ, 0 ≤ x → H (x + y) = H x + H y := by
    intro x y hx
    rcases le_or_gt 0 y with hy | hy
    · rw [hHpos x hx, hHpos y hy, hHpos (x + y) (by linarith), hadd x y hx hy]
    · rcases le_or_gt 0 (x + y) with hxy | hxy
      · rw [hHpos (x + y) hxy, hHpos x hx, hHneg y hy]
        have h := hsub x (x + y) hxy (by linarith)
        rw [show x - (x + y) = -y by ring] at h
        linarith
      · rw [hHneg (x + y) hxy, hHpos x hx, hHneg y hy]
        have h := hsub (-y) x hx (by linarith)
        rw [show -y - x = -(x + y) by ring] at h
        linarith
  have hHadd : ∀ x y : ℝ, H (x + y) = H x + H y := by
    intro x y
    rcases le_or_gt 0 x with hx | hx
    · exact hkey x y hx
    rcases le_or_gt 0 y with hy | hy
    · rw [add_comm, hkey y x hy, add_comm]
    · rw [hHneg (x + y) (by linarith), hHneg x hx, hHneg y hy,
        show -(x + y) = -x + -y by ring, hadd (-x) (-y) (by linarith) (by linarith)]
      ring
  -- linearity
  intro t ht
  have hlin : H (t • (1 : ℝ)) = t • H 1 :=
    map_real_smul (AddMonoidHom.mk' H hHadd) hHcont t 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at hlin
  rw [← hHpos t ht, ← hHpos 1 zero_le_one]
  exact hlin

/-- **A continuous multiplicative function on `(0,∞)` is a power.** -/
theorem exists_eq_rpow_of_mul {g : ℝ → ℝ} (hcont : Continuous g)
    (hpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x * g y) :
    ∃ α : ℝ, ∀ x : ℝ, 0 < x → g x = x ^ α := by
  set h : ℝ → ℝ := fun u => Real.log (g (Real.exp u)) with hhdef
  have hgexp : ∀ u : ℝ, 0 < g (Real.exp u) := fun u => hpos _ (Real.exp_pos u)
  have hhadd : ∀ u v : ℝ, h (u + v) = h u + h v := by
    intro u v
    rw [hhdef]
    simp only
    rw [Real.exp_add, hmul _ _ (Real.exp_pos u) (Real.exp_pos v),
      Real.log_mul (hgexp u).ne' (hgexp v).ne']
  have hhcont : Continuous h := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    exact ContinuousAt.log ((hcont.comp Real.continuous_exp).continuousAt) (hgexp u).ne'
  refine ⟨h 1, fun x hx => ?_⟩
  have hlin : h (Real.log x • (1 : ℝ)) = Real.log x • h 1 :=
    map_real_smul (AddMonoidHom.mk' h hhadd) hhcont (Real.log x) 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at hlin
  have hlx : h (Real.log x) = Real.log (g x) := by
    show Real.log (g (Real.exp (Real.log x))) = Real.log (g x)
    rw [Real.exp_log hx]
  rw [hlx] at hlin
  rw [Real.rpow_def_of_pos hx, ← hlin, Real.exp_log (hpos x hx)]

/-! ## The index -/

/-- **`cor:semigroup-case`.** A one-parameter symmetric cascade measurement family has a pure
power exponent, of index in `(0,2]`. -/
theorem semigroup_case (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S)
    (honeparam : ∀ s t s' t' : ℝ, 0 ≤ s → s ≤ t → 0 ≤ s' → s' ≤ t' → t - s = t' - s' →
      Fam.Φ s t = Fam.Φ s' t')
    (hnorm : exponent (μ 0 1) 1 = 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ ∀ ω : ℝ, exponent (μ 0 1) ω = |ω| ^ α := by
  set g : ℝ → ℝ := exponent (μ 0 1) with hgdef
  -- (1) one-parametricity identifies the kernels, so the exponent is linear in the scale
  have hkernel : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → μ 0 t = μ s (s + t) := by
    intro s t hs ht
    haveI := hker.isProbability 0 t le_rfl ht
    haveI := hker.isProbability s (s + t) hs (by linarith)
    refine mconvL1_injective ?_
    rw [← Phi_eq_mconvL1 hker le_rfl ht, ← Phi_eq_mconvL1 hker hs (by linarith)]
    exact honeparam 0 t s (s + t) le_rfl ht hs (by linarith) (by ring)
  have hlin : ∀ t ω : ℝ, 0 ≤ t → exponent (μ 0 t) ω = t * g ω := by
    intro t ω ht
    refine eq_mul_of_addOn_of_continuousOn (G := fun u => exponent (μ 0 u) ω) ?_ ?_ t ht
    · intro a b ha hb
      show exponent (μ 0 (a + b)) ω = exponent (μ 0 a) ω + exponent (μ 0 b) ω
      rw [exponent_add hker le_rfl ha (by linarith : a ≤ a + b) ω, ← hkernel a b ha hb]
    · exact continuousOn_exponent hker ω
  -- (2) the exponent is multiplicative in the frequency
  have hSnn : ∀ lam : ℝ, 0 < lam → 0 ≤ S lam 1 := fun lam hlam =>
    hcov.S_mapsTo lam hlam hlam (by norm_num : (1 : ℝ) ∈ Ici 0)
  have hsim : ∀ lam ω : ℝ, 0 < lam → S lam 1 * g ω = g (lam * ω) := by
    intro lam ω hlam
    have h := covariance_similarity Fam.toPreCascadeCore μ hker S hcov lam 1 ω hlam zero_le_one
    rw [hlin (S lam 1) ω (hSnn lam hlam)] at h
    exact h
  have hSval : ∀ lam : ℝ, 0 < lam → S lam 1 = g lam := by
    intro lam hlam
    have h := hsim lam 1 hlam
    simp only [hnorm, mul_one] at h
    exact h
  have hmul : ∀ x y : ℝ, 0 < x → 0 < y → g (x * y) = g x * g y := by
    intro x y hx _
    rw [← hsim x y hx, hSval x hx]
  -- the exponent is continuous and strictly positive off the origin
  have hgcont : Continuous g := continuous_exponent hker zero_le_one
  have hgpos : ∀ ω : ℝ, ω ≠ 0 → 0 < g ω :=
    (no_lattice Fam.toPreCascadeCore μ hker Fam.nondegenerate S hcov zero_lt_one).2
  have hg0 : g 0 = 0 := exponent_atZero hker zero_le_one
  obtain ⟨α, hα⟩ := exists_eq_rpow_of_mul hgcont (fun x hx => hgpos x hx.ne') hmul
  -- `α > 0`, by continuity at the origin
  have hαpos : 0 < α := by
    by_contra hcon
    have hle : α ≤ 0 := not_lt.mp hcon
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hgcont.continuousAt (x := 0)) 1 one_pos
    set x : ℝ := min (δ / 2) 1 with hxdef
    have hx0 : 0 < x := lt_min (by linarith) one_pos
    have hx1 : x ≤ 1 := min_le_right _ _
    have hxδ : dist x 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      calc x ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    have hb := hball hxδ
    rw [Real.dist_eq, hg0, sub_zero, hα x hx0] at hb
    have hone : (1 : ℝ) ≤ x ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hle
      rwa [Real.rpow_zero] at this
    rw [abs_of_nonneg (le_trans zero_le_one hone)] at hb
    linarith
  -- `α ≤ 2`, by the quadratic growth bound
  have hαle : α ≤ 2 := by
    obtain ⟨P, hP⟩ := increments_levy Fam.toPreCascadeCore μ hker le_rfl zero_le_one
    obtain ⟨hCfin, hbound⟩ := P.quadratic_growth
    set Cr : ℝ := (ENNReal.ofReal P.a
      + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν) + 2 * P.ν (Ioi 1)).toReal
      with hCr
    have hCnn : 0 ≤ Cr := ENNReal.toReal_nonneg
    have hgle : ∀ ω : ℝ, g ω ≤ Cr * (1 + ω ^ 2) := by
      intro ω
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hCfin ENNReal.ofReal_ne_top) (hbound ω)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by nlinarith [sq_nonneg ω])] at h
      rw [hgdef, hP ω]
      exact h
    have hC2 : (1 : ℝ) ≤ 2 * Cr := by
      have h1 : g 1 ≤ Cr * (1 + 1 ^ 2) := hgle 1
      rw [hnorm] at h1
      nlinarith
    by_contra hcon
    have hβ : 0 < α - 2 := by linarith [not_le.mp hcon]
    set M : ℝ := 2 * Cr + 1 with hM
    have hM1 : (1 : ℝ) ≤ M := by rw [hM]; linarith
    have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
    set ω : ℝ := M ^ (1 / (α - 2)) with hωdef
    have hω1 : (1 : ℝ) ≤ ω := by
      have := Real.rpow_le_rpow_of_exponent_le hM1 (by positivity : (0 : ℝ) ≤ 1 / (α - 2))
      rwa [Real.rpow_zero] at this
    have hω0 : (0 : ℝ) < ω := lt_of_lt_of_le zero_lt_one hω1
    have hpow : ω ^ (α - 2) = M := by
      rw [hωdef, ← Real.rpow_mul hM0.le, one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one]
    have hsplit : ω ^ α = ω ^ (2 : ℕ) * ω ^ (α - 2) := by
      rw [← Real.rpow_natCast ω 2, ← Real.rpow_add hω0]
      norm_num
    have hgω : g ω = ω ^ α := hα ω hω0
    have hsq : (1 : ℝ) ≤ ω ^ (2 : ℕ) := by nlinarith
    have hle := hgle ω
    rw [hgω, hsplit, hpow] at hle
    nlinarith [hle, hsq, hCnn, hM1]
  refine ⟨α, hαpos, hαle, fun ω => ?_⟩
  show g ω = |ω| ^ α
  rcases lt_trichotomy ω 0 with hω | hω | hω
  · have hneg : g ω = g (-ω) := (exponent_neg (μ 0 1) ω).symm
    rw [hneg, hα (-ω) (by linarith), abs_of_neg hω]
  · rw [hω, hg0, abs_zero, Real.zero_rpow hαpos.ne']
  · rw [hα ω hω, abs_of_pos hω]

end SpatialLine
