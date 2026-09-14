/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Representation
import SpatialLine.TransformBridge

/-!
# `lem:nonvanishing`: the transforms of the kernels never vanish

Blueprint: `blueprint/src/parts/04-representation.tex`, `lem:nonvanishing`.

The first statement of the article with no causal counterpart: on the half-line the positivity of
the transform was free, and here it costs (A6) and (A7). The lemma is what makes the exponent
`g_{s,t} = -log μ̂_{s,t}` well defined, and every later chapter depends on it.

## The elementary transform facts

`fourierCos μ ω = ∫ cos(ωx) dμ` needs a handful of facts the article uses everywhere: the value
`1` at `ω = 0` and at `δ₀`, the bound `|μ̂| ≤ 1`, evenness, continuity in `ω`, and the bridge to
Mathlib's `charFun` for a symmetric measure. Chapter 4 proved them in parallel with chapter 2,
and wave 1 of the proving campaign (2026-09-09) deduplicated them: the bridge
(`charFun_eq_fourierCos_of_symmetric`, `fourierCos_eq_charFun_re`) and the integrability of the
cosine integrand now live in `SpatialLine/TransformBridge.lean`, chapter 2's file, together
with the value at `δ₀`, which three chapters read; the remaining four value-and-continuity facts
stay here, where the node that consumes them is.

## What the proof consumes, and what it does not

The hypotheses are `PreCascadeCore` — literally (A1)–(A3), (A5)–(A7) — together with a kernel
family. (A4) enters only through the representation, and `IsKernelFamily.isProbability` is where
it has gone (SKELETON.md F4). No clause of `prop:fourier-toolbox` is used.

The symmetry of the kernels is `isSymmetric_of_reflL1`, *not* the node
`representation_symmetric`: the node's reviewed statement carries (A4) and (A5) as hypotheses,
which a `PreCascadeCore` does not supply, and its proof consumes neither. That is the finding of
judgement point 1 in the small, and it is why the single-operator form of the rider exists.

## The nonvanishing argument

The blueprint argues by the minimum of the (closed) zero set. The Lean runs the equivalent chain
argument, which needs no infimum: on the compact triangle `{(a,b) : s ≤ a ≤ b ≤ t}` the map
`(a,b) ↦ μ̂_{a,b}(ω)` is uniformly continuous and equals `1` on the diagonal, so there is a single
`δ > 0` with `μ̂_{a,b}(ω) > 1/2` whenever `b - a < δ`; multiplicativity then walks from `s` to `t`
in steps of `δ/2` by induction on the step count. The load-bearing hypothesis is the same one the
blueprint identifies — *joint* continuity in `(s,t)`, which is (A7) divided by the transform of a
zero-free test density, and where an indicator would not do.
-/

namespace SpatialLine

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The kernels of a cascade family

Everything here is the representation read through the axioms: the kernels are symmetric, they
convolve along the cascade, the diagonal one is `δ₀`, and their transforms are jointly continuous
in the parameters.
-/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- The operator is convolution by its kernel, as an identity of operators. -/
theorem Phi_eq_mconvL1 (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    [IsProbabilityMeasure (μ s t)] : Fam.Φ s t = mconvL1 (μ s t) :=
  eq_mconvL1_of_ae (hker.conv s t hs hst)

/-- **The kernels are symmetric.** (A3) and the uniqueness clause of the representation.

Note which form of the rider is used: `isSymmetric_of_reflL1`, not the node
`representation_symmetric`. The node carries (A4) and (A5) among its hypotheses, which a
`PreCascadeCore` does not supply and which its proof does not consume. -/
theorem isSymmetric_kernel (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    [IsProbabilityMeasure (μ s t)] : IsSymmetric (μ s t) :=
  isSymmetric_of_reflL1 (Phi_eq_mconvL1 hker hs hst) (Fam.reflection s t hs hst)

/-- **The kernels convolve along the cascade** — (A6) through the uniqueness clause. -/
theorem kernel_conv (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) : μ r t = μ r s ∗ μ s t := by
  haveI := hker.isProbability r s hr hrs
  haveI := hker.isProbability s t (hr.trans hrs) hst
  haveI := hker.isProbability r t hr (hrs.trans hst)
  refine mconvL1_injective ?_
  rw [← Phi_eq_mconvL1 hker hr (hrs.trans hst), ← mconvL1_comp,
    ← Phi_eq_mconvL1 hker hr hrs, ← Phi_eq_mconvL1 hker (hr.trans hrs) hst,
    Fam.cascade r s t hr hrs hst]

/-- **The diagonal kernel is `δ₀`** — (A6) through the uniqueness clause. -/
theorem kernel_diag (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ t t = Measure.dirac 0 := by
  haveI := hker.isProbability t t ht le_rfl
  refine mconvL1_injective ?_
  rw [← Phi_eq_mconvL1 hker ht le_rfl, Fam.diag t ht, mconvL1_dirac_zero]

/-- **The transforms multiply over adjacent intervals.** -/
theorem fourierCos_kernel_mul (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (μ r t) ω = fourierCos (μ r s) ω * fourierCos (μ s t) ω := by
  haveI := hker.isProbability r s hr hrs
  haveI := hker.isProbability s t (hr.trans hrs) hst
  haveI := hker.isProbability r t hr (hrs.trans hst)
  have hcx : ((fourierCos (μ r t) ω : ℝ) : ℂ)
      = ((fourierCos (μ r s) ω : ℝ) : ℂ) * ((fourierCos (μ s t) ω : ℝ) : ℂ) := by
    rw [← charFun_eq_fourierCos_of_symmetric (isSymmetric_kernel hker hr hrs),
      ← charFun_eq_fourierCos_of_symmetric (isSymmetric_kernel hker (hr.trans hrs) hst),
      ← charFun_eq_fourierCos_of_symmetric (isSymmetric_kernel hker hr (hrs.trans hst)),
      kernel_conv hker hr hrs hst, charFun_conv]
  exact_mod_cast hcx

/-- **The transforms are jointly continuous in the parameters.**

This is (A7) divided by the transform of the test density, and it is where the blueprint's remark
that "the test density must have a zero-free transform" is load-bearing: the Gaussian is used
because `charCLM_gaussL1_ne_zero`, and an indicator — whose transform vanishes on
`2πℤ ∖ {0}` — would not do. -/
theorem continuousOn_fourierCos_kernel (hker : IsKernelFamily Fam.Φ μ) (ω : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => fourierCos (μ p.1 p.2) ω)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} with hS
  have hA7 : ContinuousOn (fun p : ℝ × ℝ => Fam.Φ p.1 p.2 gaussL1) S := Fam.continuous gaussL1
  have hpair : ContinuousOn (fun p : ℝ × ℝ => charCLM ω (Fam.Φ p.1 p.2 gaussL1)) S :=
    (charCLM ω).continuous.comp_continuousOn hA7
  have hval : ∀ p ∈ S, ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ) * charCLM ω gaussL1
      = charCLM ω (Fam.Φ p.1 p.2 gaussL1) := by
    rintro p ⟨hp1, hp2⟩
    haveI := hker.isProbability p.1 p.2 hp1 hp2
    rw [Phi_eq_mconvL1 hker hp1 hp2, charCLM_mconvL1,
      charFun_eq_fourierCos_of_symmetric (isSymmetric_kernel hker hp1 hp2)]
  have hprod : ContinuousOn
      (fun p : ℝ × ℝ => ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ) * charCLM ω gaussL1) S :=
    hpair.congr hval
  have hcpx : ContinuousOn (fun p : ℝ × ℝ => ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ)) S := by
    have hne := charCLM_gaussL1_ne_zero ω
    refine (hprod.div_const (charCLM ω gaussL1)).congr fun p _ => ?_
    show ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ)
        = ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ) * charCLM ω gaussL1 / charCLM ω gaussL1
    rw [mul_div_assoc, div_self hne, mul_one]
  exact Complex.continuous_re.comp_continuousOn hcpx

/-! ## `lem:nonvanishing` -/

/-- **`lem:nonvanishing`, the nonvanishing clause.**

Reading: strict positivity of the *cosine* transform, at every frequency and every admissible
pair. The hypotheses are `PreCascadeCore` — literally (A1)–(A3), (A5)–(A7) — together with a
kernel family; (A4) enters only through the representation, and `IsKernelFamily.isProbability` is
where it has gone. -/
theorem nonvanishing (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    0 < fourierCos (μ s t) ω := by
  set G : ℝ × ℝ → ℝ := fun p => fourierCos (μ p.1 p.2) ω with hG
  -- the compact triangle `s ≤ a ≤ b ≤ t`
  set K : Set (ℝ × ℝ) := {p : ℝ × ℝ | s ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ t} with hK
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {p : ℝ × ℝ | s ≤ p.1} := isClosed_le continuous_const continuous_fst
    have h2 : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} := isClosed_le continuous_fst continuous_snd
    have h3 : IsClosed {p : ℝ × ℝ | p.2 ≤ t} := isClosed_le continuous_snd continuous_const
    have : K = {p : ℝ × ℝ | s ≤ p.1} ∩ ({p : ℝ × ℝ | p.1 ≤ p.2} ∩ {p : ℝ × ℝ | p.2 ≤ t}) := by
      ext p; simp [hK]
    rw [this]
    exact h1.inter (h2.inter h3)
  have hKsub : K ⊆ Icc s t ×ˢ Icc s t := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2.trans h3⟩, ⟨h1.trans h2, h3⟩⟩
  have hKcompact : IsCompact K :=
    IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) hKclosed hKsub
  have hKS : K ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
    rintro p ⟨h1, h2, _⟩
    exact ⟨hs.trans h1, h2⟩
  have hGK : ContinuousOn G K := (continuousOn_fourierCos_kernel hker ω).mono hKS
  -- a single `δ` from uniform continuity on the triangle
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hKcompact.uniformContinuousOn_of_continuous hGK) (1 / 2) (by norm_num)
  have hdiag : ∀ a : ℝ, 0 ≤ a → G (a, a) = 1 := by
    intro a ha
    simp only [hG, kernel_diag hker ha, fourierCos_dirac_zero]
  have hstep : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ t → b - a < δ → 0 < G (a, b) := by
    intro a b ha hab hbt hlt
    have hmemab : (a, b) ∈ K := ⟨ha, hab, hbt⟩
    have hmemaa : (a, a) ∈ K := ⟨ha, le_rfl, hab.trans hbt⟩
    have hdist : dist ((a, b) : ℝ × ℝ) (a, a) < δ := by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq, max_lt_iff]
      exact ⟨hδ, by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]; exact hlt⟩
    have := hunif _ hmemab _ hmemaa hdist
    rw [hdiag a (hs.trans ha), Real.dist_eq] at this
    have := abs_lt.mp this
    linarith [this.1]
  -- the chain from `s` to `t` in steps of `δ/2`
  set d : ℝ := δ / 2 with hd
  have hdpos : 0 < d := by positivity
  set r : ℕ → ℝ := fun n => min (s + n * d) t with hr
  have hrs : ∀ n, s ≤ r n := by
    intro n
    refine le_min ?_ hst
    nlinarith [Nat.cast_nonneg (α := ℝ) n, hdpos]
  have hrt : ∀ n, r n ≤ t := fun n => min_le_right _ _
  have hrmono : ∀ n, r n ≤ r (n + 1) := by
    intro n
    refine min_le_min ?_ le_rfl
    push_cast
    nlinarith [hdpos]
  have hrdiff : ∀ n, r (n + 1) - r n < δ := by
    intro n
    rcases le_total (s + n * d) t with h | h
    · have h1 : r n = s + n * d := min_eq_left h
      have h2 : r (n + 1) ≤ s + ((n : ℝ) + 1) * d := by
        rw [hr]
        push_cast
        exact min_le_left _ _
      rw [h1]
      nlinarith [hdpos]
    · have h1 : r n = t := min_eq_right h
      have h2 : r (n + 1) = t := by
        refine min_eq_right (le_trans h ?_)
        push_cast
        nlinarith [hdpos]
      rw [h1, h2]
      simpa using hδ
  have hind : ∀ n, 0 < fourierCos (μ s (r n)) ω := by
    intro n
    induction n with
    | zero =>
        have h0 : r 0 = s := by simp [hr, min_eq_left hst]
        rw [h0, kernel_diag hker hs, fourierCos_dirac_zero]
        norm_num
    | succ n ih =>
        rw [fourierCos_kernel_mul hker hs (hrs n) (hrmono n) ω]
        exact mul_pos ih (hstep (r n) (r (n + 1)) (hrs n) (hrmono n) (hrt (n + 1)) (hrdiff n))
  obtain ⟨n, hn⟩ := exists_nat_ge ((t - s) / d)
  have hreach : r n = t := by
    refine min_eq_right ?_
    have := (div_le_iff₀ hdpos).mp hn
    linarith
  rw [← hreach]
  exact hind n

/-- **`lem:nonvanishing`, the clauses on the exponent `g`.**

Reading: with nonvanishing in hand, `exponent (μ s t) = -log ∘ fourierCos (μ s t)` is the
blueprint's `g_{s,t}`, and the six clauses are: nonnegativity, evenness, continuity in `ω`, joint
continuity in `(s,t)` on the index set, `g_{t,t} = 0`, and `g_{s,t}(0) = 0`. -/
theorem nonvanishing_exponent (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) :
    (∀ s t, 0 ≤ s → s ≤ t → ∀ ω, 0 ≤ exponent (μ s t) ω) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ ω, exponent (μ s t) (-ω) = exponent (μ s t) ω) ∧
      (∀ s t, 0 ≤ s → s ≤ t → Continuous (exponent (μ s t))) ∧
      (∀ ω : ℝ, ContinuousOn (fun p : ℝ × ℝ => exponent (μ p.1 p.2) ω)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}) ∧
      (∀ t, 0 ≤ t → ∀ ω, exponent (μ t t) ω = 0) ∧
      (∀ s t, 0 ≤ s → s ≤ t → exponent (μ s t) 0 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hs hst ω
    haveI := hker.isProbability s t hs hst
    rw [exponent_apply, neg_nonneg]
    exact Real.log_nonpos (nonvanishing Fam μ hker hs hst ω).le (fourierCos_le_one (μ s t) ω)
  · intro s t _ _ ω
    simp only [exponent_apply, fourierCos_neg]
  · intro s t hs hst
    haveI := hker.isProbability s t hs hst
    exact ((continuous_fourierCos (μ s t)).log
      (fun ω => (nonvanishing Fam μ hker hs hst ω).ne')).neg
  · intro ω
    refine ContinuousOn.neg (ContinuousOn.log (continuousOn_fourierCos_kernel hker ω) ?_)
    rintro p ⟨hp1, hp2⟩
    exact (nonvanishing Fam μ hker hp1 hp2 ω).ne'
  · intro t ht ω
    rw [exponent_apply, kernel_diag hker ht, fourierCos_dirac_zero, Real.log_one, neg_zero]
  · intro s t hs hst
    haveI := hker.isProbability s t hs hst
    rw [exponent_apply, fourierCos_zero, Real.log_one, neg_zero]

end SpatialLine
