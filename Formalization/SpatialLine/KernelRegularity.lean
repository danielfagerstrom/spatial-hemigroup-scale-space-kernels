/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.MainAnalysis

/-!
# `prop:kernel-regularity`, the assembly

Blueprint: `prop:kernel-regularity`, `blueprint/src/parts/07-characterization.tex`.

The interface proper is the axiom `SpatialLine.kernel_regularity_law` in
`SpatialLine/Interfaces.lean`, ledger **A8** and **A9**. This file is the *assembly*: it checks
the interface's hypotheses for the kernels from the origin, and that check is `[T]`.

## What the assembly actually needs, and it is less than the node's proof cites

The blueprint's annotation routes the hypothesis check through
`lem:selfdecomposable-exponents` and `thm:main-characterization` for self-decomposability and
through `prop:strict-positivity`(2) for nondegeneracy. **Neither is needed.** Read the
obligation rather than the argument:

* **Self-decomposability of `μ_{0,t}` is `prop:canonical-gauge` plus `lem:additivity`.** For
  `b > 1` the factor law required by `def:self-decomposable` is an *increment of the family
  itself*: the gauge is onto `[0,∞)`, so some scale `t' < t` has `χ(t') = χ(t)/b`, and the
  exponents add, so `μ_{t',t}` has exactly the missing transform. No Lévy pair, no profile form,
  and no interface — the whole clause is a change of scale. In particular the assembly does not
  wait on `lem:selfdecomposable-exponents`(1) ⟹ (3), which is what the printed route would have
  made it wait on.

* **Nondegeneracy needs only that *some* frequency is moved**, which is
  `prop:canonical-gauge`'s last clause. `δ₀` has cosine transform `1` everywhere, so its
  exponent vanishes everywhere; the gauge carries the frequency at which `F` does not vanish
  back to scale `t`. This is the third time in the chapter that "some frequency is moved" is
  the cheap substitute for `prop:strict-positivity`(2) — after (ND) in the construction
  direction and the gauge's own nondegeneracy.

So the assembly spends the two ledger entries and Lean core, and its `#print axioms` shows
exactly `kernel_regularity_law`. The blueprint's proof of record is rewritten to this route.

Proving campaign, chapter 7, wave 3 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- **The kernels from the origin are self-decomposable.**

`def:self-decomposable` asks, for each `b > 1`, for a probability law whose transform is the
missing factor. Here it is an increment of the family: `χ` is onto `[0,∞)`, so `χ(t)/b` is
`χ(t')` for some `t' ≤ t`, and `lem:additivity` makes `μ_{t',t}` the factor. -/
theorem isSelfDecomposable_kernel (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    IsSelfDecomposable (μ 0 t) := by
  obtain ⟨-, χ, hχ0, hχm, hχs, -, -, hgauge, -, -⟩ := canonical_gauge Fam μ hker hnd S hcov
  have hχt : 0 < χ t := by
    have h := hχm Set.self_mem_Ici (ht.le : t ∈ Ici (0 : ℝ)) ht
    rwa [hχ0] at h
  intro b hb
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hquot : 0 < χ t / b := div_pos hχt hb0
  obtain ⟨t', ht'mem, ht'⟩ := hχs (le_of_lt hquot : χ t / b ∈ Ici (0 : ℝ))
  have ht'0 : (0 : ℝ) ≤ t' := ht'mem
  have ht't : t' ≤ t := by
    by_contra hcon
    have hlt : t < t' := lt_of_not_ge hcon
    have h := hχm (ht.le : t ∈ Ici (0 : ℝ)) ht'mem hlt
    rw [ht'] at h
    exact absurd h (not_lt.2 (div_lt_self hχt hb).le)
  haveI := hker.isProbability 0 t le_rfl ht.le
  haveI := hker.isProbability t' t ht'0 ht't
  refine ⟨μ t' t, hker.isProbability t' t ht'0 ht't, fun ω => ?_⟩
  rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker le_rfl ht.le) ω,
    charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker le_rfl ht.le) (ω / b),
    charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker ht'0 ht't) ω,
    ← Complex.ofReal_mul, Complex.ofReal_inj]
  have e1 : fourierCos (μ 0 t) ω = Real.exp (-(exponent (μ 0 1) (χ t * ω))) := by
    rw [fourierCos_eq_exp_neg_exponent hker le_rfl ht.le ω, hgauge t ω ht.le]
  have e2 : fourierCos (μ 0 t) (ω / b) = Real.exp (-(exponent (μ 0 1) (χ t / b * ω))) := by
    rw [fourierCos_eq_exp_neg_exponent hker le_rfl ht.le (ω / b), hgauge t (ω / b) ht.le]
    congr 2
    field_simp
  have e3 : fourierCos (μ t' t) ω
      = Real.exp (-(exponent (μ 0 1) (χ t * ω) - exponent (μ 0 1) (χ t / b * ω))) := by
    rw [fourierCos_eq_exp_neg_exponent hker ht'0 ht't ω, exponent_eq_sub hker ht'0 ht't ω,
      hgauge t ω ht.le, hgauge t' ω ht'0, ht']
  rw [e1, e2, e3, ← Real.exp_add]
  congr 1
  ring

/-- **The kernels from the origin are not `δ₀`.** The gauge produces a frequency at which the
exponent at scale `1` does not vanish, and carries it back to scale `t`; the exponent of `δ₀`
vanishes everywhere. -/
theorem kernel_ne_dirac_zero (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    μ 0 t ≠ Measure.dirac 0 := by
  intro hdir
  obtain ⟨-, χ, hχ0, hχm, -, -, -, hgauge, -, hFne⟩ := canonical_gauge Fam μ hker hnd S hcov
  obtain ⟨ω₀, hω₀⟩ := hFne
  have hχt : 0 < χ t := by
    have h := hχm Set.self_mem_Ici (ht.le : t ∈ Ici (0 : ℝ)) ht
    rwa [hχ0] at h
  have hval : exponent (μ 0 t) (ω₀ / χ t) = exponent (μ 0 1) ω₀ := by
    rw [hgauge t _ ht.le, mul_div_cancel₀ _ hχt.ne']
  have hzero : exponent (μ 0 t) (ω₀ / χ t) = 0 := by
    rw [hdir, exponent_apply, fourierCos]
    simp
  exact hω₀ (hval ▸ hzero)

/-- **`prop:kernel-regularity`, the assembly.** The kernel from the origin at any positive scale
is absolutely continuous with an even density, nonincreasing on `(0,∞)`.

Spends ledger **A8** and **A9** through `kernel_regularity_law` and nothing else: the two
hypothesis checks are `isSelfDecomposable_kernel` and `kernel_ne_dirac_zero`, both Lean core.

**Narrowed at the origin (fidelity review 2026-09-10, F6-1).** The monotonicity conjunct was
`AntitoneOn p (Ici 0)`, on the closed half-line, which forces a real bound `p 0` on the whole
density and is false for the Matérn members at `γ ≤ 1/2` — laws this development itself
constructs. It re-exports the interface, so it is narrowed with it; see the axiom's docstring in
`SpatialLine/Interfaces.lean` for the counterexample and the source reading. The blueprint's
statement, "its density is unimodal with mode at the origin", is unchanged. -/
theorem kernel_regularity (Fam : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    (μ 0 t) ≪ volume ∧ ∃ p : ℝ → ℝ,
      μ 0 t = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
        (∀ x : ℝ, p (-x) = p x) ∧ AntitoneOn p (Ioi 0) :=
  kernel_regularity_law (μ 0 t) (hker.isProbability 0 t le_rfl ht.le)
    (kernel_symmetric hker le_rfl ht.le)
    (isSelfDecomposable_kernel Fam.toPreCascadeCore μ hker Fam.nondegenerate S hcov ht)
    (kernel_ne_dirac_zero Fam.toPreCascadeCore μ hker Fam.nondegenerate S hcov ht)

end SpatialLine
