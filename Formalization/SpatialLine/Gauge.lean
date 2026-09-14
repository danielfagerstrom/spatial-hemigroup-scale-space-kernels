/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.Rigidity

/-!
# `prop:canonical-gauge`, the orbit coordinate

Blueprint: `blueprint/src/parts/06-covariance.tex`, `prop:canonical-gauge`.

`c(λ) := S_λ 1` is a continuous strictly increasing bijection of `(0,∞)` onto `(0,∞)` with
`c(1) = 1`. Its inverse is the canonical gauge.

## What proving it found, and how the argument was reorganised

The blueprint proves the three properties of `c` in the order continuity, injectivity,
direction, surjectivity, and gets *strict monotonicity* from "continuous and injective on a
connected set, hence strictly monotone, and the decreasing case is excluded by
`lem:dilation-atom`". The formalisation runs the same mathematics in a different order, because
one statement does all the work:

  **`lt_S_of_one_lt`** — for `ϰ > 1` and `u > 0`, `u < S_ϰ u`.

Its proof is the blueprint's own exclusion of the decreasing case, applied to the orbit of `u`
rather than to the orbit of `1`: if `S_ϰ u < u` then `S_{ϰⁿ} u` decreases to a limit that every
`S_ϰ` fixes, hence to `0` by `lem:action-rigidity`(4), and then `μ̂_{0,u}(ϰⁿω) → 1` for every
`ω`, so `lem:dilation-atom` makes `μ_{0,u} = δ₀`, against (ND). From it, strict monotonicity of
`λ ↦ S_λ t` is one line of the group law for **every** `t > 0` at once — which is also the first
clause of `prop:canonical-gauge`'s second half — and neither the connectedness argument nor
"continuous and injective implies monotone" is needed.

The second reorganisation is that the limits of `c` at `0` and `∞` are handled without any
continuity of `S_κ` **in the scale variable**, which the blueprint's proof uses ("since `S_λ` is
a monotone bijection of `[0,∞)` it is continuous"). Monotonicity alone gives that the supremum
and the infimum of `c((0,∞))` are fixed by every `S_κ`: `M ≤ S_κ M` for every `κ` because every
`c(λ) = S_κ(c(λ/κ)) ≤ S_κ M`, and applying that at `κ` and at `κ⁻¹` gives `S_κ M = M`. The same
two lines run for the infimum. That removes an appeal to a fact about `S` that this chapter has
not proved.
-/

namespace SpatialLine

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-! ## The action expands above `1` -/

/-- **The direction of the action.** For `ϰ > 1` and `u > 0`, `u < S_ϰ u`.

This is where `lem:dilation-atom` is spent, and it is the only place. -/
theorem lt_S_of_one_lt (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ)
    (S : ℝ → ℝ → ℝ) (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S)
    {ϰ : ℝ} (hϰ : 1 < ϰ) {u : ℝ} (hu : 0 < u) : u < S ϰ u := by
  have hϰ0 : (0:ℝ) < ϰ := lt_trans one_pos hϰ
  have hϰ1 : ϰ ≠ 1 := ne_of_gt hϰ
  have hgroup := action_rigidity_group Fam μ hker hnd S hcov
  have hfix := action_rigidity_no_fixed_point Fam μ hker hnd S hcov
  by_contra hcon
  rw [not_lt] at hcon
  have hlt : S ϰ u < u := by
    rcases eq_or_lt_of_le hcon with h | h
    · exact absurd (hfix ϰ u hϰ0 hϰ1 hu.le h) (ne_of_gt hu)
    · exact h
  -- the orbit `w n = S_{ϰⁿ} u`
  set w : ℕ → ℝ := fun n => S (ϰ ^ n) u with hwdef
  have hpowpos : ∀ n : ℕ, (0:ℝ) < ϰ ^ n := fun n => pow_pos hϰ0 n
  have hwnn : ∀ n, (0:ℝ) ≤ w n := fun n =>
    hcov.S_mapsTo _ (hpowpos n) (hpowpos n) hu.le
  have hw0 : w 0 = u := by
    simp only [hwdef, pow_zero]
    exact hgroup.2 u hu.le
  have hstep : ∀ n, S ϰ (w n) = w (n + 1) := by
    intro n
    simp only [hwdef]
    rw [hgroup.1 ϰ (ϰ ^ n) u hϰ0 (hpowpos n) hu.le]
    congr 1
    rw [pow_succ]
    ring
  have hstepinv : ∀ n, S ϰ⁻¹ (w (n + 1)) = w n := by
    intro n
    rw [← hstep n, hgroup.1 ϰ⁻¹ ϰ (w n) (inv_pos.mpr hϰ0) hϰ0 (hwnn n),
      inv_mul_cancel₀ hϰ0.ne']
    exact hgroup.2 (w n) (hwnn n)
  -- the orbit decreases
  have hdec : ∀ n, w (n + 1) < w n := by
    intro n
    induction n with
    | zero => rw [← hstep 0, hw0]; exact hlt
    | succ n ih =>
        rw [← hstep (n + 1)]
        calc S ϰ (w (n + 1)) < S ϰ (w n) :=
              hcov.S_strictMonoOn ϰ hϰ0 hϰ0 (hwnn (n + 1)) (hwnn n) ih
          _ = w (n + 1) := hstep n
  have hanti : Antitone w := antitone_nat_of_succ_le fun n => (hdec n).le
  have hbdd : BddBelow (Set.range w) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hwnn n⟩
  set L : ℝ := ⨅ n, w n with hLdef
  have hLle : ∀ n, L ≤ w n := fun n => ciInf_le hbdd n
  have hLnn : (0:ℝ) ≤ L := le_ciInf hwnn
  have htend : Tendsto w atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  -- the limit is a fixed point, hence `0`
  have hmono : ∀ κ : ℝ, 0 < κ → MonotoneOn (S κ) (Ici 0) := fun κ hκ =>
    (hcov.S_strictMonoOn κ hκ hκ).monotoneOn
  have hSLle : S ϰ L ≤ L := by
    refine le_ciInf fun n => ?_
    calc S ϰ L ≤ S ϰ (w n) := hmono ϰ hϰ0 hLnn (hwnn n) (hLle n)
      _ = w (n + 1) := hstep n
      _ ≤ w n := (hdec n).le
  have hSinvLle : S ϰ⁻¹ L ≤ L := by
    refine le_ciInf fun n => ?_
    calc S ϰ⁻¹ L ≤ S ϰ⁻¹ (w (n + 1)) :=
          hmono ϰ⁻¹ (inv_pos.mpr hϰ0) hLnn (hwnn (n + 1)) (hLle (n + 1))
      _ = w n := hstepinv n
  have hleSL : L ≤ S ϰ L := by
    have hnn : (0:ℝ) ≤ S ϰ⁻¹ L :=
      hcov.S_mapsTo ϰ⁻¹ (inv_pos.mpr hϰ0) (inv_pos.mpr hϰ0) hLnn
    have hcomp : S ϰ (S ϰ⁻¹ L) = L := by
      rw [hgroup.1 ϰ ϰ⁻¹ L hϰ0 (inv_pos.mpr hϰ0) hLnn, mul_inv_cancel₀ hϰ0.ne']
      exact hgroup.2 L hLnn
    calc L = S ϰ (S ϰ⁻¹ L) := hcomp.symm
      _ ≤ S ϰ L := hmono ϰ hϰ0 hnn hLnn hSinvLle
  have hL0 : L = 0 := hfix ϰ L hϰ0 hϰ1 hLnn (le_antisymm hSLle hleSL)
  rw [hL0] at htend
  -- the transforms of the dilates tend to `1`, so the law is `δ₀`
  haveI := hker.isProbability 0 u le_rfl hu.le
  refine kernel_ne_dirac hker hnd le_rfl hu ?_
  refine dilation_atom (μ 0 u) (fun n => ϰ ^ n) (tendsto_pow_atTop_atTop_of_one_lt hϰ) ?_
  intro ω
  have hcos : Tendsto (fun n => fourierCos (μ 0 u) (ϰ ^ n * ω)) atTop (𝓝 1) := by
    have hlim : Tendsto (fun n => fourierCos (μ 0 (w n)) ω) atTop
        (𝓝 (fourierCos (μ 0 0) ω)) := by
      have hcont := (continuousOn_fourierCos_kernel_zero hker ω) 0 (Set.self_mem_Ici)
      exact hcont.tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
          (Filter.Eventually.of_forall hwnn))
    rw [fourierCos_kernel_diag hker le_rfl ω] at hlim
    refine hlim.congr fun n => ?_
    exact fourierCos_similarity hker hcov (hpowpos n) hu.le ω
  have hsym := kernel_symmetric hker le_rfl hu.le
  have hchar : ∀ n : ℕ, charFun (μ 0 u) (ϰ ^ n * ω)
      = ((fourierCos (μ 0 u) (ϰ ^ n * ω) : ℝ) : ℂ) :=
    fun n => charFun_eq_fourierCos_of_symmetric hsym _
  simp only [hchar]
  have hlift : Tendsto (fun n : ℕ => ((fourierCos (μ 0 u) (ϰ ^ n * ω) : ℝ) : ℂ)) atTop
      (𝓝 (((1:ℝ) : ℂ))) := (Complex.continuous_ofReal.tendsto (1:ℝ)).comp hcos
  simpa using hlift

/-! ## Strict monotonicity of the ratio action -/

/-- **`λ ↦ S_λ t` is strictly increasing**, for every `t > 0`. One line of the group law from
`lt_S_of_one_lt`. -/
theorem S_strictMonoOn_ratio (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ)
    (S : ℝ → ℝ → ℝ) (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) {t : ℝ} (ht : 0 < t) :
    StrictMonoOn (fun lam => S lam t) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : (0:ℝ) < a := ha
  have hb0 : (0:ℝ) < b := hb
  have hgroup := action_rigidity_group Fam μ hker hnd S hcov
  have hSat : 0 < S a t := hcov.S_pos ha0 ha0 ht
  have hratio : (1:ℝ) < b / a := (one_lt_div ha0).mpr hab
  have hkey := lt_S_of_one_lt hker hnd S hcov hratio hSat
  have hcomp : S (b / a) (S a t) = S b t := by
    rw [hgroup.1 (b / a) a t (lt_trans one_pos hratio) ha0 ht.le]
    congr 1
    field_simp
  simpa [hcomp] using hkey

/-! ## The orbit coordinate -/

/-- **`prop:canonical-gauge`, the orbit coordinate.** `c(λ) = S_λ 1` is a continuous strictly
increasing bijection of `(0,∞)` onto `(0,∞)` with `c(1) = 1`.

Class **(a)** except the direction clause, which is (c). -/
theorem canonical_gauge_orbit (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S) :
    ContinuousOn (fun lam => S lam 1) (Ioi 0) ∧
      StrictMonoOn (fun lam => S lam 1) (Ioi 0) ∧
      SurjOn (fun lam => S lam 1) (Ioi 0) (Ioi 0) ∧
      S 1 1 = 1 := by
  have hgroup := action_rigidity_group Fam μ hker hnd S hcov
  have hfix := action_rigidity_no_fixed_point Fam μ hker hnd S hcov
  have hmono : ∀ κ : ℝ, 0 < κ → MonotoneOn (S κ) (Ici 0) := fun κ hκ =>
    (hcov.S_strictMonoOn κ hκ hκ).monotoneOn
  have hone : S 1 1 = 1 := hgroup.2 1 zero_le_one
  set c : ℝ → ℝ := fun lam => S lam 1 with hcdef
  have hcpos : ∀ lam : ℝ, 0 < lam → 0 < c lam := fun lam hlam => hcov.S_pos hlam hlam one_pos
  have hcstrict : StrictMonoOn c (Ioi 0) := S_strictMonoOn_ratio hker hnd S hcov one_pos
  have hccont : ContinuousOn c (Ioi 0) :=
    action_rigidity_continuous Fam μ hker hnd S hcov one_pos
  -- the orbit of `1` has a fixed-point-free image, so its infimum is `0` and it is unbounded
  have hshift : ∀ κ lam : ℝ, 0 < κ → 0 < lam → S κ (c lam) = c (κ * lam) := by
    intro κ lam hκ hlam
    simp only [hcdef]
    rw [hgroup.1 κ lam 1 hκ hlam zero_le_one]
  refine ⟨hccont, hcstrict, ?_, hone⟩
  intro u hu
  have hu0 : (0:ℝ) < u := hu
  -- some value of `c` is below `u`
  have hbelow : ∃ lam : ℝ, 0 < lam ∧ c lam < u := by
    by_contra hcon
    push_neg at hcon
    have hbdd : BddBelow (c '' Ioi 0) := ⟨0, by rintro _ ⟨lam, hlam, rfl⟩; exact (hcpos lam hlam).le⟩
    have h1I : (1:ℝ) ∈ Ioi (0:ℝ) := by norm_num
    have hne : (c '' Ioi 0).Nonempty := ⟨c 1, ⟨1, h1I, rfl⟩⟩
    set m : ℝ := sInf (c '' Ioi 0) with hmdef
    have hmge : u ≤ m := le_csInf hne (by rintro _ ⟨lam, hlam, rfl⟩; exact hcon lam hlam)
    have hmnn : (0:ℝ) ≤ m := le_trans hu0.le hmge
    have hkey : ∀ κ : ℝ, 0 < κ → S κ m ≤ m := by
      intro κ hκ
      refine le_csInf hne ?_
      rintro _ ⟨lam, hlam, rfl⟩
      have hlk : 0 < lam / κ := div_pos hlam hκ
      have hmle : m ≤ c (lam / κ) := csInf_le hbdd ⟨lam / κ, hlk, rfl⟩
      calc S κ m ≤ S κ (c (lam / κ)) := hmono κ hκ hmnn (hcpos _ hlk).le hmle
        _ = c (κ * (lam / κ)) := hshift κ (lam / κ) hκ hlk
        _ = c lam := by rw [mul_div_cancel₀ _ hκ.ne']
    have h2 := hkey 2 (by norm_num)
    have h2inv := hkey 2⁻¹ (by norm_num)
    have hnn2 : (0:ℝ) ≤ S 2⁻¹ m := hcov.S_mapsTo 2⁻¹ (by norm_num) (by norm_num) hmnn
    have hback : S 2 (S 2⁻¹ m) = m := by
      rw [hgroup.1 2 2⁻¹ m (by norm_num) (by norm_num) hmnn]
      norm_num
      exact hgroup.2 m hmnn
    have hge : m ≤ S 2 m := by
      calc m = S 2 (S 2⁻¹ m) := hback.symm
        _ ≤ S 2 m := hmono 2 (by norm_num) hnn2 hmnn h2inv
    have hm0 : m = 0 := hfix 2 m (by norm_num) (by norm_num) hmnn (le_antisymm h2 hge)
    linarith
  -- some value of `c` is above `u`
  have habove : ∃ lam : ℝ, 0 < lam ∧ u < c lam := by
    by_contra hcon
    push_neg at hcon
    have hbdd : BddAbove (c '' Ioi 0) := ⟨u, by rintro _ ⟨lam, hlam, rfl⟩; exact hcon lam hlam⟩
    have h1I : (1:ℝ) ∈ Ioi (0:ℝ) := by norm_num
    have hne : (c '' Ioi 0).Nonempty := ⟨c 1, ⟨1, h1I, rfl⟩⟩
    set M : ℝ := sSup (c '' Ioi 0) with hMdef
    have hMge : c 1 ≤ M := le_csSup hbdd ⟨1, h1I, rfl⟩
    have hMnn : (0:ℝ) ≤ M := le_trans (hcpos 1 one_pos).le hMge
    have hkey : ∀ κ : ℝ, 0 < κ → M ≤ S κ M := by
      intro κ hκ
      refine csSup_le hne ?_
      rintro _ ⟨lam, hlam, rfl⟩
      have hlk : 0 < lam / κ := div_pos hlam hκ
      have hmle : c (lam / κ) ≤ M := le_csSup hbdd ⟨lam / κ, hlk, rfl⟩
      calc c lam = c (κ * (lam / κ)) := by rw [mul_div_cancel₀ _ hκ.ne']
        _ = S κ (c (lam / κ)) := (hshift κ (lam / κ) hκ hlk).symm
        _ ≤ S κ M := hmono κ hκ (hcpos _ hlk).le hMnn hmle
    have h2 := hkey 2 (by norm_num)
    have h2inv := hkey 2⁻¹ (by norm_num)
    have hnn2 : (0:ℝ) ≤ S 2⁻¹ M := hcov.S_mapsTo 2⁻¹ (by norm_num) (by norm_num) hMnn
    have hback : S 2 (S 2⁻¹ M) = M := by
      rw [hgroup.1 2 2⁻¹ M (by norm_num) (by norm_num) hMnn]
      norm_num
      exact hgroup.2 M hMnn
    have hle : S 2 M ≤ M := by
      calc S 2 M ≤ S 2 (S 2⁻¹ M) := hmono 2 (by norm_num) hMnn hnn2 h2inv
        _ = M := hback
    have hM0 : M = 0 := hfix 2 M (by norm_num) (by norm_num) hMnn (le_antisymm hle h2)
    have : (0:ℝ) < c 1 := hcpos 1 one_pos
    linarith
  -- intermediate value between the two
  obtain ⟨lam₁, hlam₁, hlt₁⟩ := hbelow
  obtain ⟨lam₂, hlam₂, hlt₂⟩ := habove
  have hlam12 : lam₁ < lam₂ := by
    by_contra hcon
    push_neg at hcon
    have : c lam₂ ≤ c lam₁ := (hcstrict.monotoneOn) hlam₂ hlam₁ hcon
    linarith
  have hsub : Icc lam₁ lam₂ ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le hlam₁ hx.1
  have hivt := intermediate_value_Icc hlam12.le (hccont.mono hsub)
  have humem : u ∈ Icc (c lam₁) (c lam₂) := ⟨hlt₁.le, hlt₂.le⟩
  obtain ⟨lam, hlam, hval⟩ := hivt humem
  exact ⟨lam, hsub hlam, hval⟩

/-! ## The gauge itself, modulo `thm:increments-levy`

`prop:canonical-gauge`'s second declaration asserts seven things, of which exactly one —
`F = G(1,·) ∈ LEₛ` — is `thm:increments-levy` at `(0,1)`. It is stated here with that clause as
a **hypothesis**, so that the node is one application away once the increments theorem is
proved, and so that nothing else in it waits on an **L** node. This is the
specification-as-hypothesis move: the Lévy property of `G(1,·)` is quantified over rather than
constructed, and the statement loses nothing by it.
-/

/-- **`prop:canonical-gauge`, the gauge and the similarity form `eq:gauge`**, with the one
clause that is `thm:increments-levy` supplied as a hypothesis.

`χ` is produced existentially, with the four properties the article uses — it fixes `0`, is a
strictly increasing surjection of `[0,∞)`, intertwines the action with multiplication, and
straightens the accumulated exponent to a dilate of `F := G(1,·)`.

**The normalisation `χ 1 = 1` is a conclusion, not a hypothesis** (fidelity review R17). The
article's uniqueness clause is *about* normalised representations, so without this conjunct
nothing the necessity direction produces is known to be one. It costs one application of
`lem:dilation-invariance`: read at `t = 1`, the similarity form says `F(ω) = F(χ(1)ω)` for
every `ω`, and a dilation ratio other than `1` forces `F ≡ 0`, which `F ≢ 0` forbids. -/
theorem canonical_gauge_of_levy (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) (S : ℝ → ℝ → ℝ)
    (hcov : IsScaleCovariant Fam.Φ (Ioi 0) S)
    (hlevy : IsSymLevyExponent (exponent (μ 0 1))) :
    (∀ t : ℝ, 0 < t → StrictMonoOn (fun lam => S lam t) (Ioi 0)) ∧
      ∃ χ : ℝ → ℝ, χ 0 = 0 ∧ StrictMonoOn χ (Ici 0) ∧ SurjOn χ (Ici 0) (Ici 0) ∧
        χ 1 = 1 ∧
        (∀ lam t : ℝ, 0 < lam → 0 ≤ t → χ (S lam t) = lam * χ t) ∧
        (∀ t ω : ℝ, 0 ≤ t → exponent (μ 0 t) ω = exponent (μ 0 1) (χ t * ω)) ∧
        IsSymLevyExponent (exponent (μ 0 1)) ∧
        (∃ ω : ℝ, exponent (μ 0 1) ω ≠ 0) := by
  obtain ⟨hccont, hcstrict, hcsurj, hone⟩ :=
    canonical_gauge_orbit Fam μ hker hnd S hcov
  have hgroup := action_rigidity_group Fam μ hker hnd S hcov
  set c : ℝ → ℝ := fun lam => S lam 1 with hcdef
  have hcpos : ∀ lam : ℝ, 0 < lam → 0 < c lam := fun lam hlam => hcov.S_pos hlam hlam one_pos
  have hcinj : InjOn c (Ioi 0) := hcstrict.injOn
  set χ : ℝ → ℝ := fun t => if t ≤ 0 then 0 else Function.invFunOn c (Ioi 0) t with hχdef
  have hχ0 : χ 0 = 0 := by simp [hχdef]
  have hmemim : ∀ t : ℝ, 0 < t → t ∈ c '' (Ioi 0) := fun t ht => hcsurj ht
  have hχpos : ∀ t : ℝ, 0 < t → 0 < χ t := by
    intro t ht
    rw [hχdef]
    simp only [if_neg (not_le.mpr ht)]
    exact Function.invFunOn_mem (hmemim t ht)
  have hχc : ∀ a : ℝ, 0 < a → χ (c a) = a := by
    intro a ha
    have hpos := hcpos a ha
    show (if c a ≤ 0 then 0 else Function.invFunOn c (Ioi 0) (c a)) = a
    rw [if_neg (not_le.mpr hpos)]
    exact hcinj (Function.invFunOn_mem ⟨a, ha, rfl⟩) ha (Function.invFunOn_eq ⟨a, ha, rfl⟩)
  have hχeq : ∀ t : ℝ, 0 < t → c (χ t) = t := by
    intro t ht
    rw [hχdef]
    simp only [if_neg (not_le.mpr ht)]
    exact Function.invFunOn_eq (hmemim t ht)
  -- `χ` is strictly increasing on `[0,∞)`
  have hχmono : StrictMonoOn χ (Ici 0) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) ≤ a := ha
    have hb0 : (0:ℝ) < b := lt_of_le_of_lt ha0 hab
    rcases eq_or_lt_of_le ha0 with h | h
    · rw [← h, hχ0]
      exact hχpos b hb0
    · by_contra hcon
      rw [not_lt] at hcon
      have hmono := hcstrict.monotoneOn (hχpos b hb0) (hχpos a h) hcon
      rw [hχeq a h, hχeq b hb0] at hmono
      linarith
  refine ⟨fun t ht => S_strictMonoOn_ratio hker hnd S hcov ht, χ, hχ0, hχmono, ?_, ?_, ?_, ?_,
    hlevy, ?_⟩
  · -- surjectivity
    intro v hv
    have hv0 : (0:ℝ) ≤ v := hv
    rcases eq_or_lt_of_le hv0 with h | h
    · exact ⟨0, Set.self_mem_Ici, by rw [hχ0, h]⟩
    · exact ⟨c v, (hcpos v h).le, hχc v h⟩
  · -- the normalisation `χ 1 = 1`, review R17: the orbit coordinate fixes `1`
    have h := hχc 1 one_pos
    have hc1 : c 1 = 1 := hone
    rwa [hc1] at h
  · -- the intertwining `χ (S_λ t) = λ χ t`
    intro lam t hlam ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hcov.S_zero hlam hlam, hχ0, mul_zero]
    · have hSt : 0 < S lam t := hcov.S_pos hlam hlam h
      have hχt : 0 < χ t := hχpos t h
      have hkey : S lam t = c (lam * χ t) := by
        conv_lhs => rw [← hχeq t h]
        simp only [hcdef]
        rw [hgroup.1 lam (χ t) 1 hlam hχt zero_le_one]
      rw [hkey]
      exact hχc (lam * χ t) (mul_pos hlam hχt)
  · -- the similarity form `eq:gauge`
    intro t ω ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hχ0, zero_mul, exponent_self hker le_rfl, exponent_atZero hker zero_le_one]
    · have hχt : 0 < χ t := hχpos t h
      conv_lhs => rw [← hχeq t h]
      simp only [hcdef]
      exact covariance_similarity Fam μ hker S hcov (χ t) 1 ω hχt zero_le_one
  · -- `F` does not vanish identically, by (ND)
    by_contra hcon
    push_neg at hcon
    haveI := hker.isProbability 0 1 le_rfl zero_le_one
    refine kernel_ne_dirac hker hnd le_rfl one_pos ?_
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have hpos := kernel_transform_pos hker le_rfl zero_le_one ω
    have hlog : Real.log (fourierCos (μ 0 1) ω) = 0 := by
      have := hcon ω
      rw [exponent_apply, neg_eq_zero] at this
      exact this
    have hfc : fourierCos (μ 0 1) ω = 1 := by
      calc fourierCos (μ 0 1) ω = Real.exp (Real.log (fourierCos (μ 0 1) ω)) :=
            (Real.exp_log hpos).symm
        _ = 1 := by rw [hlog, Real.exp_zero]
    rw [charFun_eq_fourierCos_of_symmetric (kernel_symmetric hker le_rfl zero_le_one) ω, hfc]
    simp

end SpatialLine
