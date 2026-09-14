/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import SpatialLine.SelfDecomposable

/-!
# `prop:strict-positivity`(1): an admissible exponent is nondecreasing on `[0,∞)`

Blueprint: `prop:strict-positivity`, clause (1).

## The route is the dilation identity, not the integrand

The skeleton priced this clause **S** by the substitution `u = ωx`, which makes the integrand
`(1 - \cos u)k(u/ω)/u` with `k(u/ω)` nondecreasing in `ω`. That is correct and is one line of
mathematics, but it is *two* changes of variables in Lean and it repeats the computation
`profileJumpL_comp_div` already does.

The cheaper route, once (3) ⟹ (1) is in the library, is that monotonicity **is** the dilation
identity read at a single frequency: `sd_increment_isSymLevyExponent` says that
`F(d\,\cdot) - F(c\,\cdot)` is a symmetric Lévy exponent for `0 ≤ c ≤ d`, and a symmetric Lévy
exponent is nonnegative because it is a `toReal`. Evaluating at `ω = 1` gives
`F(c) ≤ F(d)` and nothing else is needed. Recorded because it is the second time in this
chapter that a node priced from the paper proof turned out to be a corollary of a node already
proved (the first is `lem:admissible-cone`'s finiteness step).

Note which hypothesis is *not* used: `F ≢ 0`. The blueprint states both clauses of
`prop:strict-positivity` under it, and only clause (2) consumes it — the hypothesis archaeology
the skeleton recorded, confirmed by the proof.

Proving campaign, wave 2, chapter 7 (2026-09-09).
-/

namespace SpatialLine

open MeasureTheory Set

/-- **`prop:strict-positivity`(1).** An admissible exponent is nondecreasing on `[0,∞)`. -/
theorem strict_positivity_monotone (P : SDProfile) : MonotoneOn P.exponent (Ici 0) := by
  intro x hx y _ hxy
  obtain ⟨R, hR⟩ := sd_increment_isSymLevyExponent P hx hxy
  have h1 : P.exponent (y * 1) - P.exponent (x * 1) = R.exponent 1 := hR 1
  have h2 : 0 ≤ R.exponent 1 := ENNReal.toReal_nonneg
  rw [mul_one, mul_one] at h1
  linarith

end SpatialLine
