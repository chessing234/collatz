import Collatz.Strategy.ExcursionHeavy
import Collatz.Strategy.PowerSeparation

/-!
# The one-excursion boundary from separation of powers

`PowerSeparation` is an explicit hypothesis in Lean. The derivation from
Rhin's published separation estimate is in `RESEARCH.md`.
-/

namespace Collatz.ExcursionPowerGap

open Collatz.ExcursionMap Collatz.ExcursionHeavy

/-- Separation closes every contracting pair, including the boundary count. -/
theorem heavy_of_contracting (hgap : PowerSeparation) {v W : Nat}
    (hv : 2 ≤ v) (hW : 1 ≤ W) (hc : 3 ^ v < 2 ^ (v + W)) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  by_cases hsmall : v ≤ 128
  · rcases dichotomy_through_128 hv hW hsmall with hlight | hheavy
    · omega
    · exact hheavy
  by_cases hlarge : v ≤ W
  · exact heavy_of_W_ge_v hv hlarge
  exact PowerSeparation.heavy_of_large_run hgap (by omega) (by omega) hc

/-- For a start above one, a complete excursion drops exactly when its
multiplicative coefficient is less than one. -/
theorem drop_iff_contracting (hgap : PowerSeparation) {n v u W e : Nat}
    (hn : 1 < n) (h : IsExcursion n v u W e) :
    e < n ↔ 3 ^ v < 2 ^ (v + W) := by
  refine ⟨drop_needs_surplus h, fun hc => ?_⟩
  have hv : 0 < v := h.2.2.2.1
  by_cases hv1 : v = 1
  · exact drop_of_v_one h hv1 hn
  exact drop_of_heavy h (heavy_of_contracting hgap (by omega) h.one_le_W hc)

end Collatz.ExcursionPowerGap
