import Collatz.Strategy.ExcursionCoefficientCoverage
import Collatz.Strategy.FirstLightBeatty
import Collatz.Strategy.PreCertified
import Collatz.Search.VerifiedRung14187

/-!
# An unconditional first-crossing horizon

The existing Beatty gap certificate and the bounded descent data
give actual descent at every first coefficient crossing with fewer
than 8,951 odd steps. This also controls first excursion endpoints.
-/

namespace Collatz.FirstLightDescent

private theorem small_drop_3997765 (n : Nat) (hn : 1 < n) (hsmall : n < 3997765) :
    ∃ j, j ≤ 256 ∧ acceleratedOrbit j n < n := by
  have hb : n < 2 ^ 10 * 3905 := by omega
  obtain ⟨j, hj, hd⟩ := Search.bounded_drop_of_blocks
    (M := 3905) (fuel := 224) (fun _ _ hm hr => Search.drops_all_3905 hm hr) hn hb
  exact ⟨j, Nat.le_trans hj (by decide), hd⟩

/-- The first crossing causes descent at any start above one
if fewer than 8,951 odd steps have occurred. -/
theorem first_light_drop_of_odd_count_lt_8951 {n k : Nat} (hn : 1 < n)
    (hf : FirstLight n k) (ha : oddCount n k < 8951) : acceleratedOrbit k n < n :=
  first_light_drop_of_beatty_certificate FirstLightConsequences.exactThrough_256
    PreCertified.bank_8951 small_drop_3997765 hn hf ha

/-- The time-indexed form of the first-crossing certificate. -/
theorem exactThrough_14186 : FirstLightConsequences.ExactThrough 14186 := by
  intro n k hn hk hf
  apply first_light_drop_of_odd_count_lt_8951 hn hf
  apply Nat.lt_of_not_ge
  intro ha
  have hpow3 : (3 : Nat) ^ 8951 ≤ 3 ^ oddCount n k := Nat.pow_le_pow_right (by decide) ha
  have hpow2 : (2 : Nat) ^ k ≤ 2 ^ 14186 := Nat.pow_le_pow_right (by decide) hk
  exact Nat.not_lt_of_ge (Nat.le_trans hpow2
    (Nat.le_trans (Nat.le_of_lt PreCertified.pow_gap_8951) hpow3)) hf.1

end Collatz.FirstLightDescent

namespace Collatz.ExcursionBudget

/-- This first-excursion result uses only repository certificates.
The time at its terminal boundary need not be bounded separately. -/
theorem Trace.first_crossing_drop_of_odd_count_lt_8951 {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : 1 < n) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 8951) : e < n := by
  obtain ⟨k, _, hf, ha, hland⟩ := h.first_light_of_first_crossing hproper hcross
  have hdrop := FirstLightDescent.first_light_drop_of_odd_count_lt_8951 hn hf (ha.symm ▸ hbound)
  exact Nat.lt_of_le_of_lt hland hdrop

end Collatz.ExcursionBudget
