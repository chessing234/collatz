import Collatz.Strategy.ExcursionBoundaryCone

/-! A uniform source and landing cap for all eight exceptional pairs. -/

namespace Collatz.ExcursionBudget

open ExcursionPowerGap DyadicPowerBounds

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem cap_comparison {a b : Nat} (hp : (a, b) ∈ boundaryPairs) :
    (10000 * 2 ^ 75 + (2431 * a + 1500)) * 3 ^ a < (10000 * 2 ^ 75) * 2 ^ b := by
  simp only [boundaryPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact strict_upper_comparison 3 _ 192 _ _ _ (by decide +kernel)

/-- Every potential failed first excursion crossing in the cone
starts and lands below `2^75`, regardless of which pair occurs. -/
theorem Trace.first_crossing_failure_cap {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 325000000000)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) : e < 2 ^ 75 := by
  have hp := h.first_crossing_failure_eight_pairs hproper hcross hbound hlarge hkeep
  have hnorm := h.scaled_affine_upper (h.offset_le_phase_charge hproper hcross)
  have hnorm' : 10000 * (2 ^ time rs * e) ≤
      (10000 * e + (2431 * oddCount rs + 1500)) * 3 ^ oddCount rs :=
    Nat.le_trans hnorm (Nat.mul_le_mul_right _
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hkeep) _))
  apply Nat.lt_of_not_ge
  intro hcap
  have hcomp : (10000 * 2 ^ 75 + (2431 * oddCount rs + 1500)) * 3 ^ oddCount rs <
      10000 * (2 ^ 75 + 0) * 2 ^ time rs := by simpa only [Nat.add_zero] using cap_comparison hp
  have hbad := landing_lt_add_of_scaled_affine (Nat.le_of_lt hcross) hcap hnorm' hcomp
  omega

end Collatz.ExcursionBudget
