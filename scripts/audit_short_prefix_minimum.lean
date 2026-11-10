import Collatz.Strategy.ShortPrefixMinimum
import Collatz.Strategy.PeakDropChains

open Collatz Collatz.BoundedEvenDefect Collatz.ShortPrefixMinimum
  Collatz.LongRunPeakRigidity Collatz.PeakDropChains

#guard minimumFromPeaks 8 95 1 == (2 ^ 95 - 5) / 3
#guard minimumFromPeaks 8 65 1 == 2 ^ 65 - 1
#guard minimumFromPeaks 8 10015 1 == (2 ^ 10015 - 5) / 3
#guard requiredRunLength 8 43 17 == 42
#guard minimumFromPeaks 8 43 17 < 2 ^ 43 * 17 - 1

-- The two successive certificates are available at different horizons.
private theorem two_drops_at_common_horizon :
    77 + oddCount (3 ^ 77 - 1) 9 = 79 + oddCount (3 ^ 79 - 1) 9 := by
  have h₁ := later_invariant (k := 9) (K := 9) (v := 79) (w := 78) (u := 1)
    (by decide) (by decide) (by decide) (by decide)
    ((scaledPeakCertificate_iff (by decide) (by decide) (by decide) (by decide)).mpr (by decide))
  have h₂ := later_invariant (k := 2) (K := 9) (v := 78) (w := 77) (u := 1)
    (by decide) (by decide) (by decide) (by decide)
    ((scaledPeakCertificate_iff (by decide) (by decide) (by decide) (by decide)).mpr (by decide))
  simpa only [Nat.mul_one] using h₂.trans h₁

#print axioms trailing_odds_of_divisible_defect
#print axioms short_fiber_of_scaled_peak
#print axioms minimumFromPeaks_correct
#print axioms minimumFromPeaks_correct_adaptive
#print axioms chain_loss_le_even_count
#print axioms adaptive_chain_cap
#print axioms fixed_chain_cap
