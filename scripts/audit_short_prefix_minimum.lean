import Collatz.Strategy.ShortPrefixMinimum

open Collatz Collatz.BoundedEvenDefect Collatz.ShortPrefixMinimum

#guard minimumFromPeaks 8 95 1 == (2 ^ 95 - 5) / 3
#guard minimumFromPeaks 8 65 1 == 2 ^ 65 - 1
#guard minimumFromPeaks 8 10015 1 == (2 ^ 10015 - 5) / 3

#print axioms trailing_odds_of_divisible_defect
#print axioms short_fiber_of_scaled_peak
#print axioms minimumFromPeaks_correct
