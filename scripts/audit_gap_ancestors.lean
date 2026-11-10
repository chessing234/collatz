import Collatz.Strategy.SynchronousGapDelay

open Collatz Collatz.SynchronousClasses Collatz.SynchronousExcursion
  Collatz.SynchronousGapDelay Collatz.MixedProgressionAncestors

example : leastAt 2 10 = 3 := by
  simpa using leastAt_leading_halving (j := 1) (u := 3) (by decide)

example : leastAt 5 27 = 27 :=
  leastAt_single_gap (v := 2) (k := 3) (u := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : ∃ q L, 8 < q ∧ acceleratedOrbit L (12 * q + 9) = 7 :=
  ancestor_in_progression (z := 7) (by decide) 2 1 9 8

#print axioms leastAt_leading_halving
#print axioms leastAt_single_gap
#print axioms delay_progression
#print axioms ancestor_with_prefix
#print axioms ancestor_in_progression
#print axioms collatz_iff_progression
#print axioms ancestor_with_delay
