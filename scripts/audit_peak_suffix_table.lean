import Collatz.Strategy.PeakSuffixTable

open Collatz Collatz.PeakSuffixTable Collatz.SuffixResidueObstruction Collatz.SynchronousClasses

example : Reject 2 2 2 := by decide
example : Reject 1 5 3 := by decide
example : ¬ Reject 1 5 2 := by decide

example : leastAt 38 (2 ^ 31 - 1) = 2 ^ 31 - 1 :=
  leastAt_seven_after_mod_eight (v := 31) (u := 1) (by decide)
    (by decide) (by decide) (by decide)

#print axioms runA_mod
#print axioms reject_target
#print axioms reject_peak
#print axioms lower_peak_of_table
#print axioms leastAt_seven_after_mod_eight
