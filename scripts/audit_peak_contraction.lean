import Collatz.Strategy.PeakContraction

open Collatz Collatz.PeakContraction Collatz.SynchronousClasses

example : Certificate 8 2 147 := by decide
example : ¬ Certificate 8 2 211 := by decide
example : ¬ Certificate 9 2 83 := by decide
example : ¬ Certificate 14 2 14867 := by decide
example : Certificate 14 4 14395 := by decide

example : leastAt 39 (2 ^ 31 - 1) < 2 ^ 31 - 1 := by
  have h := leastAt_lt_of_peak_meet (u := 1) (e := 29) (d := 2) (k := 8)
    (by decide) (by decide) (by simpa only [Nat.mul_one] using mersenne_31_meet 0)
  simpa only [Nat.mul_one] using h

#print axioms meet_of_certificate
#print axioms certificate_of_two_lifts
#print axioms synchronized_drop
#print axioms leastAt_lt_of_peak_meet
#print axioms reaches_one_drop
#print axioms periodic_peak_meet
#print axioms mersenne_31_reaches_one
#print axioms mersenne_79_reaches_one
#print axioms mersenne_111_reaches_one
#print axioms mersenne_2047_reaches_one
#print axioms separated_near_one
#print axioms mersenne_separation
#print axioms mersenne_wait_lower_bound
