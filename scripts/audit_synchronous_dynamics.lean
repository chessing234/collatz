import Collatz.Strategy.SynchronousDynamics

open Collatz Collatz.SynchronousClasses Collatz.SynchronousDynamics

example : leastAt 2 6 = 6 := by decide

example : leastAt 1 3 = 3 := leastAt_half (k := 1) (x := 3) (by decide)

example : 3 * 3359 < 2 * 10073 :=
  larger_count_contracts (k := 11) (n := 10073) (m := 3359)
    (by decide) (by decide) (by decide)

#print axioms least_half
#print axioms least_four_dvd_three
#print axioms previous_eq_odd_preimage
#print axioms smaller_mate_iff
#print axioms larger_count_contracts
#print axioms next_lt_of_larger_count
#print axioms collatz_of_larger_count_profiles
