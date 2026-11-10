import Collatz.Strategy.SynchronousExcursion

open Collatz Collatz.SynchronousClasses Collatz.SynchronousExcursion

example : leastAt 3 3 = 3 :=
  leastAt_first_halving (v := 2) (u := 1) (by decide) (by decide) (by decide)

example : leastAt 4 3 = 2 := by
  simpa using leastAt_second_halving (n := 3) (u := 1) (j := 1)
    (by decide) (by decide) (by decide) (by decide)

example : leastAt 5 23 = 7 := by
  simpa using leastAt_second_halving (n := 23) (u := 3) (j := 2)
    (by decide) (by decide) (by decide) (by decide)

example : leastAt 6 7 = 7 :=
  leastAt_after_single_halving_mod_eight (v := 3) (u := 1)
    (by decide) (by decide) (by decide) (by decide)

#print axioms leastAt_succ_of_non_two
#print axioms leastAt_first_halving
#print axioms leastAt_second_halving
#print axioms leastAt_after_single_halving
#print axioms leastAt_after_single_halving_mod_eight
