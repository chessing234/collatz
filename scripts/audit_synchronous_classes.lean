import Collatz.Strategy.SynchronousClasses

open Collatz Collatz.SynchronousClasses

example (t : Nat) :
    acceleratedOrbit 7 (128 * (3 * t + 1) + 49) = acceleratedOrbit 7 (128 * t + 59) :=
  mixed_residue_meeting (k := 7) (r := 49) (s := 59) (d := 1) (by decide) (by decide) (by decide) t

example (t : Nat) :
    acceleratedOrbit 11 (2048 * (3 * t + 1) + 1881) = acceleratedOrbit 11 (2048 * t + 1311) :=
  mixed_residue_meeting (k := 11) (r := 1881) (s := 1311) (d := 1)
    (by decide) (by decide) (by decide) t

example : leastAt 7 177 = 59 := by decide

example : leastAt 8 255 = 255 := leastAt_last_in_period 8 1 (by decide)

#print axioms least_count_power
#print axioms mixed_residue_meeting
#print axioms mixed_representative_contraction
#print axioms mem_fiber
#print axioms leastAt_last_in_period
#print axioms leastAt_eventually
#print axioms collatz_iff_synchronous_descent
