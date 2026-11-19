import Collatz.Strategy.UnequalPeakDepth

open Collatz Collatz.UnequalPeakDepth

-- The common cofactor may be even.
example : acceleratedOrbit 4 (3 ^ 17 * 66 - 1) ≠ acceleratedOrbit 5 (3 ^ 7 * 66 - 1) :=
  unequal_depths_disjoint (by decide) (by decide)

-- At a small cofactor different depths can meet.
example : acceleratedOrbit 0 (3 ^ 0 * 9 - 1) = acceleratedOrbit 5 (3 ^ 2 * 9 - 1) := by
  decide

#print axioms unequal_depths_disjoint
#print axioms depth_eq_of_large_meeting
