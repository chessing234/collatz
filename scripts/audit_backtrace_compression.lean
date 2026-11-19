import Collatz.Strategy.BacktraceCompression

open Collatz Collatz.BacktraceCompression

example : ∃ y K, y ≤ 2 ^ 100 ∧ K ≤ 100 ∧ y % 12 = (2 ^ 100) % 12 ∧
    acceleratedOrbit K y = acceleratedOrbit 100 (2 ^ 100) ∧
    acceleratedOrbit 100 y = acceleratedOrbit 100 (2 ^ 100) ∧
    K < (oddCount (2 ^ 100) 100 + 1) * (2 * (3 ^ oddCount (2 ^ 100) 100 * 12)) :=
  compress_periodic_target (m := 12) (p := 2) (x := 2 ^ 100) (L := 100)
    (by decide) (by decide) (by
      have h : acceleratedOrbit 100 (2 ^ 100) = 1 := by
        simpa only [Nat.mul_one] using SynchronousClasses.orbit_halvings 100 1
      rw [h]
      decide)

#print axioms compress_ancestor_of_period
#print axioms compress_ancestor_with_clock
#print axioms compress_ancestor
#print axioms compress_periodic_target
#print axioms strictly_smaller_of_long_backtrace
