import Collatz.Strategy.InverseFiberTransport

open Collatz Collatz.InverseFiberTransport

example : acceleratedOrbit 12 8 = 2 ∧ acceleratedOrbit 12 9 = 2 := by decide

example : 8 < 9 ∧ translate 12 1 9 < translate 12 1 8 := by decide

example : acceleratedOrbit 12 (translate 12 1 9) = 2 + 3 ^ 12 := by
  rw [orbit_translate, show acceleratedOrbit 12 9 = 2 by decide, Nat.mul_one]

#print axioms translate_parity
#print axioms translate_injective
#print axioms orbit_translate
#print axioms mem_fiber_translate
#print axioms translate_order
#print axioms stable_minimum
#print axioms least_profile_periodic
