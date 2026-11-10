import Collatz.Strategy.OrbitNearReturn

open Collatz.OrbitNearReturn Collatz.ExcursionSparseProduct

example : (1024 / (2 ^ (3 + 1) - 1) + 1) ^ 20 ≤ (1024 * 2 ^ 20) * 1024 ^ 19 :=
  width_power (n := 1024) (q := 3) (S := 1024) (by decide) (by decide) (by decide)

#print axioms sparse_tail_product_with_mass
#print axioms tail_envelope
#print axioms near_critical_window
#print axioms near_critical_count
#print axioms near_critical_power
#print axioms arbitrarily_late_minima
