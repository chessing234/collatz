import Collatz.Strategy.SynchronousGrowth

open Collatz Collatz.SynchronousGrowth

example {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ H, ∀ k, H ≤ k → 41 * halvings n k < 24 * rises n k :=
  eventual_rises_balance (P := 41) (Q := 24) hn hinj (by decide) (by decide)

#print axioms trajectory_envelope
#print axioms trajectory_multiplier_escapes
#print axioms eventual_rises_balance
#print axioms trajectory_multiplier_occupation
#print axioms exceeds_reduced_polynomial
