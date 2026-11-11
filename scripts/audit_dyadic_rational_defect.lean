import Collatz.Strategy.OddPrefixValuation

open Collatz Collatz.OddRuns Collatz.OddPrefixValuation

example {m : Nat} (hsmall : m < 351)
    (h : acceleratedOrbit 19 m = acceleratedOrbit 4 351) :
    3 + 6 ≤ 8 * (19 - oddCount m 19) :=
  valuation_add_six_le_eight_evens (i := 4) (s := 15) (t := 3) (by decide)
    ((oddRun_iff 4 351).mpr ⟨22, by decide⟩) ⟨13, by decide⟩ hsmall h

#print axioms Collatz.BoundedEvenDefect.avoids_dyadic_rational_at_precision
#print axioms Collatz.BoundedEvenDefect.avoids_odd_run_ratio
#print axioms valuation_le_two_prefix_add_two_evens
#print axioms valuation_add_six_le_eight_evens
