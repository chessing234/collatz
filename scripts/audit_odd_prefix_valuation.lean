import Collatz.Strategy.OddPrefixValuation

open Collatz Collatz.OddRuns Collatz.OddPrefixValuation

example {m : Nat} (h : acceleratedOrbit 7 m = acceleratedOrbit 4 351) :
    351 ≤ m :=
  no_smaller_meeting_with_overhead (i := 4) (s := 3)
    ((oddRun_iff 4 351).mpr ⟨22, by decide⟩) ⟨13, by decide⟩ h

#print axioms excess_odd_steps_exceed_valuation
#print axioms no_smaller_meeting_during_run
#print axioms compress_meeting_during_run
#print axioms Collatz.BoundedEvenDefect.trailing_odds_at_precision
