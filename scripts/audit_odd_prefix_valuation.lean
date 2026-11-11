import Collatz.Strategy.OddPrefixValuation
import Collatz.Strategy.TwoEvenMeeting

open Collatz Collatz.OddRuns Collatz.OddPrefixValuation

example {m : Nat} (h : acceleratedOrbit 7 m = acceleratedOrbit 4 351) :
    351 ≤ m :=
  no_smaller_meeting_with_overhead (i := 4) (s := 3)
    ((oddRun_iff 4 351).mpr ⟨22, by decide⟩) ⟨13, by decide⟩ h

#print axioms excess_odd_steps_exceed_valuation
#print axioms no_smaller_meeting_during_run
#print axioms compress_meeting_during_run
#print axioms Collatz.BoundedEvenDefect.trailing_odds_at_precision
#print axioms Collatz.TwoEvenMeeting.leading_ternary_digit
#print axioms Collatz.TwoEvenMeeting.at_least_three_evens
#print axioms Collatz.TwoEvenMeeting.three_even_meeting
#print axioms Collatz.TwoEvenMeeting.overhead_ge_valuation_add_four
