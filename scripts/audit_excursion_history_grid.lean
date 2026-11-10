import Collatz.Strategy.ExcursionHistoryGrid

open Collatz Collatz.ExcursionBudget Collatz.ExcursionMap Collatz.ExcursionLattice
open Collatz.ExcursionHistoryGrid Collatz.LiftExponent

private def prefix63 : List Run := [⟨2, 1⟩, ⟨6, 3⟩]

private theorem tracePrefix63 : Trace 63 103 prefix63 := by
  refine Trace.step (x := 91) (u := 23) ?_ (by unfold IsExcursion; decide)
  exact Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)

/-- The full history and the next run determine the visit to 103. -/
example {b : Nat} (hv : Val2 (b + 1) 3)
    (hr : (2 ^ time prefix63 * b) % 3 ^ ExcursionBudget.oddCount prefix63 =
      offset prefix63 % 3 ^ ExcursionBudget.oddCount prefix63)
    (hb : b < 2 ^ (3 + 1) * 3 ^ ExcursionBudget.oddCount prefix63) : b = 103 :=
  history_recovers_source tracePrefix63 (by decide) (Val2.of_mod (by decide)) hv hr hb

private def runs7 : List Run := [⟨1, 2⟩, ⟨3, 1⟩]
private def floors7 : List Visit := [⟨1, 13⟩, ⟨3, 7⟩]

private theorem cert7 : HistoryFloors 7 runs7 floors7 := by
  unfold runs7 floors7
  refine HistoryFloors.step ?_ (by decide) (Val2.of_mod (by decide)) (by decide) (by decide)
  exact HistoryFloors.step HistoryFloors.nil (by decide) (Val2.of_mod (by decide))
    (by decide) (by decide)

example {n e : Nat} (h : Trace n e runs7) (hn : 7 ≤ n) :
    ∃ j ≤ 7, acceleratedOrbit j n < n :=
  descent_of_history_floors h cert7 (by decide) hn (by decide)

#print axioms history_recovers_source
#print axioms incoming_floor_le_history
#print axioms descent_of_history_floors
