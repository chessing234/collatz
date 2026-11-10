import Collatz.Strategy.ExcursionMixedGrid

open Collatz Collatz.ExcursionBudget Collatz.ExcursionLattice Collatz.ExcursionMap
open Collatz.ExcursionMixedGrid Collatz.LiftExponent

private def runs63 : List Run :=
  [⟨1, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 3⟩, ⟨6, 2⟩, ⟨2, 1⟩,
   ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨6, 3⟩]

private theorem trace63 : Trace 63 61 runs63 := by
  unfold runs63
  refine Trace.step (x := 325) (u := 163) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 433) (u := 217) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 577) (u := 289) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 911) (u := 57) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 319) (u := 5) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 283) (u := 71) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 167) (u := 21) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 445) (u := 223) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 175) (u := 11) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 103) (u := 13) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 91) (u := 23) ?_ (by unfold IsExcursion; decide)
  exact Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)

private def floors63 : List Visit :=
  [⟨1, 73⟩, ⟨1, 73⟩, ⟨1, 253⟩, ⟨4, 911⟩, ⟨6, 319⟩, ⟨2, 67⟩,
   ⟨3, 71⟩, ⟨1, 121⟩, ⟨4, 175⟩, ⟨3, 103⟩, ⟨2, 91⟩, ⟨6, 63⟩]

private theorem cert63 : Floors 63 runs63 floors63 := by
  unfold runs63 floors63
  repeat first
    | exact Floors.first
    | refine Floors.next ?_ (by decide) (Val2.of_mod (by decide)) (by decide) (by decide)

set_option maxRecDepth 4096 in
private theorem floor63 : ∀ r ∈ visits 63 runs63, 63 ≤ r.source := by
  change ∀ r ∈ ([⟨1, 325⟩, ⟨1, 433⟩, ⟨1, 577⟩, ⟨4, 911⟩, ⟨6, 319⟩, ⟨2, 283⟩,
    ⟨3, 167⟩, ⟨1, 445⟩, ⟨4, 175⟩, ⟨3, 103⟩, ⟨2, 91⟩, ⟨6, 63⟩] : List Visit),
    63 ≤ r.source
  simp

example : acceleratedOrbit 54 63 < 63 := by
  change acceleratedOrbit (time runs63) 63 < 63
  rw [trace63.landing]
  exact drop_of_mixed_floors trace63 cert63 (by decide) (by decide) floor63 (by decide)

/-- The same product test works at every eligible source above the floor. -/
example {n e : Nat} (h : Trace n e runs63) (hn : 63 ≤ n) :
    ∃ j ≤ 54, acceleratedOrbit j n < n :=
  descent_of_mixed_floors h cert63 (by decide) hn (by decide)

#print axioms mixed_floor
#print axioms Floors.compare
#print axioms drop_of_mixed_floors
#print axioms descent_of_mixed_floors
