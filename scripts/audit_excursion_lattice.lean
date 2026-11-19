import Collatz.Strategy.ExcursionLattice

open Collatz Collatz.ExcursionBudget Collatz.ExcursionLattice Collatz.ExcursionMap

private def runs27 : List Run :=
  [⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 3⟩, ⟨6, 2⟩, ⟨2, 1⟩, ⟨3, 1⟩,
   ⟨1, 2⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨5, 1⟩, ⟨2, 1⟩]

private theorem trace27 : Trace 27 23 runs27 := by
  unfold runs27
  refine Trace.step (x := 61) (u := 31) ?_ (by unfold IsExcursion; decide)
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
  refine Trace.step (x := 121) (u := 61) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 31) (u := 1) ?_ (by unfold IsExcursion; decide)
  exact Trace.step (u := 7) Trace.nil (by unfold IsExcursion; decide)

private def groups27 : List Stratum :=
  [⟨1, [61, 121, 325, 433, 445, 577]⟩, ⟨2, [27, 91, 283]⟩, ⟨3, [103, 167]⟩,
   ⟨4, [175, 911]⟩, ⟨5, [31]⟩, ⟨6, [319]⟩]

set_option maxRecDepth 4096 in
private theorem groups27_perm : List.Perm (visits 27 runs27) (groups27.flatMap Stratum.entries) := by
  decide

private theorem groups27_sorted : ∀ g ∈ groups27, g.sources.Pairwise (· < ·) := by
  simp [groups27, List.pairwise_cons]

private theorem groups27_floor : ∀ r ∈ groups27.flatMap Stratum.entries, 27 ≤ r.source := by
  simp [groups27, Stratum.entries]

/-- The valuation grid certifies the fifteenth excursion's descent. -/
example : acceleratedOrbit 59 27 < 27 := by
  change acceleratedOrbit (time runs27) 27 < 27
  rw [trace27.landing]
  exact trace_grid_drop trace27 (by decide) (m := 27) (by decide)
    groups27_perm groups27_sorted groups27_floor (by decide)

#print axioms trace_product
#print axioms trace_grid_bound
#print axioms trace_grid_drop
