import Collatz.Strategy.ExcursionBudget

open Collatz Collatz.ExcursionMap Collatz.ExcursionBudget

private def runs47 : List Run :=
  [⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 3⟩, ⟨6, 2⟩, ⟨2, 1⟩,
   ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨4, 1⟩]

private theorem trace47 : Trace 47 23 runs47 := by
  unfold runs47
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
  exact Trace.step (u := 3) Trace.nil (by unfold IsExcursion; decide)

private theorem proper47 : ProperPrefixBound 2 1 runs47 := by
  simp only [runs47, ProperPrefixBound]
  decide

example : acceleratedOrbit 55 47 < 47 := by
  have htime : time runs47 = 55 := rfl
  rw [← htime, trace47.landing]
  exact drop_of_first_half trace47 (by decide) proper47 (by decide) (by decide)

example : acceleratedOrbit 5 3 < 3 := by
  let runs : List Run := [⟨2, 3⟩]
  have h : Trace 3 1 runs := Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)
  change acceleratedOrbit (time runs) 3 < 3
  rw [h.landing]
  exact drop_of_weighted_crossing (p := 5) (d := 4) h (by decide) (by decide)
    ninths_bound (by change 4 ≤ 5 ∧ True; decide) (by decide) (by decide)

#print axioms drop_of_weighted_crossing
#print axioms slope_bound_of_no_drop
