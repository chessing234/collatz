import Collatz.Strategy.OrbitOccupationBootstrap

open Collatz Collatz.OrbitCapacity Collatz.OrbitOccupationBootstrap

example : ∃ C : Nat, 2 ^ 20 ≤ C * 3 ^ 19 := by
  obtain ⟨C, hC⟩ := orbit_count_power
  have hcycle := no_merging_of_cycle AccCycle.accIsCycleOf_one
  refine ⟨C, hC (n := 1) (X := 3) (by decide) hcycle [1, 2] (by decide) ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨by decide, 0, by decide⟩
  · exact ⟨by decide, 1, by decide⟩

#print axioms bound
#print axioms tilt149_rate
#print axioms orbit_count_nineteen_twentieths
#print axioms orbit_count_power
