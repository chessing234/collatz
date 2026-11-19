import Collatz.Strategy.OrbitWindowBootstrap

open Collatz Collatz.OrbitCapacity Collatz.OrbitWindowBootstrap

example : 243 * (63 / 32) ≤ acceleratedOrbit 5 63 ∧
    acceleratedOrbit 5 63 < 243 * (63 / 32) + 243 :=
  image_interval 63 5

example : ∃ C : Nat, 3 ^ 20 ≤ C * 4 ^ 19 := by
  obtain ⟨C, hC⟩ := standard_window_power
  have hcycle := no_merging_of_cycle AccCycle.accIsCycleOf_one
  refine ⟨C, hC (n := 1) (a := 1) (X := 4) (by decide) (by decide)
    hcycle [1, 2, 4] (by decide) ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨by decide, by decide, 0, by decide⟩
  · exact ⟨by decide, by decide, 2, by decide⟩
  · exact ⟨by decide, by decide, 1, by decide⟩

#print axioms image_interval
#print axioms window_bound
#print axioms orbit_window_power
#print axioms standard_window_power
#print axioms multiplier_occupation
#print axioms exceeds_polynomial_multiplier
