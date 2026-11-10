import Collatz.Strategy.ExcursionGreedySlots

open Collatz.ExcursionGreedySlots Collatz.ExcursionLattice

private def classes : List SlotClass := [⟨1, 1⟩, ⟨0, 1⟩]

private theorem ordered : classes.Pairwise (fun p q => q.ternarySteps ≤ p.ternarySteps) := by
  simp [classes, List.pairwise_cons]

private theorem competitor : Assignment [] (classes.map (SlotClass.admits 25 1)) [37, 25] := by
  refine Assignment.cons (by simp) (by unfold SlotClass.admits; decide) ?_
  exact Assignment.cons (by simp) (by unfold SlotClass.admits; decide) Assignment.nil

private theorem greedy : Greedy [] (classes.map (SlotClass.admits 25 1)) [25, 29] := by
  refine Greedy.cons (by simp) (by unfold SlotClass.admits; decide) (fun _ _ h => h.1) ?_
  refine Greedy.cons (by simp) (by unfold SlotClass.admits; decide) ?_ Greedy.nil
  intro x hx h
  change 25 ≤ x ∧ x % 4 = 1 at h
  have hne : x ≠ 25 := by simpa using hx
  omega

/-- The earlier class can displace the later class's occupied slot. -/
example : factors 3 1 [37, 25] * ([25, 29] : List Nat).prod ≤
    ([37, 25] : List Nat).prod * factors 3 1 [25, 29] :=
  greedy_mixed_class_product ordered competitor greedy

/-- Distinctness strictly improves the bound over two copies of the
unrestricted least candidate. -/
example : factors 3 1 [25, 29] * ([25, 25] : List Nat).prod <
    ([25, 29] : List Nat).prod * factors 3 1 [25, 25] := by
  decide

#print axioms greedy_product
#print axioms exists_optimal_assignment
#print axioms greedy_mixed_class_product

open Collatz Collatz.ExcursionBudget Collatz.ExcursionMap

private def runs7 : List Run := [⟨1, 2⟩, ⟨3, 1⟩]
private def groups7 : List GreedyStratum :=
  [⟨⟨1, [13]⟩, [⟨3, 13⟩], [13]⟩, ⟨⟨3, [7]⟩, [⟨0, 7⟩], [7]⟩]

private theorem trace7 : Trace 7 5 runs7 := by
  refine Trace.step (x := 13) (u := 7) ?_ (by unfold IsExcursion; decide)
  exact Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)

private theorem groups7_cert : ∀ g ∈ groups7, g.Certified 7 := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | htail
  · refine ⟨by simp, ?_, ?_⟩
    · exact Assignment.cons (by simp) (by unfold SlotClass.admits; decide) Assignment.nil
    · refine Greedy.cons (by simp) (by unfold SlotClass.admits; decide) ?_ Greedy.nil
      intro x _ hx
      have hmod := hx.2
      change x % 108 = 13 at hmod
      rw [← hmod]
      exact Nat.mod_le _ _
  · have hlast : g = ⟨⟨3, [7]⟩, [⟨0, 7⟩], [7]⟩ := by simpa [groups7] using htail
    subst g
    refine ⟨by simp, ?_, ?_⟩
    · exact Assignment.cons (by simp) (by unfold SlotClass.admits; decide) Assignment.nil
    · exact Greedy.cons (by simp) (by unfold SlotClass.admits; decide)
        (fun _ _ hx => hx.1) Greedy.nil

example : acceleratedOrbit 7 7 < 7 := by
  change acceleratedOrbit (time runs7) 7 < 7
  rw [trace7.landing]
  exact trace_greedy_drop trace7 (by decide) (groups := groups7) (by decide)
    groups7_cert (by decide)

#print axioms trace_greedy_drop
