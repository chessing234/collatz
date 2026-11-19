import Collatz.Strategy.ExcursionAlphabetMass
import Collatz.Strategy.ExcursionWindowCount

open Collatz.ExcursionAlphabetMass Collatz.ExcursionBudget Collatz.ExcursionMap
open Collatz.ExcursionRays Collatz.ExcursionWindowCount

example : alphabetWeight (box 2 3) 5 = 21 := alphabetWeight_box 2 3

example : wordMass (box 2 3) 12 2 = 1764 := by
  have hcost : ∀ r ∈ box 2 3, cost r ≤ 5 := by
    intro r hr
    have h := mem_box.mp hr
    unfold cost
    omega
  rw [wordMass_eq hcost (by decide), alphabetWeight_box]

private theorem trace1 : Trace 1 1 [⟨1, 1⟩] :=
  Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)

private theorem trace9 : Trace 9 7 [⟨1, 1⟩] :=
  Trace.step (u := 5) Trace.nil (by unfold IsExcursion; decide)

example : ([1, 9] : List Nat).length ≤ 2 := by
  apply box_count (u := 1) (w := 1) (T := 3) (k := 1) (by decide) (by decide)
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn'
  · exact ⟨by decide, by decide, 1, [⟨1, 1⟩], trace1, rfl, by decide⟩
  · have heq : n = 9 := by simpa using hn'
    subst n
    exact ⟨by decide, by decide, 7, [⟨1, 1⟩], trace9, rfl, by decide⟩

private def oneSymbol : Fin 1 → Run := fun _ => ⟨1, 1⟩

private def samples (i : Nat) : Window oneSymbol := by
  refine ⟨1 + 32 * i, 1 + 24 * i, 1 + 18 * i, [0], [0], ?_, ?_⟩
  · have h := lift_cut (later := [⟨1, 1⟩]) trace1 i
    rw [← Nat.mul_assoc] at h
    exact h
  · have h := lift_trace trace1 (3 * i)
    change Trace (1 + 4 * (2 * (3 * i))) (1 + 3 * (2 * (3 * i))) [⟨1, 1⟩] at h
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc] at h
    exact h

example : ∃ i ≤ 1, 24 ≤ (samples i).value :=
  large_of_distinct_windows (p := 1) (q := 1) (odd := 1) (steps := 2)
    samples (by decide) (by decide) (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _) (fun i j hij _ heq => by
      change 1 + 24 * i = 1 + 24 * j at heq
      omega)

#print axioms wordMass_eq
#print axioms box_count
#print axioms box_geometric_capacity
#print axioms box_no_linear_bound
#print axioms repeat_of_small_windows
#print axioms large_of_distinct_windows
