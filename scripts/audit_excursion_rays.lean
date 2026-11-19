import Collatz.Strategy.ExcursionRays

open Collatz Collatz.ExcursionBudget Collatz.ExcursionMap Collatz.ExcursionRays

private def runs165 : List Run :=
  [⟨1, 2⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨5, 1⟩, ⟨1, 3⟩]

private theorem trace165 : Trace 165 167 runs165 := by
  unfold runs165
  refine Trace.step (x := 445) (u := 223) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 175) (u := 11) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 103) (u := 13) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 91) (u := 23) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 121) (u := 61) ?_ (by unfold IsExcursion; decide)
  refine Trace.step (x := 31) (u := 1) ?_ (by unfold IsExcursion; decide)
  exact Trace.step (u := 83) Trace.nil (by unfold IsExcursion; decide)

example (m : Nat) : (∃ y, Trace m y runs165) ↔ m % (2 ^ 28) = 165 :=
  realizes_iff_mod (r := ⟨1, 2⟩) trace165

/-- The base endpoint is high despite a contracting coefficient. The next
source on its ray and all later sources descend at shortcut time 27. -/
example (k : Nat) : acceleratedOrbit 27 (165 + 2 ^ 28 * k) < 165 + 2 ^ 28 * k ↔ 0 < k := by
  have h := ray_drop_threshold trace165 (by decide) (by decide) k
  have hs : time runs165 = 27 := rfl
  rw [hs, ← Nat.mul_assoc, ← Nat.pow_succ] at h
  exact h

#print axioms realizes_iff_mod
#print axioms canonical_trace
#print axioms ray_drop_threshold

private theorem trace19 : Trace 19 11 [⟨2, 2⟩] :=
  Trace.step (u := 5) Trace.nil (by unfold IsExcursion; decide)

example (k : Nat) : acceleratedOrbit 4 (19 + 32 * (k + 1)) < 19 + 32 * (k + 1) := by
  have h := descent_after_period_of_shared_exponents trace19 (p := 1) (q := 2)
    (d := 2) (by decide) (by decide) (by decide) (by decide) k
  have hs : time [⟨2, 2⟩] = 4 := rfl
  rw [hs, ← Nat.mul_assoc] at h
  exact h

#print axioms offset_add_denominator_le
#print axioms descent_after_period_of_shared_exponents

/-- The terminal halving supplies enough separation for the run from 9. -/
example : 7 < 9 :=
  drop_of_terminal_gap_and_size
    (r := ⟨1, 1⟩) (rs := [])
    (Trace.step (u := 5) Trace.nil (by unfold IsExcursion; decide))
    (by decide) (by decide)

example : ¬ (3 : Nat) ≤ 2 * (4 - 3) := by decide

#print axioms offset_terminal_halvings_le
#print axioms drop_of_terminal_gap_and_size
#print axioms non_drop_shift_bound

private theorem first7 : Trace 7 13 [⟨3, 1⟩] :=
  Trace.step (u := 1) Trace.nil (by unfold IsExcursion; decide)

example {b : Nat} (hb : b < 27) (hc : (16 * b) % 27 = 19) : b = 13 :=
  recover_ternary first7 (by decide) hb hc

/-- Reconstruct the cut of the profile from 7 to 5 with an incoming
modulus of 27 and outgoing modulus of 16. -/
example {b : Nat} (hb : b < 432) (hd : b % 16 = 13) (ht : (16 * b) % 27 = 19) :
    b = 13 :=
  recover_canonical_cut (later := [⟨1, 2⟩]) first7 (by decide) hb hd ht

example (k : Nat) : Trace (7 + 256 * k) (13 + 432 * k) [⟨3, 1⟩] := by
  have h := lift_cut (later := [⟨1, 2⟩]) first7 k
  rw [← Nat.mul_assoc] at h
  exact h

#print axioms quotient_eq
#print axioms recover_ternary
#print axioms recover_canonical_cut

private theorem second7 : Trace 13 5 [⟨1, 2⟩] :=
  Trace.step (u := 7) Trace.nil (by unfold IsExcursion; decide)

private theorem first263 : Trace 263 445 [⟨3, 1⟩] :=
  Trace.step (u := 33) Trace.nil (by unfold IsExcursion; decide)

private theorem second263 : Trace 445 167 [⟨1, 2⟩] :=
  Trace.step (u := 223) Trace.nil (by unfold IsExcursion; decide)

example : 13 + 432 ≤ 445 :=
  repeated_window_separation first7 first263 second7 second263 (by decide)

example : (445 : Nat) - 13 = 432 := by decide

#print axioms repeated_window_separation
