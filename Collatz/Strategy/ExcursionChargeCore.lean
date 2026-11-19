import Collatz.Basic

/-!
# Optimal integer charges for normalized excursion error

This arithmetic layer has no computational Collatz-search dependencies.
Optimality is only among integer per-run upper bounds at a fixed scale.
-/

namespace Collatz.ExcursionCharge

/-- The least integer upper bound for `s * (1 - (2/3)^v)`. -/
def charge (s v : Nat) : Nat := s - s * 2 ^ v / 3 ^ v

/-- Exact optimality among all integer charges at the selected scale. -/
theorem charge_le_iff (s v c : Nat) :
    charge s v ≤ c ↔ s * (3 ^ v - 2 ^ v) ≤ c * 3 ^ v := by
  have hp : 0 < (3 : Nat) ^ v := Nat.pow_pos (by decide)
  have he : s * (3 ^ v - 2 ^ v) ≤ c * 3 ^ v ↔
      (s - c) * 3 ^ v ≤ s * 2 ^ v := by
    rw [Nat.mul_sub, Nat.sub_mul]
    omega
  rw [he, ← Nat.le_div_iff_mul_le hp]
  unfold charge
  generalize s * 2 ^ v / 3 ^ v = q
  omega

/-- The optimal charge is valid, including scale zero and run length zero. -/
theorem charge_bound (s v : Nat) :
    s * (3 ^ v - 2 ^ v) ≤ charge s v * 3 ^ v :=
  (charge_le_iff s v (charge s v)).mp (Nat.le_refl _)

theorem charge_le_scale (s v : Nat) : charge s v ≤ s := Nat.sub_le ..

@[simp] theorem charge_zero_scale (v : Nat) : charge 0 v = 0 := by
  simp [charge]

@[simp] theorem charge_zero_run (s : Nat) : charge s 0 = 0 := by
  simp [charge]

/-- Refinement means an integer multiple of the old scale, not merely a larger scale. -/
theorem charge_refine (m s v : Nat) : charge (m * s) v ≤ m * charge s v := by
  apply (charge_le_iff (m * s) v (m * charge s v)).mpr
  calc
    _ = m * (s * (3 ^ v - 2 ^ v)) := by ac_rfl
    _ ≤ m * (charge s v * 3 ^ v) := Nat.mul_le_mul_left _ (charge_bound s v)
    _ = _ := by ac_rfl

/-- At a ternary scale large enough for this run, the charge is exact without rounding. -/
theorem charge_ternary {S v : Nat} (hv : v ≤ S) :
    charge (3 ^ S) v = 3 ^ S - 2 ^ v * 3 ^ (S - v) := by
  have hp : 0 < (3 : Nat) ^ v := Nat.pow_pos (by decide)
  have he : 3 ^ S * 2 ^ v = (2 ^ v * 3 ^ (S - v)) * 3 ^ v := by
    rw [Nat.mul_assoc, Nat.pow_sub_mul_pow 3 hv]
    ac_rfl
  simp only [charge, he, Nat.mul_div_cancel _ hp]

/-- At a sufficient ternary scale, the defining error bound is an equality. -/
theorem charge_ternary_exact {S v : Nat} (hv : v ≤ S) :
    charge (3 ^ S) v * 3 ^ v = 3 ^ S * (3 ^ v - 2 ^ v) := by
  rw [charge_ternary hv, Nat.sub_mul, Nat.mul_sub]
  have he : (2 ^ v * 3 ^ (S - v)) * 3 ^ v = 3 ^ S * 2 ^ v := by
    rw [Nat.mul_assoc, Nat.pow_sub_mul_pow 3 hv]
    ac_rfl
  rw [he]

/-- A finite scale loses every strict per-run discount once the quotient is zero. -/
theorem charge_eq_scale_iff (s v : Nat) :
    charge s v = s ↔ s * 2 ^ v < 3 ^ v := by
  have hp : 0 < (3 : Nat) ^ v := Nat.pow_pos (by decide)
  have hq : s * 2 ^ v / 3 ^ v ≤ s := by
    apply Nat.div_le_of_le_mul
    simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_left s (Nat.pow_le_pow_left (by decide : 2 ≤ 3) v)
  have he : charge s v = s ↔ s * 2 ^ v / 3 ^ v < 1 := by
    unfold charge
    generalize s * 2 ^ v / 3 ^ v = q at hq ⊢
    omega
  rw [he, Nat.div_lt_iff_lt_mul hp, Nat.one_mul]

/-- No fixed scale gives a strict discount for all run lengths.
The explicit run length `2*s` already saturates its charge. -/
theorem charge_saturates (s : Nat) : charge s (2 * s) = s := by
  apply (charge_eq_scale_iff s (2 * s)).mpr
  have h := Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := s))
    (Nat.pow_pos (by decide : 0 < 4) (n := s))
  calc
    s * 2 ^ (2 * s) = s * 4 ^ s := by rw [Nat.pow_mul]
    _ < 2 ^ s * 4 ^ s := h
    _ = 8 ^ s := by rw [← Nat.mul_pow]
    _ ≤ 9 ^ s := Nat.pow_le_pow_left (by decide) _
    _ = 3 ^ (2 * s) := by rw [Nat.pow_mul]

/-- Merely increasing the scale need not improve its normalized charge. -/
theorem larger_scale_can_worsen : charge 3 1 * 4 < charge 4 1 * 3 := by decide

/-- The three previously overcharged short runs have strictly smaller costs. -/
theorem short_ninths :
    charge 9 3 = 7 ∧ charge 9 4 = 8 ∧ charge 9 5 = 8 := by decide

end Collatz.ExcursionCharge
