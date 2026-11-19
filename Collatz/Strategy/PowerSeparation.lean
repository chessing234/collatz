/-! Integer consequences of the separation estimate derived in `RESEARCH.md`. -/

namespace Collatz

/-- A normalized separation bound in integer arithmetic. -/
def PowerSeparation : Prop :=
  ∀ v s : Nat, 3 ^ v < 2 ^ s → 2 ^ s ≤ 2 * s ^ 14 * (2 ^ s - 3 ^ v)

namespace PowerSeparation

private theorem polynomial_le_two_pow (v : Nat) (hv : 128 ≤ v) :
    2 * (2 * v) ^ 14 ≤ 2 ^ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  clear hv
  induction k with
  | zero => decide
  | succ k ih =>
    let v := 128 + k
    change 2 * (2 * v) ^ 14 ≤ 2 ^ v at ih
    change 2 * (2 * (v + 1)) ^ 14 ≤ 2 ^ (v + 1)
    have hv : 128 ≤ v := by dsimp [v]; omega
    have hscale : 128 * (2 * (v + 1)) ≤ 129 * (2 * v) := by omega
    have hp := Nat.pow_le_pow_left hscale 14
    rw [Nat.mul_pow 128 (2 * (v + 1)) 14, Nat.mul_pow 129 (2 * v) 14] at hp
    have hstep : (2 * (v + 1)) ^ 14 ≤ 2 * (2 * v) ^ 14 := by
      apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 128 ^ 14)
      calc
        128 ^ 14 * (2 * (v + 1)) ^ 14 ≤ 129 ^ 14 * (2 * v) ^ 14 := hp
        _ ≤ (128 ^ 14 * 2) * (2 * v) ^ 14 := Nat.mul_le_mul_right _ (by decide)
        _ = 128 ^ 14 * (2 * (2 * v) ^ 14) := Nat.mul_assoc ..
    calc
      2 * (2 * (v + 1)) ^ 14 ≤ 2 * (2 * (2 * v) ^ 14) :=
        Nat.mul_le_mul_left _ hstep
      _ = (2 * (2 * v) ^ 14) * 2 := by ac_rfl
      _ ≤ 2 ^ v * 2 := Nat.mul_le_mul_right _ ih
      _ = 2 ^ (v + 1) := (Nat.pow_succ ..).symm

/-- The gap at large run lengths absorbs the whole cofactor-free error. -/
theorem heavy_of_large_run (hgap : PowerSeparation) {v W : Nat}
    (hv : 128 ≤ v) (hW : W ≤ v) (hc : 3 ^ v < 2 ^ (v + W)) :
    3 ^ v ≤ 2 ^ W * (2 ^ v - 1) := by
  let gap := 2 ^ (v + W) - 3 ^ v
  have hle : v + W ≤ 2 * v := by omega
  have hpoly : 2 * (v + W) ^ 14 ≤ 2 ^ v :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 14))
      (polynomial_le_two_pow v hv)
  have hscaled : 2 ^ (v + W) ≤ 2 ^ v * gap :=
    Nat.le_trans (hgap v (v + W) hc) (Nat.mul_le_mul_right _ hpoly)
  rw [Nat.pow_add] at hscaled
  have hgap_le : 2 ^ W ≤ gap := Nat.le_of_mul_le_mul_left hscaled (Nat.two_pow_pos v)
  have hsplit : 2 ^ W * (2 ^ v - 1) = 2 ^ (v + W) - 2 ^ W := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm, ← Nat.pow_add]
  rw [hsplit]
  dsimp [gap] at hgap_le
  omega

end PowerSeparation
end Collatz
