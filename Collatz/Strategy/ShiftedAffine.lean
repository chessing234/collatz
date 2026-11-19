import Collatz.Strategy.AffineExact

namespace Collatz.RunAlgebra

open Collatz.AffineExact

/-! ## The shifted accumulator -/

/-- The additive defect after `j` steps in the coordinate `u = x + 1`.  Odd steps
transport it (`A ↦ 3A`); even steps create it (`A ↦ A + 2 ^ j`). -/
def runA : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x =>
      if acceleratedOrbit j x % 2 = 1 then 3 * runA j x else runA j x + 2 ^ j

@[simp] theorem runA_zero (x : Nat) : runA 0 x = 0 := rfl

theorem runA_odd {j x : Nat} (h : acceleratedOrbit j x % 2 = 1) :
    runA (j + 1) x = 3 * runA j x := by
  rw [runA, if_pos h]

theorem runA_even {j x : Nat} (h : acceleratedOrbit j x % 2 = 0) :
    runA (j + 1) x = runA j x + 2 ^ j := by
  rw [runA, if_neg (by omega)]

/-- **The two accumulators, related.**  Stated without subtraction:
`runA = affineC + 2 ^ j − 3 ^ a`. -/
theorem runA_eq (x : Nat) : ∀ j : Nat,
    runA j x + 3 ^ oddCount x j = affineC j x + 2 ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, runA_even he, affineC_even he, Arith.two_pow_succ]
      omega
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hcount, runA_odd ho, affineC_odd ho, Arith.two_pow_succ,
        Arith.three_pow_succ]
      omega

/-- **The shifted exact law.**  In the coordinate `u = x + 1` the multiplier is
`3 ^ a / 2 ^ j` and the *entire* additive defect is `runA`. -/
theorem shifted_affine_exact (x j : Nat) :
    2 ^ j * (acceleratedOrbit j x + 1)
      = 3 ^ oddCount x j * (x + 1) + runA j x := by
  have hex := affine_exact x j
  have hrel := runA_eq x j
  have hL : (2:Nat) ^ j * (acceleratedOrbit j x + 1)
      = 2 ^ j * acceleratedOrbit j x + 2 ^ j := by
    rw [Nat.mul_add, Nat.mul_one]
  have hR : (3:Nat) ^ oddCount x j * (x + 1) = 3 ^ oddCount x j * x + 3 ^ oddCount x j := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

end Collatz.RunAlgebra
