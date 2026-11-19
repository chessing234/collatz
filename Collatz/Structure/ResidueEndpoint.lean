import Collatz.Structure.Density

/-! The small representative of a binary class lands in the small
representative interval of its ternary image class. -/

namespace Collatz.ResidueEndpoint

open Collatz.Arith Collatz.Congruence Collatz.Density

/-- A representative below `2^k` has endpoint strictly below `3^a`, where
`a` is the number of odd steps in its prefix. -/
theorem representative_lt_three_pow {k r : Nat} (hr : r < 2 ^ k) :
    acceleratedOrbit k r < 3 ^ oddCount r k := by
  induction k generalizing r with
  | zero => simpa [acceleratedOrbit] using hr
  | succ k ih =>
    let q := r / 2 ^ k
    let s := r % 2 ^ k
    have hs : s < 2 ^ k := Nat.mod_lt _ (two_pow_pos _)
    have hq : q < 2 := (Nat.div_lt_iff_lt_mul (two_pow_pos k)).mpr (by
      rw [← two_pow_succ]; exact hr)
    have ho : oddCount r k = oddCount s k := oddCount_mod r k
    have heq : acceleratedOrbit k r = 3 ^ oddCount s k * q + acceleratedOrbit k s := by
      conv => lhs; rw [← Nat.div_add_mod r (2 ^ k)]
      exact accOrbit_pow_two_mul_add k q s
    have hprev : acceleratedOrbit k r < 2 * 3 ^ oddCount r k := by
      have hb := Nat.mul_le_mul_left (3 ^ oddCount s k) (show q ≤ 1 by omega)
      rw [Nat.mul_one] at hb
      have ht := ih hs
      rw [heq, ho]
      omega
    rw [acceleratedOrbit_succ_step, oddCount_succ_last]
    rcases mod_two_eq_zero_or_one (acceleratedOrbit k r) with he | hd
    · rw [he, Nat.add_zero, acceleratedStep, if_pos he]
      omega
    · rw [hd, three_pow_succ, acceleratedStep, if_neg (by omega)]
      omega

/-- Reducing the input modulo `2^k` and the output modulo `3^a` commutes
with the orbit prefix. This also identifies the binary and ternary quotients. -/
theorem quotient_remainder (n k : Nat) :
    acceleratedOrbit k n / 3 ^ oddCount n k = n / 2 ^ k ∧
    acceleratedOrbit k n % 3 ^ oddCount n k = acceleratedOrbit k (n % 2 ^ k) := by
  let r := n % 2 ^ k
  have hr : r < 2 ^ k := Nat.mod_lt _ (two_pow_pos _)
  have ha : oddCount n k = oddCount r k := oddCount_mod n k
  have he : acceleratedOrbit k n = 3 ^ oddCount r k * (n / 2 ^ k) + acceleratedOrbit k r := by
    conv => lhs; rw [← Nat.div_add_mod n (2 ^ k)]
    exact accOrbit_pow_two_mul_add _ _ _
  have hlo := representative_lt_three_pow hr
  rw [he, ha]
  constructor
  · rw [Nat.mul_add_div (three_pow_pos _), Nat.div_eq_of_lt hlo, Nat.add_zero]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

end Collatz.ResidueEndpoint
