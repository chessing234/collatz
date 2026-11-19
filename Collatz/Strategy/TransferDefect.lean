import Collatz.Strategy.GapBarriers

/-!
# Finite-memory transfer functions

On odd inputs the odd-to-odd step is `T(n) = (3n+1) / 2^{v₂(3n+1)}`.
A level-`k` potential depends on an odd input only through its residue
modulo `2^k`. For every `k ≥ 1` the odd integer `2^{k+1} - 1` lies in the
class `-1`, and its image `3·2^k - 1` lies in that same class, after exactly
one halving. The step strictly increases the input. Thus every level-`k`
potential is constant across a strict increase, and the uniform defect of the
centered cocycle cannot fall below `log 2`.
-/

namespace Collatz.TransferDefect

open Collatz Collatz.GapBarriers

private theorem two_pow_sub_one_lt (k : Nat) : 2 ^ k - 1 < 2 ^ k := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

private theorem mod_add_multiple (m r q : Nat) (hr : r < m) :
    (r + q * m) % m = r := by
  induction q with
  | zero => simp [Nat.mod_eq_of_lt hr]
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_mod, ih, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt hr]

/-- Both endpoints of the ghost step are congruent to `-1` modulo `2^k`. -/
theorem ghost_class (k : Nat) :
    (2 ^ (k + 1) - 1) % 2 ^ k = 2 ^ k - 1 ∧
      (3 * 2 ^ k - 1) % 2 ^ k = 2 ^ k - 1 := by
  have hr := two_pow_sub_one_lt k
  constructor
  · have hsplit : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rw [hsplit]
    exact mod_add_multiple (2 ^ k) (2 ^ k - 1) 1 hr
  · have hsplit : 3 * 2 ^ k - 1 = (2 ^ k - 1) + 2 * 2 ^ k := by omega
    rw [hsplit]
    exact mod_add_multiple (2 ^ k) (2 ^ k - 1) 2 hr

private theorem two_mul_pow (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

private theorem double_sub_one (a : Nat) (ha : 0 < a) :
    2 * a - 1 = 2 * (a - 1) + 1 := by
  have hsum : (a - 1) + 1 = a := by omega
  calc
    2 * a - 1 = 2 * ((a - 1) + 1) - 1 := by rw [hsum]
    _ = 2 * (a - 1) + 2 - 1 := by rw [Nat.mul_add]
    _ = 2 * (a - 1) + 1 := by omega

/-- `2^{k+1}-1` takes one halving and lands on `3·2^k-1`. -/
theorem ghost_step (k : Nat) (hk : 1 ≤ k) :
    OddStep (2 ^ (k + 1) - 1) 1 (3 * 2 ^ k - 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · have hsplit : 3 * 2 ^ k - 1 = 2 * (3 * 2 ^ (k - 1) - 1) + 1 := by
      cases k with
      | zero => omega
      | succ k =>
        rw [Nat.succ_sub_one]
        have hfactor : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by
          rw [two_mul_pow, Nat.mul_left_comm]
        have hinner : 0 < 3 * 2 ^ k := by
          have hpow := Nat.two_pow_pos k
          omega
        rw [hfactor]
        exact double_sub_one (3 * 2 ^ k) hinner
    rw [hsplit, Nat.mul_add_mod_self_left]
  · rw [Nat.pow_one, two_mul_pow]
    have hthree : 2 * (3 * 2 ^ k) = 3 * (2 * 2 ^ k) := by rw [Nat.mul_left_comm]
    have hpos : 0 < 3 * 2 ^ k := by
      have hpow := Nat.two_pow_pos k
      omega
    have hL : 2 * (3 * 2 ^ k - 1) = 2 * (3 * 2 ^ k) - 2 := by
      have h := double_sub_one (3 * 2 ^ k) hpos
      omega
    have hR : 3 * (2 * 2 ^ k) - 2 = 3 * (2 * 2 ^ k - 1) + 1 := by
      have hsum : (2 * 2 ^ k - 1) + 1 = 2 * 2 ^ k := by omega
      calc
        3 * (2 * 2 ^ k) - 2 = 3 * ((2 * 2 ^ k - 1) + 1) - 2 := by rw [hsum]
        _ = 3 * (2 * 2 ^ k - 1) + 3 - 2 := by rw [Nat.mul_add]
        _ = 3 * (2 * 2 ^ k - 1) + 1 := by omega
    calc
      2 * (3 * 2 ^ k - 1) = 2 * (3 * 2 ^ k) - 2 := hL
      _ = 3 * (2 * 2 ^ k) - 2 := by rw [hthree]
      _ = 3 * (2 * 2 ^ k - 1) + 1 := hR

/-- The ghost step is a strict increase inside one residue class. -/
theorem ghost_increases (k : Nat) (hk : 1 ≤ k) :
    let n := 2 ^ (k + 1) - 1
    let m := 3 * 2 ^ k - 1
    OddStep n 1 m ∧ n % 2 ^ k = m % 2 ^ k ∧ n < m := by
  refine ⟨ghost_step k hk, ?_, ?_⟩
  · have hclass := ghost_class k
    rw [hclass.1, hclass.2]
  · exact lt_of_k_one
      (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero k))) (ghost_step k hk)

/-- Every potential that depends only on `k` bits is constant on the ghost
step, while the odd-to-odd image is strictly larger. -/
theorem level_potential_constant_on_increase {k : Nat} (hk : 1 ≤ k)
    {α : Type} (η : Nat → α)
    (hmod : ∀ x y, x % 2 ^ k = y % 2 ^ k → η x = η y) :
    ∃ n m, OddStep n 1 m ∧ n < m ∧ η n = η m := by
  let n := 2 ^ (k + 1) - 1
  let m := 3 * 2 ^ k - 1
  obtain ⟨hstep, hcong, hlt⟩ := ghost_increases k hk
  exact ⟨n, m, hstep, hlt, hmod n m hcong⟩

/-- No positive level-`k` weight can turn the ghost step into a factor of
`3/2` or smaller. The ratio `m/n` strictly exceeds `3/2`, while the two
weights agree. -/
theorem level_weight_misses_three_halves {k : Nat} (hk : 1 ≤ k) (q : Nat → Nat)
    (hmod : ∀ x y, x % 2 ^ k = y % 2 ^ k → q x = q y)
    (hq : ∀ x, 0 < x → 0 < q x) :
    ∃ n m, OddStep n 1 m ∧ 3 * n * q m < 2 * m * q n := by
  let n := 2 ^ (k + 1) - 1
  let m := 3 * 2 ^ k - 1
  obtain ⟨hstep, hcong, hlt⟩ := ghost_increases k hk
  have hn : 0 < n := by omega
  have hm : 0 < m := oddStep_pos hstep
  have hqeq : q n = q m := hmod n m hcong
  refine ⟨n, m, hstep, ?_⟩
  have hmul : 2 * m = 3 * n + 1 := by
    have h := hstep.2.2
    rwa [Nat.pow_one] at h
  have hqpos : 0 < q n := hq n hn
  calc
    3 * n * q m = 3 * n * q n := by rw [hqeq]
    _ < (3 * n + 1) * q n := Nat.mul_lt_mul_of_pos_right (by omega) hqpos
    _ = 2 * m * q n := by rw [hmul]

end Collatz.TransferDefect
