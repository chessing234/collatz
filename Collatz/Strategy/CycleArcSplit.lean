import Collatz.Strategy.CyclicOrder
import Collatz.Strategy.CycleCollisionBudget
import Collatz.Strategy.Discrepancy
import Collatz.Strategy.InfiniteWord
import Collatz.Strategy.RotationLaw
import Collatz.Structure.CycleSum

/-! A split of a cycle into two contracting arcs constrains the actual
endpoint distance. Cyclic window counts show which arithmetic splits
must occur, even though the order of their bits is unknown. -/

namespace Collatz.CycleArcSplit

open Collatz.Arith Collatz.AccCycle Collatz.Sum

/-- Summing the odd counts of all cyclic windows of length `k` counts each
odd position exactly `k` times. -/
theorem cyclic_window_sum {n L : Nat} (h : AccIsCycleOf n L) (k : Nat) :
    sumRange L (fun i => oddCount (acceleratedOrbit i n) k) = k * oddCount n L := by
  induction k with
  | zero => simp [Congruence.oddCount_zero, sumRange_const]
  | succ k ih =>
    have hshift : sumRange L (fun i => acceleratedOrbit k (acceleratedOrbit i n) % 2) = oddCount n L := by
      rw [← RotationLaw.oddCount_rotation_invariant h k, CycleSum.oddCount_eq_sumRange]
      apply sumRange_congr
      intro i _
      rw [acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k i]
    have hs : sumRange L (fun i => oddCount (acceleratedOrbit i n) (k + 1)) =
        sumRange L (fun i => oddCount (acceleratedOrbit i n) k +
          acceleratedOrbit k (acceleratedOrbit i n) % 2) :=
      sumRange_congr (fun i _ => Density.oddCount_succ_last (acceleratedOrbit i n) k)
    rw [hs, sumRange_add, ih, hshift, Nat.succ_mul]

private theorem adjacent_window_eq (n k i : Nat) :
    oddCount (acceleratedOrbit i n) k + acceleratedOrbit (k + i) n % 2 =
      acceleratedOrbit i n % 2 + oddCount (acceleratedOrbit (i + 1) n) k := by
  have hs := AccumulatorArith.oddCount_add (acceleratedOrbit i n) 1 k
  rw [Nat.add_comm 1 k, Density.oddCount_succ_last] at hs
  have hhead : oddCount (acceleratedOrbit i n) 1 = acceleratedOrbit i n % 2 := by
    rw [Density.oddCount_succ_last, Congruence.oddCount_zero, acceleratedOrbit_zero, Nat.zero_add]
  have hnext : acceleratedOrbit 1 (acceleratedOrbit i n) = acceleratedOrbit (i + 1) n := by
    rw [acceleratedOrbit_add, Nat.add_comm 1 i]
  rw [hhead, hnext, acceleratedOrbit_add] at hs
  exact hs

private theorem adjacent_window_bound (n k i : Nat) :
    oddCount (acceleratedOrbit (i + 1) n) k ≤ oddCount (acceleratedOrbit i n) k + 1 ∧
      oddCount (acceleratedOrbit i n) k ≤ oddCount (acceleratedOrbit (i + 1) n) k + 1 := by
  have hs := adjacent_window_eq n k i
  omega

/-- Any integer within strictly less than one of the cyclic mean odd count
is attained by some window. This includes the floor and ceiling of the mean. -/
theorem exists_window_count {n L k b : Nat} (h : AccIsCycleOf n L)
    (hlo : L * b < k * oddCount n L + L) (hhi : k * oddCount n L < L * b + L) :
    ∃ i, i < L ∧ oddCount (acceleratedOrbit i n) k = b := by
  apply Classical.byContradiction
  intro hno
  let f := fun i => oddCount (acceleratedOrbit i n) k
  have hne (i : Nat) (hi : i < L) : f i ≠ b := fun he => hno ⟨i, hi, he⟩
  have hs (i : Nat) : f (i + 1) ≤ f i + 1 ∧ f i ≤ f (i + 1) + 1 := adjacent_window_bound n k i
  have hsum : sumRange L f = k * oddCount n L := cyclic_window_sum h k
  rcases Nat.lt_or_ge (f 0) b with hb | hb
  · have hbelow (i : Nat) (hi : i < L) : f i < b := by
      induction i with
      | zero => exact hb
      | succ i ih =>
        have hp := ih (by omega)
        have ha := (hs i).1
        have hn := hne (i + 1) hi
        omega
    have hbound := sumRange_le (f := f) (g := fun _ => b - 1) (fun i hi => by have := hbelow i hi; omega)
    change sumRange L f ≤ sumRange L (fun _ => b - 1) at hbound
    rw [hsum, sumRange_const] at hbound
    have ht : L * (b - 1) + L = L * b := by
      have he : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
      calc
        _ = L * (b - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = _ := by rw [he]
    omega
  · have habove (i : Nat) (hi : i < L) : b < f i := by
      induction i with
      | zero => have := hne 0 hi; omega
      | succ i ih =>
        have hp := ih (by omega)
        have ha := (hs i).2
        have hn := hne (i + 1) hi
        omega
    have hbound := sumRange_le (f := fun _ => b + 1) (fun i hi => habove i hi)
    change sumRange L (fun _ => b + 1) ≤ sumRange L f at hbound
    rw [hsum, sumRange_const, Nat.mul_succ] at hbound
    omega

/-- In the near-resonant range, every arithmetic division of the power
gap into two contracting coefficients occurs on the cycle. -/
theorem arithmetic_split_realized {n L k b : Nat} (h : AccIsCycleOf n L)
    (hnear : 2 ^ L < 3 ^ (oddCount n L + 1)) (hk : 0 < k) (hkL : k < L)
    (hb : b ≤ oddCount n L) (hf : 3 ^ b ≤ 2 ^ k) (hr : 3 ^ (oddCount n L - b) ≤ 2 ^ (L - k)) :
    ∃ i, i < L ∧ oddCount (acceleratedOrbit i n) k = b := by
  let a := oddCount n L
  have h₁ := CyclicOrder.light_walk_lt (L := L) (a := a) (A := b) hnear hk hf
  have h₂ := CyclicOrder.light_walk_lt (L := L) (a := a) (A := a - b) hnear
    (by omega : 0 < L - k) hr
  have he₁ : (a + 1) * k = a * k + k := by rw [Nat.succ_mul]
  have he₂ : L * (a - b) = L * a - L * b := Nat.mul_sub_left_distrib ..
  have he₃ : (a + 1) * (L - k) = L * a - a * k + (L - k) := by
    rw [Nat.succ_mul, Nat.mul_sub_left_distrib, Nat.mul_comm a L]
  have hb' : L * b ≤ L * a := Nat.mul_le_mul_left L hb
  have hk' : a * k ≤ L * a := by
    rw [Nat.mul_comm L a]
    exact Nat.mul_le_mul_left a (Nat.le_of_lt hkL)
  rw [he₁] at h₁
  rw [he₂, he₃] at h₂
  refine exists_window_count h ?_ ?_
  · change L * b < k * a + L
    rw [Nat.mul_comm k a]
    omega
  · change k * a < L * b + L
    rw [Nat.mul_comm k a]
    omega

private theorem pow_le_distance_of_same_residue {x y t : Nat} (hxy : x < y)
    (hres : x % 2 ^ t = y % 2 ^ t) : 2 ^ t ≤ y - x := by
  let d := 2 ^ t
  have hx := Nat.div_add_mod x d
  have hy := Nat.div_add_mod y d
  have he : y - x = d * (y / d - x / d) := by
    rw [Nat.mul_sub_left_distrib]
    change x % d = y % d at hres
    omega
  exact Nat.le_of_dvd (by omega) ⟨_, he⟩

/-- For any rise, the return arc's own gap pays for the separation of the
two endpoints. This also applies when the ascending arc expands. -/
theorem matching_prefix_pays_return_gap {x L k t : Nat} (h : AccIsCycleOf x L) (hk : k ≤ L)
    (hrise : x < acceleratedOrbit k x)
    (hpar : parityVector x t = parityVector (acceleratedOrbit k x) t) :
    let y := acceleratedOrbit k x
    let c := oddCount y (L - k)
    2 ^ t * 3 ^ c ≤ (2 ^ (L - k) - 3 ^ c) * x := by
  let y := acceleratedOrbit k x
  let C := 3 ^ oddCount y (L - k)
  let B := 2 ^ (L - k)
  have hback : acceleratedOrbit (L - k) y = x := by
    change acceleratedOrbit (L - k) (acceleratedOrbit k x) = x
    rw [acceleratedOrbit_add, Nat.sub_add_cancel hk, h.2]
  have hupper := Discrepancy.orbit_lower y (L - k)
  rw [hback] at hupper
  change C * y ≤ B * x at hupper
  have hlo := Nat.mul_le_mul_right C
    (pow_le_distance_of_same_residue hrise (InfiniteWord.mod_eq_of_parityVector_eq hpar))
  change 2 ^ t * C ≤ (y - x) * C at hlo
  rw [Nat.mul_sub_right_distrib, Nat.mul_comm y C, Nat.mul_comm x C] at hlo
  have hbase : C * x ≤ B * x :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hrise)) hupper
  change 2 ^ t * C ≤ (B - C) * x
  rw [Nat.mul_sub_right_distrib]
  omega

/-- For a pair of endpoints whose two connecting arcs contract, the two
heights are within the ratio `2^L / 3^a` of each other. -/
theorem contracting_split_endpoint_ratios {x L k : Nat} (h : AccIsCycleOf x L) (hk : k ≤ L)
    (hf : 3 ^ oddCount x k ≤ 2 ^ k)
    (hr : 3 ^ oddCount (acceleratedOrbit k x) (L - k) ≤ 2 ^ (L - k)) :
    3 ^ oddCount x L * acceleratedOrbit k x ≤ 2 ^ L * x ∧
      3 ^ oddCount x L * x ≤ 2 ^ L * acceleratedOrbit k x := by
  let y := acceleratedOrbit k x
  have hsum : k + (L - k) = L := by omega
  have hback : acceleratedOrbit (L - k) y = x := by
    change acceleratedOrbit (L - k) (acceleratedOrbit k x) = x
    rw [acceleratedOrbit_add, Nat.add_comm (L - k) k, hsum, h.2]
  have hcount := AccumulatorArith.oddCount_add x k (L - k)
  rw [hsum] at hcount
  have hA : 3 ^ oddCount x L = 3 ^ oddCount x k * 3 ^ oddCount y (L - k) := by
    rw [hcount, Nat.pow_add]
  have hB : 2 ^ L = 2 ^ k * 2 ^ (L - k) := by rw [← Nat.pow_add, hsum]
  obtain ⟨c, hc⟩ := acceleratedOrbit_affine x k
  obtain ⟨d, hd⟩ := acceleratedOrbit_affine y (L - k)
  rw [hback] at hd
  have hlower : 3 ^ oddCount x k * x ≤ 2 ^ k * y := by
    change 2 ^ k * y = 3 ^ oddCount x k * x + c at hc
    omega
  have hreturn : 3 ^ oddCount y (L - k) * y ≤ 2 ^ (L - k) * x := by omega
  change 3 ^ oddCount x L * y ≤ 2 ^ L * x ∧ 3 ^ oddCount x L * x ≤ 2 ^ L * y
  rw [hA, hB]
  constructor
  · rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul hf hreturn
  · calc
      _ = 3 ^ oddCount y (L - k) * (3 ^ oddCount x k * x) := by ac_rfl
      _ ≤ 2 ^ (L - k) * (2 ^ k * y) := Nat.mul_le_mul hr hlower
      _ = _ := by ac_rfl

/-- A matching parity prefix makes the distance between the two distinct
endpoints at least `2^t`. The cycle gap must pay for that distance. -/
theorem matching_prefix_pays_cycle_gap {x L k t : Nat} (hx : 0 < x)
    (h : AccIsCycleOf x L) (hk : k ≤ L)
    (hf : 3 ^ oddCount x k ≤ 2 ^ k)
    (hr : 3 ^ oddCount (acceleratedOrbit k x) (L - k) ≤ 2 ^ (L - k))
    (hdist : acceleratedOrbit k x ≠ x)
    (hpar : parityVector x t = parityVector (acceleratedOrbit k x) t) :
    2 ^ t * 3 ^ oddCount x L ≤ (2 ^ L - 3 ^ oddCount x L) * min x (acceleratedOrbit k x) := by
  let y := acceleratedOrbit k x
  let A := 3 ^ oddCount x L
  let B := 2 ^ L
  have hAB : A ≤ B := Nat.le_of_lt (accCycle_bounds hx h).2.2
  obtain ⟨hxy, hyx⟩ := contracting_split_endpoint_ratios h hk hf hr
  change A * y ≤ B * x at hxy
  change A * x ≤ B * y at hyx
  have hres := InfiniteWord.mod_eq_of_parityVector_eq hpar
  change 2 ^ t * A ≤ (B - A) * min x y
  rcases Nat.lt_or_ge x y with hlt | hle
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
    have hlow := Nat.mul_le_mul_right A (pow_le_distance_of_same_residue hlt hres)
    rw [Nat.mul_sub_right_distrib, Nat.mul_comm y A, Nat.mul_comm x A] at hlow
    rw [Nat.mul_sub_right_distrib]
    have hbase := Nat.mul_le_mul_right x hAB
    omega
  · have hlt : y < x := Nat.lt_of_le_of_ne hle hdist
    rw [Nat.min_eq_right hle]
    have hlow := Nat.mul_le_mul_right A (pow_le_distance_of_same_residue hlt hres.symm)
    rw [Nat.mul_sub_right_distrib, Nat.mul_comm x A, Nat.mul_comm y A] at hlow
    rw [Nat.mul_sub_right_distrib]
    have hbase := Nat.mul_le_mul_right y hAB
    omega

private theorem orbit_mod_period {n L : Nat} (h : AccIsCycleOf n L) (i : Nat) :
    acceleratedOrbit i n = acceleratedOrbit (i % L) n := by
  calc
    _ = acceleratedOrbit (L * (i / L) + i % L) n := by rw [Nat.div_add_mod]
    _ = acceleratedOrbit (i % L) (acceleratedOrbit (L * (i / L)) n) := by
      rw [acceleratedOrbit_add, Nat.add_comm (i % L)]
    _ = _ := by rw [accOrbit_mul_period h.2]

/-- A nonzero proper offset cannot have one constant odd count at all rotations. -/
theorem exists_window_count_ne_of_least_period {n L k b : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n) (hk : 0 < k) (hkL : k < L) :
    ∃ i, i < L ∧ oddCount (acceleratedOrbit i n) k ≠ b := by
  apply Classical.byContradiction
  intro hno
  have hall (i : Nat) : oddCount (acceleratedOrbit i n) k = b := by
    rw [orbit_mod_period h i]
    apply Classical.byContradiction
    intro hne
    exact hno ⟨i % L, Nat.mod_lt _ h.1, hne⟩
  have hpar (i : Nat) : acceleratedOrbit i n % 2 = acceleratedOrbit i (acceleratedOrbit k n) % 2 := by
    have hs := adjacent_window_eq n k i
    rw [hall i, hall (i + 1)] at hs
    rw [acceleratedOrbit_add, Nat.add_comm i k]
    omega
  apply hmin k hk hkL
  symm
  apply InfiniteWord.eq_of_parityVector_eq_all
  intro t
  unfold parityVector
  rw [show (fun i => acceleratedOrbit i n % 2) =
    (fun i => acceleratedOrbit i (acceleratedOrbit k n) % 2) from funext hpar]

private theorem count_excess_forces_jump {x L k b : Nat} (hk : k ≤ L) (hb : b ≤ oddCount x L)
    (hexcess : b < oddCount x k) (hr : 3 ^ (oddCount x L - b) ≤ 2 ^ (L - k)) :
    3 * 3 ^ oddCount x L * x ≤ 2 ^ L * acceleratedOrbit k x := by
  let a := oddCount x L
  have hlow := Discrepancy.orbit_lower x k
  have hp : 3 ^ b * 3 ≤ 3 ^ oddCount x k := by
    rw [← Nat.pow_succ]
    exact three_pow_le_three_pow hexcess
  have hp' : 3 * (3 ^ b * x) ≤ 2 ^ k * acceleratedOrbit k x := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 (3 ^ b)]
    exact Nat.le_trans (Nat.mul_le_mul_right _ hp) hlow
  have hA : 3 ^ a = 3 ^ b * 3 ^ (a - b) := by rw [← Nat.pow_add, Nat.add_sub_of_le hb]
  have hB : 2 ^ L = 2 ^ k * 2 ^ (L - k) := by rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  change 3 * 3 ^ a * x ≤ 2 ^ L * acceleratedOrbit k x
  rw [hA, hB]
  calc
    _ = (3 * (3 ^ b * x)) * 3 ^ (a - b) := by ac_rfl
    _ ≤ (2 ^ k * acceleratedOrbit k x) * 2 ^ (L - k) := Nat.mul_le_mul hp' hr
    _ = _ := by ac_rfl

/-- A least cycle admitting a contracting arithmetic split must also have
a large change in height at the same offset, in one of the two directions. -/
theorem arithmetic_split_forces_large_ratio {n L k b : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n) (hk : 0 < k) (hkL : k < L)
    (hb : b ≤ oddCount n L) (hf : 3 ^ b ≤ 2 ^ k) (hr : 3 ^ (oddCount n L - b) ≤ 2 ^ (L - k)) :
    ∃ i, i < L ∧
      let x := acceleratedOrbit i n
      let y := acceleratedOrbit k x
      (3 * 3 ^ oddCount n L * x ≤ 2 ^ L * y) ∨ (3 * 3 ^ oddCount n L * y ≤ 2 ^ L * x) := by
  obtain ⟨i, hi, hne⟩ := exists_window_count_ne_of_least_period (b := b) h hmin hk hkL
  refine ⟨i, hi, ?_⟩
  let x := acceleratedOrbit i n
  let y := acceleratedOrbit k x
  let a := oddCount n L
  have hx := accIsCycleOf_orbit h i
  have hax : oddCount x L = a := RotationLaw.oddCount_rotation_invariant h i
  change oddCount x k ≠ b at hne
  change (3 * 3 ^ a * x ≤ 2 ^ L * y) ∨ (3 * 3 ^ a * y ≤ 2 ^ L * x)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · right
    have hsplit : a = oddCount x k + oddCount y (L - k) := by
      rw [← hax]
      exact Discrepancy.oddCount_split (Nat.le_of_lt hkL)
    have hay : oddCount y L = a := (RotationLaw.oddCount_rotation_invariant hx k).trans hax
    have hback : acceleratedOrbit (L - k) y = x := by
      change acceleratedOrbit (L - k) (acceleratedOrbit k x) = x
      rw [acceleratedOrbit_add, Nat.sub_add_cancel (Nat.le_of_lt hkL), hx.2]
    have hjump := count_excess_forces_jump (x := y) (L := L) (k := L - k) (b := a - b)
      (by omega) (by rw [hay]; omega) (by omega) (by
        rw [hay, show a - (a - b) = b by omega, show L - (L - k) = k by omega]
        exact hf)
    rwa [hback, hay] at hjump
  · left
    have hjump := count_excess_forces_jump (x := x) (L := L) (k := k) (b := b)
      (Nat.le_of_lt hkL) (by rw [hax]; exact hb) hgt (by rw [hax]; exact hr)
    rwa [hax] at hjump

/-- A realizable arithmetic split requires two distinct, close heights.
Even without matching any positive number of parity bits, each height is
at least the reciprocal relative gap `3^a/(2^L-3^a)`. -/
theorem arithmetic_split_forces_high_points {n L k b : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n)
    (hnear : 2 ^ L < 3 ^ (oddCount n L + 1)) (hk : 0 < k) (hkL : k < L)
    (hb : b ≤ oddCount n L) (hf : 3 ^ b ≤ 2 ^ k) (hr : 3 ^ (oddCount n L - b) ≤ 2 ^ (L - k)) :
    ∃ i, i < L ∧ 3 ^ oddCount n L ≤
      (2 ^ L - 3 ^ oddCount n L) * min (acceleratedOrbit i n) (acceleratedOrbit (k + i) n) := by
  obtain ⟨i, hi, hcount⟩ := arithmetic_split_realized h hnear hk hkL hb hf hr
  let x := acceleratedOrbit i n
  let y := acceleratedOrbit k x
  have hx := accIsCycleOf_orbit h i
  have hax : oddCount x L = oddCount n L := RotationLaw.oddCount_rotation_invariant h i
  have hd : y ≠ x := by
    intro he
    have he' : acceleratedOrbit i (acceleratedOrbit k n) = acceleratedOrbit i n := by
      calc
        _ = acceleratedOrbit k (acceleratedOrbit i n) := by
          rw [acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm i k]
        _ = _ := he
    exact hmin k hk hkL (CycleCollisionBudget.periodic_eq_of_synchronized
      ⟨L, accIsCycleOf_orbit h k⟩ ⟨L, h⟩ he')
  have hsplit := Discrepancy.oddCount_split (n := x) (L := L) (Nat.le_of_lt hkL)
  change oddCount x L = oddCount x k + oddCount y (L - k) at hsplit
  change oddCount x k = b at hcount
  rw [hax, hcount] at hsplit
  have hf' : 3 ^ oddCount x k ≤ 2 ^ k := by rw [hcount]; exact hf
  have hr' : 3 ^ oddCount y (L - k) ≤ 2 ^ (L - k) := by
    rw [show oddCount y (L - k) = oddCount n L - b by omega]
    exact hr
  have hw := matching_prefix_pays_cycle_gap (t := 0) (acceleratedOrbit_positive hn i)
    hx (Nat.le_of_lt hkL) hf' hr' hd (by rfl)
  change 2 ^ 0 * 3 ^ oddCount x L ≤ (2 ^ L - 3 ^ oddCount x L) * min x y at hw
  rw [Nat.pow_zero, Nat.one_mul, hax, show y = acceleratedOrbit (k + i) n from
    acceleratedOrbit_add k i n] at hw
  exact ⟨i, hi, hw⟩

/-- A strictly shorter odd-count pair with at least as small a normalized
gap supplies a proper contracting split of the candidate period. -/
theorem split_of_smaller_odd_count {L a k b : Nat} (hb : b < a)
    (hlight : 3 ^ b < 2 ^ k) (hbetter : 3 ^ a * 2 ^ k ≤ 2 ^ L * 3 ^ b) :
    0 < k ∧ k < L ∧ 3 ^ (a - b) ≤ 2 ^ (L - k) := by
  have hk : 0 < k := by
    cases k with
    | zero => have hp := three_pow_pos b; simp at hlight
    | succ k => exact Nat.succ_pos _
  have hkL : k < L := by
    apply Nat.lt_of_not_ge
    intro hge
    have hpow := two_pow_le_two_pow hge
    have hlt := Nat.mul_lt_mul_of_pos_left (three_pow_lt_three_pow hb) (two_pow_pos L)
    rw [Nat.mul_comm (2 ^ L) (3 ^ a)] at hlt
    exact Nat.not_lt_of_ge (Nat.le_trans (Nat.mul_le_mul_left (3 ^ a) hpow) hbetter) hlt
  refine ⟨hk, hkL, Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (three_pow_pos b) (two_pow_pos k))⟩
  calc
    (3 ^ b * 2 ^ k) * 3 ^ (a - b) = 3 ^ a * 2 ^ k := by
      rw [Nat.mul_right_comm, ← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hb)]
    _ ≤ 2 ^ L * 3 ^ b := hbetter
    _ = (3 ^ b * 2 ^ k) * 2 ^ (L - k) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hkL), Nat.mul_comm (3 ^ b)]

/-- Unless its normalized gap beats every smaller odd count, a near-resonant
least cycle must contain two distinct points at least `3^a/(2^L-3^a)`,
as well as a jump at the same offset by a ratio at least `3·3^a/2^L`. -/
theorem smaller_gap_forces_height_and_spread {n L k b : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n)
    (hnear : 2 ^ L < 3 ^ (oddCount n L + 1)) (hb : b < oddCount n L)
    (hlight : 3 ^ b < 2 ^ k) (hbetter : 3 ^ oddCount n L * 2 ^ k ≤ 2 ^ L * 3 ^ b) :
    (∃ i, i < L ∧ 3 ^ oddCount n L ≤
      (2 ^ L - 3 ^ oddCount n L) * min (acceleratedOrbit i n) (acceleratedOrbit (k + i) n)) ∧
    (∃ i, i < L ∧
      let x := acceleratedOrbit i n
      let y := acceleratedOrbit k x
      (3 * 3 ^ oddCount n L * x ≤ 2 ^ L * y) ∨ (3 * 3 ^ oddCount n L * y ≤ 2 ^ L * x)) := by
  obtain ⟨hk, hkL, hr⟩ := split_of_smaller_odd_count hb hlight hbetter
  exact ⟨arithmetic_split_forces_high_points hn h hmin hnear hk hkL (Nat.le_of_lt hb) (Nat.le_of_lt hlight) hr,
    arithmetic_split_forces_large_ratio h hmin hk hkL (Nat.le_of_lt hb) (Nat.le_of_lt hlight) hr⟩

private theorem mixed_powers_lt {A B L k : Nat} (hA : 0 < A) (hAB : A < B) (hkL : k < L) :
    A ^ L * B ^ k < A ^ k * B ^ L := by
  let r := L - k
  have he : k + r = L := by dsimp [r]; omega
  have ha : A ^ L = A ^ k * A ^ r := by rw [← Nat.pow_add, he]
  have hb : B ^ L = B ^ k * B ^ r := by rw [← Nat.pow_add, he]
  have hp : 0 < A ^ k * B ^ k := Nat.mul_pos (Nat.pow_pos hA) (Nat.pow_pos (by omega))
  rw [ha, hb]
  calc
    _ = (A ^ k * B ^ k) * A ^ r := by ac_rfl
    _ < (A ^ k * B ^ k) * B ^ r :=
      Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hAB (by dsimp [r]; omega)) hp
    _ = _ := by ac_rfl

/-- An expanding coefficient of size at most `3·3^a/2^L` still has an
odd count within one of the cyclic mean, so some arc realizes it. -/
theorem mildly_expanding_window_realized {n L k b : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hk : 0 < k) (hkL : k < L)
    (hexpand : 2 ^ k < 3 ^ b) (hcap : 2 ^ L * 3 ^ b ≤ 3 * 3 ^ oddCount n L * 2 ^ k) :
    ∃ i, i < L ∧ oddCount (acceleratedOrbit i n) k = b := by
  let a := oddCount n L
  let A := 3 ^ a
  let B := 2 ^ L
  let U := 3 ^ b
  let V := 2 ^ k
  have hAB : A < B := (accCycle_bounds hn h).2.2
  have hmean : a * k < L * b :=
    CyclicOrder.heavy_walk_pos hAB hk (Nat.le_of_lt hexpand)
  have hcap' : B * U ≤ (3 * A) * V := hcap
  have hv : V ^ L = B ^ k := by
    dsimp [V, B]
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm k L]
  have hp := Nat.pow_le_pow_left hcap' L
  rw [Nat.mul_pow B U, Nat.mul_pow (3 * A) V, Nat.mul_pow 3 A, hv] at hp
  have hlt : B ^ L * U ^ L < B ^ L * (3 ^ L * A ^ k) := calc
    _ ≤ (3 ^ L * A ^ L) * B ^ k := hp
    _ = 3 ^ L * (A ^ L * B ^ k) := by ac_rfl
    _ < 3 ^ L * (A ^ k * B ^ L) :=
      Nat.mul_lt_mul_of_pos_left (mixed_powers_lt (three_pow_pos _) hAB hkL) (three_pow_pos _)
    _ = _ := by ac_rfl
  have hb : (3 : Nat) ^ (b * L) < 3 ^ (L + a * k) := by
    have ht := Nat.lt_of_mul_lt_mul_left hlt
    change (3 ^ b : Nat) ^ L < 3 ^ L * (3 ^ a : Nat) ^ k at ht
    rw [← Nat.pow_mul 3 b L, ← Nat.pow_mul 3 a k, ← Nat.pow_add] at ht
    exact ht
  have hhi : b * L < L + a * k := by
    apply Nat.lt_of_not_ge
    intro hge
    exact Nat.not_lt_of_ge (three_pow_le_three_pow hge) hb
  refine exists_window_count h ?_ ?_
  · change L * b < k * a + L
    rw [Nat.mul_comm L b, Nat.mul_comm k a]
    omega
  · change k * a < L * b + L
    rw [Nat.mul_comm k a]
    omega

/-- A small expanding coefficient imposes an orbit height requirement
even when no split into two contracting coefficients exists. -/
theorem mildly_expanding_window_forces_height {n L k b : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hk : 0 < k) (hkL : k < L)
    (hexpand : 2 ^ k < 3 ^ b) (hcap : 2 ^ L * 3 ^ b ≤ 3 * 3 ^ oddCount n L * 2 ^ k) :
    ∃ i, i < L ∧ 3 ^ (oddCount n L - b) ≤
      (2 ^ (L - k) - 3 ^ (oddCount n L - b)) * acceleratedOrbit i n := by
  obtain ⟨i, hi, hcount⟩ := mildly_expanding_window_realized hn h hk hkL hexpand hcap
  let x := acceleratedOrbit i n
  let y := acceleratedOrbit k x
  have hx := accIsCycleOf_orbit h i
  have hpos := acceleratedOrbit_positive hn i
  have hax : oddCount x L = oddCount n L := RotationLaw.oddCount_rotation_invariant h i
  have hlo := Discrepancy.orbit_lower x k
  change oddCount x k = b at hcount
  rw [hcount] at hlo
  have hrise : x < y := Nat.lt_of_mul_lt_mul_left (a := 2 ^ k)
    (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hexpand hpos) hlo)
  have hs := Discrepancy.oddCount_split (n := x) (L := L) (Nat.le_of_lt hkL)
  change oddCount x L = oddCount x k + oddCount y (L - k) at hs
  rw [hax, hcount] at hs
  have hc : oddCount y (L - k) = oddCount n L - b := by omega
  have hp := matching_prefix_pays_return_gap (t := 0) hx (Nat.le_of_lt hkL) hrise (by rfl)
  change 2 ^ 0 * 3 ^ oddCount y (L - k) ≤ (2 ^ (L - k) - 3 ^ oddCount y (L - k)) * x at hp
  rw [Nat.pow_zero, Nat.one_mul, hc] at hp
  exact ⟨i, hi, hp⟩

end Collatz.CycleArcSplit
