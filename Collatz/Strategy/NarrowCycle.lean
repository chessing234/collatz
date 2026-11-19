import Collatz.Strategy.CycleArcSplit
import Collatz.Strategy.AccumulatorAutomaton
import Collatz.Strategy.GapOne
import Collatz.Strategy.CycleLemma

/-! A narrow range forces balance in all equal-length cyclic windows.
An adjacent swap between two realized periodic words has an independent
arithmetic obstruction. -/

namespace Collatz.NarrowCycle

open Collatz.Arith Collatz.AccCycle Collatz.AffineExact
open Collatz.Sum Collatz.CyclicOrder

/-- Equal-length windows of the cycle have odd counts differing by at most one. -/
def Balanced (n L : Nat) : Prop :=
  ∀ i j k, k ≤ L → oddCount (acceleratedOrbit i n) k ≤ oddCount (acceleratedOrbit j n) k + 1

/-- If `R` is the ratio of maximum to minimum cycle height and `P` is
the cycle coefficient, then `R² < 9P` forces balance. -/
theorem balanced_of_narrow {n L m M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hwidth : 2 ^ L * (M * M) < 9 * 3 ^ oddCount n L * (m * m)) : Balanced n L := by
  intro i j k hk
  apply Nat.le_of_not_gt
  intro hdiff
  let x := acceleratedOrbit i n
  let y := acceleratedOrbit j n
  let a := oddCount n L
  let b := oddCount y k
  let U := 3 ^ b
  let V := 2 ^ k
  let A := 3 ^ a
  let B := 2 ^ L
  have hpow : 9 * U ≤ 3 ^ oddCount x k := by
    change 9 * 3 ^ b ≤ 3 ^ oddCount x k
    rw [show (9 : Nat) = 3 ^ 2 from rfl, ← Nat.pow_add]
    exact three_pow_le_three_pow (by change b + 1 < oddCount x k at hdiff; omega)
  have hhigh : 9 * U * m ≤ V * M := by
    calc
      _ ≤ 3 ^ oddCount x k * x := Nat.mul_le_mul hpow (hlo i)
      _ ≤ V * acceleratedOrbit k x := Discrepancy.orbit_lower x k
      _ ≤ _ := Nat.mul_le_mul_left V (by rw [show x = acceleratedOrbit i n from rfl, acceleratedOrbit_add]; exact hhi _)
  have hlow : A * (V * m) ≤ B * (U * M) := by
    have hy := Discrepancy.orbit_upper (acceleratedOrbit_positive hn j) (accIsCycleOf_orbit h j) hk
    rw [RotationLaw.oddCount_rotation_invariant h j] at hy
    calc
      _ ≤ A * (V * acceleratedOrbit k y) := Nat.mul_le_mul_left A
        (Nat.mul_le_mul_left V (by rw [show y = acceleratedOrbit j n from rfl, acceleratedOrbit_add]; exact hlo _))
      _ ≤ B * (U * y) := hy
      _ ≤ _ := Nat.mul_le_mul_left B (Nat.mul_le_mul_left U (hhi j))
  have hscaled : (U * V) * (9 * A * (m * m)) ≤ (U * V) * (B * (M * M)) := by
    calc
      _ = (9 * U * m) * (A * (V * m)) := by ac_rfl
      _ ≤ (V * M) * (B * (U * M)) := Nat.mul_le_mul hhigh hlow
      _ = _ := by ac_rfl
  exact Nat.not_le_of_gt hwidth
    (Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos (three_pow_pos b) (two_pow_pos k)))

/-- Matching parities give the same odd count and affine correction. -/
theorem same_parities_same_accumulator {x y : Nat} (k : Nat)
    (h : ∀ i, i < k → acceleratedOrbit i x % 2 = acceleratedOrbit i y % 2) :
    oddCount x k = oddCount y k ∧ affineC k x = affineC k y := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hcount, hc⟩ := ih (fun i hi => h i (by omega))
    have he := h k (Nat.lt_succ_self k)
    constructor
    · rw [Density.oddCount_succ_last, Density.oddCount_succ_last, hcount, he]
    · rcases mod_two_eq_zero_or_one (acceleratedOrbit k x) with heven | hodd
      · rw [affineC_even heven, affineC_even (he.symm.trans heven), hc]
      · rw [affineC_odd hodd, affineC_odd (he.symm.trans hodd), hc]

private theorem even_odd_prefix {x : Nat} (he : x % 2 = 0) (ho : acceleratedOrbit 1 x % 2 = 1) :
    oddCount x 2 = 1 ∧ affineC 2 x = 2 := by
  have h0 : acceleratedOrbit 0 x % 2 = 0 := he
  constructor
  · change oddCount x (1 + 1) = 1
    rw [Density.oddCount_succ_last, ho, show (1 : Nat) = 0 + 1 from rfl,
      Density.oddCount_succ_last, Congruence.oddCount_zero, h0]
  · change affineC (1 + 1) x = 2
    rw [affineC_odd ho, affineC_even h0, affineC_zero]

private theorem odd_even_prefix {y : Nat} (ho : y % 2 = 1) (he : acceleratedOrbit 1 y % 2 = 0) :
    oddCount y 2 = 1 ∧ affineC 2 y = 1 := by
  have h0 : acceleratedOrbit 0 y % 2 = 1 := ho
  constructor
  · change oddCount y (1 + 1) = 1
    rw [Density.oddCount_succ_last, he, show (1 : Nat) = 0 + 1 from rfl,
      Density.oddCount_succ_last, Congruence.oddCount_zero, h0]
  · change affineC (1 + 1) y = 1
    rw [affineC_even he, affineC_odd h0, affineC_zero]

/-- Two realized period words `01·u` and `10·u` force gap one. The gap
divides their accumulator difference, which is a power of three. -/
theorem adjacent_swap_forces_trivial {x y L : Nat} (hx : 0 < x) (hy : 0 < y)
    (hpx : AccIsCycleOf x L) (hpy : AccIsCycleOf y L)
    (hex : x % 2 = 0) (hox : acceleratedOrbit 1 x % 2 = 1)
    (hoy : y % 2 = 1) (hey : acceleratedOrbit 1 y % 2 = 0)
    (hsame : ∀ i, i < L - 2 → acceleratedOrbit i (acceleratedOrbit 2 x) % 2 =
      acceleratedOrbit i (acceleratedOrbit 2 y) % 2) : L = 2 ∧ (x = 1 ∨ x = 2) := by
  let k := L - 2
  let u := acceleratedOrbit 2 x
  let v := acceleratedOrbit 2 y
  let q := oddCount u k
  let C := affineC k u
  let D := 2 ^ L - 3 ^ oddCount x L
  have hsum : 2 + k = L := Nat.add_sub_of_le (two_le_length_of_accCycle hx hpx)
  obtain ⟨hcount, hC⟩ := same_parities_same_accumulator k hsame
  change q = oddCount v k at hcount
  change C = affineC k v at hC
  obtain ⟨hcx, hax⟩ := even_odd_prefix hex hox
  obtain ⟨hcy, hay⟩ := odd_even_prefix hoy hey
  have hcntx : oddCount x L = 1 + q := by
    have h := AccumulatorArith.oddCount_add x 2 k
    rw [hsum, hcx] at h
    exact h
  have hcnty : oddCount y L = oddCount x L := by
    have h := AccumulatorArith.oddCount_add y 2 k
    rw [hsum, hcy] at h
    change oddCount y L = 1 + oddCount v k at h
    rw [← hcount, ← hcntx] at h
    exact h
  have hdX : D * x = 3 ^ q * 2 + 2 ^ 2 * C := by
    have h := AccumulatorArith.affineC_add x 2 k
    rw [hsum, hax] at h
    exact (CycleAccumulator.cycle_gap_mul hx hpx).trans h
  have hdY : D * y = 3 ^ q * 1 + 2 ^ 2 * C := by
    have h := AccumulatorArith.affineC_add y 2 k
    rw [hsum, hay] at h
    change affineC L y = 3 ^ oddCount v k * 1 + 2 ^ 2 * affineC k v at h
    rw [← hcount, ← hC] at h
    have hd := CycleAccumulator.cycle_gap_mul hy hpy
    rw [hcnty] at hd
    exact hd.trans h
  have hdiff : D * x - D * y = 3 ^ q := by rw [hdX, hdY, Nat.mul_one]; omega
  have hdiv : D ∣ 3 ^ q := by
    rw [← hdiff]
    exact Nat.dvd_sub (Nat.dvd_mul_right D x) (Nat.dvd_mul_right D y)
  have hdiv' := Nat.dvd_trans hdiv (Nat.pow_dvd_pow 3 (show q ≤ oddCount x L by omega))
  have hg : D = 1 := AccumulatorAutomaton.eq_one_of_dvd_gap_and_three_pow
    (accCycle_bounds hx hpx).2.2 (Nat.dvd_refl D) hdiv'
  obtain ⟨hL, _, ht⟩ := GapOne.gap_one_forces_trivial hx hpx hg
  exact ⟨hL, ht⟩

private theorem sum_strict_at {L i : Nat} {f g : Nat → Nat} (hi : i < L)
    (hle : ∀ j, j < L → f j ≤ g j) (hlt : f i < g i) : sumRange L f < sumRange L g := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [sumRange_succ, sumRange_succ]
    have hh := hle L (Nat.lt_succ_self L)
    have ht (j : Nat) (hj : j < L) := hle j (by omega)
    by_cases hil : i < L
    · have hs := ih hil ht
      omega
    · have he : i = L := by omega
      have hs := sumRange_le ht
      rw [he] at hlt
      omega

private theorem walk_rotation_bounds {n L i k : Nat} (h : AccIsCycleOf n L)
    (hbal : Balanced n L) (hi : i < L) (hk : k ≤ L) :
    -(L : Int) < walk (acceleratedOrbit i n) L k ∧
      walk (acceleratedOrbit i n) L k < (L : Int) := by
  let f := fun j => oddCount (acceleratedOrbit j n) k
  let b := f i
  let a := oddCount n L
  have hsum : sumRange L f = k * a := CycleArcSplit.cyclic_window_sum h k
  have hhi : k * a < L * b + L := by
    have ht := sum_strict_at (f := f) (g := fun _ => b + 1) hi (fun j _ => hbal j i k hk) (by
      change b < b + 1
      omega)
    rw [hsum, sumRange_const, Nat.mul_succ] at ht
    exact ht
  have hlo : L * b < k * a + L := by
    by_cases hb : 0 < b
    · have ht := sum_strict_at (f := fun _ => b - 1) (g := f) hi (fun j _ => by
        have he := hbal i j k hk
        change b ≤ f j + 1 at he
        omega) (by change b - 1 < b; omega)
      rw [hsum, sumRange_const] at ht
      have hs : L * (b - 1) + L = L * b := by
        rw [← show L * (b - 1 + 1) = L * (b - 1) + L by rw [Nat.mul_add, Nat.mul_one],
          Nat.sub_add_cancel (Nat.succ_le_of_lt hb)]
      omega
    · have he : b = 0 := by omega
      rw [he, Nat.mul_zero]
      have := h.1
      omega
  have hhi' := Int.ofNat_lt.mpr hhi
  have hlo' := Int.ofNat_lt.mpr hlo
  simp only [Int.natCast_add, Int.natCast_mul] at hhi' hlo'
  unfold walk
  rw [RotationLaw.oddCount_rotation_invariant h i]
  change -(L : Int) < (L : Int) * (b : Int) - (a : Int) * (k : Int) ∧
    (L : Int) * (b : Int) - (a : Int) * (k : Int) < (L : Int)
  rw [Int.mul_comm (a : Int) (k : Int)]
  omega

private theorem walk_pair_bound {n L i j : Nat} (h : AccIsCycleOf n L)
    (hbal : Balanced n L) (hi : i < L) (hj : j < L) : walk n L i < walk n L j + L := by
  rcases Nat.le_total j i with hji | hij
  · have hs := walk_shift h.2 j (i - j)
    rw [Nat.add_sub_of_le hji] at hs
    have hb := (walk_rotation_bounds h hbal hj (by omega : i - j ≤ L)).2
    omega
  · have hs := walk_shift h.2 i (j - i)
    rw [Nat.add_sub_of_le hij] at hs
    have hb := (walk_rotation_bounds h hbal hi (by omega : j - i ≤ L)).1
    omega

private theorem equal_walk_impossible_ordered {n L i j : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hbal : Balanced n L)
    (hij : i < j) (hj : j < L) (heq : walk n L i = walk n L j) : False := by
  let k := j - i
  let b := oddCount (acceleratedOrbit i n) k
  let a := oddCount n L
  let f := fun j => oddCount (acceleratedOrbit j n) k
  have hk : 0 < k := by dsimp [k]; omega
  have hkL : k < L := by dsimp [k]; omega
  have hz := walk_shift h.2 i k
  rw [show i + k = j by dsimp [k]; omega, ← heq] at hz
  unfold walk at hz
  rw [RotationLaw.oddCount_rotation_invariant h i] at hz
  change (L : Int) * (b : Int) - (a : Int) * (k : Int) = _ at hz
  have hmean : L * b = k * a := by
    exact Int.ofNat_inj.mp (show ((L * b : Nat) : Int) = ((k * a : Nat) : Int) from by
      rw [Int.natCast_mul, Int.natCast_mul, Int.mul_comm (k : Int) (a : Int)]
      omega)
  have hsum : sumRange L f = L * b := (CycleArcSplit.cyclic_window_sum h k).trans hmean.symm
  obtain ⟨r, hr, hne⟩ := CycleArcSplit.exists_window_count_ne_of_least_period (b := b) h hmin hk hkL
  change f r ≠ b at hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hupper (t : Nat) (_ : t < L) : f t ≤ b := by
      have hv := hbal t r k (Nat.le_of_lt hkL)
      change f t ≤ f r + 1 at hv
      omega
    have hs := sum_strict_at (f := f) (g := fun _ => b) hr hupper hlt
    rw [hsum, sumRange_const] at hs
    omega
  · have hlower (t : Nat) (_ : t < L) : b ≤ f t := by
      have hv := hbal r t k (Nat.le_of_lt hkL)
      change f r ≤ f t + 1 at hv
      omega
    have hs := sum_strict_at (f := fun _ => b) (g := f) hr hlower hgt
    rw [hsum, sumRange_const] at hs
    omega

private theorem balanced_walk_inj {n L i j : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hbal : Balanced n L)
    (hi : i < L) (hj : j < L) (heq : walk n L i = walk n L j) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | he | hji
  · exact False.elim (equal_walk_impossible_ordered h hmin hbal hij hj heq)
  · exact he
  · exact False.elim (equal_walk_impossible_ordered h hmin hbal hji hi heq.symm)

private theorem balanced_walk_extremes {n L : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hbal : Balanced n L) :
    ∃ i j, i < L ∧ j < L ∧ walk n L j = walk n L i + L - 1 ∧
      ∀ t, walk n L i ≤ walk n L t ∧ walk n L t < walk n L i + L := by
  let i := CycleLemma.argMin (walk n L) (L - 1)
  have hL := h.1
  have hi : i < L := by
    have hp := CycleLemma.argMin_le (walk n L) (L - 1)
    change i ≤ L - 1 at hp
    omega
  have hrange (t : Nat) (ht : t < L) : walk n L i ≤ walk n L t ∧ walk n L t < walk n L i + L :=
    ⟨CycleLemma.argMin_min (walk n L) (L - 1) t (by omega), walk_pair_bound h hbal ht hi⟩
  have hex : ∃ j, j < L ∧ walk n L j = walk n L i + L - 1 := by
    apply Classical.byContradiction
    intro hno
    let f := fun t => (walk n L t - walk n L i).toNat
    have hcast (t : Nat) (ht : t < L) : (f t : Int) = walk n L t - walk n L i :=
      Int.toNat_of_nonneg (by have := (hrange t ht).1; omega)
    have hcap (t : Nat) (ht : t ≤ L - 1) : f t < L - 1 := by
      have htl : t < L := by omega
      have heq := hcast t htl
      have hv := (hrange t htl).2
      have hn : walk n L t ≠ walk n L i + L - 1 := fun he => hno ⟨t, htl, he⟩
      omega
    obtain ⟨u, v, huv, hv, heq⟩ := Pigeonhole.exists_repeat (N := L - 1) hcap (Nat.le_refl _)
    have huL : u < L := by omega
    have hvL : v < L := by omega
    have hu' := hcast u huL
    have hv' := hcast v hvL
    have he : walk n L u = walk n L v := by omega
    have := balanced_walk_inj h hmin hbal huL hvL he
    omega
  obtain ⟨j, hj, he⟩ := hex
  refine ⟨i, j, hi, hj, he, fun t => ?_⟩
  rw [walk_mod hL h.2 t]
  exact hrange _ (Nat.mod_lt t hL)

/-- The discrepancy change is the parity contribution minus the mean. -/
theorem walk_step (n L i : Nat) : walk n L (i + 1) - walk n L i =
    (L : Int) * ((acceleratedOrbit i n % 2 : Nat) : Int) - (oddCount n L : Int) := by
  unfold walk
  rw [Density.oddCount_succ_last]
  simp only [Int.natCast_add]
  rw [Int.mul_add, Int.mul_add]
  omega

private theorem add_mod_period_ne {L i t : Nat} (hi : i < L) (ht : 0 < t) (htL : t < L) :
    (i + t) % L ≠ i := by
  intro he
  by_cases hsmall : i + t < L
  · rw [Nat.mod_eq_of_lt hsmall] at he
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : L ≤ i + t), Nat.mod_eq_of_lt (by omega : i + t - L < L)] at he
    omega

/-- A balanced least-period orbit contains two rotations related by one
adjacent swap across the extrema of its discrepancy walk. The arithmetic
obstruction to that swap forces the trivial cycle. -/
theorem balanced_least_cycle_trivial {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hbal : Balanced n L) :
    L = 2 ∧ (n = 1 ∨ n = 2) := by
  have hL := two_le_length_of_accCycle hn h
  obtain ⟨i, j, hi, hj, he, hb⟩ := balanced_walk_extremes h hmin hbal
  let g := fun t => walk n L (i + t) - walk n L (j + t)
  have hg0 : g 0 = 1 - (L : Int) := by dsimp [g]; omega
  have hgL : g L = 1 - (L : Int) := by
    dsimp [g]
    rw [walk_period h.2 i, walk_period h.2 j]
    omega
  have hshift (t : Nat) (ht : t ≤ L) : g t = 1 - (L : Int) ∨ g t = 1 := by
    let p := oddCount (acceleratedOrbit i n) t
    let q := oddCount (acceleratedOrbit j n) t
    have hpq : p ≤ q + 1 := hbal i j t ht
    have hqp : q ≤ p + 1 := hbal j i t ht
    have hp := walk_shift h.2 i t
    have hq := walk_shift h.2 j t
    have hd : g t = 1 - (L : Int) + (L : Int) * ((p : Int) - (q : Int)) := by
      have hsplit : g t = walk n L i - walk n L j +
          (walk (acceleratedOrbit i n) L t - walk (acceleratedOrbit j n) L t) := by
        dsimp [g]
        omega
      rw [hsplit, show walk n L i - walk n L j = 1 - (L : Int) by omega]
      have hpt : walk (acceleratedOrbit i n) L t =
          (L : Int) * (p : Int) - (oddCount n L : Int) * (t : Int) := by
        unfold walk
        rw [RotationLaw.oddCount_rotation_invariant h i]
      have hqt : walk (acceleratedOrbit j n) L t =
          (L : Int) * (q : Int) - (oddCount n L : Int) * (t : Int) := by
        unfold walk
        rw [RotationLaw.oddCount_rotation_invariant h j]
      rw [hpt, hqt, Int.mul_sub]
      omega
    rcases Nat.lt_trichotomy p q with hlt | heq | hgt
    · have hpq' : (p : Int) - (q : Int) = -1 := by omega
      rw [hpq', Int.mul_neg, Int.mul_one] at hd
      have hlo := (hb (i + t)).1
      have hhi := (hb (j + t)).2
      dsimp [g] at hd
      omega
    · left
      rw [heq, Int.sub_self, Int.mul_zero, Int.add_zero] at hd
      exact hd
    · right
      have hpq' : (p : Int) - (q : Int) = 1 := by omega
      rw [hpq', Int.mul_one] at hd
      omega
  have hflat (t : Nat) (ht : 0 < t) (htL : t < L) : g t = 1 := by
    rcases hshift t (Nat.le_of_lt htL) with hlow | hhigh
    · have hu := (hb (i + t)).1
      have hv := (hb (j + t)).2
      dsimp [g] at hlow
      have heq : walk n L (i + t) = walk n L i := by omega
      rw [walk_mod h.1 h.2 (i + t)] at heq
      exact False.elim (add_mod_period_ne hi ht htL
        (balanced_walk_inj h hmin hbal (Nat.mod_lt _ h.1) hi heq))
    · exact hhigh
  have hstep (t : Nat) : g (t + 1) - g t =
      (L : Int) * (((acceleratedOrbit (i + t) n % 2 : Nat) : Int) -
        ((acceleratedOrbit (j + t) n % 2 : Nat) : Int)) := by
    have halg (c p q a : Int) : (c * p - a) - (c * q - a) = c * (p - q) := by
      rw [Int.mul_sub]
      omega
    calc
      _ = (walk n L (i + t + 1) - walk n L (i + t)) -
          (walk n L (j + t + 1) - walk n L (j + t)) := by
        dsimp [g]
        rw [show i + (t + 1) = i + t + 1 by omega, show j + (t + 1) = j + t + 1 by omega]
        omega
      _ = _ := by rw [walk_step, walk_step]; exact halg _ _ _ _
  have hbits_start : acceleratedOrbit i n % 2 = 1 ∧ acceleratedOrbit j n % 2 = 0 := by
    have hs := hstep 0
    rw [hg0, hflat 1 (by omega) (by omega), Nat.add_zero, Nat.add_zero] at hs
    rcases mod_two_eq_zero_or_one (acceleratedOrbit i n) with hp | hp <;>
      rcases mod_two_eq_zero_or_one (acceleratedOrbit j n) with hq | hq <;>
      simp [hp, hq] at hs ⊢ <;> omega
  have hbits_end : acceleratedOrbit (i + (L - 1)) n % 2 = 0 ∧
      acceleratedOrbit (j + (L - 1)) n % 2 = 1 := by
    have hs := hstep (L - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ L), hgL, hflat (L - 1) (by omega) (by omega)] at hs
    rcases mod_two_eq_zero_or_one (acceleratedOrbit (i + (L - 1)) n) with hp | hp <;>
      rcases mod_two_eq_zero_or_one (acceleratedOrbit (j + (L - 1)) n) with hq | hq <;>
      simp [hp, hq] at hs ⊢ <;> omega
  have hbits_mid (t : Nat) (ht : 0 < t) (htL : t + 1 < L) :
      acceleratedOrbit (i + t) n % 2 = acceleratedOrbit (j + t) n % 2 := by
    have hs := hstep t
    rw [hflat t ht (by omega), hflat (t + 1) (by omega) htL] at hs
    rcases mod_two_eq_zero_or_one (acceleratedOrbit (i + t) n) with hp | hp <;>
      rcases mod_two_eq_zero_or_one (acceleratedOrbit (j + t) n) with hq | hq <;>
      simp [hp, hq] at hs ⊢ <;> omega
  let x := acceleratedOrbit (i + (L - 1)) n
  let y := acceleratedOrbit (j + (L - 1)) n
  have horb1 (r : Nat) : acceleratedOrbit 1 (acceleratedOrbit (r + (L - 1)) n) = acceleratedOrbit r n := by
    rw [acceleratedOrbit_add, show 1 + (r + (L - 1)) = r + L by omega,
      ← acceleratedOrbit_add, h.2]
  have horb2 (r t : Nat) : acceleratedOrbit t (acceleratedOrbit 2 (acceleratedOrbit (r + (L - 1)) n)) =
      acceleratedOrbit (r + (t + 1)) n := by
    rw [acceleratedOrbit_add, acceleratedOrbit_add,
      show t + 2 + (r + (L - 1)) = (r + (t + 1)) + L by omega, ← acceleratedOrbit_add, h.2]
  have hox : acceleratedOrbit 1 x % 2 = 1 := by rw [show x = _ from rfl, horb1]; exact hbits_start.1
  have hey : acceleratedOrbit 1 y % 2 = 0 := by rw [show y = _ from rfl, horb1]; exact hbits_start.2
  have hsame (t : Nat) (ht : t < L - 2) : acceleratedOrbit t (acceleratedOrbit 2 x) % 2 =
      acceleratedOrbit t (acceleratedOrbit 2 y) % 2 := by
    rw [show x = _ from rfl, show y = _ from rfl, horb2, horb2]
    exact hbits_mid (t + 1) (by omega) (by omega)
  obtain ⟨heL, _⟩ := adjacent_swap_forces_trivial
    (acceleratedOrbit_positive hn _) (acceleratedOrbit_positive hn _)
    (accIsCycleOf_orbit h _) (accIsCycleOf_orbit h _)
    hbits_end.1 hox hbits_end.2 hey hsame
  exact ⟨heL, accIsCycleOf_two_length hn (heL ▸ h)⟩

/-- Every least nontrivial positive cycle has squared height ratio at
least nine times its period coefficient. -/
theorem nontrivial_cycle_width_lower {n L m M : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hnon : 2 < n)
    (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M) :
    9 * 3 ^ oddCount n L * (m * m) ≤ 2 ^ L * (M * M) := by
  apply Nat.le_of_not_gt
  intro hwidth
  have ht := (balanced_least_cycle_trivial hn h hmin (balanced_of_narrow hn h hlo hhi hwidth)).2
  omega

end Collatz.NarrowCycle
