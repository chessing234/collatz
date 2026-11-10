import Collatz.Strategy.ExcursionSparseProduct
import Collatz.Strategy.AccumulatorArith

/-!
# Geometric occupation bounds for injective Collatz orbits

The Garcia–Tal argument separates starts with compressed images from
exceptional parity words. This dyadic version uses an integer moment and
applies the resulting occupation bound to reciprocal correction products.
-/

namespace Collatz.OrbitCapacity

open Collatz.ExcursionSparseProduct Collatz.Sum
open Collatz.ExcursionLattice (factors)

/-- The image of the first `c` dyadic periods fits below `c * 3^a`
on each parity vector with `a` odd steps. -/
theorem image_lt {k x c : Nat} (hx : x < c * 2 ^ k) :
    acceleratedOrbit k x < c * 3 ^ oddCount x k := by
  induction k generalizing x c with
  | zero => simpa [oddCount, parityVector] using hx
  | succ k ih =>
    have hsplit : k + 1 = 1 + k := by omega
    have hcount : oddCount x 1 = x % 2 := by
      rcases Arith.mod_two_eq_zero_or_one x with he | ho
      · simp [oddCount, parityVector, he]
      · simp [oddCount, parityVector, ho]
    rw [hsplit, AccumulatorArith.oddCount_add, hcount, Nat.pow_add]
    rw [Nat.add_comm 1 k, ← acceleratedOrbit_add]
    change acceleratedOrbit k (acceleratedStep x) <
      c * (3 ^ (x % 2) * 3 ^ oddCount (acceleratedStep x) k)
    rw [Nat.pow_succ 2, ← Nat.mul_assoc] at hx
    rcases Arith.mod_two_eq_zero_or_one x with he | ho
    · have hstep : acceleratedStep x < c * 2 ^ k := by simp [acceleratedStep, he]; omega
      simpa [he] using ih hstep
    · have hstep : acceleratedStep x < (c * 3) * 2 ^ k := by
        simp [acceleratedStep, ho]
        rw [Nat.mul_right_comm c 3 (2 ^ k)]
        omega
      simpa only [ho, Nat.pow_one, Nat.mul_assoc] using ih hstep

private theorem length_filter_range (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).length = countRange n p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, countRange_succ]
    cases h : p n <;> simp [h]

private def heavy (h x : Nat) : Bool := decide (3 * h < oddCount x (5 * h))

private theorem heavy_length_le (h : Nat) :
    ((List.range (2 ^ (5 * h) * 2)).filter (heavy h)).length ≤ 2 * 31 ^ h := by
  let k := 5 * h
  have hmoment : sumRange (2 ^ k * 2) (fun x => 2 ^ oddCount x k) = 2 * 3 ^ k := by
    rw [Nat.mul_comm (2 ^ k) 2, sumRange_two_mul]
    have hshift : sumRange (2 ^ k) (fun i => 2 ^ oddCount (2 ^ k + i) k) =
        Density.weightSum k :=
      sumRange_congr (fun _ hi => by rw [Density.oddCount_two_pow_add hi])
    change Density.weightSum k + _ = _
    rw [hshift, Density.weightSum_eq]
    omega
  have hcount : 2 ^ (3 * h) * countRange (2 ^ k * 2) (heavy h) ≤ 2 * 3 ^ k := by
    rw [← hmoment]
    apply mul_countRange_le
    intro x _ hx
    have hx' : 3 * h < oddCount x k := of_decide_eq_true hx
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hx')
  rw [length_filter_range]
  apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos (3 * h))
  calc
    _ ≤ 2 * 3 ^ k := hcount
    _ = 2 * 243 ^ h := by rw [show k = 5 * h from rfl, Nat.pow_mul]
    _ ≤ 2 * (8 * 31) ^ h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) h)
    _ = 2 ^ (3 * h) * (2 * 31 ^ h) := by
      rw [Nat.pow_mul 2, Nat.mul_pow]
      change 2 * (8 ^ h * 31 ^ h) = 8 ^ h * (2 * 31 ^ h)
      ac_rfl

/-- A list of distinct sources with distinct images after `5*h` steps
occupies at most `4*31^h` positions below `2^(5*h+1)`. -/
theorem occupation (h : Nat) {xs : List Nat} (hxs : xs.Nodup)
    (hsmall : ∀ x ∈ xs, x < 2 ^ (5 * h) * 2)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, acceleratedOrbit (5 * h) x = acceleratedOrbit (5 * h) y →
      x = y) : xs.length ≤ 4 * 31 ^ h := by
  let large := xs.filter (heavy h)
  let light := xs.filter (fun x => !(heavy h x))
  have hlarge : large.length ≤ 2 * 31 ^ h := by
    have hs : large ⊆ (List.range (2 ^ (5 * h) * 2)).filter (heavy h) := by
      intro x hx
      obtain ⟨hx, hh⟩ := List.mem_filter.mp hx
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (hsmall x hx), hh⟩
    have hn : large.Nodup := List.filter_sublist.nodup hxs
    exact Nat.le_trans (hn.length_le_of_subset hs) (heavy_length_le h)
  let images := light.map (acceleratedOrbit (5 * h))
  have hnd : images.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.filter_sublist.nodup hxs)
    intro x y hx hy hne heq
    exact hne (hinj x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 heq)
  have himage : images ⊆ List.range (2 * 27 ^ h) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hx, hh⟩ := List.mem_filter.mp hx
    have hodd : oddCount x (5 * h) ≤ 3 * h := by
      simpa [heavy, Nat.not_lt] using hh
    have hbound := image_lt (k := 5 * h) (c := 2)
      (by simpa only [Nat.mul_comm 2 (2 ^ (5 * h))] using hsmall x hx)
    apply List.mem_range.mpr
    refine Nat.lt_of_lt_of_le hbound (Nat.mul_le_mul_left _ ?_)
    simpa only [Nat.pow_mul] using Nat.pow_le_pow_right (by decide : 0 < 3) hodd
  have hlight : light.length ≤ 2 * 27 ^ h := by
    simpa only [images, List.length_map, List.length_range] using hnd.length_le_of_subset himage
  have hsplit : large.length + light.length = xs.length := by
    simpa only [large, light, List.length_append] using (List.filter_append_perm (heavy h) xs).length_eq
  have h27 : 2 * 27 ^ h ≤ 2 * 31 ^ h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) h)
  omega

/-- One stride works for every positive injective orbit. -/
theorem capacity {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ P, 0 < P ∧ DyadicCapacity (fun i => acceleratedOrbit i n) P := by
  obtain ⟨b, hb⟩ := ExcursionAlphabetMass.exists_weight_power (by decide : 31 < 32) 8
  have hb0 : 0 < b := by
    cases b with
    | zero => simp at hb
    | succ b => exact Nat.succ_pos b
  let P := 5 * b
  have hP : 0 < P := Nat.mul_pos (by decide) hb0
  refine ⟨P, hP, ?_⟩
  intro j xs hnd hx
  by_cases hj : j = 0
  · subst j
    have hs : xs ⊆ [1] := by
      intro x hmem
      obtain ⟨hlt, i, rfl⟩ := hx x hmem
      have hp := acceleratedOrbit_positive hn i
      simp [cutoff] at hlt
      simp
      omega
    simpa using hnd.length_le_of_subset hs
  have hsmall : ∀ x ∈ xs, x < 2 ^ (5 * (b * j)) * 2 := by
    intro x hmem
    simpa only [cutoff, P, Nat.mul_assoc] using (hx x hmem).1
  have himages (x : Nat) (hxm : x ∈ xs) (y : Nat) (hym : y ∈ xs)
      (hxy : acceleratedOrbit (5 * (b * j)) x = acceleratedOrbit (5 * (b * j)) y) :
      x = y := by
    obtain ⟨_, i, rfl⟩ := hx x hxm
    obtain ⟨_, t, rfl⟩ := hx y hym
    rw [acceleratedOrbit_add, acceleratedOrbit_add] at hxy
    have hit := Nat.add_left_cancel (hinj _ _ hxy)
    rw [hit]
  have hcnt := occupation (b * j) hnd hsmall himages
  have hpower : 8 ^ j * 31 ^ (b * j) ≤ 2 ^ (P * j) := by
    simpa only [show 32 = 2 ^ 5 by decide, P, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
      using Nat.pow_le_pow_left hb j
  have hscale : 2 ^ j * 4 ≤ 8 ^ j := by
    rw [show 4 = 2 ^ 2 by decide, ← Nat.pow_add, show 8 = 2 ^ 3 by decide, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos j)
  calc
    2 ^ j * xs.length ≤ (2 ^ j * 4) * 31 ^ (b * j) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hcnt
    _ ≤ 8 ^ j * 31 ^ (b * j) := Nat.mul_le_mul_right _ hscale
    _ ≤ 2 ^ (P * j) := hpower
    _ = 2 ^ j * 2 ^ ((P - 1) * j) := by
      rw [← Nat.pow_add, show j + (P - 1) * j = P * j from
        calc
          _ = 1 * j + (P - 1) * j := by rw [Nat.one_mul]
          _ = (1 + (P - 1)) * j := by rw [Nat.add_mul]
          _ = P * j := by rw [show 1 + (P - 1) = P by omega]]

private theorem step_bound (x : Nat) :
    2 * acceleratedStep x ≤ 3 ^ (x % 2) * (x + 1) := by
  have hb : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hb with hb | hb <;> simp [acceleratedStep, hb] <;> omega

private def orbitPrefix (n k : Nat) : List Nat :=
  (List.range k).map (fun i => acceleratedOrbit i n)

private theorem prefix_succ (n k : Nat) :
    orbitPrefix n (k + 1) = orbitPrefix n k ++ [acceleratedOrbit k n] := by
  simp [orbitPrefix, List.range_succ]

private theorem correction_bound (n k : Nat) :
    2 ^ k * acceleratedOrbit k n * (orbitPrefix n k).prod ≤
      n * 3 ^ oddCount n k * factors 1 1 (orbitPrefix n k) := by
  induction k with
  | zero => simp [orbitPrefix, factors, oddCount, parityVector]
  | succ k ih =>
    let x := acceleratedOrbit k n
    let bit := x % 2
    let xs := orbitPrefix n k
    rw [prefix_succ, acceleratedOrbit_succ_step, Density.oddCount_succ_last,
      Nat.pow_add 3, Nat.pow_succ 2 k]
    have hden : (xs ++ [x]).prod = xs.prod * x := by simp
    have hnum : factors 1 1 (xs ++ [x]) = factors 1 1 xs * (x + 1) := by
      simp [factors]
    change (2 ^ k * 2) * acceleratedStep x * (xs ++ [x]).prod ≤
      n * (3 ^ oddCount n k * 3 ^ bit) * factors 1 1 (xs ++ [x])
    rw [hden, hnum]
    calc
      _ = 2 ^ k * (xs.prod * x) * (2 * acceleratedStep x) := by ac_rfl
      _ ≤ 2 ^ k * (xs.prod * x) * (3 ^ bit * (x + 1)) := Nat.mul_le_mul_left _ (step_bound x)
      _ = (2 ^ k * x * xs.prod) * (3 ^ bit * (x + 1)) := by ac_rfl
      _ ≤ (n * 3 ^ oddCount n k * factors 1 1 xs) * (3 ^ bit * (x + 1)) :=
        Nat.mul_le_mul_right _ ih
      _ = _ := by ac_rfl

/-- With sparse dyadic occupation, an injective orbit stays below a
fixed multiple of its affine multiplier. -/
theorem orbit_envelope_of_capacity {P n : Nat} (hP : 0 < P) (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hcap : DyadicCapacity (fun i => acceleratedOrbit i n) P) :
    ∃ C, ∀ k, 2 ^ k * acceleratedOrbit k n ≤ C * n * 3 ^ oddCount n k := by
  have hp := acceleratedOrbit_positive hn
  obtain ⟨C, hC⟩ := reciprocal_product_of_capacity hP hp hcap
  refine ⟨C, ?_⟩
  intro k
  let xs := orbitPrefix n k
  have hnd : xs.Nodup := by
    apply List.pairwise_map.mpr
    have hnd : (List.range k).Nodup := List.nodup_range
    exact hnd.imp (fun hne heq => hne (hinj _ _ heq))
  have hmember : ∀ x ∈ xs, ∃ i, acceleratedOrbit i n = x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    exact ⟨i, hi⟩
  have hpos : 0 < xs.prod := by
    apply List.prod_pos_iff_forall_pos_nat.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hmember x hx
    exact hp i
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc
    2 ^ k * acceleratedOrbit k n * xs.prod ≤ n * 3 ^ oddCount n k * factors 1 1 xs :=
      correction_bound n k
    _ ≤ n * 3 ^ oddCount n k * (C * xs.prod) := Nat.mul_le_mul_left _ (hC xs hnd hmember)
    _ = (C * n * 3 ^ oddCount n k) * xs.prod := by ac_rfl

/-- For every fixed bound, the multiplier eventually exceeds that bound. -/
def MultiplierEscapes (n : Nat) : Prop :=
  ∀ R, ∃ H, ∀ k, H ≤ k → R * 2 ^ k < 3 ^ oddCount n k

theorem multiplier_escapes_of_envelope {C n : Nat}
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hC : ∀ k, 2 ^ k * acceleratedOrbit k n ≤ C * n * 3 ^ oddCount n k) :
    MultiplierEscapes n := by
  intro R
  obtain ⟨H, hH⟩ := injective_eventually_above _ hinj (C * n * R)
  refine ⟨H, ?_⟩
  intro k hk
  apply Nat.lt_of_not_ge
  intro hsmall
  have hle : 2 ^ k * acceleratedOrbit k n ≤ 2 ^ k * (C * n * R) := by
    calc
      _ ≤ C * n * 3 ^ oddCount n k := hC k
      _ ≤ C * n * (R * 2 ^ k) := Nat.mul_le_mul_left _ hsmall
      _ = _ := by ac_rfl
  exact Nat.not_le_of_gt (hH k hk) (Nat.le_of_mul_le_mul_left hle (Nat.two_pow_pos k))

/-- Every positive injective shortcut orbit has an affine envelope. -/
theorem orbit_envelope {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ C, ∀ k, 2 ^ k * acceleratedOrbit k n ≤ C * n * 3 ^ oddCount n k := by
  obtain ⟨P, hP, hcap⟩ := capacity hn hinj
  exact orbit_envelope_of_capacity hP hn hinj hcap

/-- A divergent shortcut orbit has an affine multiplier tending to infinity. -/
theorem multiplier_escapes {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    MultiplierEscapes n := by
  obtain ⟨_, hC⟩ := orbit_envelope hn hinj
  exact multiplier_escapes_of_envelope hinj hC

end Collatz.OrbitCapacity
