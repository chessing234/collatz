import Collatz.Strategy.SynchronousDynamics
import Collatz.Strategy.OrbitWindowBootstrap

/-!
# Growth of a divergent sequence of least class representatives

On the class permutation, an even state halves exactly, and a rising
odd state is bounded by the usual shortcut step. Descending odd steps
can be omitted from the multiplier. Sparse class minima bound the
correction of the remaining steps.
-/

namespace Collatz.SynchronousGrowth

open Collatz.SynchronousClasses Collatz.SynchronousDynamics Collatz.OrbitCapacity
open Collatz.ExcursionSparseProduct
open Collatz.ExcursionLattice (factors)

private noncomputable def riseBit (n i : Nat) : Nat :=
  if trajectory n i < trajectory n (i + 1) then 1 else 0

private noncomputable def halfBit (n i : Nat) : Nat :=
  if trajectory n i % 2 = 0 then 1 else 0

/-- The number of strictly rising steps of the class minima. -/
noncomputable def rises (n k : Nat) : Nat :=
  Sum.sumRange k (riseBit n)

/-- The number of exact halving steps of the class minima. -/
noncomputable def halvings (n k : Nat) : Nat :=
  Sum.sumRange k (halfBit n)

private theorem trajectory_step_bound {n : Nat} (hn : 0 < n) (i : Nat) :
    2 ^ (riseBit n i + halfBit n i) * trajectory n (i + 1) ≤
      3 ^ riseBit n i * (trajectory n i + 1) := by
  let x := trajectory n i
  let y := trajectory n (i + 1)
  have hpos : 0 < x := trajectory_positive hn i
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · have hx : x = 2 * (x / 2) := by omega
    have hy : y = x / 2 := trajectory_even_step hx
    have hntr : ¬x < y := by omega
    have hr : riseBit n i = 0 := if_neg hntr
    have hh : halfBit n i = 1 := if_pos he
    rw [hr, hh]
    change 2 * y ≤ 1 * (x + 1)
    omega
  · have hh : halfBit n i = 0 := if_neg (by omega : x % 2 ≠ 0)
    by_cases hr : x < y
    · have hr' : riseBit n i = 1 := if_pos hr
      rw [hr', hh]
      change 2 * y ≤ 3 * (x + 1)
      have hle : y ≤ acceleratedStep x := by
        dsimp [y, x]
        rw [trajectory_step]
        exact least_le_self _
      have hstep := shortcut_step_bound x
      rw [ho, Nat.pow_one] at hstep
      exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hstep
    · have hr' : riseBit n i = 0 := if_neg hr
      rw [hr', hh]
      simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul]
      exact Nat.le_trans (Nat.le_of_not_gt hr) (Nat.le_succ _)

private theorem least_reciprocal :
    ∃ C, ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, 0 < x ∧ least x = x) → factors 1 1 xs ≤ C * xs.prod := by
  obtain ⟨C, hC⟩ := least_count_power
  let A := C * 2 ^ 19 + 1
  let J := A.log2 + 1
  apply reciprocal_product_of_mass (P := 20) (J := J) (A := A)
    (by decide) (Nat.le_of_lt Nat.lt_log2_self) (fun _ h => h.1)
  intro j xs hnd hx
  apply count_mass_twenty
  exact hC (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) xs hnd (fun x hxmem =>
    ⟨(hx x hxmem).1, (hx x hxmem).2.2⟩)

/-- The global class count gives a uniform affine upper envelope
after omitting every descending odd step. -/
theorem trajectory_envelope :
    ∃ C, ∀ {n : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      ∀ k, 2 ^ (rises n k + halvings n k) * trajectory n k ≤
        C * (trajectory n 0 * 3 ^ rises n k) := by
  obtain ⟨C, hC⟩ := least_reciprocal
  refine ⟨C, ?_⟩
  intro n hn hinj k
  let xs := sequencePrefix (trajectory n) k
  have hnd : xs.Nodup := by
    apply List.pairwise_map.mpr
    have hi : (List.range k).Nodup := List.nodup_range
    exact hi.imp (fun hne heq => hne (trajectory_injective hinj _ _ heq))
  have hm : ∀ x ∈ xs, 0 < x ∧ least x = x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨trajectory_positive hn i, least_idempotent _⟩
  have hprod : 1 * factors 1 1 xs ≤ C * xs.prod := by
    simpa only [Nat.one_mul] using hC xs hnd hm
  have henv := sequence_scaled_envelope (values := trajectory n)
    (den := fun i => 2 ^ (rises n i + halvings n i))
    (gain := fun i => 3 ^ rises n i)
    (denStep := fun i => 2 ^ (riseBit n i + halfBit n i))
    (gainStep := fun i => 3 ^ riseBit n i)
    (trajectory_positive hn) (by rfl) (by rfl)
    (by
      intro i
      rw [← Nat.pow_add]
      simp only [rises, halvings, Sum.sumRange_succ]
      congr 1
      ac_rfl)
    (by intro i; simp only [rises, Sum.sumRange_succ, Nat.pow_add])
    (trajectory_step_bound hn) hprod
  simpa only [Nat.one_mul] using henv

/-- The reduced multiplier of a divergent class trajectory
tends to infinity. -/
theorem trajectory_multiplier_escapes {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∀ R, ∃ H, ∀ k, H ≤ k → R * 2 ^ (rises n k + halvings n k) < 3 ^ rises n k := by
  obtain ⟨C, hC⟩ := trajectory_envelope
  intro R
  obtain ⟨H, hH⟩ := injective_eventually_above _ (trajectory_injective hinj)
    (C * (trajectory n 0 * R))
  refine ⟨H, ?_⟩
  intro k hk
  apply Nat.lt_of_not_ge
  intro hsmall
  let D := 2 ^ (rises n k + halvings n k)
  have hle : D * trajectory n k ≤ D * (C * (trajectory n 0 * R)) := by
    calc
      _ ≤ C * (trajectory n 0 * 3 ^ rises n k) := hC hn hinj k
      _ ≤ C * (trajectory n 0 * (R * D)) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ hsmall)
      _ = _ := by ac_rfl
  exact Nat.not_le_of_gt (hH k hk) (Nat.le_of_mul_le_mul_left hle (Nat.two_pow_pos _))

/-- A divergent class trajectory must eventually exceed any
rising-to-halving ratio with a contracting integer power witness. -/
theorem eventual_rises_balance {n P Q : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hP : 0 < P) (hbase : 3 ^ P ≤ 2 ^ (P + Q)) :
    ∃ H, ∀ k, H ≤ k → P * halvings n k < Q * rises n k := by
  obtain ⟨H, hH⟩ := trajectory_multiplier_escapes hn hinj 1
  refine ⟨H, ?_⟩
  intro k hk
  apply Nat.lt_of_not_ge
  intro hbad
  let r := rises n k
  let w := halvings n k
  have he : (P + Q) * r ≤ (r + w) * P := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm r P, Nat.mul_comm w P]
    exact Nat.add_le_add_left hbad _
  have hpow : (3 ^ r) ^ P ≤ (2 ^ (r + w)) ^ P := by
    calc
      _ = (3 ^ P) ^ r := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm r P]
      _ ≤ (2 ^ (P + Q)) ^ r := Nat.pow_le_pow_left hbase _
      _ ≤ _ := by
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) he
  have hcontra := (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hP)).mp hpow
  exact Nat.not_le_of_gt (by simpa only [Nat.one_mul] using hH k hk) hcontra

/-- Omitting the descending odd steps preserves the occupation
bound on times when the reduced multiplier is small. -/
theorem trajectory_multiplier_occupation {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ C, ∀ R (times : List Nat), times.Nodup →
      (∀ i ∈ times, 3 ^ rises n i ≤ R * 2 ^ (rises n i + halvings n i)) →
      times.length ^ 20 ≤ C * (R + 1) ^ 19 := by
  obtain ⟨B, hB⟩ := trajectory_envelope
  obtain ⟨C, hC⟩ := least_count_power
  refine ⟨C * (B * trajectory n 0 + 1) ^ 19,
    OrbitWindowBootstrap.multiplier_occupation_of_count
      (values := trajectory n) (den := fun i => 2 ^ (rises n i + halvings n i))
      (gain := fun i => 3 ^ rises n i) (B := B) (C := C) (fun _ => Nat.two_pow_pos _)
      (trajectory_injective hinj) ?_ ?_⟩
  · intro i
    simpa only [Nat.mul_assoc] using hB hn hinj i
  · intro X hX xs hnd hx
    apply hC hX xs hnd
    intro x hxm
    obtain ⟨hlt, i, rfl⟩ := hx x hxm
    exact ⟨hlt, least_idempotent _⟩

/-- The reduced multiplier must still exceed any polynomial ceiling
of exponent below `20/19` at arbitrarily late times. -/
theorem exceeds_reduced_polynomial {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    {p q : Nat} (hrate : 19 * p < 20 * q) (D H : Nat) :
    ∃ i, H ≤ i ∧ D * (i + 1) ^ p * (2 ^ (rises n i + halvings n i)) ^ q <
      (3 ^ rises n i) ^ q := by
  obtain ⟨_, hC⟩ := trajectory_multiplier_occupation hn hinj
  exact OrbitWindowBootstrap.exceeds_polynomial_of_occupation
    (den := fun i => 2 ^ (rises n i + halvings n i))
    (gain := fun i => 3 ^ rises n i) hC hrate D H

end Collatz.SynchronousGrowth
