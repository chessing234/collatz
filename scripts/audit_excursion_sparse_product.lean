import Collatz.Strategy.ExcursionSparseProduct

open Collatz.ExcursionLattice Collatz.ExcursionSparseProduct

private def tailSample : List Nat := [33, 35, 129, 131]

private theorem tailCapacity (j : Nat) :
    (tailSample.filter (fun x => decide (x < cutoff 2 j))).length ≤ 2 ^ ((2 - 1) * j) := by
  match j with
  | 0 | 1 => decide
  | j + 2 =>
    have hf : (tailSample.filter (fun x => decide (x < cutoff 2 (j + 2)))).length ≤ 4 :=
      List.filter_sublist.length_le
    have hp : 2 ^ 2 ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    simpa using Nat.le_trans hf hp

example : factors 1 1 tailSample ≤ 2 * tailSample.prod :=
  sparse_tail_product (P := 2) (H := 3) (by decide) (by decide)
    (by simp [tailSample, cutoff]) (by simp [tailSample, cutoff]) tailCapacity

example : factors 1 1 [5, 9] ≤ 2 * ([5, 9] : List Nat).prod :=
  reciprocal_le_two (D := 16) (by decide) (fun x => 16 / x + 1) [5, 9]
    (by simp) (by decide)

#print axioms reciprocal_le_two
#print axioms sparse_tail_product
#print axioms reciprocal_product_of_capacity
#print axioms box_coefficient_envelope
#print axioms coefficient_escapes_of_box
