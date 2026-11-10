import Collatz.Strategy.ExcursionSparseProduct
import Collatz.Strategy.SieveGrowth

/-!
# Multiplier growth when a Collatz orbit omits a parity word

Excluding one parity block gives a geometric saving on disjoint windows.
The resulting capacity bounds the entire multiplicative correction product.
-/

namespace Collatz.ForbiddenParity

open Collatz.ExcursionSparseProduct

/-- The shortcut orbit never enters the residue corresponding to the
forbidden parity block. -/
def Avoids (L r n : Nat) : Prop :=
  ∀ j, acceleratedOrbit j n % 2 ^ L ≠ r

theorem Avoids.shift {L r n : Nat} (h : Avoids L r n) (j : Nat) :
    Avoids L r (acceleratedOrbit j n) := by
  intro i
  rw [acceleratedOrbit_add]
  exact h (i + j)

private def allowed (L r : Nat) : List (List Nat) :=
  ((List.range (2 ^ L)).erase r).map (fun a => parityVector a L)

private theorem allowed_length {L r : Nat} (hr : r < 2 ^ L) :
    (allowed L r).length = 2 ^ L - 1 := by
  rw [allowed, List.length_map, List.length_erase_of_mem (List.mem_range.mpr hr), List.length_range]

private theorem mem_allowed {L r n : Nat} (h : n % 2 ^ L ≠ r) :
    parityVector n L ∈ allowed L r := by
  rw [parityVector_mod_pow_two]
  exact List.mem_map_of_mem ((List.mem_erase_of_ne h).mpr
    (List.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _))))

private def words (alphabet : List (List Nat)) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap (fun a => (words alphabet k).map (a ++ ·))

private theorem words_length (alphabet : List (List Nat)) (k : Nat) :
    (words alphabet k).length = alphabet.length ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp [words, List.map_const', List.sum_replicate_nat, ih, Nat.pow_succ']

private theorem mem_words {L r n : Nat} (h : Avoids L r n) (k : Nat) :
    parityVector n (L * k) ∈ words (allowed L r) k := by
  induction k generalizing n with
  | zero => simp [words, parityVector]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (L * k), SieveGrowth.parityVector_add, words]
    have hfirst : n % 2 ^ L ≠ r := by simpa using h 0
    exact List.mem_flatMap.mpr ⟨_, mem_allowed hfirst,
      List.mem_map_of_mem (ih (h.shift L))⟩

private def extend (alphabet : List (List Nat)) (k : Nat) : List (List Nat) :=
  (words alphabet k).flatMap (fun w => [w ++ [0], w ++ [1]])

private theorem extend_length (alphabet : List (List Nat)) (k : Nat) :
    (extend alphabet k).length = 2 * alphabet.length ^ k := by
  simp [extend, List.map_const', List.sum_replicate_nat, words_length, Nat.mul_comm]

private theorem mem_extend {L r n : Nat} (h : Avoids L r n) (k : Nat) :
    parityVector n (L * k + 1) ∈ extend (allowed L r) k := by
  rw [SieveGrowth.parityVector_add]
  apply List.mem_flatMap.mpr
  refine ⟨_, mem_words h k, ?_⟩
  have hb : acceleratedOrbit (L * k) n % 2 = 0 ∨ acceleratedOrbit (L * k) n % 2 = 1 := by
    omega
  rcases hb with hb | hb <;> simp [parityVector, hb]

/-- Below the period for `L*k+1` parity bits, at most `2*(2^L-1)^k`
distinct starts can avoid the specified residue on their entire future. -/
theorem count {L r k : Nat} {xs : List Nat} (hr : r < 2 ^ L) (hnodup : xs.Nodup)
    (hx : ∀ x ∈ xs, x < 2 ^ (L * k) * 2 ∧ Avoids L r x) :
    xs.length ≤ 2 * (2 ^ L - 1) ^ k := by
  let encoded := xs.map (fun x => parityVector x (L * k + 1))
  have hb : ∀ x ∈ xs, x < 2 ^ (L * k + 1) := by
    intro x hxmem
    simpa only [Nat.pow_succ] using (hx x hxmem).1
  have hnd : encoded.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ hnodup
    intro x y hxm hym hne heq
    exact hne (parityVector_injective_mod_pow_two _ x y (hb x hxm) (hb y hym) heq)
  have hsub : encoded ⊆ extend (allowed L r) k := by
    intro p hp
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hp
    exact mem_extend (hx x hxm).2 k
  simpa only [encoded, List.length_map, extend_length, allowed_length hr]
    using hnd.length_le_of_subset hsub

/-- Positive states avoiding one parity block have geometrically sparse
dyadic counts, with a stride depending only on the block length. -/
theorem capacity {L r : Nat} {states : Nat → Nat} (hL : 0 < L)
    (hr : r < 2 ^ L) (hpos : ∀ i, 0 < states i) (havoid : ∀ i, Avoids L r (states i)) :
    ∃ P, 0 < P ∧ DyadicCapacity states P := by
  let A := 2 ^ L - 1
  have hA : A < 2 ^ L := by dsimp [A]; have := Nat.two_pow_pos L; omega
  obtain ⟨h, hh⟩ := ExcursionAlphabetMass.exists_weight_power hA 4
  have hpos' : 0 < h := by
    cases h with
    | zero => simp at hh
    | succ h => exact Nat.succ_pos h
  let P := L * h
  have hP : 0 < P := Nat.mul_pos hL hpos'
  refine ⟨P, hP, ?_⟩
  intro j xs hnodup hxs
  by_cases hj : j = 0
  · subst j
    have hsub : xs ⊆ [1] := by
      intro x hmem
      obtain ⟨hlt, i, rfl⟩ := hxs x hmem
      have hp := hpos i
      simp [cutoff] at hlt
      simp
      omega
    simpa using hnodup.length_le_of_subset hsub
  have hcnt : xs.length ≤ 2 * A ^ (h * j) :=
    count hr hnodup (fun x hmem => by
      obtain ⟨hlt, i, rfl⟩ := hxs x hmem
      exact ⟨by simpa only [cutoff, P, Nat.mul_assoc] using hlt, havoid i⟩)
  have hpow : 4 ^ j * A ^ (h * j) ≤ 2 ^ (P * j) := by
    simpa only [P, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc] using Nat.pow_le_pow_left hh j
  have ht : 2 ^ j * 2 ≤ 4 ^ j := by
    rw [← Nat.pow_succ, show 4 = 2 ^ 2 by decide, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos j)
  calc
    2 ^ j * xs.length ≤ (2 ^ j * 2) * A ^ (h * j) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hcnt
    _ ≤ 4 ^ j * A ^ (h * j) := Nat.mul_le_mul_right _ ht
    _ ≤ 2 ^ (P * j) := hpow
    _ = 2 ^ j * 2 ^ ((P - 1) * j) := by
      have he : j + (P - 1) * j = P * j := by
        calc
          _ = 1 * j + (P - 1) * j := by rw [Nat.one_mul]
          _ = (1 + (P - 1)) * j := by rw [Nat.add_mul]
          _ = P * j := by rw [show 1 + (P - 1) = P by omega]
      rw [← Nat.pow_add, he]

end Collatz.ForbiddenParity
