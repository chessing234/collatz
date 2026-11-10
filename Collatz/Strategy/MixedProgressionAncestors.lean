import Collatz.Exploration.DyadicConvergentClasses
import Collatz.Strategy.SynchronousClasses

/-!
# Ancestors in mixed dyadic and ternary progressions

Any target that is a unit modulo three has arbitrarily large
ancestors in every progression of modulus a product of powers
of two and three. The same conclusion for reachability classes
follows by advancing an arbitrary positive target to a unit.
-/

namespace Collatz.MixedProgressionAncestors

open Collatz.Reach Collatz.SynchronousClasses
  Collatz.Exploration.ThreePowerUnits Collatz.Exploration.AffinePowerMatch
  Collatz.Exploration.DyadicConvergentClasses

private theorem matching_doubling (a B z H : Nat) (hB : B % 3 ≠ 0) (hz : z % 3 ≠ 0) :
    ∃ q e, H < q ∧ 3 ^ a * q + B = 2 ^ e * z := by
  obtain ⟨p, hp⟩ := power_representation a z hz
  let C := 3 ^ a * H + B
  obtain ⟨t, ht, hres⟩ := unbounded_exponents a B (p + C) hB
  let e := t - p
  have he : e + p = t := Nat.sub_add_cancel (by omega)
  have hesize : C ≤ e := by omega
  have hmod : (2 ^ e * z) % 3 ^ a = B % 3 ^ a := by
    rw [Nat.mul_mod, ← hp, ← Nat.mul_mod, ← Nat.pow_add, he, hres]
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hesize
  have hlarge : C < 2 ^ e * z :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.le_trans hpow (Nat.le_mul_of_pos_right _ (by omega)))
  obtain ⟨q, hq⟩ := translate_of_residue (by omega : B ≤ 2 ^ e * z) hmod
  exact ⟨q, e, index_large hq hlarge, hq⟩

/-- The prescribed prefix followed by one odd step realizes a unit
ternary progression. Its endpoint can be placed on any unit target's
doubling ray. -/
theorem ancestor_with_prefix (k s b r z H : Nat) (hz : z % 3 ≠ 0) :
    ∃ q e, H < q ∧
      acceleratedOrbit (k + 1) (2 ^ k * (3 ^ s * q + b) + r) = 2 ^ e * z := by
  let a := oddCount r k
  let B := 3 ^ a * b + acceleratedOrbit k r
  let A := 3 ^ (a + s)
  let ε := 1 - B % 2
  let base := A * ε + B
  have hA : A % 2 = 1 := Arith.three_pow_odd (a + s)
  have hbase : base % 2 = 1 := by
    dsimp only [base]
    rw [Nat.add_mod, Nat.mul_mod, hA, Nat.one_mul, Nat.mod_mod]
    dsimp only [ε]
    omega
  let C := acceleratedStep base
  have hC : C % 3 ≠ 0 := odd_step_unit base hbase
  obtain ⟨t, e, ht, hmatch⟩ := matching_doubling (a + s + 1) C z H hC hz
  refine ⟨2 * t + ε, e, by omega, ?_⟩
  have hmiddle : acceleratedOrbit k (2 ^ k * (3 ^ s * (2 * t + ε) + b) + r) =
      2 * (A * t) + base := by
    rw [Congruence.accOrbit_pow_two_mul_add]
    change 3 ^ a * (3 ^ s * (2 * t + ε) + b) + acceleratedOrbit k r = _
    dsimp only [base, A, B]
    rw [Nat.mul_add (3 ^ a), ← Nat.mul_assoc, ← Nat.pow_add,
      Nat.mul_add (3 ^ (a + s)), Nat.mul_left_comm (3 ^ (a + s))]
    omega
  have hodd : (2 * (A * t) + base) % 2 ≠ 0 := by omega
  have hstep : acceleratedStep (2 * (A * t) + base) = 3 ^ (a + s + 1) * t + C := by
    have hC' : C = (3 * base + 1) / 2 := by
      dsimp only [C]
      rw [acceleratedStep, if_neg (by omega)]
    rw [acceleratedStep, if_neg hodd, hC', Nat.pow_succ', Nat.mul_assoc]
    change (3 * (2 * (A * t) + base) + 1) / 2 = 3 * (A * t) + (3 * base + 1) / 2
    omega
  rw [acceleratedOrbit_succ_step, hmiddle, hstep]
  exact hmatch

/-- Every unit target has ancestors of arbitrarily large index in
each progression with a dyadic and ternary modulus. -/
theorem ancestor_in_progression {z : Nat} (hz : z % 3 ≠ 0) (k s c H : Nat) :
    ∃ q L, H < q ∧ acceleratedOrbit L ((2 ^ k * 3 ^ s) * q + c) = z := by
  let b := c / 2 ^ k
  let r := c % 2 ^ k
  obtain ⟨q, e, hq, he⟩ := ancestor_with_prefix k s b r z H hz
  have hc : 2 ^ k * b + r = c := Nat.div_add_mod _ _
  have hform : 2 ^ k * (3 ^ s * q + b) + r = (2 ^ k * 3 ^ s) * q + c := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, hc]
  rw [hform] at he
  refine ⟨q, e + (k + 1), hq, ?_⟩
  rw [← acceleratedOrbit_add e (k + 1), he, orbit_halvings]

/-- Proving convergence on any single progression of modulus
2^k 3^s is equivalent to the full Collatz conjecture. -/
theorem collatz_iff_progression (k s c H : Nat) :
    (∀ n, 0 < n → ReachesOne n) ↔
      ∀ q, H < q → ReachesOne ((2 ^ k * 3 ^ s) * q + c) := by
  have positive (q : Nat) (hq : H < q) : 0 < (2 ^ k * 3 ^ s) * q + c :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide)))
      (by omega)) (Nat.le_add_right _ _)
  constructor
  · exact fun h q hq => h _ (positive q hq)
  · intro h
    have unit_reaches (z : Nat) (hz : z % 3 ≠ 0) : ReachesOne z := by
      obtain ⟨q, L, hq, he⟩ := ancestor_in_progression hz k s c H
      have hreach := (reachesOne_accOrbit_iff (positive q hq) L).mp (h q hq)
      rwa [he] at hreach
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      apply (reachesOne_accStep_iff hn).mpr
      by_cases he : n % 2 = 0
      · rw [acceleratedStep, if_pos he]
        exact ih (n / 2) (by omega) (by omega)
      · exact unit_reaches _ (odd_step_unit n (by omega))

end Collatz.MixedProgressionAncestors
