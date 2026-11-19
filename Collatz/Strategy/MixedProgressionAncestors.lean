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

private theorem matching_doubling (j B z H : Nat) (hB : B % 3 ≠ 0) (hz : z % 3 ≠ 0) :
    ∃ q e, H < q ∧ e ≤ (3 ^ (j + 1) * H + B).log2 + 1 + 4 * 3 ^ j ∧
      3 ^ (j + 1) * q + B = 2 ^ e * z := by
  let M := 3 ^ (j + 1)
  let P := 2 * 3 ^ j
  let C := M * H + B
  let R := C.log2 + 1
  obtain ⟨p, hp, hpmod⟩ := bounded_exponent j z hz
  obtain ⟨t, ht, htmod⟩ := bounded_exponent j B hB
  change p < P at hp
  change t < P at ht
  have hP : 0 < P := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  let w := (p + R) / P + 1
  let T := t + P * w
  let e := T - p
  have hlo : p + R < P * w := by
    have h := (Nat.div_lt_iff_lt_mul hP).mp (Nat.lt_succ_self ((p + R) / P))
    simpa only [w, Nat.mul_comm P] using h
  have hhi : P * w ≤ p + R + P := by
    dsimp only [w]
    rw [Nat.mul_succ]
    exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
  have he : e + p = T := Nat.sub_add_cancel (by change p ≤ t + P * w; omega)
  have helo : R ≤ e := by change e + p = t + P * w at he; omega
  have hehi : e ≤ R + 4 * 3 ^ j := by
    change e + p = t + P * w at he
    have hP' : P + P = 4 * 3 ^ j := by dsimp [P]; omega
    omega
  have hM : 1 < M := by
    dsimp only [M]
    rw [Nat.pow_succ]
    have h := Nat.pow_pos (by decide : 0 < 3) (n := j)
    omega
  have hTmod : 2 ^ T % M = B % M := by
    rw [power_period_shift M P t w hM (Collatz.Exploration.ThreePowerLift.period_mod j)]
    exact htmod
  have hmod : (2 ^ e * z) % M = B % M := by
    change 2 ^ p % M = z % M at hpmod
    rw [Nat.mul_mod, ← hpmod, ← Nat.mul_mod, ← Nat.pow_add, he, hTmod]
  have hC : C ≠ 0 := by omega
  have hR : C < 2 ^ R := (Nat.log2_lt hC).mp (Nat.lt_succ_self _)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) helo
  have hlarge : C < 2 ^ e * z :=
    Nat.lt_of_lt_of_le hR (Nat.le_trans hpow (Nat.le_mul_of_pos_right _ (by omega)))
  obtain ⟨q, hq⟩ := translate_of_residue (by omega : B ≤ 2 ^ e * z) hmod
  exact ⟨q, e, index_large hq hlarge, hehi, hq⟩

/-- The prescribed prefix followed by one odd step realizes a unit
ternary progression. Its endpoint can be placed on any unit target's
doubling ray. -/
theorem ancestor_with_prefix_bound (k s b r H : Nat) :
    ∃ E, ∀ z, z % 3 ≠ 0 → ∃ q e, H < q ∧ e ≤ E ∧
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
  refine ⟨(3 ^ (a + s + 1) * H + C).log2 + 1 + 4 * 3 ^ (a + s), ?_⟩
  intro z hz
  obtain ⟨t, e, ht, he, hmatch⟩ := matching_doubling (a + s) C z H hC hz
  refine ⟨2 * t + ε, e, by omega, he, ?_⟩
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

theorem ancestor_with_prefix (k s b r z H : Nat) (hz : z % 3 ≠ 0) :
    ∃ q e, H < q ∧
      acceleratedOrbit (k + 1) (2 ^ k * (3 ^ s * q + b) + r) = 2 ^ e * z := by
  obtain ⟨_, h⟩ := ancestor_with_prefix_bound k s b r H
  obtain ⟨q, e, hq, _, he⟩ := h z hz
  exact ⟨q, e, hq, he⟩

/-- Every unit target has ancestors of arbitrarily large index in
each progression with a dyadic and ternary modulus. The total number
of shortcut steps is bounded independently of the unit target. -/
theorem ancestor_in_progression_bound (k s c H : Nat) :
    ∃ M, ∀ z, z % 3 ≠ 0 → ∃ q L, H < q ∧ L ≤ M ∧
      acceleratedOrbit L ((2 ^ k * 3 ^ s) * q + c) = z := by
  let b := c / 2 ^ k
  let r := c % 2 ^ k
  obtain ⟨E, hE⟩ := ancestor_with_prefix_bound k s b r H
  refine ⟨E + (k + 1), fun z hz => ?_⟩
  obtain ⟨q, e, hq, hbound, he⟩ := hE z hz
  have hc : 2 ^ k * b + r = c := Nat.div_add_mod _ _
  have hform : 2 ^ k * (3 ^ s * q + b) + r = (2 ^ k * 3 ^ s) * q + c := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, hc]
  rw [hform] at he
  refine ⟨q, e + (k + 1), hq, by omega, ?_⟩
  rw [← acceleratedOrbit_add e (k + 1), he, orbit_halvings]

theorem ancestor_in_progression {z : Nat} (hz : z % 3 ≠ 0) (k s c H : Nat) :
    ∃ q L, H < q ∧ acceleratedOrbit L ((2 ^ k * 3 ^ s) * q + c) = z := by
  obtain ⟨_, h⟩ := ancestor_in_progression_bound k s c H
  obtain ⟨q, L, hq, _, hval⟩ := h z hz
  exact ⟨q, L, hq, hval⟩

private theorem progression_positive {k s c H q : Nat} (hq : H < q) :
    0 < (2 ^ k * 3 ^ s) * q + c :=
  Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide)))
    (by omega)) (Nat.le_add_right _ _)

/-- Every progression with a mixed dyadic and ternary modulus admits
a finite verification transfer with a fixed multiplicative overhead. -/
theorem finite_verification_transfer (k s c H : Nat) :
    ∃ M, ∀ X,
      (∀ q, H < q → (2 ^ k * 3 ^ s) * q + c ≤ 2 ^ M * X →
        ReachesOne ((2 ^ k * 3 ^ s) * q + c)) →
      ∀ n, 0 < n → n ≤ X → ReachesOne n := by
  obtain ⟨B, hB⟩ := ancestor_in_progression_bound k s c H
  refine ⟨B + 1, fun X h => ?_⟩
  have unit_reaches (z : Nat) (hz : z % 3 ≠ 0) (hX : z ≤ 2 * X) : ReachesOne z := by
    obtain ⟨q, L, hq, hL, he⟩ := hB z hz
    let x := (2 ^ k * 3 ^ s) * q + c
    have hpos : 0 < x := progression_positive hq
    have hbound : x ≤ 2 ^ L * z := by
      have ha := AffineExact.affine_exact x L
      change acceleratedOrbit L x = z at he
      rw [he] at ha
      have hprod := Nat.le_mul_of_pos_left x (Nat.pow_pos (by decide : 0 < 3) (n := oddCount x L))
      omega
    have hsize : x ≤ 2 ^ (B + 1) * X := by
      calc
        _ ≤ 2 ^ L * z := hbound
        _ ≤ 2 ^ B * (2 * X) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hL) hX
        _ = _ := by rw [Nat.pow_succ, Nat.mul_assoc]
    have hreach := (reachesOne_accOrbit_iff hpos L).mp (h q hq hsize)
    rwa [he] at hreach
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn hX
    apply (reachesOne_accStep_iff hn).mpr
    by_cases he : n % 2 = 0
    · rw [acceleratedStep, if_pos he]
      exact ih (n / 2) (by omega) (by omega) (by omega)
    · have hstep : acceleratedStep n ≤ 2 * X := by
        rw [acceleratedStep, if_neg he]
        omega
      exact unit_reaches _ (odd_step_unit n (by omega)) hstep

/-- Proving convergence on any single progression of modulus
2^k 3^s is equivalent to the full Collatz conjecture. -/
theorem collatz_iff_progression (k s c H : Nat) :
    (∀ n, 0 < n → ReachesOne n) ↔
      ∀ q, H < q → ReachesOne ((2 ^ k * 3 ^ s) * q + c) := by
  constructor
  · exact fun h q hq => h _ (progression_positive hq)
  · intro h n hn
    obtain ⟨_, htransfer⟩ := finite_verification_transfer k s c H
    exact htransfer n (fun q hq _ => h q hq) n hn (Nat.le_refl _)

end Collatz.MixedProgressionAncestors
