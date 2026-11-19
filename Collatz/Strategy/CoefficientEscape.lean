import Collatz.Strategy.OrbitCorrectionBudget
import Collatz.Strategy.AlignedOrbitOrder
import Collatz.Strategy.CoefficientSuffix
import Collatz.Strategy.ProductCeiling
import Collatz.Strategy.PowerSeparation
import Collatz.Core.Minimum
import Collatz.Strategy.ThreeAdicEscape

/-! A divergent orbit has an actual suffix with strictly expanding
coefficients at every positive time. Strict coefficient stopping at large
starts suffices to rule out divergence. -/

namespace Collatz.CoefficientEscape

open Collatz.Arith Collatz.Congruence Collatz.OrbitCorrectionBudget

private theorem nonrepeating_tail {n : Nat}
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (t : Nat) :
    ∀ i j, acceleratedOrbit i (acceleratedOrbit t n) =
      acceleratedOrbit j (acceleratedOrbit t n) → i = j := by
  intro i j h
  rw [acceleratedOrbit_add, acceleratedOrbit_add] at h
  exact Nat.add_right_cancel (hnr _ _ h)

private theorem bernoulli_nat (a d q : Nat) : a ^ q * (a + q * d) ≤ a * (a + d) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep : a * (a + (q + 1) * d) ≤ (a + q * d) * (a + d) := by
      calc
        _ = a * (a + q * d) + a * d := by rw [Nat.succ_mul, ← Nat.add_assoc, Nat.mul_add]
        _ ≤ (a + q * d) * a + (a + q * d) * d := by
          rw [Nat.mul_comm a (a + q * d)]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_add_right _ _)) _
        _ = _ := by rw [Nat.mul_add]
    calc
      _ = a ^ q * (a * (a + (q + 1) * d)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ a ^ q * ((a + q * d) * (a + d)) := Nat.mul_le_mul_left _ hstep
      _ = (a ^ q * (a + q * d)) * (a + d) := by rw [Nat.mul_assoc]
      _ ≤ (a * (a + d) ^ q) * (a + d) := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [Nat.pow_succ, Nat.mul_assoc]

set_option exponentiation.threshold 512 in
private theorem power_limit_of_offset_order {n p q : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hinc : n < acceleratedOrbit p n) (hq : 0 < q)
    (hle : ∀ j, j < q → 3 ^ oddCount (acceleratedOrbit p n) (p * j) * acceleratedOrbit (p * j) n ≤
      3 ^ oddCount n (p * j) * acceleratedOrbit (p * j) (acceleratedOrbit p n)) :
    (2 ^ p) ^ q < 2 ^ 263 * (3 ^ oddCount n p) ^ q := by
  let C := 2 ^ 263
  let A := 3 ^ oddCount n p
  let B := 2 ^ p
  let X := 3 ^ oddCount n (p * q) * n
  let Y := acceleratedOrbit (p * q) n
  have hbase : B ^ q = 2 ^ (p * q) := (Nat.pow_mul ..).symm
  have hscaled := AlignedOrbitOrder.iterated_offset_order hinc hq hle
  change X < 3 ^ (oddCount n p * q) * Y at hscaled
  rw [Nat.pow_mul] at hscaled
  have hceil : B ^ q * Y ≤ C * X := by
    rw [hbase]
    exact global_coefficient_ceiling hn hnr
  have h₁ := Nat.mul_lt_mul_of_pos_left hscaled (Nat.pow_pos (n := q) (Nat.two_pow_pos p))
  have h₂ := Nat.mul_le_mul_left (A ^ q) hceil
  change B ^ q * X < B ^ q * (A ^ q * Y) at h₁
  rw [show B ^ q * (A ^ q * Y) = A ^ q * (B ^ q * Y) by ac_rfl] at h₁
  have hh := Nat.lt_of_lt_of_le h₁ h₂
  rw [show A ^ q * (C * X) = (C * A ^ q) * X by ac_rfl] at hh
  exact Nat.lt_of_mul_lt_mul_right hh

set_option exponentiation.threshold 512 in
/-- An increasing offset with a contracting power coefficient forces two
prefix counts to separate on a positive nonrepeating orbit. The separation
is either a difference of at least three or a consecutive pair of twos. -/
theorem contracting_increase_forces_count_separation {n p : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hinc : n < acceleratedOrbit p n) (hcontract : 3 ^ oddCount n p < 2 ^ p) :
    let q := 2 ^ 263 * 3 ^ oddCount n p
    let d := AlignedOrbitOrder.countDifference n (acceleratedOrbit p n)
    ∃ t, t ≤ p * q ∧
      (d t < -2 ∨ 2 < d t ∨ (t < p * q ∧ (d t = -2 ∨ d t = 2) ∧ (d (t + 1) = -2 ∨ d (t + 1) = 2))) := by
  let C := 2 ^ 263
  let A := 3 ^ oddCount n p
  let B := 2 ^ p
  let q := C * A
  let d := AlignedOrbitOrder.countDifference n (acceleratedOrbit p n)
  have hA : 0 < A := Nat.pow_pos (by decide)
  have hq : 0 < q := Nat.mul_pos (Nat.two_pow_pos _) hA
  change ∃ t, t ≤ p * q ∧
    (d t < -2 ∨ 2 < d t ∨ (t < p * q ∧ (d t = -2 ∨ d t = 2) ∧ (d (t + 1) = -2 ∨ d (t + 1) = 2)))
  apply Classical.byContradiction
  intro hno
  have hnear (t : Nat) (ht : t ≤ p * q) : -2 ≤ d t ∧ d t ≤ 2 := by
    constructor
    · exact Int.le_of_not_gt (fun h => hno ⟨t, ht, Or.inl h⟩)
    · exact Int.le_of_not_gt (fun h => hno ⟨t, ht, Or.inr (Or.inl h)⟩)
  have hsep (t : Nat) (ht : t < p * q) (he : d t = -2 ∨ d t = 2) :
      -1 ≤ d (t + 1) ∧ d (t + 1) ≤ 1 := by
    have hh := hnear (t + 1) (by omega)
    by_cases he' : d (t + 1) = -2 ∨ d (t + 1) = 2
    · exact False.elim (hno ⟨t, by omega, Or.inr (Or.inr ⟨ht, he, he'⟩)⟩)
    · omega
  have hsmall := power_limit_of_offset_order hn hnr hinc hq (fun j hj => by
    have hle := Nat.mul_le_mul_left p (Nat.le_of_lt hj)
    exact AlignedOrbitOrder.scaled_orbit_le_of_isolated_double (Nat.le_of_lt hinc)
      (fun t ht => hnear t (by omega)) (fun t ht => hsep t (by omega)))
  change B ^ q < C * A ^ q at hsmall
  have hbig : (C + 1) * A ^ q ≤ B ^ q := by
    have hBernoulli := bernoulli_nat A 1 q
    rw [Nat.mul_one] at hBernoulli
    have he : A + q = (C + 1) * A := by dsimp only [q]; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [he, ← Nat.mul_assoc, Nat.mul_comm (A ^ q), Nat.mul_comm _ A] at hBernoulli
    have hh : (C + 1) * A ^ q ≤ (A + 1) ^ q := Nat.le_of_mul_le_mul_left hBernoulli hA
    exact Nat.le_trans hh (Nat.pow_le_pow_left hcontract q)
  rw [Nat.add_mul, Nat.one_mul] at hbig
  omega

set_option exponentiation.threshold 512 in
/-- An increasing but contracting window on a nonrepeating orbit forces
a later window of the same length with at least two more odd steps. -/
theorem contracting_increase_forces_odd_count_rise {n p : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hinc : n < acceleratedOrbit p n) (hcontract : 3 ^ oddCount n p < 2 ^ p) :
    let A := 3 ^ oddCount n p
    let q := (2 ^ 263 * A) / (2 ^ p - A) + 1
    ∃ t, t ≤ p * q ∧ oddCount n p + 2 ≤ oddCount (acceleratedOrbit t n) p := by
  let C := 2 ^ 263
  let A := 3 ^ oddCount n p
  let B := 2 ^ p
  let D := B - A
  let q := (C * A) / D + 1
  have hD : 0 < D := by dsimp [D, B, A]; omega
  have hq : 0 < q := Nat.succ_pos _
  change ∃ t, t ≤ p * q ∧ oddCount n p + 2 ≤ oddCount (acceleratedOrbit t n) p
  apply Classical.byContradiction
  intro hno
  have hsmall := power_limit_of_offset_order hn hnr hinc hq (fun j hj => by
    apply AlignedOrbitOrder.scaled_orbit_le_from (s := 0) (Nat.zero_le _) (by simpa using Nat.le_of_lt hinc)
    intro t _ ht
    have hle := Nat.mul_le_mul_left p (Nat.le_of_lt hj)
    have hct := Nat.lt_of_not_ge (fun he => hno ⟨t, by omega, he⟩)
    have h₁ := AccumulatorArith.oddCount_add n p t
    have h₂ := AccumulatorArith.oddCount_add n t p
    rw [Nat.add_comm p t] at h₁
    omega)
  change B ^ q < C * A ^ q at hsmall
  have hlarge : C * A ≤ A + q * D := by
    have hh := Nat.lt_mul_div_succ (C * A) hD
    change C * A < D * q at hh
    rw [Nat.mul_comm D q] at hh
    omega
  have hBernoulli := bernoulli_nat A D q
  have hsum : A + D = B := by dsimp [D, A, B]; omega
  rw [hsum] at hBernoulli
  have hbound := Nat.le_trans (Nat.mul_le_mul_left (A ^ q) hlarge) hBernoulli
  rw [show A ^ q * (C * A) = A * (C * A ^ q) by ac_rfl] at hbound
  exact Nat.not_le_of_gt hsmall (Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos (by decide)))

set_option exponentiation.threshold 512 in
/-- Power separation bounds the first forced odd-count rise by a polynomial
in the length of the original contracting window. -/
theorem contracting_increase_forces_polynomial_count_rise (hsep : PowerSeparation) {n p : Nat}
    (hn : 0 < n) (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hinc : n < acceleratedOrbit p n) (hcontract : 3 ^ oddCount n p < 2 ^ p) :
    ∃ t, t ≤ p * (2 ^ 264 * p ^ 14 + 1) ∧ oddCount n p + 2 ≤ oddCount (acceleratedOrbit t n) p := by
  let A := 3 ^ oddCount n p
  let D := 2 ^ p - A
  obtain ⟨t, ht, hct⟩ := contracting_increase_forces_odd_count_rise hn hnr hinc hcontract
  have hD : 0 < D := Nat.sub_pos_of_lt hcontract
  have hA : A ≤ 2 * p ^ 14 * D :=
    Nat.le_trans (Nat.le_of_lt hcontract) (hsep (oddCount n p) p hcontract)
  have hbound := Nat.mul_le_mul_left (2 ^ 263) hA
  have hfactor : (2 : Nat) ^ 263 * (2 * p ^ 14 * D) = 2 ^ 264 * p ^ 14 * D := calc
    _ = (2 ^ 263 * 2) * p ^ 14 * D := by ac_rfl
    _ = _ := by rw [show (2 : Nat) ^ 263 * 2 = 2 ^ 264 from (Nat.pow_succ 2 263).symm]
  rw [hfactor] at hbound
  have hdiv := Nat.div_le_div_right (c := D) hbound
  rw [Nat.mul_div_left _ hD] at hdiv
  have ht' : t ≤ p * ((2 ^ 263 * A) / D + 1) := ht
  exact ⟨t, Nat.le_trans ht' (Nat.mul_le_mul_left p (Nat.add_le_add_right hdiv 1)), hct⟩

/-- At the first two-step odd-count rise, the later window grows by
more than a factor of nine over the same length. -/
theorem contracting_increase_forces_ninefold_rise {n p : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hinc : n < acceleratedOrbit p n) (hcontract : 3 ^ oddCount n p < 2 ^ p) :
    let A := 3 ^ oddCount n p
    let q := (2 ^ 263 * A) / (2 ^ p - A) + 1
    ∃ t, t ≤ p * q ∧ oddCount (acceleratedOrbit t n) p = oddCount n p + 2 ∧
      9 * acceleratedOrbit t n < acceleratedOrbit (t + p) n := by
  obtain ⟨s, hs, hsct⟩ := contracting_increase_forces_odd_count_rise hn hnr hinc hcontract
  obtain ⟨t, ht, hmin⟩ := Minimum.exists_min_lt
    (P := fun t => oddCount n p + 2 ≤ oddCount (acceleratedOrbit t n) p) ⟨s, hsct⟩
  let y := acceleratedOrbit p n
  have hcount (j : Nat) : oddCount n p + oddCount y j =
      oddCount n j + oddCount (acceleratedOrbit j n) p := by
    have h₁ := AccumulatorArith.oddCount_add n p j
    have h₂ := AccumulatorArith.oddCount_add n j p
    rw [Nat.add_comm p j] at h₁
    dsimp only [y]
    omega
  have hexact : oddCount (acceleratedOrbit t n) p = oddCount n p + 2 := by
    have ht₀ : t ≠ 0 := by intro he; rw [he, acceleratedOrbit_zero] at ht; omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht₀
    change oddCount n p + 2 ≤ oddCount (acceleratedOrbit (j + 1) n) p at ht
    change oddCount (acceleratedOrbit (j + 1) n) p = oddCount n p + 2
    have hsmall : oddCount (acceleratedOrbit j n) p < oddCount n p + 2 := by
      apply Nat.lt_of_not_ge
      intro hj
      have := hmin j hj
      omega
    have hstep := AlignedOrbitOrder.countDifference_succ n y j
    unfold AlignedOrbitOrder.countDifference at hstep
    have h₁ := hcount j
    have h₂ := hcount (j + 1)
    have hy := Nat.mod_lt (acceleratedOrbit j y) (by decide : 0 < 2)
    omega
  have hnorm : 3 ^ oddCount y t * acceleratedOrbit t n ≤ 3 ^ oddCount n t * acceleratedOrbit t y := by
    apply AlignedOrbitOrder.scaled_orbit_le_from (s := 0) (Nat.zero_le _) (by simpa using Nat.le_of_lt hinc)
    intro j _ hj
    have hc := hcount j
    by_cases hl : oddCount n p + 2 ≤ oddCount (acceleratedOrbit j n) p
    · have := hmin j hl
      omega
    · omega
  have hdiff : oddCount n t + 2 ≤ oddCount y t := by have := hcount t; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) hdiff
  have hle := Nat.le_trans (Nat.mul_le_mul_right (acceleratedOrbit t n) hpow) hnorm
  rw [Nat.pow_add, Nat.mul_assoc] at hle
  have hle' := Nat.le_of_mul_le_mul_left hle (Nat.pow_pos (by decide))
  have hne : 9 * acceleratedOrbit t n ≠ acceleratedOrbit t y := fun he =>
    AccumulatorArith.three_not_dvd_orbit_of_odd_step (by omega : 0 < oddCount y t)
      ⟨3 * acceleratedOrbit t n, he.symm.trans (Nat.mul_assoc 3 3 _)⟩
  refine ⟨t, Nat.le_trans (hmin s hsct) hs, hexact, ?_⟩
  have hlt := Nat.lt_of_le_of_ne hle' hne
  unfold y at hlt
  rwa [acceleratedOrbit_add] at hlt

private theorem twice_coefficient_times_start {n k : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hfloor : ∀ i, i < k → 8192 ^ 22 ≤ acceleratedOrbit i n) :
    2 ^ k * acceleratedOrbit k n ≤ 2 * (3 ^ oddCount n k * n) := by
  let x : Rat := (2 : Rat) ^ k * (acceleratedOrbit k n : Rat)
  let y : Rat := (3 : Rat) ^ oddCount n k * (n : Rat)
  have hx : 0 ≤ x := Rat.mul_nonneg (Rat.pow_nonneg (by decide))
    (Rat.natCast_le_natCast.mpr (Nat.zero_le _))
  have hmargin : (1 / 2 : Rat) ≤ 1 - (263 / 4 : Rat) * ((6561 : Rat) / 8192) ^ 22 := by decide +kernel
  have hbound : (1 / 2 : Rat) * x ≤ y := Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_right hmargin hx) (coefficient_floor_bound hn hnr hfloor)
  have h : x ≤ 2 * y := by grind
  apply Rat.natCast_le_natCast.mp
  simpa [Rat.natCast_mul, Rat.natCast_pow, x, y] using h

set_option exponentiation.threshold 512 in
/-- The coefficient of any positive nonrepeating orbit tends to infinity.
The conclusion is expressed with a natural lower bound and no logarithms. -/
theorem eventually_coefficient_ge {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (C : Nat) :
    ∃ N, ∀ k, N ≤ k → C * 2 ^ k ≤ 3 ^ oddCount n k := by
  let B := 2 ^ 263 * n
  obtain ⟨N, hN⟩ := eventually_ge_of_nonrepeating hnr (C * B)
  refine ⟨N, fun k hk => ?_⟩
  apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos (two_pow_pos 263) hn)
  calc
    (C * 2 ^ k) * B = 2 ^ k * (C * B) := by ac_rfl
    _ ≤ 2 ^ k * acceleratedOrbit k n := Nat.mul_le_mul_left _ (hN k hk)
    _ ≤ 2 ^ 263 * (3 ^ oddCount n k * n) := global_coefficient_ceiling hn hnr
    _ = 3 ^ oddCount n k * B := by dsimp only [B]; ac_rfl

private def inverseCoefficient (n k : Nat) : Rat := (2 : Rat) ^ k / (3 : Rat) ^ oddCount n k

private theorem inverseCoefficient_add (n j k : Nat) :
    inverseCoefficient n (j + k) =
      inverseCoefficient n j * inverseCoefficient (acceleratedOrbit j n) k := by
  have hp (q : Rat) (u v : Nat) : q ^ (u + v) = q ^ u * q ^ v := by
    induction v with
    | zero => simp [Rat.mul_one]
    | succ v ih => rw [← Nat.add_assoc, Rat.pow_succ, ih, Rat.pow_succ, Rat.mul_assoc]
  simp only [inverseCoefficient, AccumulatorArith.oddCount_add, hp, Rat.div_def, Rat.inv_mul_rev]
  grind

private theorem inverseCoefficient_mul (n k : Nat) :
    inverseCoefficient n k * (3 : Rat) ^ oddCount n k = (2 : Rat) ^ k := by
  rw [inverseCoefficient, Rat.div_def, Rat.mul_assoc,
    Rat.inv_mul_cancel _ (by have := Rat.pow_pos (a := (3 : Rat)) (n := oddCount n k) (by decide); grind),
    Rat.mul_one]

private theorem inverseCoefficient_pos (n k : Nat) : 0 < inverseCoefficient n k := by
  rw [inverseCoefficient, Rat.div_def]
  exact Rat.mul_pos (Rat.pow_pos (by decide)) (Rat.inv_pos.mpr (Rat.pow_pos (by decide)))

private theorem inverseCoefficient_zero (n : Nat) : inverseCoefficient n 0 = 1 := by
  simp [inverseCoefficient, oddCount_zero, Rat.div_def]
  decide +kernel

private theorem inverseCoefficient_le_one_iff (n k : Nat) :
    inverseCoefficient n k ≤ 1 ↔ 2 ^ k ≤ 3 ^ oddCount n k := by
  have hp : 0 < (3 : Rat) ^ oddCount n k := Rat.pow_pos (by decide)
  constructor
  · intro h
    have h' := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)
    rw [inverseCoefficient_mul, Rat.one_mul] at h'
    exact Rat.natCast_le_natCast.mp (by simpa [Rat.natCast_pow] using h')
  · intro h
    apply Rat.le_of_mul_le_mul_right _ hp
    rw [inverseCoefficient_mul, Rat.one_mul]
    simpa [Rat.natCast_pow] using Rat.natCast_le_natCast.mpr h

private theorem strict_of_inverseCoefficient_le_one {n k : Nat} (hk : 0 < k)
    (h : inverseCoefficient n k ≤ 1) : 2 ^ k < 3 ^ oddCount n k := by
  apply Nat.lt_of_le_of_ne ((inverseCoefficient_le_one_iff n k).mp h)
  intro he
  have h0 := two_pow_even hk
  rw [he, three_pow_odd] at h0
  omega

/-- Every nonrepeating orbit has a suffix beyond any prescribed time and
height whose every positive-length prefix has coefficient strictly above one. -/
theorem arbitrarily_late_strict_suffix {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (time height : Nat) : ∃ j, time ≤ j ∧ height ≤ acceleratedOrbit j n ∧
      ∀ k, 0 < k → 2 ^ k < 3 ^ oddCount (acceleratedOrbit j n) k := by
  obtain ⟨t, ht⟩ := eventually_ge_of_nonrepeating hnr height
  let base := t + time
  let a := acceleratedOrbit base n
  have ha : 0 < a := acceleratedOrbit_positive hn base
  obtain ⟨N, hN⟩ := eventually_coefficient_ge ha (nonrepeating_tail hnr base) 1
  have htail : ∀ k, N ≤ k → inverseCoefficient a k ≤ inverseCoefficient a 0 := by
    intro k hk
    rw [inverseCoefficient_zero]
    exact (inverseCoefficient_le_one_iff a k).mpr (by simpa using hN k hk)
  obtain ⟨j, _, hmax⟩ := CoefficientSuffix.global_maximum_of_tail_bound
    (inverseCoefficient a) N htail
  refine ⟨j + base, by dsimp [base]; omega, ht _ (by dsimp [base]; omega), ?_⟩
  intro k hk
  have hm := hmax (j + k)
  rw [inverseCoefficient_add] at hm
  have hle : inverseCoefficient (acceleratedOrbit j a) k ≤ 1 := by
    apply Rat.le_of_mul_le_mul_left _ (inverseCoefficient_pos a j)
    rwa [Rat.mul_one]
  have hstrict := strict_of_inverseCoefficient_le_one hk hle
  dsimp [a] at hstrict
  rwa [acceleratedOrbit_add] at hstrict

/-- An expanding path into `n` contains a smaller positive start. From
that start the prefix to `n` expands at every step, and any further
window with all coefficients above one extends the property. -/
theorem smaller_start_of_expanding_ancestor {m k n : Nat} (hm : 0 < m)
    (hland : acceleratedOrbit k m = n) (hexpand : 2 ^ k < 3 ^ oddCount m k) :
    ∃ j, j < k ∧ 0 < acceleratedOrbit j m ∧ acceleratedOrbit j m < n ∧
      ∀ L, (∀ t, 0 < t → t ≤ L → 2 ^ t < 3 ^ oddCount n t) →
        ∀ t, 0 < t → t ≤ k - j + L → 2 ^ t < 3 ^ oddCount (acceleratedOrbit j m) t := by
  obtain ⟨j, hj, hmax⟩ := CoefficientSuffix.prefix_maximum (inverseCoefficient m) k
  have hlt : j < k := by
    apply Nat.lt_of_le_of_ne hj
    intro hje
    have h0 := hmax 0 (Nat.zero_le k)
    rw [inverseCoefficient_zero, hje] at h0
    have hp : 0 < (3 : Rat) ^ oddCount m k := Rat.pow_pos (by decide)
    have hc := Rat.mul_le_mul_of_nonneg_right h0 (Rat.le_of_lt hp)
    rw [Rat.one_mul, inverseCoefficient_mul] at hc
    exact Nat.not_le_of_gt hexpand (Rat.natCast_le_natCast.mp (by simpa [Rat.natCast_pow] using hc))
  have hwindow (L : Nat) (hstay : ∀ t, 0 < t → t ≤ L → 2 ^ t < 3 ^ oddCount n t)
      (t : Nat) (htL : t ≤ k + L) : inverseCoefficient m t ≤ inverseCoefficient m j := by
    by_cases ht : t ≤ k
    · exact hmax t ht
    let s := t - k
    have he : t = k + s := by dsimp [s]; omega
    have hs : 0 < s := by dsimp [s]; omega
    have hb := (inverseCoefficient_le_one_iff n s).mpr (Nat.le_of_lt (hstay s hs (by dsimp [s]; omega)))
    rw [he, inverseCoefficient_add, hland]
    have hmul := Rat.mul_le_mul_of_nonneg_left hb (Rat.le_of_lt (inverseCoefficient_pos m k))
    rw [Rat.mul_one] at hmul
    exact Rat.le_trans hmul (hmax k (Nat.le_refl k))
  let z := acceleratedOrbit j m
  have hz : 0 < z := acceleratedOrbit_positive hm j
  have hstrict (L : Nat) (hstay : ∀ t, 0 < t → t ≤ L → 2 ^ t < 3 ^ oddCount n t)
      (t : Nat) (ht : 0 < t) (htL : t ≤ k - j + L) : 2 ^ t < 3 ^ oddCount z t := by
    have hb := hwindow L hstay (j + t) (by omega)
    rw [inverseCoefficient_add] at hb
    apply strict_of_inverseCoefficient_le_one ht
    apply Rat.le_of_mul_le_mul_left _ (inverseCoefficient_pos m j)
    rwa [Rat.mul_one]
  let l := k - j
  have hlj : l + j = k := by dsimp [l]; omega
  have htail : acceleratedOrbit l z = n := by
    rw [show z = acceleratedOrbit j m from rfl, acceleratedOrbit_add, hlj, hland]
  obtain ⟨c, hc⟩ := acceleratedOrbit_affine z l
  rw [htail] at hc
  have hlast : 2 ^ l < 3 ^ oddCount z l := hstrict 0 (by intro t ht ht0; omega)
    l (by dsimp [l]; omega) (by simp [l])
  have hmul := Nat.mul_lt_mul_of_pos_right hlast hz
  have hzlt := Nat.lt_of_mul_lt_mul_left (a := 2 ^ l) (by omega : 2 ^ l * z < 2 ^ l * n)
  exact ⟨j, hlt, hz, hzlt, hstrict⟩

private theorem smaller_strict_start_of_expanding_ancestor {m k n : Nat} (hm : 0 < m)
    (hland : acceleratedOrbit k m = n) (hexpand : 2 ^ k < 3 ^ oddCount m k)
    (hstay : ∀ t, 0 < t → 2 ^ t < 3 ^ oddCount n t) :
    ∃ j, j < k ∧ 0 < acceleratedOrbit j m ∧ acceleratedOrbit j m < n ∧
      ∀ t, 0 < t → 2 ^ t < 3 ^ oddCount (acceleratedOrbit j m) t := by
  obtain ⟨j, hj, hz, hzlt, hwin⟩ := smaller_start_of_expanding_ancestor hm hland hexpand
  exact ⟨j, hj, hz, hzlt, fun t ht => hwin t (fun s hs _ => hstay s hs) t ht (by omega)⟩

/-- If any positive trajectory diverges, there is a positive start whose
forward coefficients always expand and whose every positive ancestor path
has coefficient at most one. The ancestor lengths are unrestricted. -/
theorem two_sided_witness_of_nonrepeating {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ x, 0 < x ∧ (∀ t, 0 < t → 2 ^ t < 3 ^ oddCount x t) ∧
      ∀ m k, 0 < m → acceleratedOrbit k m = x → 3 ^ oddCount m k ≤ 2 ^ k := by
  obtain ⟨j, _, hj, hstay⟩ := arbitrarily_late_strict_suffix hn hnr 0 1
  obtain ⟨x, hx, hstrict, hmin⟩ := Minimum.exists_min_pos
    (P := fun x => ∀ t, 0 < t → 2 ^ t < 3 ^ oddCount x t)
    ⟨acceleratedOrbit j n, hj, hstay⟩
  refine ⟨x, hx, hstrict, fun m k hm hland => Nat.le_of_not_gt ?_⟩
  intro he
  obtain ⟨j, _, hj, hjlt, hjstrict⟩ := smaller_strict_start_of_expanding_ancestor hm hland he hstrict
  exact hmin (acceleratedOrbit j m) hj hjlt hjstrict

/-- If every ancestor coprime to three has coefficient at most one, the
coefficient from any positive ancestor is at most `3/2`. -/
theorem ancestor_bound_of_unit_ancestor_bound {x : Nat}
    (hback : ∀ m k, 0 < m → ¬ 3 ∣ m → acceleratedOrbit k m = x → 3 ^ oddCount m k ≤ 2 ^ k)
    {m k : Nat} (hm : 0 < m) (hland : acceleratedOrbit k m = x) :
    2 * 3 ^ oddCount m k ≤ 3 * 2 ^ k := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [acceleratedOrbit_succ] at hland
    have hpos : 0 < acceleratedStep m := acceleratedOrbit_positive hm 1
    rcases mod_two_eq_zero_or_one m with h0 | h1
    · rw [oddCount_succ_of_even h0, Nat.pow_succ]
      have hb := ih hpos hland
      omega
    · have hunit : ¬ 3 ∣ acceleratedStep m := ThreeAdicEscape.odd_escape_persistent h1 0
      have hb := hback (acceleratedStep m) k hpos hunit hland
      rw [oddCount_succ_of_odd h1, Nat.pow_succ, Nat.pow_succ]
      omega

/-- The least strict start among nonmultiples of three excludes all expanding
paths from other nonmultiples, and all paths with coefficient above `3/2`. -/
theorem two_sided_unit_witness_of_nonrepeating {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ x, 0 < x ∧ ¬ 3 ∣ x ∧ (∀ t, 0 < t → 2 ^ t < 3 ^ oddCount x t) ∧
      ∀ m k, 0 < m → acceleratedOrbit k m = x →
        (¬ 3 ∣ m → 3 ^ oddCount m k ≤ 2 ^ k) ∧ 2 * 3 ^ oddCount m k ≤ 3 * 2 ^ k := by
  obtain ⟨j, hjn, hj, hstay⟩ := arbitrarily_late_strict_suffix hn hnr n 1
  have hunit : ¬ 3 ∣ acceleratedOrbit j n := by
    intro hd
    have hdiv := (ThreeAdicEscape.orbit_divisible_three_iff j n).mp hd
    have hle := Nat.le_of_dvd hn hdiv
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hjn
    have hlt := lt_two_pow_self n
    omega
  obtain ⟨x, hx, ⟨hxu, hstrict⟩, hmin⟩ := Minimum.exists_min_pos
    (P := fun x => (¬ 3 ∣ x) ∧ ∀ t, 0 < t → 2 ^ t < 3 ^ oddCount x t)
    ⟨acceleratedOrbit j n, hj, hunit, hstay⟩
  have hback (m k : Nat) (hm : 0 < m) (hmu : ¬ 3 ∣ m) (hland : acceleratedOrbit k m = x) :
      3 ^ oddCount m k ≤ 2 ^ k := by
    apply Nat.le_of_not_gt
    intro he
    obtain ⟨i, _, hi, hilt, histrict⟩ := smaller_strict_start_of_expanding_ancestor hm hland he hstrict
    exact hmin (acceleratedOrbit i m) hi hilt ⟨ThreeAdicEscape.never_enters_three hmu i, histrict⟩
  exact ⟨x, hx, hxu, hstrict, fun m k hm hland =>
    ⟨fun hmu => hback m k hm hmu hland, ancestor_bound_of_unit_ancestor_bound hback hm hland⟩⟩

private theorem nonrepeating_of_no_repeat {n : Nat}
    (hn : ¬ ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n) :
    ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j := by
  intro i j heq
  rcases Nat.lt_trichotomy i j with hlt | h | hgt
  · exact False.elim (hn ⟨i, j, hlt, heq⟩)
  · exact h
  · exact False.elim (hn ⟨j, i, hgt, heq.symm⟩)

/-- At any chosen height, universal strict coefficient stopping rules out
nonrepeating trajectories. No lower bound on the amount of contraction is needed. -/
theorem repeats_of_high_strict_crossings (height : Nat)
    (hcross : ∀ x, height ≤ x → ∃ k, 3 ^ oddCount x k < 2 ^ k) {n : Nat} (hn : 0 < n) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  apply Classical.byContradiction
  intro hno
  obtain ⟨j, _, hj, hstay⟩ := arbitrarily_late_strict_suffix hn (nonrepeating_of_no_repeat hno) 0 height
  obtain ⟨k, hk⟩ := hcross (acceleratedOrbit j n) hj
  have hkpos : 0 < k := by
    cases k with
    | zero => simp [oddCount_zero] at hk
    | succ k => exact Nat.succ_pos _
  exact Nat.not_lt_of_ge (Nat.le_of_lt (hstay k hkpos)) hk

private theorem period_odd_count {x L : Nat} (h : acceleratedOrbit L x = x) (r : Nat) :
    oddCount x (r * L) = r * oddCount x L := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul, Nat.add_comm (r * L), AccumulatorArith.oddCount_add, h, ih, Nat.succ_mul,
      Nat.add_comm]

private theorem powers_separate {A B : Nat} (hA : 0 < A) (hAB : A < B) (C : Nat) :
    ∃ r, C * A ^ r < B ^ r := by
  let r := C * A + 1
  have hbern := ProductCeiling.pow_add_one_ge r A
  have hscale : (A + 1) ^ r * A ≤ B ^ r * A :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.succ_le_of_lt hAB) _)
  refine ⟨r, Nat.lt_of_mul_lt_mul_right (a := A) ?_⟩
  calc
    (C * A ^ r) * A = A ^ r * (C * A) := by ac_rfl
    _ < A ^ r * (A + r) := Nat.mul_lt_mul_of_pos_left (by dsimp [r]; omega) (Nat.pow_pos hA)
    _ ≤ (A + 1) ^ r * A := hbern
    _ ≤ B ^ r * A := hscale

/-- A high nonrepeating orbit must attain a large coefficient within each
of the collision bounds for an initial dyadic interval. -/
theorem high_nonrepeating_coefficient_peak {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hfloor : ∀ i, 8192 ^ 22 ≤ acceleratedOrbit i n) (b : Nat) :
    ∃ k, k ≤ 4 * 3 ^ (8 * b) ∧ 2 ^ (13 * b) * 2 ^ k ≤ 2 * n * 3 ^ oddCount n k := by
  have hhit : ∃ k, k ≤ 4 * 3 ^ (8 * b) ∧ 2 ^ (13 * b) ≤ acceleratedOrbit k n := by
    apply Classical.byContradiction
    intro hno
    obtain ⟨i, j, hij, _, he⟩ := SynchronizedCollision.collision_in_aligned_blocks
      (f := fun i => acceleratedOrbit i n) (b := b) (lo := 0) (blocks := 1)
      (N := 4 * 3 ^ (8 * b)) (fun i hi => by
        simp only [Nat.zero_mul, Nat.zero_le, Nat.zero_add, Nat.one_mul, true_and]
        exact Nat.lt_of_not_ge (fun hge => hno ⟨i, hi, hge⟩)) (by simp)
    rw [acceleratedOrbit_add, acceleratedOrbit_add] at he
    have heq := hnr _ _ he
    omega
  obtain ⟨k, hk, hlarge⟩ := hhit
  refine ⟨k, hk, ?_⟩
  calc
    2 ^ (13 * b) * 2 ^ k ≤ acceleratedOrbit k n * 2 ^ k := Nat.mul_le_mul_right _ hlarge
    _ = 2 ^ k * acceleratedOrbit k n := Nat.mul_comm ..
    _ ≤ 2 * (3 ^ oddCount n k * n) :=
      twice_coefficient_times_start hn hnr (fun i _ => hfloor i)
    _ = _ := by ac_rfl

private theorem count_eq_filter_length (n : Nat) (p : Nat → Bool) :
    Sum.countRange n p = ((List.range n).filter p).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Sum.countRange_succ, List.range_succ, List.filter_append, List.length_append, ih]
    cases h : p n <;> simp [h]

private theorem count_mapped_le {R M : Nat} {f : Nat → Nat} (p : Nat → Bool)
    (hbound : ∀ i, i < R → f i < M)
    (hinj : ∀ i j, i < R → j < R → f i = f j → i = j) :
    Sum.countRange R (fun i => p (f i)) ≤ Sum.countRange M p := by
  let l := (List.range R).filter (fun i => p (f i))
  have hnd : (l.map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (List.nodup_range.filter _)
    intro i j hi hj hne he
    exact hne (hinj i j (List.mem_range.mp (List.mem_filter.mp hi).1)
      (List.mem_range.mp (List.mem_filter.mp hj).1) he)
  have hs : l.map f ⊆ (List.range M).filter p := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hmem, hpi⟩ := List.mem_filter.mp hi
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (hbound i (List.mem_range.mp hmem)), hpi⟩
  have h := hnd.length_le_of_subset hs
  rw [List.length_map] at h
  simpa only [l, count_eq_filter_length] using h

private theorem oddCount_blocks (n k R : Nat) :
    oddCount n (R * k) = Sum.sumRange R (fun i => oddCount (acceleratedOrbit (i * k) n) k) := by
  induction R with
  | zero => simp [oddCount_zero]
  | succ R ih =>
    rw [Nat.succ_mul, AccumulatorArith.oddCount_add, ih, Sum.sumRange_succ]

set_option exponentiation.threshold 2048 in
private theorem block_weight_comparison : (8 : Nat) ^ 2000 ≤ 5 ^ 1260 * 3 ^ 1940 := by
  decide +kernel

set_option exponentiation.threshold 2048 in
private theorem block_density_margin : 2 * (3 : Nat) ^ 1261 ≤ 2 ^ 2000 := by
  decide +kernel

set_option exponentiation.threshold 2048 in
private theorem block_high_count (b : Nat) :
    Sum.countRange (2 ^ (2000 * b)) (fun r => decide (1260 * b ≤ oddCount r (2000 * b))) ≤
      3 ^ (1200 * b) := by
  have hcount := Density.count_odd_at_least_weighted
    (A := 5) (B := 3) (k := 2000 * b) (c := 1260 * b) (by decide)
  change (5 ^ (1260 * b) * 3 ^ (2000 * b - 1260 * b)) * _ ≤ 8 ^ (2000 * b) at hcount
  rw [show 2000 * b - 1260 * b = 740 * b by omega] at hcount
  have h := Nat.pow_le_pow_left block_weight_comparison b
  rw [Nat.mul_pow, ← Nat.pow_mul 8 2000 b, ← Nat.pow_mul 5 1260 b, ← Nat.pow_mul 3 1940 b] at h
  have hscale : 8 ^ (2000 * b) ≤ (5 ^ (1260 * b) * 3 ^ (740 * b)) * 3 ^ (1200 * b) := by
    rw [show 1940 * b = 740 * b + 1200 * b by omega, Nat.pow_add, ← Nat.mul_assoc] at h
    exact h
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans hcount hscale)
    (Nat.mul_pos (Nat.pow_pos (by decide)) (three_pow_pos _))

set_option exponentiation.threshold 2048 in
/-- A nonrepeating orbit must cross the ceiling within the indicated number
of disjoint blocks. Its average odd count forces many blocks from the
small weighted parity tail. -/
theorem nonrepeating_ceiling_hit {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (b : Nat) :
    ∃ i, i ≤ (740 * 3 ^ (1200 * b) + 1) * (2000 * b) ∧ 2 ^ (2000 * b) ≤ acceleratedOrbit i n := by
  by_cases hb : b = 0
  · exact ⟨0, Nat.zero_le _, by simpa [hb] using Nat.succ_le_of_lt hn⟩
  let k := 2000 * b
  let R := 740 * 3 ^ (1200 * b) + 1
  let f := fun i => acceleratedOrbit (i * k) n
  let p := fun r => decide (1260 * b ≤ oddCount r k)
  let H := Sum.countRange R (fun i => p (f i))
  have hk : 0 < k := by dsimp only [k]; omega
  have hR : 0 < R := by dsimp only [R]; omega
  apply Classical.byContradiction
  intro hno
  have hbound (i : Nat) (hi : i < R) : f i < 2 ^ k := by
    have ht := Nat.mul_le_mul_right k (Nat.le_of_lt hi)
    exact Nat.lt_of_not_ge (fun he => hno ⟨i * k, ht, he⟩)
  have hinj (i j : Nat) (_ : i < R) (_ : j < R) (he : f i = f j) : i = j :=
    Nat.eq_of_mul_eq_mul_right hk (hnr _ _ he)
  have hH : H ≤ 3 ^ (1200 * b) :=
    Nat.le_trans (count_mapped_le p hbound hinj) (block_high_count b)
  have havg : (1261 * b) * R ≤ oddCount n (R * k) := by
    have hsmall : n < 2 ^ k := by simpa [f, acceleratedOrbit_zero] using hbound 0 hR
    have hfour : 4 ≤ 3 ^ (1200 * b) :=
      Nat.le_trans (by decide : 4 ≤ 3 ^ 2) (three_pow_le_three_pow (by omega))
    have hRlarge : 2263 ≤ R := by dsimp only [R]; omega
    have hreserve : 263 + k ≤ b * R := by
      have hb₁ : 1 ≤ b := Nat.pos_of_ne_zero hb
      have hmul := Nat.mul_le_mul_left b hRlarge
      have hs := Nat.mul_le_mul_left 263 hb₁
      rw [Nat.mul_one] at hs
      rw [show b * 2263 = 2000 * b + 263 * b by grind] at hmul
      dsimp only [k]
      omega
    have hs := Nat.pow_le_pow_left block_density_margin (b * R)
    rw [Nat.mul_pow, ← Nat.pow_mul 3 1261, ← Nat.pow_mul 2 2000,
      show 1261 * (b * R) = (1261 * b) * R by ac_rfl,
      show 2000 * (b * R) = R * k by dsimp only [k]; ac_rfl] at hs
    have hl : 2 ^ (263 + k) * 3 ^ ((1261 * b) * R) ≤ 2 ^ (R * k) :=
      Nat.le_trans (Nat.mul_le_mul_right _ (two_pow_le_two_pow hreserve)) hs
    have hu : 2 ^ (R * k) ≤ 2 ^ (263 + k) * 3 ^ oddCount n (R * k) := by
      calc
        _ ≤ 2 ^ (R * k) * acceleratedOrbit (R * k) n :=
          Nat.le_mul_of_pos_right _ (acceleratedOrbit_positive hn _)
        _ ≤ 2 ^ 263 * (3 ^ oddCount n (R * k) * n) := global_coefficient_ceiling hn hnr
        _ ≤ 2 ^ 263 * (3 ^ oddCount n (R * k) * 2 ^ k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_of_lt hsmall))
        _ = _ := by rw [Nat.pow_add 2 263 k]; ac_rfl
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
      (Nat.le_of_mul_le_mul_left (Nat.le_trans hl hu) (two_pow_pos _))
  have hupper : oddCount n (R * k) ≤ R * (1260 * b) + (740 * b) * H := by
    rw [oddCount_blocks]
    have hterm := Sum.sumRange_le (n := R)
      (g := fun i => 1260 * b + (740 * b) * (if p (f i) then 1 else 0)) (fun i _ => by
        change oddCount (f i) k ≤ _
        by_cases h : p (f i) = true
        · rw [if_pos h, Nat.mul_one]
          have hlen : oddCount (f i) k ≤ 2000 * b := AffineExact.oddCount_le_self (f i) k
          omega
        · rw [if_neg h, Nat.mul_zero, Nat.add_zero]
          have hl : ¬1260 * b ≤ oddCount (f i) k := by simpa only [p, decide_eq_true_eq] using h
          omega)
    rw [Sum.sumRange_add, Sum.sumRange_const, Sum.sumRange_const_mul] at hterm
    exact hterm
  have hscale := Nat.mul_le_mul_left (740 * b) hH
  have hle : b * R ≤ b * (740 * 3 ^ (1200 * b)) := by
    have he : (1261 * b) * R = R * (1260 * b) + b * R := by grind
    rw [he] at havg
    calc
      _ ≤ (740 * b) * H := Nat.le_of_add_le_add_left (Nat.le_trans havg hupper)
      _ ≤ (740 * b) * 3 ^ (1200 * b) := hscale
      _ = _ := by ac_rfl
  have hr := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hb)
  dsimp only [R] at hr
  omega

private theorem ceiling_horizon_le {i b : Nat}
    (hi : i ≤ (740 * 3 ^ (1200 * b) + 1) * (2000 * b)) :
    i + 1 ≤ 1482001 * 3 ^ (1201 * b) := by
  have hb : b ≤ 3 ^ b :=
    Nat.le_trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := b))) (two_pow_le_three_pow b)
  have hp : 1 ≤ 3 ^ (1200 * b) := one_le_three_pow _
  have hprod : (740 * 3 ^ (1200 * b) + 1) * (2000 * b) ≤ 1482000 * 3 ^ (1201 * b) := by
    calc
      _ ≤ (741 * 3 ^ (1200 * b)) * (2000 * 3 ^ b) :=
        Nat.mul_le_mul (by rw [show 741 = 740 + 1 by decide, Nat.add_mul, Nat.one_mul]; omega)
          (Nat.mul_le_mul_left _ hb)
      _ = _ := by
        rw [show 1201 * b = 1200 * b + b by omega, Nat.pow_add,
          show 1482000 = 741 * 2000 by decide]
        ac_rfl
  have hone := one_le_three_pow (1201 * b)
  omega

/-- The block visit bound excludes a polynomial upper envelope of exponent
`p/q` whenever the stated power comparison holds. -/
theorem repeats_of_power_orbit_bound {n p q : Nat} (hn : 0 < n)
    (hsep : 3 ^ (1201 * p) < 2 ^ (2000 * q)) (C : Nat)
    (hbound : ∀ i, (acceleratedOrbit i n) ^ q ≤ C * (i + 1) ^ p) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  apply Classical.byContradiction
  intro hno
  have hnr := nonrepeating_of_no_repeat hno
  obtain ⟨b, hb⟩ := powers_separate (three_pow_pos (1201 * p)) hsep (C * 1482001 ^ p)
  obtain ⟨i, hi, hhit⟩ := nonrepeating_ceiling_hit hn hnr b
  have htime := ceiling_horizon_le hi
  have hlarge : (2 ^ (2000 * q)) ^ b ≤ (C * 1482001 ^ p) * (3 ^ (1201 * p)) ^ b := by
    calc
      _ = (2 ^ (2000 * b)) ^ q := by
        rw [← Nat.pow_mul 2 (2000 * q) b, ← Nat.pow_mul 2 (2000 * b) q,
          show 2000 * q * b = 2000 * b * q by ac_rfl]
      _ ≤ (acceleratedOrbit i n) ^ q := Nat.pow_le_pow_left hhit q
      _ ≤ C * (i + 1) ^ p := hbound i
      _ ≤ C * (1482001 * 3 ^ (1201 * b)) ^ p :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htime p)
      _ = _ := by
        rw [Nat.mul_pow, ← Nat.pow_mul 3 (1201 * b) p, ← Nat.pow_mul 3 (1201 * p) b,
          show 1201 * b * p = 1201 * p * b by ac_rfl]
        ac_rfl
  exact Nat.not_lt_of_ge hlarge hb

set_option exponentiation.threshold 512 in
private theorem growth_comparison_base : (3 : Nat) ^ 227 ≤ 2 ^ 360 := by
  decide +kernel

private theorem pow_compare_from_ratio {A B m n s t : Nat} (hA : 1 < A) (hn : n ≠ 0)
    (hbase : A ^ m ≤ B ^ n) (he : s * n < m * t) : A ^ s < B ^ t := by
  apply (Nat.pow_lt_pow_iff_left hn).mp
  calc
    _ = A ^ (s * n) := (Nat.pow_mul ..).symm
    _ < A ^ (m * t) := Nat.pow_lt_pow_right hA he
    _ = (A ^ m) ^ t := Nat.pow_mul ..
    _ ≤ (B ^ n) ^ t := Nat.pow_le_pow_left hbase _
    _ = _ := by rw [← Nat.pow_mul B n, ← Nat.pow_mul B t, Nat.mul_comm n]

set_option exponentiation.threshold 50000 in
private theorem twenty_one_twenty_growth_comparison :
    (3 : Nat) ^ (1201 * 21) < 2 ^ (2000 * 20) :=
  pow_compare_from_ratio (s := 1201 * 21) (t := 2000 * 20)
    (by decide) (by decide) growth_comparison_base (by decide)

/-- Every positive orbit bounded above by a constant times
`(i+1)^(21/20)` eventually repeats. -/
theorem repeats_of_twenty_one_twenty_orbit_bound {n : Nat} (hn : 0 < n) (C : Nat)
    (hbound : ∀ i, (acceleratedOrbit i n) ^ 20 ≤ C * (i + 1) ^ 21) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n :=
  repeats_of_power_orbit_bound hn twenty_one_twenty_growth_comparison C hbound

set_option exponentiation.threshold 512 in
/-- An upper envelope with the same exponent for the homogeneous
coefficient also forces repetition. -/
theorem repeats_of_power_coefficient_bound {n p q : Nat} (hn : 0 < n)
    (hsep : 3 ^ (1201 * p) < 2 ^ (2000 * q)) (C : Nat)
    (hbound : ∀ i, (3 ^ oddCount n i) ^ q ≤ C * (i + 1) ^ p * (2 ^ i) ^ q) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  apply Classical.byContradiction
  intro hno
  have hnr := nonrepeating_of_no_repeat hno
  let B := (2 ^ 263 * n) ^ q * C
  have horbit (i : Nat) : (acceleratedOrbit i n) ^ q ≤ B * (i + 1) ^ p := by
    have hcoef : 2 ^ i * acceleratedOrbit i n ≤ (2 ^ 263 * n) * 3 ^ oddCount n i :=
      Nat.le_trans (global_coefficient_ceiling hn hnr) (Nat.le_of_eq (by ac_rfl))
    have hpower := Nat.pow_le_pow_left hcoef q
    rw [Nat.mul_pow, Nat.mul_pow] at hpower
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (2 ^ i) ^ q from Nat.pow_pos (two_pow_pos i))
    calc
      _ ≤ (2 ^ 263 * n) ^ q * (3 ^ oddCount n i) ^ q := hpower
      _ ≤ (2 ^ 263 * n) ^ q * (C * (i + 1) ^ p * (2 ^ i) ^ q) :=
        Nat.mul_le_mul_left _ (hbound i)
      _ = _ := by dsimp only [B]; ac_rfl
  exact hno (repeats_of_power_orbit_bound hn hsep B horbit)

set_option exponentiation.threshold 2048 in
private theorem linear_growth_comparison :
    (3 : Nat) ^ (1201 * 1) < 2 ^ (2000 * 1) :=
  Nat.lt_of_lt_of_le (three_pow_lt_three_pow (by decide : 1201 < 1261))
    (Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)) block_density_margin)

/-- An orbit with a homogeneous coefficient bounded by a linear function
of time must eventually repeat. -/
theorem repeats_of_linear_coefficient_bound {n : Nat} (hn : 0 < n) (C : Nat)
    (hbound : ∀ k, 3 ^ oddCount n k ≤ C * (k + 1) * 2 ^ k) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n :=
  repeats_of_power_coefficient_bound hn linear_growth_comparison C (by
    simpa only [Nat.pow_one] using hbound)

/-- The homogeneous coefficient of a nonrepeating orbit exceeds every
envelope of exponent `p/q` arbitrarily late, under the same comparison. -/
theorem power_coefficient_peaks {n p q : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hsep : 3 ^ (1201 * p) < 2 ^ (2000 * q)) (C N : Nat) :
    ∃ k, N ≤ k ∧ C * (k + 1) ^ p * (2 ^ k) ^ q < (3 ^ oddCount n k) ^ q := by
  apply Classical.byContradiction
  intro hno
  let B := C + (3 ^ N) ^ q
  have hbound (k : Nat) : (3 ^ oddCount n k) ^ q ≤ B * (k + 1) ^ p * (2 ^ k) ^ q := by
    by_cases hk : N ≤ k
    · have h : (3 ^ oddCount n k) ^ q ≤ C * (k + 1) ^ p * (2 ^ k) ^ q :=
        Nat.le_of_not_gt (fun he => hno ⟨k, hk, he⟩)
      exact Nat.le_trans h (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (Nat.le_add_right C ((3 ^ N) ^ q))))
    · have h := three_pow_le_three_pow (Nat.le_trans (AffineExact.oddCount_le_self n k) (by omega : k ≤ N))
      calc
        _ ≤ (3 ^ N) ^ q := Nat.pow_le_pow_left h q
        _ ≤ B := Nat.le_add_left ((3 ^ N) ^ q) C
        _ ≤ B * (k + 1) ^ p := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
        _ ≤ B * (k + 1) ^ p * (2 ^ k) ^ q := Nat.le_mul_of_pos_right _ (Nat.pow_pos (two_pow_pos k))
  obtain ⟨i, j, hij, he⟩ := repeats_of_power_coefficient_bound hn hsep B hbound
  exact Nat.ne_of_lt hij (hnr _ _ he)

/-- The homogeneous coefficient of a positive nonrepeating orbit beats
every linear multiple arbitrarily late. -/
theorem superlinear_coefficient_peaks {n : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (C N : Nat) : ∃ k, N ≤ k ∧ C * (k + 1) * 2 ^ k < 3 ^ oddCount n k := by
  simpa only [Nat.pow_one] using power_coefficient_peaks hn hnr linear_growth_comparison C N

/-- Once a positive orbit repeats, its coefficient eventually beats any
prescribed integer contraction factor. -/
theorem factor_crossing_of_repeat {n : Nat} (hn : 0 < n)
    (hrep : ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n) (C : Nat) :
    ∃ k, C * 3 ^ oddCount n k < 2 ^ k := by
  obtain ⟨i, j, hij, h⟩ := hrep
  let x := acceleratedOrbit i n
  let L := j - i
  have hperiod : AccCycle.AccIsCycleOf x L := by
    refine ⟨by dsimp [L]; omega, ?_⟩
    rw [show x = acceleratedOrbit i n from rfl, acceleratedOrbit_add,
      show L + i = j by dsimp [L]; omega, ← h]
  let A := (3 : Nat) ^ oddCount x L
  let B := (2 : Nat) ^ L
  have hAB : A < B := (AccCycle.accCycle_bounds (acceleratedOrbit_positive hn i) hperiod).2.2
  obtain ⟨r, hr⟩ := powers_separate (three_pow_pos (oddCount x L)) hAB (C * 3 ^ oddCount n i)
  refine ⟨i + r * L, ?_⟩
  rw [AccumulatorArith.oddCount_add, show acceleratedOrbit i n = x from rfl,
    period_odd_count hperiod.2, Nat.pow_add, Nat.pow_add,
    Nat.mul_comm r (oddCount x L), Nat.mul_comm r L, Nat.pow_mul 3, Nat.pow_mul 2]
  change C * (3 ^ oddCount n i * A ^ r) < 2 ^ i * B ^ r
  rw [← Nat.mul_assoc]
  exact Nat.lt_of_lt_of_le hr (Nat.le_mul_of_pos_left _ (two_pow_pos _))

/-- At every fixed positive height threshold, universal strict coefficient
stopping is equivalent to every positive orbit eventually repeating. -/
theorem strict_crossings_iff_repetition {height : Nat} (hh : 0 < height) :
    (∀ n, height ≤ n → ∃ k, 3 ^ oddCount n k < 2 ^ k) ↔
      ∀ n, 0 < n → ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  constructor
  · intro hc n hn
    exact repeats_of_high_strict_crossings height hc hn
  · intro hr n hn
    simpa using factor_crossing_of_repeat (Nat.lt_of_lt_of_le hh hn)
      (hr n (Nat.lt_of_lt_of_le hh hn)) 1

/-- Each nonmultiple of three either has a contracting prefix or has an
expanding ancestor that survives the restriction to nonmultiples of three.
For an unrestricted ancestor the coefficient must exceed `3/2`. -/
def UnitCoefficientCover : Prop :=
  ∀ x, 0 < x → ¬ 3 ∣ x →
    (∃ k, 3 ^ oddCount x k < 2 ^ k) ∨
      ∃ m k, 0 < m ∧ acceleratedOrbit k m = x ∧
        ((¬ 3 ∣ m) ∧ 2 ^ k < 3 ^ oddCount m k ∨ 3 * 2 ^ k < 2 * 3 ^ oddCount m k)

/-- The two-sided unit covering criterion captures exactly the divergence
part of Collatz, and permits a backward certificate in place of a forward one. -/
theorem unit_cover_iff_repetition : UnitCoefficientCover ↔
    ∀ n, 0 < n → ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  constructor
  · intro h n hn
    apply Classical.byContradiction
    intro hno
    obtain ⟨x, hx, hxu, hstay, hback⟩ :=
      two_sided_unit_witness_of_nonrepeating hn (nonrepeating_of_no_repeat hno)
    rcases h x hx hxu with ⟨k, hk⟩ | ⟨m, k, hm, hland, hstrong⟩
    · have hpos : 0 < k := by
        cases k with
        | zero => simp at hk
        | succ k => exact Nat.succ_pos _
      exact Nat.not_lt_of_ge (Nat.le_of_lt (hstay k hpos)) hk
    · rcases hstrong with ⟨hmu, he⟩ | he
      · exact Nat.not_lt_of_ge ((hback m k hm hland).1 hmu) he
      · exact Nat.not_lt_of_ge (hback m k hm hland).2 he
  · intro h x hx _
    exact Or.inl (by simpa using factor_crossing_of_repeat hx (h x hx) 1)

/-- The two-sided unit covering criterion and cycle exclusion imply the
canonical Collatz statement. -/
theorem collatz_of_unit_cover_and_cycle_exclusion (hcover : UnitCoefficientCover)
    (hcycles : ∀ x L, 0 < x → AccCycle.AccIsCycleOf x L → x ≤ 2) : CollatzConjecture := by
  apply collatz_of_high_half_crossings_and_cycle_exclusion _ hcycles
  intro x hx
  have hp : 0 < x := Nat.lt_of_lt_of_le (by decide) hx
  obtain ⟨k, hk⟩ := factor_crossing_of_repeat hp (unit_cover_iff_repetition.mp hcover x hp) 2
  exact ⟨k, Nat.le_of_lt hk⟩

/-- A polynomial upper envelope of exponent `21/20` on every positive
shortcut orbit would discharge the divergence obligation of Collatz. -/
theorem collatz_of_power_envelope_and_cycle_exclusion
    (hbound : ∀ n, 0 < n → ∃ C, ∀ i, (acceleratedOrbit i n) ^ 20 ≤ C * (i + 1) ^ 21)
    (hcycles : ∀ x L, 0 < x → AccCycle.AccIsCycleOf x L → x ≤ 2) : CollatzConjecture := by
  apply collatz_of_unit_cover_and_cycle_exclusion _ hcycles
  apply unit_cover_iff_repetition.mpr
  intro n hn
  obtain ⟨C, hC⟩ := hbound n hn
  exact repeats_of_twenty_one_twenty_orbit_bound hn C hC

/-- Strict coefficient crossings above any fixed threshold and exclusion
of nontrivial cycles suffice for the standard Collatz proposition. -/
theorem collatz_of_strict_crossings_and_cycle_exclusion (height : Nat)
    (hcross : ∀ n, height ≤ n → ∃ k, 3 ^ oddCount n k < 2 ^ k)
    (hcycles : ∀ x L, 0 < x → AccCycle.AccIsCycleOf x L → x ≤ 2) : CollatzConjecture := by
  apply collatz_of_high_half_crossings_and_cycle_exclusion _ hcycles
  intro x hx
  have hp : 0 < x := Nat.lt_of_lt_of_le (by decide) hx
  obtain ⟨k, hk⟩ := factor_crossing_of_repeat hp (repeats_of_high_strict_crossings height hcross hp) 2
  exact ⟨k, Nat.le_of_lt hk⟩

end Collatz.CoefficientEscape
