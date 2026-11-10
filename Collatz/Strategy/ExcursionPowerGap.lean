import Collatz.Strategy.ExcursionFloorFibres

/-!
# An integer bracket for gaps between powers of two and three

For a small positive gap, the exponent quotient must lie between
1054/665 and 4701/2966. The fractions have determinant one, so an
integer fraction strictly between them has denominator at least
3631. The comparisons use integer powers and a binomial estimate.
-/

namespace Collatz.ExcursionPowerGap

set_option exponentiation.threshold 9000

private theorem scaled_power_gap {A B : Nat} (hAB : A ≤ B) (q : Nat) :
    A * B ^ q ≤ A ^ (q + 1) + (q * (B - A)) * B ^ q := by
  let gap := B - A
  have hsum : A + gap = B := by dsimp [gap]; omega
  induction q with
  | zero => simp
  | succ q ih =>
    have hterm : A ^ (q + 1) * B = A ^ (q + 1) * A + A ^ (q + 1) * gap := by
      calc
        _ = A ^ (q + 1) * (A + gap) := by rw [hsum]
        _ = _ := Nat.mul_add ..
    have hpow : A ^ (q + 1) ≤ B ^ (q + 1) := Nat.pow_le_pow_left hAB _
    have hlast := Nat.mul_le_mul_right gap hpow
    change A * B ^ (q + 1) ≤ A ^ ((q + 1) + 1) + ((q + 1) * gap) * B ^ (q + 1)
    calc
      _ = (A * B ^ q) * B := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (A ^ (q + 1) + (q * gap) * B ^ q) * B := Nat.mul_le_mul_right B ih
      _ = A ^ ((q + 1) + 1) + A ^ (q + 1) * gap + (q * gap) * B ^ (q + 1) := by
        rw [Nat.add_mul, hterm, ← Nat.pow_succ A (q + 1), Nat.pow_succ B q, Nat.mul_assoc (q * gap)]
      _ ≤ A ^ ((q + 1) + 1) + B ^ (q + 1) * gap + (q * gap) * B ^ (q + 1) :=
        Nat.add_le_add_right (Nat.add_le_add_left hlast _) _
      _ = _ := by
        simp only [Nat.add_mul, Nat.one_mul]
        ac_rfl

private theorem powered_ratio_below {A B q K : Nat} (hA : 0 < A) (hAB : A ≤ B)
    (hsmall : (K + 1) * (q * (B - A)) < A) :
    K * B ^ q < (K + 1) * A ^ q := by
  let D := q * (B - A)
  have hD : D ≤ A := by
    have h := Nat.mul_le_mul_right D (show 1 ≤ K + 1 by omega)
    rw [Nat.one_mul] at h
    exact Nat.le_trans h (Nat.le_of_lt hsmall)
  have hmain : (A - D) * B ^ q ≤ A ^ (q + 1) := by
    have hscaled := scaled_power_gap hAB q
    have he : (A - D) * B ^ q + D * B ^ q = A * B ^ q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hD]
    change A * B ^ q ≤ A ^ (q + 1) + D * B ^ q at hscaled
    omega
  have hmargin : K * A < (K + 1) * (A - D) := by
    rw [Nat.mul_sub_left_distrib, Nat.add_mul K 1 A, Nat.one_mul]
    change (K + 1) * D < A at hsmall
    omega
  have hB : 0 < B := Nat.lt_of_lt_of_le hA hAB
  apply Nat.lt_of_mul_lt_mul_left (a := A)
  calc
    _ = (K * A) * B ^ q := by ac_rfl
    _ < ((K + 1) * (A - D)) * B ^ q :=
      Nat.mul_lt_mul_of_pos_right hmargin (Nat.pow_pos hB)
    _ = (K + 1) * ((A - D) * B ^ q) := by ac_rfl
    _ ≤ (K + 1) * A ^ (q + 1) := Nat.mul_le_mul_left _ hmain
    _ = _ := by rw [Nat.pow_succ]; ac_rfl

private theorem upper_scale_small {a : Nat} (ha : 17 ≤ a) :
    2049 * (2966 * a) < 3 ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  clear ha
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    have hpow : 3 ^ (17 + (k + 1)) = 3 ^ (17 + k) * 3 := by
      rw [← Nat.add_assoc, Nat.pow_succ]
    rw [hpow]
    omega

private theorem lower_cross_product {a b p q : Nat} (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b)
    (hbase : 2 ^ p < 3 ^ q) : p * a < b * q := by
  apply Nat.lt_of_not_ge
  intro h
  have hpower : (2 ^ b) ^ q ≤ ((2 : Nat) ^ p) ^ a := by
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) h
  have hstrict := Nat.pow_lt_pow_left hbase (Nat.ne_of_gt ha)
  have hcompare : (3 ^ a) ^ q ≤ (2 ^ b) ^ q :=
    Nat.pow_le_pow_left (Nat.le_of_lt hAB) q
  have he : ((3 : Nat) ^ q) ^ a = (3 ^ a) ^ q := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm q a]
  rw [he] at hstrict
  exact (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hstrict hcompare)) hpower

private theorem lower_bracket {a b : Nat} (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b) :
    1054 * a < b * 665 :=
  lower_cross_product ha hAB (by decide +kernel)

private theorem upper_cross_product {a b p q K : Nat} (ha : 0 < a)
    (hAB : 3 ^ a < 2 ^ b) (hbase : 3 ^ q ≤ 2 ^ p)
    (hscaled : (K + 1) * 3 ^ q ≤ K * 2 ^ p)
    (hsmall : (K + 1) * (q * (2 ^ b - 3 ^ a)) < 3 ^ a) :
    b * q < p * a := by
  have hclose : K * (2 ^ b) ^ q < (K + 1) * (3 ^ a) ^ q :=
    powered_ratio_below (Nat.pow_pos (by decide)) (Nat.le_of_lt hAB) hsmall
  apply Nat.lt_of_not_ge
  intro h
  have hpower : ((2 : Nat) ^ p) ^ a ≤ (2 ^ b) ^ q := by
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) h
  have hraised : (K + 1) * ((3 : Nat) ^ q) ^ a ≤ K * ((2 : Nat) ^ p) ^ a := by
    let X : Nat := 3 ^ q
    let Y : Nat := 2 ^ p
    change (K + 1) * X ^ a ≤ K * Y ^ a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    rw [Nat.pow_succ X k, Nat.pow_succ Y k]
    calc
      _ = ((K + 1) * X) * X ^ k := by rw [Nat.mul_comm (X ^ k) X, ← Nat.mul_assoc]
      _ ≤ (K * Y) * Y ^ k := Nat.mul_le_mul hscaled (Nat.pow_le_pow_left hbase _)
      _ = _ := by rw [Nat.mul_comm (Y ^ k) Y, ← Nat.mul_assoc]
  have he : ((3 : Nat) ^ q) ^ a = (3 ^ a) ^ q := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm q a]
  rw [he] at hraised
  exact (Nat.not_le_of_gt hclose) (Nat.le_trans hraised (Nat.mul_le_mul_left _ hpower))

private theorem upper_bracket {a b : Nat} (ha : 17 ≤ a) (hAB : 3 ^ a < 2 ^ b)
    (hgap : 2 ^ b - 3 ^ a ≤ a) : b * 2966 < 4701 * a := by
  have hsmall : 2049 * (2966 * (2 ^ b - 3 ^ a)) < 3 ^ a :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hgap)) (upper_scale_small ha)
  exact upper_cross_product (K := 2048) (by omega) hAB (by decide +kernel)
    (by decide +kernel) hsmall

private theorem three_power_add_le_four (a : Nat) : 3 ^ a + a ≤ 4 ^ a := by
  induction a with
  | zero => decide
  | succ a ih =>
    have h := Nat.mul_le_mul_right 3 ih
    rw [Nat.add_mul] at h
    have hpos : 0 < (4 : Nat) ^ a := Nat.pow_pos (by decide)
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

private def smallGapCheck : Bool :=
  (List.range 17).all fun a => (List.range 34).all fun b =>
    decide (0 < a → 3 ^ a < 2 ^ b → a < 2 * (2 ^ b - 3 ^ a))

private theorem small_gap {a b : Nat} (ha : 0 < a) (ha' : a < 17) (hAB : 3 ^ a < 2 ^ b) :
    a < 2 * (2 ^ b - 3 ^ a) := by
  by_cases hb : b < 34
  · have hcheck : smallGapCheck = true := by decide +kernel
    have h₁ := List.all_eq_true.mp hcheck a (List.mem_range.mpr ha')
    have h₂ := List.all_eq_true.mp h₁ b (List.mem_range.mpr hb)
    exact of_decide_eq_true h₂ ha hAB
  · have hpow : 4 ^ a ≤ 2 ^ b := by
      change (2 ^ 2) ^ a ≤ 2 ^ b
      rw [← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hbound := Nat.le_trans (three_power_add_le_four a) hpow
    omega

/-- Every positive one-sided gap with odd exponent below 3,631
exceeds half that exponent. The proof uses the two integer
brackets and a finite check only for exponents below 17. -/
theorem gap_gt_half_odd_exponent {a b : Nat} (ha : 0 < a) (ha' : a < 3631)
    (hAB : 3 ^ a < 2 ^ b) : a < 2 * (2 ^ b - 3 ^ a) := by
  by_cases hs : a < 17
  · exact small_gap ha hs hAB
  · apply Nat.lt_of_not_ge
    intro h
    have hlo := lower_bracket ha hAB
    have hhi := upper_bracket (by omega : 17 ≤ a) hAB (by omega)
    omega

private theorem odd_lt_two_thirds_time {a b : Nat} (hAB : 3 ^ a < 2 ^ b) :
    3 * a < 2 * b := by
  have hleft : 2 ^ (3 * a) ≤ (3 ^ a) ^ 2 := by
    calc
      _ = ((2 : Nat) ^ 3) ^ a := Nat.pow_mul ..
      _ ≤ ((3 : Nat) ^ 2) ^ a := Nat.pow_le_pow_left (by decide) _
      _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm 2 a]
  have hstrict : 2 ^ (3 * a) < 2 ^ (2 * b) := by
    calc
      _ < (2 ^ b) ^ 2 := Nat.lt_of_le_of_lt hleft (Nat.pow_lt_pow_left hAB (by decide))
      _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm b 2]
  apply Nat.lt_of_not_ge
  intro h
  exact (Nat.not_le_of_gt hstrict) (Nat.pow_le_pow_right (by decide) h)

/-- A convenient finite range expressed in the power-of-two
exponent, for comparison with an external large-exponent bound. -/
theorem gap_gt_half_odd_exponent_of_time_lt {a b : Nat} (ha : 0 < a) (hb : b < 5000)
    (hAB : 3 ^ a < 2 ^ b) : a < 2 * (2 ^ b - 3 ^ a) := by
  have hab := odd_lt_two_thirds_time hAB
  exact gap_gt_half_odd_exponent ha (by omega) hAB

/-- The precise integer conclusion needed from a large-exponent
linear-forms estimate. It remains a named hypothesis in Lean. -/
def LargeExponentGap : Prop :=
  ∀ a b : Nat, 0 < a → 5000 ≤ b → 3 ^ a < 2 ^ b → a < 2 * (2 ^ b - 3 ^ a)

theorem gap_gt_half_odd_exponent_of_tail (tail : LargeExponentGap)
    {a b : Nat} (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b) : a < 2 * (2 ^ b - 3 ^ a) := by
  by_cases hb : b < 5000
  · exact gap_gt_half_odd_exponent_of_time_lt ha hb hAB
  · exact tail a b ha (by omega) hAB

/-- A scaled one-step bound propagates linearly in the exponent. -/
theorem bernoulli_scaled {X Y K : Nat} (hXY : X ≤ Y)
    (hscale : (K + 1) * X ≤ K * Y) (a : Nat) :
    (K + a) * X ^ a ≤ K * Y ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hlin : (K + (a + 1)) * X ≤ (K + a) * Y := by
      have h := Nat.add_le_add hscale (Nat.mul_le_mul_left a hXY)
      simpa only [← Nat.add_mul, Nat.add_assoc, Nat.add_comm 1 a] using h
    calc
      _ = X ^ a * ((K + (a + 1)) * X) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ X ^ a * ((K + a) * Y) := Nat.mul_le_mul_left _ hlin
      _ = ((K + a) * X ^ a) * Y := by ac_rfl
      _ ≤ (K * Y ^ a) * Y := Nat.mul_le_mul_right Y ih
      _ = _ := by rw [Nat.pow_succ, Nat.mul_assoc]

private theorem not_between_neighbors {a b p q r s : Nat} (hdet : q * r = s * p + 1)
    (hbound : a < q + s) (hleft : p * a < b * q) : r * a ≤ b * s := by
  apply Nat.le_of_not_gt
  intro hright
  let u := b * q - p * a
  let v := r * a - b * s
  have hu : 0 < u := Nat.sub_pos_iff_lt.mpr hleft
  have hv : 0 < v := Nat.sub_pos_iff_lt.mpr hright
  have hleft' : u + p * a = b * q := Nat.sub_add_cancel (Nat.le_of_lt hleft)
  have hright' : v + b * s = r * a := Nat.sub_add_cancel (Nat.le_of_lt hright)
  have hsu : s * u + s * (p * a) = s * (b * q) := by rw [← Nat.mul_add, hleft']
  have hqv : q * v + s * (b * q) = q * (r * a) := by
    rw [show s * (b * q) = q * (b * s) by ac_rfl, ← Nat.mul_add, hright']
  have hprod : q * (r * a) = s * (p * a) + a := by
    rw [← Nat.mul_assoc, hdet, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have hmin := Nat.add_le_add (Nat.le_mul_of_pos_right s hu) (Nat.le_mul_of_pos_right q hv)
  omega

/-- Below the denominator sum, a contracting exponent ratio is
at least the upper member of a determinant-one bracket. -/
theorem exponent_cross_ge_of_bracket {a b p q r s : Nat}
    (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b) (hbound : a < q + s)
    (hdet : q * r = s * p + 1) (hleft : 2 ^ p < 3 ^ q) :
    r * a ≤ b * s :=
  not_between_neighbors hdet hbound (lower_cross_product ha hAB hleft)

/-- A determinant-one bracket gives a uniform, explicit bound on
the reciprocal relative gap multiplied by the odd exponent. -/
theorem odd_weight_le_gap_of_bracket {a b p q r s K : Nat}
    (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b) (hbound : a < q + s)
    (hdet : q * r = s * p + 1) (hleft : 2 ^ p < 3 ^ q)
    (hK : 0 < K) (hscale : (K + 1) * 3 ^ s ≤ K * 2 ^ r) :
    a * 3 ^ a ≤ (s * (K + a)) * (2 ^ b - 3 ^ a) := by
  have hupper : 3 ^ s ≤ 2 ^ r := by
    apply Nat.le_of_mul_le_mul_left _ hK
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ K)) hscale
  let A := 3 ^ a
  let B := 2 ^ b
  let D := B - A
  have hpos : 0 < A := Nat.pow_pos (by decide)
  have hright := exponent_cross_ge_of_bracket ha hAB hbound hdet hleft
  have hpow : (K + a) * A ^ s ≤ K * B ^ s := by
    calc
      _ = (K + a) * (3 ^ s) ^ a := by
        dsimp [A]
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm a s]
      _ ≤ K * (2 ^ r) ^ a := bernoulli_scaled hupper hscale a
      _ ≤ _ := Nat.mul_le_mul_left K (by
        dsimp [B]
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) hright)
  change a * A ≤ (s * (K + a)) * D
  rw [Nat.mul_right_comm s (K + a) D, Nat.mul_comm (s * D)]
  by_cases hD : s * D ≤ A
  · have hdiff : (A - s * D) * B ^ s ≤ A ^ (s + 1) := by
      have hraw := scaled_power_gap (Nat.le_of_lt hAB) s
      have hsum : (A - s * D) * B ^ s + (s * D) * B ^ s = A * B ^ s := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hD]
      change A * B ^ s ≤ A ^ (s + 1) + (s * D) * B ^ s at hraw
      omega
    have hprod : ((K + a) * (A - s * D)) * A ^ s ≤ (K * A) * A ^ s := by
      calc
        _ = (A - s * D) * ((K + a) * A ^ s) := by ac_rfl
        _ ≤ (A - s * D) * (K * B ^ s) := Nat.mul_le_mul_left _ hpow
        _ = K * ((A - s * D) * B ^ s) := by ac_rfl
        _ ≤ K * A ^ (s + 1) := Nat.mul_le_mul_left _ hdiff
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
    have hcancel := Nat.le_of_mul_le_mul_right hprod (Nat.pow_pos hpos)
    have hsum : (K + a) * (A - s * D) + (K + a) * (s * D) = K * A + a * A := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hD, Nat.add_mul]
    omega
  · exact Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_of_not_ge hD)

private def endpointGapCheck : Bool :=
  (List.range 23).all fun a => (List.range 46).all fun b =>
    decide (0 < a → 3 ^ a < 2 ^ b → 3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a))

private theorem endpoint_gap_small {a b : Nat} (ha : 0 < a) (ha' : a < 23)
    (hAB : 3 ^ a < 2 ^ b) : 3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a) := by
  by_cases hb : b < 46
  · have hcheck : endpointGapCheck = true := by decide +kernel
    have h₁ := List.all_eq_true.mp hcheck a (List.mem_range.mpr ha')
    have h₂ := List.all_eq_true.mp h₁ b (List.mem_range.mpr hb)
    exact of_decide_eq_true h₂ ha hAB
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    have hB : 4 ^ (k + 1) ≤ 2 ^ b := by
      change (2 ^ 2) ^ (k + 1) ≤ 2 ^ b
      rw [← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hA : 3 ^ (k + 1) + 3 ^ k ≤ 4 ^ (k + 1) := by
      rw [Nat.pow_succ, Nat.pow_succ]
      have hp : (3 : Nat) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by decide) k
      have h := Nat.mul_le_mul_right 4 hp
      omega
    have hgap : 3 ^ k ≤ 2 ^ b - 3 ^ (k + 1) := by omega
    have hpow : 3 ≤ 2 ^ (k + 1 + 1) := by
      exact Nat.le_trans (by decide : 3 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    calc
      _ = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm (3 ^ k) 3]
      _ ≤ _ := Nat.mul_le_mul hpow hgap

/-- This stronger gap suffices for descent at the final landing
after a full source period. -/
theorem endpoint_gap_of_odd_lt {a b : Nat} (ha : 0 < a) (ha' : a < 6291)
    (hAB : 3 ^ a < 2 ^ b) : 3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a) := by
  by_cases hs : a < 23
  · exact endpoint_gap_small ha hs hAB
  · apply Nat.le_of_not_gt
    intro hgap
    have hp : 2049 * 5626 ≤ 2 ^ (a + 1) := by
      exact Nat.le_trans (by decide : 2049 * 5626 ≤ 2 ^ 24)
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hsmall : 2049 * (5626 * (2 ^ b - 3 ^ a)) < 3 ^ a := by
      rw [← Nat.mul_assoc]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hp) hgap
    have hlo := lower_bracket ha hAB
    have hhi := upper_cross_product (K := 2048) (p := 8917) ha hAB
      (by decide +kernel) (by decide +kernel) hsmall
    omega

theorem endpoint_gap_of_time_lt {a b : Nat} (ha : 0 < a) (hb : b < 9000)
    (hAB : 3 ^ a < 2 ^ b) : 3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a) := by
  have hab := odd_lt_two_thirds_time hAB
  exact endpoint_gap_of_odd_lt ha (by omega) hAB

/-- The exact integer tail needed for a final-landing conclusion
on every noncanonical source. -/
def LargeEndpointGap : Prop :=
  ∀ a b : Nat, 0 < a → 9000 ≤ b → 3 ^ a < 2 ^ b →
    3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a)

theorem endpoint_gap_of_tail (tail : LargeEndpointGap)
    {a b : Nat} (ha : 0 < a) (hAB : 3 ^ a < 2 ^ b) :
    3 ^ a ≤ 2 ^ (a + 1) * (2 ^ b - 3 ^ a) := by
  by_cases hb : b < 9000
  · exact endpoint_gap_of_time_lt ha hb hAB
  · exact tail a b ha (by omega) hAB

end Collatz.ExcursionPowerGap

namespace Collatz.ExcursionBudget

open Collatz.ExcursionPowerGap

/-- Below the checked odd-exponent bound, every larger genuine
realization of a contracting coefficient word descends. -/
theorem Trace.larger_realization_descends_of_odd_count_lt {n m x y : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) (hnm : n < m)
    (hodd : oddCount rs < 3631) (hcross : 3 ^ oddCount rs < 2 ^ time rs) :
    ∃ k, k ≤ time rs ∧ Collatz.acceleratedOrbit k m < m := by
  have hlen : 0 < rs.length := Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero_iff.mp h))
  have hp := Nat.lt_of_lt_of_le hlen h₁.length_le_oddCount
  exact h₁.larger_realization_descends h₂ hne hnm
    (Nat.lt_of_le_of_lt h₁.length_le_oddCount (gap_gt_half_odd_exponent hp hodd hcross))

/-- The large-exponent logarithmic estimate leaves only the least
realization to check for any genuine contracting coefficient word. -/
theorem Trace.larger_realization_descends_of_large_gap (tail : LargeExponentGap)
    {n m x y : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) (hnm : n < m)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) :
    ∃ k, k ≤ time rs ∧ Collatz.acceleratedOrbit k m < m := by
  have hlen : 0 < rs.length := Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero_iff.mp h))
  have hp := Nat.lt_of_lt_of_le hlen h₁.length_le_oddCount
  exact h₁.larger_realization_descends h₂ hne hnm
    (Nat.lt_of_le_of_lt h₁.length_le_oddCount (gap_gt_half_odd_exponent_of_tail tail hp hcross))

end Collatz.ExcursionBudget
