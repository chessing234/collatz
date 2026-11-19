import Collatz.Strategy.BoundaryWidthCycle
import Collatz.Strategy.GapPrimes

/-! A discrepancy strip one unit wider than the period has two interior
exceptions when the extreme rotations are compared. Their affine sum
leads to the polynomial `X² - X Y + Y²` modulo the full power gap. -/

namespace Collatz.OneExtraCycle

open Collatz.Arith Collatz.AccCycle Collatz.AffineExact Collatz.CyclicOrder Collatz.Sum

/-- Congruent integers have congruent powers. -/
theorem dvd_pow_sub {d x y : Int} (h : d ∣ x - y) (s : Nat) : d ∣ x ^ s - y ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Int.pow_succ, Int.pow_succ, show x ^ s * x - y ^ s * y =
      (x ^ s - y ^ s) * x + (x - y) * y ^ s by grind]
    exact Int.dvd_add (Int.dvd_trans ih (Int.dvd_mul_right _ _)) (Int.dvd_trans h (Int.dvd_mul_right _ _))

/-- A natural factor coprime to the modulus can be cancelled in integer divisibility. -/
theorem cancel_coprime_factor {d a : Nat} {x : Int} (hc : d.Coprime a)
    (h : (d : Int) ∣ (a : Int) * x) : (d : Int) ∣ x := by
  have hh := (Int.dvd_gcd_mul_iff_dvd_mul (k := (d : Int)) (n := (a : Int)) (m := x)).mpr h
  rw [Int.gcd_natCast_natCast, hc.gcd_eq_one] at hh
  simpa using hh

/-- The positive gap of the two powers is prime to two and three. -/
theorem gap_coprime_two_three {a L : Nat} (ha : 0 < a) (hL : 0 < L) (hlt : 3 ^ a < 2 ^ L) :
    (2 ^ L - 3 ^ a).Coprime 2 ∧ (2 ^ L - 3 ^ a).Coprime 3 := by
  let d := 2 ^ L - 3 ^ a
  have h2 : d % 2 = 1 := GapPrimes.gap_odd hL ha hlt
  have h3 : d % 3 = 1 ∨ d % 3 = 2 := by
    have h := GapPrimes.gap_not_three ha hlt
    omega
  constructor
  · change d.gcd 2 = 1
    rw [Nat.gcd_comm d 2, Nat.gcd_rec 2 d, h2]
    decide
  · change d.gcd 3 = 1
    rw [Nat.gcd_comm d 3, Nat.gcd_rec 3 d]
    rcases h3 with he | he <;> rw [he] <;> decide

private theorem constant_divides_from_sixth_powers {d x s : Nat} {y c : Int}
    (hcop : d.Coprime x) (h6 : (d : Int) ∣ (x : Int) ^ 6 - y ^ 6)
    (he : (d : Int) ∣ c * (x : Int) ^ s - y ^ s) : (d : Int) ∣ c ^ 6 - 1 := by
  have h₁ := dvd_pow_sub he 6
  have h₂ := dvd_pow_sub h6 s
  rw [Int.mul_pow, ← Int.pow_mul (a := (x : Int)), ← Int.pow_mul (a := y)] at h₁
  rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm 6 s] at h₂
  have h := Int.dvd_sub h₁ h₂
  rw [show (c ^ 6 * (x : Int) ^ (s * 6) - y ^ (s * 6)) -
      ((x : Int) ^ (s * 6) - y ^ (s * 6)) =
      ((x ^ (s * 6) : Nat) : Int) * (c ^ 6 - 1) by rw [Int.natCast_pow]; grind] at h
  exact cancel_coprime_factor (hcop.pow_right _) h

/-- The cyclotomic congruence and the adjacent-phase equation leave only
the common divisor of `2^6-1` and `3^6-1`, which is seven. -/
theorem gap_divides_seven_of_quadratic {L a k b : Nat} (ha : 0 < a) (hL : 0 < L)
    (hlt : 3 ^ a < 2 ^ L) (hphase : a * k + 1 = L * b)
    (hpoly : ((2 ^ L - 3 ^ a : Nat) : Int) ∣
      ((2 : Int) ^ k) ^ 2 - (2 : Int) ^ k * (3 : Int) ^ b + ((3 : Int) ^ b) ^ 2) :
    2 ^ L - 3 ^ a ∣ 7 := by
  let d := 2 ^ L - 3 ^ a
  let x := 2 ^ k
  let X : Int := x
  let Y := (3 : Int) ^ b
  let A := (3 : Int) ^ a
  let B := (2 : Int) ^ L
  have hX : X = (2 : Int) ^ k := by simp [X, x, Int.natCast_pow]
  have hd : (d : Int) = B - A := by
    dsimp [d, B, A]
    rw [Int.ofNat_sub (Nat.le_of_lt hlt), Int.natCast_pow, Int.natCast_pow]
    rfl
  have hgap : (d : Int) ∣ B - A := ⟨1, by rw [← hd, Int.mul_one]⟩
  have hquad : (d : Int) ∣ X ^ 2 - X * Y + Y ^ 2 := by rw [hX]; exact hpoly
  have hcubic : (d : Int) ∣ X ^ 3 + Y ^ 3 := by
    rw [show X ^ 3 + Y ^ 3 = (X ^ 2 - X * Y + Y ^ 2) * (X + Y) by grind]
    exact Int.dvd_trans hquad (Int.dvd_mul_right _ _)
  have h6 : (d : Int) ∣ (x : Int) ^ 6 - Y ^ 6 := by
    change (d : Int) ∣ X ^ 6 - Y ^ 6
    rw [show X ^ 6 - Y ^ 6 = (X ^ 3 + Y ^ 3) * (X ^ 3 - Y ^ 3) by grind]
    exact Int.dvd_trans hcubic (Int.dvd_mul_right _ _)
  have h₂ : (d : Int) ∣ (2 : Int) * (x : Int) ^ a - Y ^ a := by
    change (d : Int) ∣ 2 * X ^ a - Y ^ a
    have hleft : 2 * X ^ a = B ^ b := by
      rw [hX, ← Int.pow_mul, show B = (2 : Int) ^ L from rfl, ← Int.pow_mul,
        Nat.mul_comm k a, ← hphase, Int.pow_succ, Int.mul_comm]
    have hright : Y ^ a = A ^ b := by
      dsimp [Y, A]
      rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm b a]
    rw [hleft, hright]
    exact dvd_pow_sub hgap b
  have h₃ : (d : Int) ∣ (3 : Int) * (x : Int) ^ L - Y ^ L := by
    change (d : Int) ∣ 3 * X ^ L - Y ^ L
    have hleft : X ^ L = B ^ k := by
      rw [hX, ← Int.pow_mul, show B = (2 : Int) ^ L from rfl, ← Int.pow_mul, Nat.mul_comm k L]
    have hright : Y ^ L = 3 * A ^ k := by
      dsimp [Y, A]
      rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm b L, ← hphase, Int.pow_succ, Int.mul_comm]
    rw [hleft, hright, ← Int.mul_sub]
    exact Int.dvd_trans (dvd_pow_sub hgap k) (Int.dvd_mul_left _ _)
  have hcop : d.Coprime x := (gap_coprime_two_three ha hL hlt).1.pow_right k
  have h63 : (d : Int) ∣ (63 : Int) := constant_divides_from_sixth_powers hcop h6 h₂
  have h728 : (d : Int) ∣ (728 : Int) := constant_divides_from_sixth_powers hcop h6 h₃
  exact Int.dvd_gcd h63 h728

private theorem prefix_odd_le {n j L : Nat} (h : j ≤ L) : oddCount n j ≤ oddCount n L := by
  have hs := Discrepancy.oddCount_split (n := n) h
  omega

/-- Summation by parts expresses the accumulator using the full odd count
and the remaining odd counts after each step. -/
theorem affine_prefix_area (n L : Nat) : ∀ j, j ≤ L →
    2 * 3 ^ (oddCount n L - oddCount n j) * affineC j n + 2 ^ j * 3 ^ (oddCount n L - oddCount n j) =
      3 ^ oddCount n L + sumRange j (fun t => 2 ^ t * 3 ^ (oddCount n L - oddCount n (t + 1))) := by
  intro j
  induction j with
  | zero => intro _; simp [Congruence.oddCount_zero]
  | succ j ih =>
    intro hj
    let a := oddCount n L
    let u := oddCount n j
    let v := oddCount n (j + 1)
    let F := 3 ^ (a - u)
    let G := 3 ^ (a - v)
    let S := sumRange j (fun t => 2 ^ t * 3 ^ (a - oddCount n (t + 1)))
    have hprev : 2 * F * affineC j n + 2 ^ j * F = 3 ^ a + S := ih (by omega)
    have hv : v ≤ a := prefix_odd_le hj
    have hcount : v = u + acceleratedOrbit j n % 2 := Density.oddCount_succ_last n j
    rw [sumRange_succ]
    change 2 * G * affineC (j + 1) n + 2 ^ (j + 1) * G = 3 ^ a + (S + 2 ^ j * G)
    rcases mod_two_eq_zero_or_one (acceleratedOrbit j n) with h0 | h1
    · have he : G = F := by
        change 3 ^ (a - v) = 3 ^ (a - u)
        rw [show v = u by omega]
      rw [affineC_even h0, he, Nat.pow_succ]
      grind
    · have he : F = G * 3 := by
        dsimp [F, G]
        rw [← Nat.pow_succ]
        congr 1
        omega
      rw [he] at hprev
      rw [affineC_odd h1, Nat.pow_succ]
      grind

theorem affine_area (n L : Nat) : 2 * affineC L n + 2 ^ L =
    3 ^ oddCount n L + sumRange L (fun t => 2 ^ t * 3 ^ (oddCount n L - oddCount n (t + 1))) := by
  simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using affine_prefix_area n L L (Nat.le_refl _)

private theorem sum_at_index (f : Nat → Nat) {j t : Nat} (ht : t < j) :
    sumRange j (fun i => if i = t then f i else 0) = f t := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [sumRange_succ]
    by_cases he : j = t
    · rw [if_pos he, he]
      have hz : sumRange t (fun i => if i = t then f i else 0) = 0 := by
        rw [sumRange_congr (g := fun _ => 0) (fun i hi => if_neg (Nat.ne_of_lt hi)), sumRange_const, Nat.mul_zero]
      rw [hz, Nat.zero_add]
    · rw [if_neg he, Nat.add_zero]
      exact ih (by omega)

private theorem sum_after_step_at (f : Nat → Nat) {L t : Nat} (ht : 0 < t) (htL : t ≤ L) :
    sumRange L (fun i => if i + 1 = t then f i else 0) = f (t - 1) := by
  have he : ∀ i : Nat, i + 1 = t ↔ i = t - 1 := fun _ => by omega
  simp only [he]
  exact sum_at_index f (by omega)

private theorem cancel_adjacent_phase {L a k b t : Nat} (he : a * k + 1 = L * b)
    (hd : L ∣ a * t) : L ∣ t := by
  have hm : (L * b) * t = (a * t) * k + t := by
    rw [← he, Nat.add_mul, Nat.one_mul]
    ac_rfl
  have hd₁ : L ∣ (L * b) * t := ⟨b * t, by ac_rfl⟩
  have hd₂ : L ∣ (a * t) * k := Nat.dvd_trans hd (Nat.dvd_mul_right _ _)
  have hs := Nat.dvd_sub hd₁ hd₂
  rw [hm, Nat.add_sub_cancel_left] at hs
  exact hs

private theorem phase_injective_in_period {n L k b i j : Nat}
    (hphase : oddCount n L * k + 1 = L * b) (hi : i < L) (hj : j < L)
    (hd : (L : Int) ∣ walk n L i - walk n L j) : i = j := by
  rcases Nat.le_total i j with hle | hle
  · have hrev := Int.dvd_neg.mpr hd
    rw [show -(walk n L i - walk n L j) = walk n L j - walk n L i by omega] at hrev
    have hd' := cancel_adjacent_phase hphase ((BoundaryWidthCycle.phase_dvd_iff hle).mp hrev)
    by_cases he : i = j
    · exact he
    · have hbad := Nat.le_of_dvd (show 0 < j - i by omega) hd'
      omega
  · have hd' := cancel_adjacent_phase hphase ((BoundaryWidthCycle.phase_dvd_iff hle).mp hd)
    by_cases he : i = j
    · exact he
    · have hbad := Nat.le_of_dvd (show 0 < i - j by omega) hd'
      omega

private theorem extra_strip_unique_interior {u v l : Int} (hu₁ : 0 ≤ u) (hu₂ : u ≤ l + 1)
    (hv₁ : 2 ≤ v) (hv₂ : v ≤ l - 1) (hd : l ∣ u - v) : u = v := by
  rcases Int.lt_trichotomy u v with hlt | he | hgt
  · have hh := Int.dvd_neg.mpr hd
    rw [show -(u - v) = v - u by omega] at hh
    have hs := Int.le_of_dvd (show 0 < v - u by omega) hh
    omega
  · exact he
  · have hs := Int.le_of_dvd (show 0 < u - v by omega) hd
    omega

private theorem one_extra_coordinates {n L k : Nat} (h : AccIsCycleOf n L) (hL : 3 ≤ L)
    (hk : 0 < k) (hkL : k < L) (hmax : walk n L k = (L : Int) + 1)
    (hstrip : ∀ t, 0 ≤ walk n L t ∧ walk n L t ≤ (L : Int) + 1) :
    ∃ b, oddCount n L * k + 1 = L * b ∧ oddCount n k = b + 1 ∧
      oddCount n (L - k) = oddCount n L - b + 1 ∧ k ≠ L - k ∧
      ∀ t, 0 < t → t < L →
        oddCount (acceleratedOrbit k n) t + (if t = k ∨ t = L - k then 2 else 1) = oddCount n t := by
  let a := oddCount n L
  let b := oddCount n k - 1
  let r := L - k
  let W := walk n L
  have hr : 0 < r := by dsimp [r]; omega
  have hrL : r < L := by dsimp [r]; omega
  have hrsum : r + k = L := Nat.sub_add_cancel (Nat.le_of_lt hkL)
  have hmax' : (L : Int) * (oddCount n k : Int) - (a : Int) * (k : Int) = (L : Int) + 1 := hmax
  have hbpos : 0 < oddCount n k := by
    by_cases hz : oddCount n k = 0
    · have hpos := Int.mul_nonneg (show 0 ≤ (a : Int) by omega) (show 0 ≤ (k : Int) by omega)
      rw [hz] at hmax'
      simp at hmax'
      omega
    · omega
  have hb : oddCount n k = b + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hbpos)).symm
  have hba : b ≤ a := by have := prefix_odd_le (n := n) (Nat.le_of_lt hkL); omega
  have hphaseZ : (a : Int) * (k : Int) + 1 = (L : Int) * (b : Int) := by
    rw [hb, Int.natCast_add, Int.mul_add] at hmax'
    have he : ((1 : Nat) : Int) = 1 := rfl
    rw [he, Int.mul_one] at hmax'
    omega
  have hphase : a * k + 1 = L * b := by
    exact Int.ofNat_inj.mp (show ((a * k + 1 : Nat) : Int) = ((L * b : Nat) : Int) from by
      rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul]
      exact hphaseZ)
  have hmod (t : Nat) : (L : Int) ∣ W (t + k) - W t - 1 := by
    refine ⟨(oddCount n (t + k) : Int) - (oddCount n t : Int) - (b : Int), ?_⟩
    change walk n L (t + k) - walk n L t - 1 = _
    unfold walk
    rw [Int.natCast_add, Int.mul_add]
    simp only [Int.mul_sub]
    dsimp [a] at hphaseZ
    omega
  have hWr : W r = (L : Int) - 1 := by
    have hh := hmod r
    rw [hrsum, show W L = 0 from walk_full n L] at hh
    have hn := Int.dvd_neg.mpr hh
    rw [show -(0 - W r - 1) = W r + 1 by omega] at hn
    have hd := Int.dvd_sub hn (Int.dvd_refl (L : Int))
    rw [show W r + 1 - L = W r - (L - 1) by omega] at hd
    exact extra_strip_unique_interior (hstrip r).1 (hstrip r).2 (by omega) (by omega) hd
  have hkr : k ≠ r := by
    intro he
    rw [← he] at hWr
    change W k = (L : Int) + 1 at hmax
    omega
  have hcount_r : oddCount n r = a - b + 1 := by
    have he : a * r = L * a - a * k := by dsimp [r]; rw [Nat.mul_sub_left_distrib, Nat.mul_comm a L]
    have he' : a * r = L * (a - b) + 1 := by
      rw [he, Nat.mul_sub_left_distrib]
      have hmul := Nat.mul_le_mul_left L hba
      omega
    have hw : (L : Int) * (oddCount n r : Int) - (a : Int) * (r : Int) = (L : Int) - 1 := hWr
    have hp := congrArg (fun t : Nat => (t : Int)) he'
    change ((a * r : Nat) : Int) = ((L * (a - b) + 1 : Nat) : Int) at hp
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul] at hp
    exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (L : Int) ≠ 0 by omega) (by
      rw [Int.natCast_add, Int.mul_add]
      have h1 : ((1 : Nat) : Int) = 1 := rfl
      rw [h1, Int.mul_one]
      omega))
  have hjump (t : Nat) (ht : 0 < t) (htL : t < L) :
      W (t + k) - W t = if t = k ∨ t = r then 1 - (L : Int) else 1 := by
    by_cases he : t = k ∨ t = r
    · rw [if_pos he]
      rcases he with htk | htr
      · subst t
        have hh := hmod k
        change W k = (L : Int) + 1 at hmax
        rw [hmax] at hh
        have hd := Int.dvd_add hh (Int.dvd_refl (L : Int))
        rw [show W (k + k) - (L + 1) - 1 + L = W (k + k) - 2 by omega] at hd
        have hv := extra_strip_unique_interior (hstrip (k + k)).1 (hstrip (k + k)).2
          (by omega : (2 : Int) ≤ 2) (by omega : (2 : Int) ≤ L - 1) hd
        change W (k + k) = 2 at hv
        rw [hmax, hv]
        omega
      · rw [htr, hrsum, hWr, show W L = 0 from walk_full n L]
        omega
    · rw [if_neg he]
      have hnot₀ : W t ≠ 0 ∧ W t ≠ (L : Int) := by
        have hne₀ : t ≠ 0 := by omega
        have hD (hd : (L : Int) ∣ W t) : False := by
          apply hne₀
          apply phase_injective_in_period hphase htL (by omega : 0 < L)
          rw [walk_zero, Int.sub_zero]
          exact hd
        exact ⟨fun hz => hD (hz ▸ Int.dvd_zero _), fun hz => hD (hz ▸ Int.dvd_refl _)⟩
      have hnot₁ : W t ≠ 1 ∧ W t ≠ (L : Int) + 1 := by
        have hD (hd : (L : Int) ∣ W t - W k) : False := he (Or.inl
          (phase_injective_in_period hphase htL hkL hd))
        change W k = (L : Int) + 1 at hmax
        constructor
        · intro ht'
          apply hD
          rw [ht', hmax, show (1 : Int) - (L + 1) = -L by omega]
          exact Int.dvd_neg.mpr (Int.dvd_refl _)
        · intro ht'
          apply hD
          rw [ht', hmax, Int.sub_self]
          exact Int.dvd_zero _
      have hnot_r : W t ≠ (L : Int) - 1 := by
        intro heq
        apply he
        right
        apply phase_injective_in_period hphase htL hrL
        change (L : Int) ∣ W t - W r
        rw [heq, hWr, Int.sub_self]
        exact Int.dvd_zero _
      have hlo := (hstrip t).1
      have hhi := (hstrip t).2
      change 0 ≤ W t at hlo
      change W t ≤ (L : Int) + 1 at hhi
      have hd := hmod t
      rw [show W (t + k) - W t - 1 = W (t + k) - (W t + 1) by omega] at hd
      have hh := extra_strip_unique_interior (hstrip (t + k)).1 (hstrip (t + k)).2
        (by omega : 2 ≤ W t + 1) (by omega : W t + 1 ≤ (L : Int) - 1) hd
      change W (t + k) = W t + 1 at hh
      omega
  refine ⟨b, hphase, hb, hcount_r, hkr, fun t ht htL => ?_⟩
  have hs := walk_shift h.2 k t
  rw [Nat.add_comm k t] at hs
  change walk (acceleratedOrbit k n) L t = W (t + k) - W k at hs
  have hx : W t = (L : Int) * (oddCount n t : Int) - (a : Int) * (t : Int) := rfl
  have hy : walk (acceleratedOrbit k n) L t =
      (L : Int) * (oddCount (acceleratedOrbit k n) t : Int) - (a : Int) * (t : Int) := by
    unfold walk
    rw [RotationLaw.oddCount_rotation_invariant h k]
  rw [hy] at hs
  have hj := hjump t ht htL
  change W k = (L : Int) + 1 at hmax
  by_cases he : t = k ∨ t = r
  · rw [if_pos he] at hj ⊢
    exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (L : Int) ≠ 0 by omega) (by
      rw [Int.natCast_add, Int.mul_add]
      change (L : Int) * (oddCount (acceleratedOrbit k n) t : Int) + (L : Int) * 2 = _
      omega))
  · rw [if_neg he] at hj ⊢
    exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (L : Int) ≠ 0 by omega) (by
      rw [Int.natCast_add, Int.mul_add]
      change (L : Int) * (oddCount (acceleratedOrbit k n) t : Int) + (L : Int) * 1 = _
      omega))

private theorem shifted_area_sum {n L k : Nat} (h : AccIsCycleOf n L)
    (hk : 0 < k) (hkL : k < L) (hkr : k ≠ L - k)
    (hcount : ∀ t, 0 < t → t < L →
      oddCount (acceleratedOrbit k n) t + (if t = k ∨ t = L - k then 2 else 1) = oddCount n t) :
    let a := oddCount n L
    let y := acceleratedOrbit k n
    let F := fun t => 2 ^ t * 3 ^ (a - oddCount n (t + 1))
    let G := fun t => 2 ^ t * 3 ^ (a - oddCount y (t + 1))
    sumRange L G + 2 ^ L = 3 * sumRange L F + 6 * F (k - 1) + 6 * F (L - k - 1) := by
  let a := oddCount n L
  let y := acceleratedOrbit k n
  let F := fun t => 2 ^ t * 3 ^ (a - oddCount n (t + 1))
  let G := fun t => 2 ^ t * 3 ^ (a - oddCount y (t + 1))
  let r := L - k
  let B := 2 ^ L
  let hit := fun s t => if t + 1 = s then F t else 0
  have hy : oddCount y L = a := RotationLaw.oddCount_rotation_invariant h k
  have hr : 0 < r := by dsimp [r]; omega
  have hrL : r < L := by dsimp [r]; omega
  have hp (t : Nat) (ht : t < L) : G t + (if t + 1 = L then B else 0) =
      3 * F t + 6 * hit k t + 6 * hit r t := by
    by_cases he : t + 1 = L
    · have hf : F t = 2 ^ t := by dsimp [F, a]; rw [he, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      have hg : G t = 2 ^ t := by dsimp [G]; rw [he, hy, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      have hB : B = 2 ^ t * 2 := by dsimp [B]; rw [← he, Nat.pow_succ]
      have hk' : t + 1 ≠ k := by omega
      have hr' : t + 1 ≠ r := by omega
      simp only [hf, hg, hB, he, if_true, hit, if_neg hk', if_neg hr', Nat.mul_zero, Nat.add_zero]
      omega
    · have hw := hcount (t + 1) (by omega) (by omega)
      let d := if t + 1 = k ∨ t + 1 = r then 2 else 1
      change oddCount y (t + 1) + d = oddCount n (t + 1) at hw
      have hle := prefix_odd_le (n := n) (show t + 1 ≤ L by omega)
      have hsub : a - oddCount y (t + 1) = a - oddCount n (t + 1) + d := by
        change oddCount n (t + 1) ≤ a at hle
        omega
      have hscale : G t = F t * 3 ^ d := by dsimp [G, F]; rw [hsub, Nat.pow_add, Nat.mul_assoc]
      rw [hscale, if_neg he, Nat.add_zero]
      by_cases hk' : t + 1 = k
      · have hr' : t + 1 ≠ r := by omega
        simp only [d, Or.inl hk', if_true, hit, if_neg hr', Nat.mul_zero, Nat.add_zero, if_pos hk']
        rw [show (3 : Nat) ^ 2 = 9 by decide]
        omega
      · by_cases hr' : t + 1 = r
        · simp only [d, Or.inr hr', if_true, hit, if_neg hk', if_pos hr', Nat.mul_zero, Nat.add_zero]
          rw [show (3 : Nat) ^ 2 = 9 by decide]
          omega
        · have hne : ¬ (t + 1 = k ∨ t + 1 = r) := by omega
          simp only [d, if_neg hne, Nat.pow_one, hit, if_neg hk', if_neg hr', Nat.mul_zero, Nat.add_zero]
          exact Nat.mul_comm ..
  have hs := sumRange_congr hp
  have hlast := sum_after_step_at (fun _ => B) (t := L) h.1 (Nat.le_refl _)
  have hk' := sum_after_step_at F (t := k) hk (Nat.le_of_lt hkL)
  have hr' := sum_after_step_at F (t := r) hr (Nat.le_of_lt hrL)
  simp only [sumRange_add, sumRange_const_mul, hit, hlast, hk', hr'] at hs
  exact hs

private theorem one_extra_gap_divides_seven {n L k : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hL : 3 ≤ L) (hk : 0 < k) (hkL : k < L) (hmax : walk n L k = (L : Int) + 1)
    (hstrip : ∀ t, 0 ≤ walk n L t ∧ walk n L t ≤ (L : Int) + 1) :
    (2 ^ L - 3 ^ oddCount n L) ∣ 7 ∧
      ∃ b, oddCount n L * k + 1 = L * b := by
  obtain ⟨b, hphase, hbk, hbr, hkr, hcount⟩ := one_extra_coordinates h hL hk hkL hmax hstrip
  let a := oddCount n L
  let y := acceleratedOrbit k n
  let r := L - k
  let d := 2 ^ L - 3 ^ a
  let F := fun t => 2 ^ t * 3 ^ (a - oddCount n (t + 1))
  let G := fun t => 2 ^ t * 3 ^ (a - oddCount y (t + 1))
  have ha := oddCount_pos_of_accCycle hn h
  have hlt := (accCycle_bounds hn h).2.2
  have hr : 0 < r := by dsimp [r]; omega
  have hrL : r < L := by dsimp [r]; omega
  have hbpos : 0 < b := by
    by_cases hb : b = 0
    · simp [hb] at hphase
    · omega
  have hble : b + 1 ≤ a := by
    have he := prefix_odd_le (n := n) (Nat.le_of_lt hkL)
    change oddCount n k ≤ a at he
    omega
  have hF (t c : Nat) (ht : 0 < t) (hc : c + 1 ≤ a)
      (he : oddCount n t = c + 1) : 6 * F (t - 1) = 2 ^ t * 3 ^ (a - c) := by
    dsimp [F]
    rw [Nat.sub_add_cancel (show 1 ≤ t by omega), he]
    calc
      _ = (2 ^ (t - 1) * 2) * (3 ^ (a - (c + 1)) * 3) := by
        rw [show (6 : Nat) = 2 * 3 by decide]
        ac_rfl
      _ = _ := by
        rw [← Nat.pow_succ, ← Nat.pow_succ]
        change 2 ^ (t - 1 + 1) * 3 ^ (a - (c + 1) + 1) = _
        rw [Nat.sub_add_cancel (show 1 ≤ t by omega), show a - (c + 1) + 1 = a - c by omega]
  have hkF := hF k b hk hble hbk
  have hrF := hF r (a - b) hr (by omega) hbr
  rw [show a - (a - b) = b by omega] at hrF
  have hs := shifted_area_sum h hk hkL hkr hcount
  change sumRange L G + 2 ^ L = 3 * sumRange L F + 6 * F (k - 1) + 6 * F (r - 1) at hs
  rw [hkF, hrF] at hs
  have hx := affine_area n L
  have hy := affine_area y L
  rw [RotationLaw.oddCount_rotation_invariant h k] at hy
  change 2 * affineC L n + 2 ^ L = 3 ^ a + sumRange L F at hx
  change 2 * affineC L y + 2 ^ L = 3 ^ a + sumRange L G at hy
  rw [← CycleAccumulator.cycle_gap_mul hn h] at hx
  rw [← RotationLaw.affine_cycle_eq_rotation hn h k] at hy
  change 2 * (d * n) + 2 ^ L = 3 ^ a + sumRange L F at hx
  change 2 * (d * y) + 2 ^ L = 3 ^ a + sumRange L G at hy
  have he : 2 * (d * y) + 2 * 3 ^ a = 6 * (d * n) + 2 ^ L + 2 ^ k * 3 ^ (a - b) + 2 ^ r * 3 ^ b := by
    omega
  let X := (2 : Int) ^ k
  let Y := (3 : Int) ^ b
  let U := (3 : Int) ^ (a - b)
  let V := (2 : Int) ^ r
  let A := (3 : Int) ^ a
  let B := (2 : Int) ^ L
  have hcast : (d : Int) = B - A := by
    dsimp [d, B, A]
    rw [Int.ofNat_sub (Nat.le_of_lt hlt), Int.natCast_pow, Int.natCast_pow]
    rfl
  have hd : (d : Int) ∣ B - A := ⟨1, by rw [← hcast, Int.mul_one]⟩
  have harea : (d : Int) ∣ X * U + V * Y - A := by
    have hz := congrArg (fun z : Nat => (z : Int)) he
    change ((2 * (d * y) + 2 * 3 ^ a : Nat) : Int) =
      ((6 * (d * n) + 2 ^ L + 2 ^ k * 3 ^ (a - b) + 2 ^ r * 3 ^ b : Nat) : Int) at hz
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hz
    change 2 * ((d : Int) * (y : Int)) + 2 * A =
      6 * ((d : Int) * (n : Int)) + B + X * U + V * Y at hz
    refine ⟨2 * (y : Int) - 6 * (n : Int) - 1, ?_⟩
    grind
  have hA : Y * U = A := by
    dsimp [Y, U, A]
    rw [← Int.pow_add, Nat.add_sub_of_le (by omega : b ≤ a)]
  have hB : X * V = B := by
    dsimp [X, V, B, r]
    rw [← Int.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hkL)]
  have hquad' := Int.dvd_sub (Int.dvd_trans harea (Int.dvd_mul_right _ (X * Y)))
    (Int.dvd_trans hd (Int.dvd_mul_right _ (Y ^ 2)))
  rw [show (X * U + V * Y - A) * (X * Y) - (B - A) * Y ^ 2 =
      A * (X ^ 2 - X * Y + Y ^ 2) by rw [← hA, ← hB]; grind] at hquad'
  have hcop := (gap_coprime_two_three ha h.1 hlt).2.pow_right a
  have hquad := cancel_coprime_factor hcop (by
    change (d : Int) ∣ ((3 ^ a : Nat) : Int) * (X ^ 2 - X * Y + Y ^ 2)
    rwa [Int.natCast_pow])
  exact ⟨gap_divides_seven_of_quadratic ha h.1 hlt hphase hquad, b, hphase⟩

private theorem pow_mod_two_phase (x m e : Nat) (hm : 1 < m) (h : x ^ 2 % m = 1) :
    x ^ e % m = x ^ (e % 2) % m := by
  calc
    _ = x ^ (2 * (e / 2) + e % 2) % m := congrArg (fun t => x ^ t % m) (Nat.div_add_mod e 2).symm
    _ = _ := by
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod (x ^ 2), h, Nat.one_pow,
        Nat.mod_eq_of_lt hm, Nat.one_mul, Nat.mod_mod]

private theorem seven_gap_incompatible_with_adjacent_phase {L a k b : Nat} (hL : 3 ≤ L) (ha : 0 < a)
    (hlt : 3 ^ a < 2 ^ L) (hseven : 2 ^ L - 3 ^ a = 7) (hphase : a * k + 1 = L * b) : False := by
  have he := Nat.sub_add_cancel (Nat.le_of_lt hlt)
  rw [hseven] at he
  have hmodL : 2 ^ L % 3 = 1 := by
    have hp := congrArg (fun t : Nat => t % 3) he
    rw [Nat.add_mod, GapOne.three_pow_mod_three ha] at hp
    exact hp.symm
  have hmoda : 3 ^ a % 8 = 1 := by
    have hp := congrArg (fun t : Nat => t % 8) he
    rw [Nat.add_mod, GapOne.two_pow_mod_eight hL] at hp
    have h7 : 7 % 8 = 7 := by decide
    rw [h7] at hp
    have hr := Nat.mod_lt (3 ^ a) (by decide : 0 < 8)
    omega
  rw [pow_mod_two_phase 2 3 L (by decide) (by decide)] at hmodL
  rw [pow_mod_two_phase 3 8 a (by decide) (by decide)] at hmoda
  have hL0 : L % 2 = 0 := by
    by_cases hh : L % 2 = 0
    · exact hh
    · rw [show L % 2 = 1 by omega] at hmodL
      exact False.elim ((by decide : ¬ 2 ^ 1 % 3 = 1) hmodL)
  have ha0 : a % 2 = 0 := by
    by_cases hh : a % 2 = 0
    · exact hh
    · rw [show a % 2 = 1 by omega] at hmoda
      exact False.elim ((by decide : ¬ 3 ^ 1 % 8 = 1) hmoda)
  have hL' : L = 2 * (L / 2) := by have := Nat.div_add_mod L 2; omega
  have ha' : a = 2 * (a / 2) := by have := Nat.div_add_mod a 2; omega
  rw [hL', ha'] at hphase
  simp only [Nat.mul_assoc] at hphase
  omega

/-- A least positive cycle is trivial if its discrepancy width is at
most one greater than the period. The extra unit introduces two exceptions
whose combined correction forces a gap dividing seven. -/
theorem width_at_most_period_add_one_forces_trivial {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hwidth : ∀ i j, walk n L i ≤ walk n L j + L + 1) : L = 2 ∧ (n = 1 ∨ n = 2) := by
  by_cases htwo : L = 2
  · exact ⟨htwo, accIsCycleOf_two_length hn (htwo ▸ h)⟩
  have hL : 3 ≤ L := by have := two_le_length_of_accCycle hn h; omega
  by_cases hsmall : ∀ i j, walk n L i ≤ walk n L j + L
  · exact BoundaryWidthCycle.width_at_most_period_forces_trivial hn h hleast hsmall
  have hex : ∃ i j, walk n L i = walk n L j + L + 1 := by
    apply Classical.byContradiction
    intro hno
    apply hsmall
    intro i j
    have hle := hwidth i j
    have hne : walk n L i ≠ walk n L j + L + 1 := fun he => hno ⟨i, j, he⟩
    omega
  obtain ⟨i, j, he⟩ := hex
  let r := j % L
  let x := acceleratedOrbit r n
  have hr : r < L := Nat.mod_lt _ h.1
  have he' : walk n L i = walk n L r + L + 1 := by rw [← walk_mod h.1 h.2 j]; exact he
  have hstrip (t : Nat) : 0 ≤ walk x L t ∧ walk x L t ≤ (L : Int) + 1 := by
    have hs := walk_shift h.2 r t
    change walk x L t = walk n L (r + t) - walk n L r at hs
    have hlo := hwidth i (r + t)
    have hhi := hwidth (r + t) r
    omega
  obtain ⟨k, hkL, hval⟩ := walk_range' h.1 h.2 hr i
  have hmax : walk x L k = (L : Int) + 1 := by change walk x L k = _ at hval; omega
  have hk : 0 < k := by
    by_cases h0 : k = 0
    · rw [h0, walk_zero] at hmax
      omega
    · omega
  have hp := accIsCycleOf_orbit h r
  have hx := acceleratedOrbit_positive hn r
  obtain ⟨hd, b, hphase⟩ := one_extra_gap_divides_seven hx hp hL hk hkL hmax hstrip
  let d := 2 ^ L - 3 ^ oddCount x L
  have hlt := (accCycle_bounds hx hp).2.2
  change d ∣ 7 at hd
  have hcases : d = 1 ∨ d = 7 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 7) hd
    have hfinite : ∀ u : Fin 8, u.val ∣ 7 → u.val = 1 ∨ u.val = 7 := by decide +kernel
    exact hfinite ⟨d, by omega⟩ hd
  rcases hcases with h1 | h7
  · have hL' := (GapOne.gap_one_forces_trivial hx hp h1).1
    exact ⟨hL', accIsCycleOf_two_length hn (hL' ▸ h)⟩
  · exact False.elim (seven_gap_incompatible_with_adjacent_phase hL
      (oddCount_pos_of_accCycle hx hp) hlt h7 hphase)

/-- A hypothetical nontrivial least period needs a scaled discrepancy
spread of at least `L+2` within one period. -/
theorem nontrivial_cycle_needs_extra_width {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hnon : 2 < n) :
    ∃ i j, i < L ∧ j < L ∧ walk n L j + L + 2 ≤ walk n L i := by
  apply Classical.byContradiction
  intro hno
  have hwidth (i j : Nat) : walk n L i ≤ walk n L j + L + 1 := by
    rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
    have hn' : ¬ walk n L (j % L) + L + 2 ≤ walk n L (i % L) := fun hge =>
      hno ⟨i % L, j % L, Nat.mod_lt _ h.1, Nat.mod_lt _ h.1, hge⟩
    omega
  have ht := (width_at_most_period_add_one_forces_trivial hn h hleast hwidth).2
  omega

end Collatz.OneExtraCycle
