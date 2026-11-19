import Collatz.Strategy.BranchingDuality
import Collatz.Strategy.ExcursionBoundaryCharge
import Collatz.Strategy.ExcursionFiniteCrossing

/-!
# A single exceptional pair below the next exponent bound

A failed first crossing above the verified source range must
have a small relative coefficient gap. A determinant-one
bracket gives the lower side of its allowable exponent ratio.
An exact interval comparison with a slightly enlarged base
rules out every ratio strictly above the upper member.
-/

namespace Collatz.ExcursionPowerGap

open Collatz.DyadicPowerBounds

private theorem persists_under_power {X Y a N : Nat} (hY : 0 < Y)
    (ha : a ≤ N) (h : 2 * Y ^ a ≤ X ^ a) : 2 * Y ^ N ≤ X ^ N := by
  have hYX : Y ≤ X := by
    apply Nat.le_of_not_gt
    intro hlt
    have hp := Nat.pow_le_pow_left (Nat.le_of_lt hlt) a
    have hpos := Nat.pow_pos (n := a) hY
    omega
  have hsplit : a + (N - a) = N := Nat.add_sub_of_le ha
  calc
    _ = (2 * Y ^ a) * Y ^ (N - a) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsplit]
    _ ≤ X ^ a * X ^ (N - a) := Nat.mul_le_mul h (Nat.pow_le_pow_left hYX _)
    _ = _ := by rw [← Nat.pow_add, hsplit]

/-- An enlarged-base power comparison bounds the cross product of
any exponents with the indicated small positive gap. -/
theorem exponent_cross_le_of_gap {a b r s N F : Nat} (hF : 0 < F) (ha : a ≤ N)
    (hAB : 3 ^ a < 2 ^ b) (hgap : F * (2 ^ b - 3 ^ a) ≤ a * 3 ^ a)
    (hpower : (3 * (F + 1)) ^ (s * N) < F ^ (s * N) * 2 ^ (r * N + 1)) :
    b * s ≤ r * a := by
  let X := (3 * (F + 1)) ^ s
  let Y := F ^ s * 2 ^ r
  have hlin : F * 2 ^ b ≤ (F + a) * 3 ^ a := by
    have hsum : 3 ^ a + (2 ^ b - 3 ^ a) = 2 ^ b :=
      Nat.add_sub_of_le (Nat.le_of_lt hAB)
    rw [← hsum, Nat.mul_add, Nat.add_mul]
    exact Nat.add_le_add_left hgap _
  have hbern : (F + a) * F ^ a ≤ F * (F + 1) ^ a :=
    bernoulli_scaled (Nat.le_succ F) (Nat.le_of_eq (Nat.mul_comm ..)) a
  have hbase : F ^ a * 2 ^ b ≤ (3 * (F + 1)) ^ a := by
    apply Nat.le_of_mul_le_mul_left _ hF
    calc
      _ = F ^ a * (F * 2 ^ b) := by ac_rfl
      _ ≤ F ^ a * ((F + a) * 3 ^ a) := Nat.mul_le_mul_left _ hlin
      _ = ((F + a) * F ^ a) * 3 ^ a := by ac_rfl
      _ ≤ (F * (F + 1) ^ a) * 3 ^ a := Nat.mul_le_mul_right _ hbern
      _ = _ := by rw [Nat.mul_pow]; ac_rfl
  have hrepack (i : Nat) : 2 * Y ^ i = F ^ (i * s) * 2 ^ (r * i + 1) := by
    dsimp only [Y]
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm s i, Nat.pow_succ]
    ac_rfl
  apply Nat.le_of_not_gt
  intro hlarge
  have hle : 2 * Y ^ a ≤ X ^ a := by
    calc
      _ = F ^ (a * s) * 2 ^ (r * a + 1) := hrepack a
      _ ≤ F ^ (a * s) * 2 ^ (b * s) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ = (F ^ a * 2 ^ b) ^ s := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
      _ ≤ ((3 * (F + 1)) ^ a) ^ s := Nat.pow_le_pow_left hbase _
      _ = X ^ a := by dsimp only [X]; rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm a s]
  have hlargeN := persists_under_power
    (Nat.mul_pos (Nat.pow_pos hF) (Nat.two_pow_pos _)) ha hle
  have hsmallN : X ^ N < 2 * Y ^ N := by
    rw [hrepack, Nat.mul_comm N s]
    simpa only [X, ← Nat.pow_mul] using hpower
  exact Nat.not_le_of_gt hsmallN hlargeN

private def floorScale : Nat := 7 * 2 ^ 70
private def specialOdd : Nat := 72057431991
private def specialTime : Nat := 114208327604
private def oddLimit : Nat := 137528045312

private theorem boundary_lower : (2 : Nat) ^ 103768467013 < 3 ^ 65470613321 :=
  lower_comparison 3 65470613321 128 103768467013 (by decide +kernel)

private theorem boundary_enlarged_power :
    (3 * (floorScale + 1)) ^ (specialOdd * oddLimit) <
      floorScale ^ (specialOdd * oddLimit) * 2 ^ (specialTime * oddLimit + 1) :=
  shifted_power_comparison (3 * (floorScale + 1)) (specialOdd * oddLimit)
    floorScale (specialOdd * oddLimit) (specialTime * oddLimit + 1) 192 (by decide +kernel)

/-- In the stated range there is only one exponent pair compatible
with the required relative gap. -/
theorem boundary_pair_of_scaled_gap {a b : Nat} (ha : 0 < a) (hbound : a < 137528045312)
    (hAB : 3 ^ a < 2 ^ b) (hgap : (7 * 2 ^ 70) * (2 ^ b - 3 ^ a) ≤ a * 3 ^ a) :
    a = 72057431991 ∧ b = 114208327604 := by
  have hleft : specialTime * a ≤ b * specialOdd :=
    exponent_cross_ge_of_bracket (p := 103768467013) (q := 65470613321)
      ha hAB hbound (by decide) boundary_lower
  have hright : b * specialOdd ≤ specialTime * a :=
    exponent_cross_le_of_gap (F := floorScale) (N := oddLimit)
      (by decide) (Nat.le_of_lt hbound) hAB hgap boundary_enlarged_power
  have he := Nat.le_antisymm hleft hright
  have hdvd : specialOdd ∣ specialTime * a := ⟨b, he.trans (Nat.mul_comm ..)⟩
  have hdiv := (Nat.dvd_gcd_mul_iff_dvd_mul).mpr hdvd
  have hgcd : Nat.gcd specialOdd specialTime = 1 := by decide +kernel
  rw [hgcd, Nat.one_mul] at hdiv
  obtain ⟨m, hm⟩ := hdiv
  change a = 72057431991 * m at hm
  change 114208327604 * a = b * 72057431991 at he
  have hm1 : m = 1 := by omega
  omega

private theorem strict_gap_of_extra {A B scale charge : Nat} (hA : 0 < A)
    (hAB : A ≤ B) (h : (scale + charge + 1) * A ≤ scale * B) :
    charge * A < scale * (B - A) := by
  have he : scale * B = scale * A + scale * (B - A) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hAB]
  rw [he, Nat.add_mul, Nat.add_mul, Nat.one_mul] at h
  omega

private def boundaryCap : Nat := 3 * 2 ^ 70

private theorem boundary_source_comparison :
    (300 * boundaryCap + (81 * specialOdd + 24) + 1) * (3 : Nat) ^ specialOdd ≤
      300 * boundaryCap * 2 ^ specialTime :=
  upper_comparison 3 specialOdd 192
    (300 * boundaryCap + (81 * specialOdd + 24) + 1)
    (300 * boundaryCap) specialTime (by decide +kernel)

private theorem boundary_pair_gap_for_source_cap (h : (3 : Nat) ^ specialOdd < 2 ^ specialTime) :
    (81 * specialOdd + 24) * (3 : Nat) ^ specialOdd <
      (300 * boundaryCap) * (2 ^ specialTime - 3 ^ specialOdd) :=
  strict_gap_of_extra (A := 3 ^ specialOdd) (B := 2 ^ specialTime)
    (Nat.pow_pos (by decide)) (Nat.le_of_lt h) boundary_source_comparison

private theorem transfer_source_cap {a b s t : Nat} (ha : a = s) (hb : b = t)
    (hcross : 3 ^ a < 2 ^ b)
    (hgap : 3 ^ s < 2 ^ t →
      (81 * s + 24) * 3 ^ s < (300 * boundaryCap) * (2 ^ t - 3 ^ s)) :
    (81 * a + 24) * 3 ^ a < (300 * boundaryCap) * (2 ^ b - 3 ^ a) := by
  subst s
  subst t
  exact hgap hcross

end Collatz.ExcursionPowerGap

namespace Collatz.ExcursionBudget

open Collatz.ExcursionPowerGap

/-- Above (2^{71}), any failed first excursion crossing with fewer
than 137,528,045,312 odd steps has the stated exact exponent pair. -/
theorem Trace.first_crossing_failure_boundary_pair {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) :
    oddCount rs = 72057431991 ∧ time rs = 114208327604 := by
  let a := oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let D := B - A
  have ha : 7 ≤ a := by
    apply Nat.le_of_not_gt
    intro hs
    have hn := h.first_crossing_failure_source_lt hproper hcross (by omega) hkeep
    omega
  have hsum : A + D = B := Nat.add_sub_of_le (Nat.le_of_lt hcross)
  have hD : D * n ≤ offset rs := by
    apply Nat.le_of_add_le_add_left (a := A * n)
    rw [← Nat.add_mul, hsum, h.affine]
    exact Nat.mul_le_mul_left _ hkeep
  have hcharge : 18 * offset rs ≤ (5 * a + 1) * A := h.offset_le_five_odd_add_one hproper
  have hsmall : (7 * 2 ^ 70) * D ≤ a * A := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 36)
    calc
      _ = 7 * (18 * (D * (2 ^ 71))) := by
        rw [show (2 : Nat) ^ 71 = 2 * 2 ^ 70 from Nat.pow_succ']
        ac_rfl
      _ ≤ 7 * (18 * (D * n)) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlarge))
      _ ≤ 7 * (18 * offset rs) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD)
      _ ≤ 7 * ((5 * a + 1) * A) := Nat.mul_le_mul_left _ hcharge
      _ ≤ _ := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
  exact boundary_pair_of_scaled_gap (by omega) hbound hcross hsmall

/-- The possible endpoint failure lies below (3cdot2^{70}).
The landing has the same upper bound as its source. -/
theorem Trace.first_crossing_failure_boundary_window {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) :
    oddCount rs = 72057431991 ∧ time rs = 114208327604 ∧ e < 3 * 2 ^ 70 := by
  obtain ⟨ha, hb⟩ := h.first_crossing_failure_boundary_pair hproper hcross hbound hlarge hkeep
  refine ⟨ha, hb, ?_⟩
  let A := 3 ^ oddCount rs
  let B := 2 ^ time rs
  let D := B - A
  have hsum : A + D = B := Nat.add_sub_of_le (Nat.le_of_lt hcross)
  have hgap : (81 * oddCount rs + 24) * A < (300 * boundaryCap) * D := by
    change (81 * oddCount rs + 24) * 3 ^ oddCount rs <
      (300 * boundaryCap) * (2 ^ time rs - 3 ^ oddCount rs)
    have ha' : oddCount rs = specialOdd := ha
    have hb' : time rs = specialTime := hb
    exact transfer_source_cap ha' hb' hcross boundary_pair_gap_for_source_cap
  have hbudget : D * e ≤ offset rs := by
    apply Nat.le_of_add_le_add_left (a := A * e)
    rw [← Nat.add_mul, hsum, ← h.affine]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hkeep) _
  apply Nat.lt_of_not_ge
  intro he
  have hle : (300 * boundaryCap) * D ≤ (81 * oddCount rs + 24) * A := by
    calc
      _ = 300 * (D * boundaryCap) := by ac_rfl
      _ ≤ 300 * (D * e) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)
      _ ≤ 300 * offset rs := Nat.mul_le_mul_left _ hbudget
      _ ≤ _ := h.offset_le_credited_odd hproper
  exact Nat.not_le_of_gt hgap hle

/-- The finite range of Bařina's verification used here, stated as
an external premise. -/
def VerifiedBelowTwoPow71 : Prop :=
  ∀ n : Nat, 0 < n → n < 2 ^ 71 → Reach.ReachesOne n

/-- A value in the boundary window that is two modulo three has
an odd predecessor below the verified floor. -/
theorem reaches_one_of_two_mod_three_below_boundary (verified : VerifiedBelowTwoPow71)
    {x : Nat} (hx : 0 < x) (hcap : x < 3 * 2 ^ 70) (hmod : x % 3 = 2) :
    Reach.ReachesOne x := by
  let p := BranchingDuality.oddPreimage x
  have hp : 0 < p := by unfold p BranchingDuality.oddPreimage; omega
  have hlt : p < 2 ^ 71 := by unfold p BranchingDuality.oddPreimage; omega
  have hs : acceleratedStep p = x := BranchingDuality.oddPreimage_step hx (by omega)
  exact hs ▸ (Reach.reachesOne_accStep_iff hp).mp (verified p hp hlt)

/-- A nonconvergent source and its surviving first-crossing landing
must also avoid the inverse branch from the verified range. -/
theorem Trace.first_crossing_failure_boundary_residues (verified : VerifiedBelowTwoPow71)
    {n e : Nat} {rs : List Run} (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) (hno : ¬ Reach.ReachesOne n) :
    n % 3 ≠ 2 ∧ e % 3 = 1 := by
  obtain ⟨_, _, hcap⟩ :=
    h.first_crossing_failure_boundary_window hproper hcross hbound hlarge hkeep
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hlarge
  have he : 0 < e := Nat.lt_of_lt_of_le hn hkeep
  constructor
  · intro hmod
    exact hno (reaches_one_of_two_mod_three_below_boundary verified hn
      (Nat.lt_of_le_of_lt hkeep hcap) hmod)
  · have hodd : 0 < Collatz.oddCount n (time rs) := by
      rw [h.shortcut_odd_count]
      exact h.odd_count_pos_of_crossing hcross
    have hnot0 : e % 3 ≠ 0 := by
      intro hmod
      have hdiv := Nat.dvd_of_mod_eq_zero hmod
      exact AccumulatorArith.three_not_dvd_orbit_of_odd_step hodd (h.landing.symm ▸ hdiv)
    have hnot2 : e % 3 ≠ 2 := by
      intro hmod
      have hr := reaches_one_of_two_mod_three_below_boundary verified he hcap hmod
      exact hno (Reach.reachesOne_of_accOrbit hn (h.landing.symm ▸ hr))
    omega

end Collatz.ExcursionBudget
