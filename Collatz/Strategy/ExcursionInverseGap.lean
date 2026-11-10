import Collatz.Strategy.ExcursionBoundaryPair
import Collatz.Strategy.InverseCover
import Collatz.Structure.Minimal

/-!
# Inverse contraction at the exceptional excursion landing

The gap between the exceptional landing and its source is much smaller
than the absolute boundary window. At a least counterexample this allows
a contracting inverse word of the landing to produce a smaller
counterexample. A second determinant-one bracket controls the inverse
coefficient through a longer odd-step horizon.
-/

namespace Collatz.ExcursionBudget

open Collatz.DyadicPowerBounds Collatz.ExcursionPowerGap

private def floorValue : Nat := 2 ^ 71
private def landingAllowance : Nat := 6443285299

set_option maxRecDepth 4096 in
private theorem boundary_landing_comparison :
    (300 * floorValue + (81 * 72057431991 + 24)) * (3 : Nat) ^ 72057431991 <
      300 * (floorValue + landingAllowance) * 2 ^ 114208327604 :=
  strict_upper_comparison 3 72057431991 192 _ _ 114208327604 (by decide +kernel)

/-- The positive offset and the mandatory coefficient loss together
bound the difference between the landing and the source. -/
theorem Trace.landing_lt_source_add_of_boundary_pair {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hlarge : 2 ^ 71 ≤ n)
    (ha : oddCount rs = 72057431991) (hb : time rs = 114208327604) :
    e < n + 6443285299 := by
  let A := 3 ^ oddCount rs
  let B := 2 ^ time rs
  let J := 81 * oddCount rs + 24
  let d := n - floorValue
  have hd : floorValue + d = n := Nat.add_sub_of_le hlarge
  have hcomp : (300 * floorValue + J) * A < 300 * (floorValue + landingAllowance) * B := by
    simpa only [A, B, J, ha, hb] using boundary_landing_comparison
  have hnormalize : 300 * (B * e) ≤ (300 * n + J) * A := by
    rw [← h.affine, Nat.mul_add, Nat.add_mul]
    have hcharge : 300 * offset rs ≤ J * A := h.offset_le_credited_odd hproper
    have hterm : 300 * (A * n) = (300 * n) * A := by ac_rfl
    rw [hterm]
    exact Nat.add_le_add_left hcharge _
  change e < n + landingAllowance
  apply Nat.lt_of_mul_lt_mul_left (a := 300 * B)
  calc
    _ = 300 * (B * e) := by ac_rfl
    _ ≤ (300 * n + J) * A := hnormalize
    _ = (300 * floorValue + J) * A + 300 * d * A := by
      rw [← hd, Nat.mul_add, Nat.add_right_comm, Nat.add_mul]
    _ < 300 * (floorValue + landingAllowance) * B + 300 * d * B :=
      Nat.add_lt_add_of_lt_of_le hcomp (Nat.mul_le_mul_left _ (Nat.le_of_lt hcross))
    _ = (300 * B) * (floorValue + landingAllowance) + (300 * B) * d := by
      rw [Nat.mul_right_comm 300 (floorValue + landingAllowance) B, Nat.mul_right_comm 300 d B]
    _ = (300 * B) * (n + landingAllowance) := by
      rw [← Nat.mul_add, Nat.add_right_comm floorValue landingAllowance, hd]

private theorem inverse_upper : (3 : Nat) ^ 137528045312 < 2 ^ 217976794617 := by
  simpa only [Nat.one_mul] using
    strict_upper_comparison 3 137528045312 192 1 1 217976794617 (by decide +kernel)

private theorem inverse_lower_scaled :
    (floorValue + landingAllowance) * (2 : Nat) ^ 539722056247 ≤
      floorValue * 3 ^ 340526703945 :=
  Nat.le_of_lt (scaled_lower_comparison 3 340526703945 192 _ _ 539722056247
    (by decide +kernel))

set_option maxRecDepth 4096 in
/-- The inverse slope of any contracting word below the odd-step
horizon compensates for the exceptional landing allowance. -/
theorem inverse_gap_at_boundary {a b : Nat} (ha : 0 < a) (hbound : a < 478054749257)
    (hcross : 2 ^ b < 3 ^ a) :
    (2 ^ 71 + 6443285299) * 2 ^ b ≤ 2 ^ 71 * 3 ^ a := by
  change (floorValue + landingAllowance) * 2 ^ b ≤ floorValue * 3 ^ a
  have hdet : 340526703945 * 217976794617 = 137528045312 * 539722056247 + 1 :=
    by decide +kernel
  have hside : b * 340526703945 ≤ 539722056247 * a :=
    inverse_exponent_cross_le_of_bracket ha (by decide : 0 < 137528045312)
      hcross hbound hdet inverse_upper
  exact inverse_scaled_gap_of_cross_le (p := 539722056247) (q := 340526703945)
    (r := 217976794617) (s := 137528045312) (K := floorValue)
    (L := floorValue + landingAllowance) ha hside hdet (Nat.le_of_lt inverse_upper)
    (by decide : 0 < floorValue) (by decide : floorValue ≤ floorValue + landingAllowance)
    inverse_lower_scaled

/-- At the next mediant the arithmetic comparison alone no longer
compensates for the allowance. -/
theorem inverse_gap_boundary_mediant :
    (2 : Nat) ^ 757698850864 < 3 ^ 478054749257 ∧
      floorValue * 3 ^ 478054749257 < (floorValue + landingAllowance) * 2 ^ 757698850864 := by
  exact ⟨lower_comparison 3 478054749257 192 757698850864 (by decide +kernel),
    strict_upper_comparison 3 478054749257 192 floorValue (floorValue + landingAllowance)
      757698850864 (by decide +kernel)⟩

open Collatz.Minimal Collatz.InverseCover

/-- An inverse word can overcome a bounded forward increase at a
least counterexample if its slope pays for the allowance. -/
theorem no_inverse_word_of_near_minimal_landing {n e k N M : Nat} {w : List Nat}
    (hmin : MinimalCounterexample n) (hland : acceleratedOrbit k n = e)
    (hN : 0 < N) (hn : N ≤ n) (he : e < n + M)
    (hslope : (N + M) * 2 ^ w.sum ≤ N * 3 ^ w.length) : ¬ Valid e w := by
  intro hw
  let P := 2 ^ w.sum
  let Q := 3 ^ w.length
  have hep : 0 < e := hland ▸ acceleratedOrbit_positive hmin.1.1 k
  have hp := follow_pos hep hw
  have hlt : follow e w < n := by
    apply Nat.lt_of_mul_lt_mul_left (a := N * Q)
    calc
      _ = N * (Q * follow e w) := by ac_rfl
      _ ≤ N * (P * e) := Nat.mul_le_mul_left _ (follow_le hw)
      _ < N * (P * (n + M)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left he (Nat.two_pow_pos _)) hN
      _ = P * (N * n + N * M) := by rw [← Nat.mul_add]; ac_rfl
      _ ≤ P * (N * n + n * M) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)
      _ = ((N + M) * P) * n := by rw [Nat.mul_comm n M, ← Nat.add_mul]; ac_rfl
      _ ≤ (N * Q) * n := Nat.mul_le_mul_right _ hslope
  have hr := reachesOne_of_lt_minimal hmin hp hlt
  have hre := (Reach.reachesOne_accOrbit_iff hp w.sum).mp hr
  rw [follow_orbit hw] at hre
  exact hmin.1.2 (Reach.reachesOne_of_accOrbit hmin.1.1 (hland.symm ▸ hre))

/-- At the first excursion crossing of a least counterexample,
any inverse word with fewer than 478,054,749,257 odd steps at the
exceptional landing has inverse coefficient at least one. -/
theorem Trace.no_inverse_contraction_of_boundary {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hmin : MinimalCounterexample n)
    {w : List Nat} (hw : Valid e w) (hdepth : w.length < 478054749257) :
    3 ^ w.length ≤ 2 ^ w.sum := by
  apply Nat.le_of_not_gt
  intro hcontract
  have hkeep : n ≤ e := Nat.le_of_not_gt fun he =>
    not_accOrbit_lt_of_minimal hmin (time rs) (h.landing.symm ▸ he)
  obtain ⟨ha, hb⟩ := h.first_crossing_failure_boundary_pair hproper hcross hbound hlarge hkeep
  have hnear := h.landing_lt_source_add_of_boundary_pair hproper hcross hlarge ha hb
  have hpos : 0 < w.length := by
    cases w with
    | nil => simp at hcontract
    | cons => simp
  exact no_inverse_word_of_near_minimal_landing hmin h.landing (Nat.two_pow_pos 71)
    hlarge hnear (inverse_gap_at_boundary hpos hdepth hcontract) hw

/-- An admissible contracting inverse word at a representative
excludes its entire ternary residue class from the boundary landing. -/
theorem Trace.boundary_landing_avoids_inverse_residue {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hmin : MinimalCounterexample n)
    {r : Nat} {w : List Nat} (hw : Valid r w) (hdepth : w.length < 478054749257)
    (hcontract : 2 ^ w.sum < 3 ^ w.length) : e % 3 ^ w.length ≠ r % 3 ^ w.length := by
  intro hres
  have hres' : e % 3 ^ (0 + w.length) = r % 3 ^ (0 + w.length) := by
    simpa only [Nat.zero_add] using hres
  have hvalid := (follow_congr 0 hres' hw).1
  exact Nat.not_le_of_gt hcontract
    (h.no_inverse_contraction_of_boundary hproper hcross hbound hlarge hmin hvalid hdepth)

/-- Two short inverse words sharpen the terminal congruence
under the same explicit finite verification premise. -/
theorem Trace.boundary_landing_avoids_mod_nine_and_eighty_one
    (verified : VerifiedBelowTwoPow71) {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hmin : MinimalCounterexample n) :
    (e % 9 = 1 ∨ e % 9 = 7) ∧ e % 81 ≠ 10 := by
  have hlarge : 2 ^ 71 ≤ n := Nat.le_of_not_gt fun hn => hmin.1.2 (verified n hmin.1.1 hn)
  have hkeep : n ≤ e := Nat.le_of_not_gt fun he =>
    not_accOrbit_lt_of_minimal hmin (time rs) (h.landing.symm ▸ he)
  have hmod := (h.first_crossing_failure_boundary_residues verified hproper hcross
    hbound hlarge hkeep hmin.1.2).2
  have h4 : e % 9 ≠ 4 := h.boundary_landing_avoids_inverse_residue hproper hcross hbound
    hlarge hmin (w := [2, 1]) (r := 4) (by decide) (by decide) (by decide)
  have h10 : e % 81 ≠ 10 := h.boundary_landing_avoids_inverse_residue hproper hcross hbound
    hlarge hmin (w := [2, 2, 1, 1]) (r := 10) (by decide) (by decide) (by decide)
  exact ⟨by omega, h10⟩

end Collatz.ExcursionBudget
