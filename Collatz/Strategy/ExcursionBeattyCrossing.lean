import Collatz.Strategy.AccumulatorValuation
import Collatz.Strategy.BeattyPhaseBound
import Collatz.Strategy.ExcursionInverseGap
import Collatz.Strategy.FirstLightBeatty

/-!
# Beatty charges at the first excursion crossing

The first shortcut crossing happens in the terminal even run of the
first excursion crossing. The accumulator has already stopped changing
there. A uniform phase-block bound therefore improves the excursion
offset charge and the exceptional landing allowance.
-/

namespace Collatz.ExcursionBudget

open AffineExact FirstLightDescent RealizableBound DyadicPowerBounds ExcursionPowerGap

private theorem Trace.offset_eq_accumulator {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    offset rs = affineC (time rs) n := by
  have hf := affine_exact n (time rs)
  rw [h.landing, h.shortcut_odd_count] at hf
  have ha := h.affine
  omega

/-- The terminal halving run leaves the first-light accumulator unchanged. -/
theorem Trace.offset_le_beatty_of_first_crossing {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) : offset rs ≤ Bcap (oddCount rs) := by
  obtain ⟨k, hk, hf, ha, _⟩ := h.first_light_of_first_crossing hproper hcross
  let d := time rs - k
  have hsplit : k + d = time rs := Nat.add_sub_of_le hk
  have htail : Collatz.oddCount (acceleratedOrbit k n) d = 0 := by
    have hcount := AccumulatorArith.oddCount_add n k d
    rw [hsplit, h.shortcut_odd_count, ha] at hcount
    omega
  rw [h.offset_eq_accumulator, ← hsplit, AccumulatorArith.affineC_add, htail,
    AccumulatorValuation.affineC_eq_zero_of_no_odd htail, Nat.pow_zero,
    Nat.one_mul, Nat.mul_zero, Nat.add_zero, ← ha]
  exact affineC_le_beatty_of_heavy_proper hf.2

/-- A phase-block charge for every first excursion crossing. -/
theorem Trace.offset_le_phase_charge {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) :
    10000 * offset rs ≤ (2431 * oddCount rs + 1500) * 3 ^ oddCount rs :=
  Nat.le_trans (Nat.mul_le_mul_left _ (h.offset_le_beatty_of_first_crossing hproper hcross))
    (BeattyPhaseBound.beatty_charge _)

private def floorValue : Nat := 2 ^ 71
private def landingAllowance : Nat := 4504940378
private def sourceCap : Nat := 3178644722122268046850

private theorem phase_landing_comparison :
    (10000 * floorValue + (2431 * 72057431991 + 1500)) * (3 : Nat) ^ 72057431991 <
      10000 * (floorValue + landingAllowance) * 2 ^ 114208327604 :=
  strict_upper_comparison 3 72057431991 192 _ _ 114208327604 (by decide +kernel)

private theorem phase_source_comparison :
    (10000 * sourceCap + (2431 * 72057431991 + 1500)) * (3 : Nat) ^ 72057431991 <
      10000 * sourceCap * 2 ^ 114208327604 :=
  strict_upper_comparison 3 72057431991 192 _ _ 114208327604 (by decide +kernel)

set_option maxRecDepth 4096 in
/-- The phase-block charge reduces the exceptional forward increase. -/
theorem Trace.landing_lt_source_add_of_phase_charge {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hlarge : 2 ^ 71 ≤ n)
    (ha : oddCount rs = 72057431991) (hb : time rs = 114208327604) :
    e < n + 4504940378 := by
  apply landing_lt_add_of_scaled_affine (N := floorValue) (M := landingAllowance)
    (Nat.le_of_lt hcross) hlarge
    (h.scaled_affine_upper (h.offset_le_phase_charge hproper hcross))
  simpa only [ha, hb] using phase_landing_comparison

/-- Source and landing fit below the cap from the phase-block charge. -/
theorem Trace.landing_lt_cap_of_phase_charge {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hkeep : n ≤ e)
    (ha : oddCount rs = 72057431991) (hb : time rs = 114208327604) :
    e < 3178644722122268046850 := by
  have hnorm := h.scaled_affine_upper (h.offset_le_phase_charge hproper hcross)
  have hnorm' : 10000 * (2 ^ time rs * e) ≤
      (10000 * e + (2431 * oddCount rs + 1500)) * 3 ^ oddCount rs :=
    Nat.le_trans hnorm (Nat.mul_le_mul_right _
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hkeep) _))
  apply Nat.lt_of_not_ge
  intro hcap
  have hcomp : (10000 * sourceCap + (2431 * oddCount rs + 1500)) * 3 ^ oddCount rs <
      10000 * (sourceCap + 0) * 2 ^ time rs := by
    simpa only [ha, hb, Nat.add_zero] using phase_source_comparison
  have hbad := landing_lt_add_of_scaled_affine (Nat.le_of_lt hcross) hcap hnorm' hcomp
  omega

private theorem inverse_upper : (3 : Nat) ^ 137528045312 < 2 ^ 217976794617 := by
  simpa only [Nat.one_mul] using
    strict_upper_comparison 3 137528045312 192 1 1 217976794617 (by decide +kernel)

private theorem phase_inverse_lower :
    (floorValue + landingAllowance) * (2 : Nat) ^ 757698850864 ≤
      floorValue * 3 ^ 478054749257 :=
  Nat.le_of_lt (scaled_lower_comparison 3 478054749257 192 _ _ 757698850864 (by decide +kernel))

set_option maxRecDepth 4096 in
/-- A longer inverse horizon follows from the smaller allowance. -/
theorem inverse_gap_at_phase_boundary {a b : Nat} (ha : 0 < a) (hbound : a < 615582794569)
    (hcross : 2 ^ b < 3 ^ a) : (2 ^ 71 + 4504940378) * 2 ^ b ≤ 2 ^ 71 * 3 ^ a := by
  change (floorValue + landingAllowance) * 2 ^ b ≤ floorValue * 3 ^ a
  have hdet : 478054749257 * 217976794617 = 137528045312 * 757698850864 + 1 := by decide +kernel
  have hside : b * 478054749257 ≤ 757698850864 * a :=
    inverse_exponent_cross_le_of_bracket ha (by decide : 0 < 137528045312)
      hcross hbound hdet inverse_upper
  exact inverse_scaled_gap_of_cross_le (p := 757698850864) (q := 478054749257)
    (r := 217976794617) (s := 137528045312) (K := floorValue)
    (L := floorValue + landingAllowance) ha hside hdet (Nat.le_of_lt inverse_upper)
    (by decide : 0 < floorValue) (by decide : floorValue ≤ floorValue + landingAllowance)
    phase_inverse_lower

/-- The refined no-inverse-contraction conclusion at a least counterexample. -/
theorem Trace.no_inverse_contraction_of_phase_boundary {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 137528045312)
    (hlarge : 2 ^ 71 ≤ n) (hmin : Minimal.MinimalCounterexample n)
    {w : List Nat} (hw : InverseCover.Valid e w) (hdepth : w.length < 615582794569) :
    3 ^ w.length ≤ 2 ^ w.sum := by
  apply Nat.le_of_not_gt
  intro hcontract
  have hkeep : n ≤ e := Nat.le_of_not_gt fun he =>
    Minimal.not_accOrbit_lt_of_minimal hmin (time rs) (h.landing.symm ▸ he)
  obtain ⟨ha, hb⟩ := h.first_crossing_failure_boundary_pair hproper hcross hbound hlarge hkeep
  have hnear := h.landing_lt_source_add_of_phase_charge hproper hcross hlarge ha hb
  have hpos : 0 < w.length := by
    cases w with
    | nil => simp at hcontract
    | cons => simp
  exact no_inverse_word_of_near_minimal_landing hmin h.landing (Nat.two_pow_pos 71)
    hlarge hnear (inverse_gap_at_phase_boundary hpos hdepth hcontract) hw

end Collatz.ExcursionBudget
