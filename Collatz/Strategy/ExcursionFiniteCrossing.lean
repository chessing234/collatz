import Collatz.Strategy.DyadicPowerBounds
import Collatz.Strategy.ExcursionCoefficientCoverage

/-!
# Finite reduction for first excursion crossings

A determinant-one bracket bounds the source of any failed first
crossing with fewer than 6,586,818,670 odd steps. The comparisons
use kernel-checked dyadic intervals with 128-bit rounding.
The published finite stopping-time result is stated separately
as a hypothesis of the final descent theorem.
-/

namespace Collatz.ExcursionPowerGap

open Collatz.DyadicPowerBounds

private theorem wide_lower : (2 : Nat) ^ 9809721694 < 3 ^ 6189245291 :=
  lower_comparison 3 6189245291 128 9809721694 (by decide +kernel)

private theorem wide_upper_scaled :
    (9448000000 + 1) * (3 : Nat) ^ 397573379 ≤ 9448000000 * 2 ^ 630138897 :=
  upper_comparison 3 397573379 128 (9448000000 + 1) 9448000000 630138897
    (by decide +kernel)

/-- A single kernel-checked bracket controls the relative gap throughout
the stated odd-exponent range. -/
theorem wide_odd_weight_le_gap {a b : Nat} (ha : 0 < a) (hbound : a < 6586818670)
    (hcross : 3 ^ a < 2 ^ b) :
    a * 3 ^ a ≤ (397573379 * (9448000000 + a)) * (2 ^ b - 3 ^ a) := by
  exact odd_weight_le_gap_of_bracket (p := 9809721694) (q := 6189245291)
    (r := 630138897) (s := 397573379) (K := 9448000000)
    ha hcross hbound (by decide) wide_lower (by decide) wide_upper_scaled

end Collatz.ExcursionPowerGap

namespace Collatz.ExcursionBudget

open Collatz.ExcursionPowerGap Collatz.FirstLightDescent

private theorem weight_ones (rs : List Run) : weight (fun _ => 1) rs = rs.length := by
  induction rs with
  | nil => rfl
  | cons run rs ih => simp only [weight, List.length_cons, ih, Nat.add_comm]

/-- Every failed first excursion crossing with fewer than
6,586,818,670 odd steps starts below 6.4 quintillion. -/
theorem Trace.first_crossing_failure_source_lt {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 6586818670)
    (hkeep : n ≤ e) : n < 6400000000000000000 := by
  let a := oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let D := B - A
  have hD : 0 < D := Nat.sub_pos_iff_lt.mpr hcross
  have hsum : A + D = B := Nat.add_sub_of_le (Nat.le_of_lt hcross)
  have hbudget : D * n ≤ offset rs := by
    apply Nat.le_of_add_le_add_left (a := A * n)
    rw [← Nat.add_mul, hsum, h.affine]
    exact Nat.mul_le_mul_left _ hkeep
  have hoffset : offset rs ≤ A * rs.length := by
    have hcharge (v : Nat) : 1 * (3 ^ v - 2 ^ v) ≤ 1 * 3 ^ v := by
      exact Nat.mul_le_mul_left _ (Nat.sub_le ..)
    simpa only [Nat.one_mul, weight_ones] using
      offset_le_weight (charge := fun _ => 1) hcharge hproper
  have hgap : a * A ≤ (397573379 * (9448000000 + a)) * D :=
    wide_odd_weight_le_gap (h.odd_count_pos_of_crossing hcross) hbound hcross
  have hsize : n ≤ 397573379 * (9448000000 + a) := by
    apply Nat.le_of_mul_le_mul_right _ hD
    rw [Nat.mul_comm n D]
    exact Nat.le_trans hbudget (Nat.le_trans hoffset
      (Nat.le_trans (Nat.mul_le_mul_left A h.length_le_oddCount)
        (by rwa [Nat.mul_comm A])))
  change a < 6586818670 at hbound
  omega

/-- The finite coefficient-stopping-time equality of Rozier and
Terracol, Corollary 5.4, in first-light form. -/
def PublishedFiniteFirstLight : Prop :=
  ∀ {n k : Nat}, 1 < n → n ≤ 28000000000000000000 → FirstLight n k →
    acceleratedOrbit k n < n

/-- The published finite range covers every potential failure within
the wide odd-exponent bracket. -/
theorem Trace.first_crossing_drop_of_published_range (verified : PublishedFiniteFirstLight)
    {n e : Nat} {rs : List Run} (h : Trace n e rs) (hn : 1 < n)
    (hproper : ProperPrefixBound 1 1 rs) (hcross : 3 ^ oddCount rs < 2 ^ time rs)
    (hbound : oddCount rs < 6586818670) : e < n := by
  apply Nat.lt_of_not_ge
  intro hkeep
  have hsmall := h.first_crossing_failure_source_lt hproper hcross hbound hkeep
  obtain ⟨k, _, hfirst, _, hland⟩ := h.first_light_of_first_crossing hproper hcross
  have hdrop := verified hn (by omega) hfirst
  exact Nat.not_le_of_gt hdrop (Nat.le_trans hkeep hland)

end Collatz.ExcursionBudget
