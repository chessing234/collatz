import Collatz.Strategy.FirstLightBlockTransfer
import Collatz.Strategy.RealizableBound

/-!
# A Beatty ceiling at the first coefficient crossing

The heavy proper prefixes alone place each odd step no later than
the corresponding Beatty position. The resulting accumulator bound
transfers existing power-gap certificates to first-crossing descent.
-/

namespace Collatz.FirstLightDescent

open AffineExact RealizableBound FirstLightConsequences

/-- A heavy proper prefix controls the time of each odd step,
including the last one contributing to the accumulator. -/
theorem affineC_le_beatty_of_heavy_proper {n k : Nat}
    (hproper : ∀ i, i < k → 2 ^ i ≤ 3 ^ oddCount n i) :
    affineC k n ≤ Bcap (oddCount n k) := by
  induction k with
  | zero => simp [affineC, oddCount]
  | succ k ih =>
    have hcap := ih (fun i hi => hproper i (by omega))
    have hlast := Density.oddCount_succ_last n k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · have hcount : oddCount n (k + 1) = oddCount n k := by omega
      rw [hcount, affineC_even he]
      exact hcap
    · have hcount : oddCount n (k + 1) = oddCount n k + 1 := by omega
      have htime := le_fexp_of_pow_le (hproper k (by omega))
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) htime
      rw [hcount, affineC_odd ho, Bcap_succ]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hcap) hpow

/-- A Beatty power-gap certificate gives an absolute source bound for
every failure to descend at the first coefficient crossing. -/
theorem first_light_failure_source_lt_of_beatty {n k c : Nat}
    (hf : FirstLight n k) (hfail : n ≤ acceleratedOrbit k n)
    (hgap : Bcap (oddCount n k) + 3 ^ oddCount n k * c <
      2 * 2 ^ fexp (oddCount n k) * c) : n < c := by
  let a := oddCount n k
  let A := 3 ^ a
  let B := 2 * 2 ^ fexp a
  let D := B - A
  have hAB : A ≤ B := by
    simpa only [A, B, Arith.two_pow_succ] using (Nat.le_of_lt (lt_fexp a))
  have hsum : A + D = B := Nat.add_sub_of_le hAB
  have hfloor : fexp a < k := Nat.lt_of_not_ge fun h =>
    Nat.not_lt_of_ge (Nat.le_trans (Arith.two_pow_le_two_pow h) (fexp_le a)) hf.1
  have hpow : B ≤ 2 ^ k := by
    simpa only [B, Arith.two_pow_succ] using
      (Arith.two_pow_le_two_pow (Nat.succ_le_of_lt hfloor))
  have hcap : affineC k n ≤ Bcap a := affineC_le_beatty_of_heavy_proper hf.2
  have hbound : B * n ≤ A * n + Bcap a := by
    calc
      _ ≤ 2 ^ k * n := Nat.mul_le_mul_right _ hpow
      _ ≤ 2 ^ k * acceleratedOrbit k n := Nat.mul_le_mul_left _ hfail
      _ = A * n + affineC k n := affine_exact n k
      _ ≤ _ := Nat.add_le_add_left hcap _
  change Bcap a + A * c < B * c at hgap
  rw [← hsum, Nat.add_mul] at hgap hbound
  apply Nat.lt_of_not_ge
  intro hge
  have hmono := Nat.mul_le_mul_left D hge
  omega

/-- A Beatty gap and bounded finite descent certify the first crossing
at every source, with the odd count serving as the arithmetic index. -/
theorem first_light_drop_of_beatty_certificate {A c H n k : Nat}
    (hexact : ExactThrough H)
    (hgap : ∀ a, a < A → Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c)
    (hsmall : ∀ x, 1 < x → x < c → ∃ j, j ≤ H ∧ acceleratedOrbit j x < x)
    (hn : 1 < n) (hf : FirstLight n k) (ha : oddCount n k < A) :
    acceleratedOrbit k n < n := by
  apply Nat.lt_of_not_ge
  intro hfail
  have hsource := first_light_failure_source_lt_of_beatty hf hfail (hgap _ ha)
  obtain ⟨j, hj, hdrop⟩ := hsmall n hn hsource
  exact Nat.not_le_of_gt (first_light_drop_of_bounded_drop hexact hn hj hdrop hf) hfail

end Collatz.FirstLightDescent
