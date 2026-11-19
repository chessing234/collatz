import Collatz.Core.Minimum
import Collatz.Structure.Density
import Collatz.Strategy.PowerSeparation

/-! A polynomial start-size criterion for coefficient crossings at arbitrary
depth. The mathematical derivation of `PowerSeparation` from Rhin's
published separation estimate is in `RESEARCH.md`. -/

namespace Collatz

namespace FirstLightPowerGap

open Collatz.Arith

/-- Direct orbit form of the first-crossing accumulator bound. An odd step
adds `2^i`, which the proper-prefix hypothesis bounds by `3^oddCount n i`. -/
private theorem prefix_upper (n k : Nat) (h : ∀ i, i < k → 2 ^ i ≤ 3 ^ oddCount n i) :
    3 * (2 ^ k * acceleratedOrbit k n) ≤ 3 ^ oddCount n k * (3 * n + oddCount n k) := by
  induction k with
  | zero => simp [oddCount, parityVector]
  | succ k ih =>
    have hprev := ih (fun i hi => h i (by omega))
    have hcount := Density.oddCount_succ_last n k
    have hscale : 2 ^ (k + 1) * acceleratedOrbit (k + 1) n =
        2 ^ k * (2 * acceleratedStep (acceleratedOrbit k n)) := by
      rw [two_pow_succ, acceleratedOrbit_succ_step]
      ac_rfl
    rw [hscale, hcount]
    rcases mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · have hstep : 2 * acceleratedStep (acceleratedOrbit k n) = acceleratedOrbit k n := by
        rw [acceleratedStep, if_pos he]
        omega
      simpa only [hstep, he, Nat.add_zero] using hprev
    · have hstep : 2 * acceleratedStep (acceleratedOrbit k n) = 3 * acceleratedOrbit k n + 1 := by
        rw [acceleratedStep, if_neg (by omega)]
        omega
      rw [hstep, ho, three_pow_succ]
      calc
        _ = 3 * (3 * (2 ^ k * acceleratedOrbit k n)) + 3 * 2 ^ k := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        _ ≤ 3 * (3 ^ oddCount n k * (3 * n + oddCount n k)) + 3 * 3 ^ oddCount n k :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hprev)
            (Nat.mul_le_mul_left _ (h k (Nat.lt_succ_self k)))
        _ = _ := by simp only [Nat.add_assoc, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

/-- A positive start that survives its first coefficient crossing must fit
below a polynomial in the crossing time and odd-step count. -/
theorem start_bound_of_failure (hgap : PowerSeparation) {n k : Nat}
    (hn : 0 < n) (hc : 3 ^ oddCount n k < 2 ^ k)
    (hprior : ∀ i, i < k → 2 ^ i ≤ 3 ^ oddCount n i) (hf : n ≤ acceleratedOrbit k n) :
    3 * n < 2 * k ^ 14 * oddCount n k := by
  let a := oddCount n k
  let gap := 2 ^ k - 3 ^ a
  have hpos : 0 < gap := Nat.sub_pos_of_lt hc
  have hfail : 3 * gap * n ≤ a * 3 ^ a := by
    have h := Nat.le_trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (2 ^ k) hf))
      (prefix_upper n k hprior)
    have hsplit : 3 ^ a + gap = 2 ^ k := Nat.add_sub_of_le (Nat.le_of_lt hc)
    change 3 * (2 ^ k * n) ≤ 3 ^ a * (3 * n + a) at h
    rw [← hsplit, Nat.add_mul, Nat.mul_add, Nat.mul_add] at h
    rw [Nat.mul_left_comm 3 (3 ^ a) n] at h
    have hdebt := Nat.le_of_add_le_add_left h
    simpa only [Nat.mul_assoc, Nat.mul_comm a (3 ^ a)] using hdebt
  have ha : 0 < a := by
    by_cases heq : a = 0
    · rw [heq, Nat.zero_mul] at hfail
      have := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 3) hpos) hn
      omega
    · omega
  have hsep : 2 ^ k ≤ 2 * k ^ 14 * gap := hgap a k hc
  apply Nat.lt_of_mul_lt_mul_left (a := gap)
  calc
    gap * (3 * n) = 3 * gap * n := by ac_rfl
    _ ≤ a * 3 ^ a := hfail
    _ < a * 2 ^ k := Nat.mul_lt_mul_of_pos_left hc ha
    _ ≤ a * (2 * k ^ 14 * gap) := Nat.mul_le_mul_left _ hsep
    _ = gap * (2 * k ^ 14 * a) := by ac_rfl

/-- The first coefficient crossing and first actual descent agree within
the polynomial budget. The supplied crossing can be any crossing by `t`. -/
theorem first_stopping_times_agree (hgap : PowerSeparation) {n t : Nat}
    (hn : 0 < n) (hc : 3 ^ oddCount n t < 2 ^ t) (hsize : 2 * t ^ 15 ≤ 3 * n) :
    ∃ k, k ≤ t ∧ 3 ^ oddCount n k < 2 ^ k ∧ acceleratedOrbit k n < n ∧
      ∀ i, i < k → 2 ^ i ≤ 3 ^ oddCount n i ∧ n ≤ acceleratedOrbit i n := by
  obtain ⟨k, hk, hmin⟩ := Minimum.exists_min (P := fun k => 3 ^ oddCount n k < 2 ^ k) ⟨t, hc⟩
  have hkt : k ≤ t := by
    apply Nat.le_of_not_gt
    exact fun ht => hmin t ht hc
  have hprior : ∀ i, i < k → 2 ^ i ≤ 3 ^ oddCount n i :=
    fun i hi => Nat.le_of_not_gt (hmin i hi)
  have hd : acceleratedOrbit k n < n := by
    apply Nat.lt_of_not_ge
    intro hno
    have hfail := start_bound_of_failure hgap hn hk hprior hno
    have hcount : oddCount n k ≤ k := by
      simpa [oddCount, parityVector] using
        (List.count_le_length (a := 1) (l := parityVector n k))
    have hbound : 2 * k ^ 14 * oddCount n k ≤ 2 * t ^ 15 := calc
      _ ≤ (2 * t ^ 14) * t :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkt _))
          (Nat.le_trans hcount hkt)
      _ = 2 * (t ^ 14 * t) := Nat.mul_assoc ..
      _ = _ := congrArg (2 * ·) (Nat.pow_succ t 14).symm
    omega
  refine ⟨k, hkt, hk, hd, fun i hi => ⟨hprior i hi, ?_⟩⟩
  obtain ⟨b, hb⟩ := acceleratedOrbit_affine n i
  have hmul := Nat.mul_le_mul_right n (hprior i hi)
  exact Nat.le_of_mul_le_mul_left (by omega) (two_pow_pos i)

/-- A never-dropping orbit stays on the noncontracting side at all depths
within its polynomial budget. -/
theorem heavy_prefix_of_neverDrops (hgap : PowerSeparation) {n t : Nat}
    (hn : 0 < n) (h : ∀ k, n ≤ acceleratedOrbit k n) (hsize : 2 * t ^ 15 ≤ 3 * n) :
    2 ^ t ≤ 3 ^ oddCount n t := by
  apply Nat.le_of_not_gt
  intro hc
  obtain ⟨k, _, _, hd, _⟩ := first_stopping_times_agree hgap hn hc hsize
  exact Nat.not_lt_of_ge (h k) hd

end FirstLightPowerGap
end Collatz
