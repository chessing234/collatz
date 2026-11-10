import Collatz.Strategy.ExcursionBudget

/-!
# A sharper offset bound at first excursion crossings

A nonterminal unit odd run has slope at most three quarters.
If its landing coefficient is still heavy, its entrance weight
is therefore at most three quarters. Longer odd runs already
cost at most five eighteenth per odd step. Only a terminal unit
run can need one extra eighteenth.
-/

namespace Collatz.ExcursionBudget

private theorem charge_nonunit {v : Nat} (hv : v ≠ 1) :
    18 * (3 ^ v - 2 ^ v) ≤ (5 * v) * 3 ^ v := by
  by_cases h : 4 ≤ v
  · exact Nat.le_trans (Nat.mul_le_mul_left 18 (Nat.sub_le ..))
      (Nat.mul_le_mul_right _ (by omega))
  · have hv' : v = 0 ∨ v = 2 ∨ v = 3 := by omega
    rcases hv' with rfl | rfl | rfl <;> decide

private theorem last_charge {v A B extra : Nat} (hprev : B ≤ A)
    (hunit : v = 1 → extra = 1 ∨ 4 * B ≤ 3 * A) :
    18 * (B * (3 ^ v - 2 ^ v)) ≤ (5 * v + extra) * (3 ^ v * A) := by
  by_cases hv : v = 1
  · rcases hunit hv with he | hsmall
    · subst v
      subst extra
      change 18 * (B * 1) ≤ 6 * (3 * A)
      rw [Nat.mul_one, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hprev
    · subst v
      change 18 * (B * 1) ≤ (5 + extra) * (3 * A)
      have hbase : 18 * (B * 1) ≤ 5 * (3 * A) := by omega
      exact Nat.le_trans hbase (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · calc
      _ = B * (18 * (3 ^ v - 2 ^ v)) := Nat.mul_left_comm ..
      _ ≤ A * ((5 * v) * 3 ^ v) := Nat.mul_le_mul hprev (charge_nonunit hv)
      _ = (5 * v) * (3 ^ v * A) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

private theorem extend_charge (r : Run) (rs : List Run) {extra : Nat}
    (hprev : 18 * offset rs ≤ (5 * oddCount rs) * 3 ^ oddCount rs)
    (hlast : 18 * (2 ^ time rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps)) ≤
      (5 * r.oddSteps + extra) * (3 ^ r.oddSteps * 3 ^ oddCount rs)) :
    18 * offset (r :: rs) ≤ (5 * oddCount (r :: rs) + extra) * 3 ^ oddCount (r :: rs) := by
  calc
    _ = 3 ^ r.oddSteps * (18 * offset rs) +
        18 * (2 ^ time rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps)) := by
      rw [offset, Nat.mul_add, Nat.mul_left_comm 18]
    _ ≤ 3 ^ r.oddSteps * ((5 * oddCount rs) * 3 ^ oddCount rs) +
        (5 * r.oddSteps + extra) * (3 ^ r.oddSteps * 3 ^ oddCount rs) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hprev) hlast
    _ = _ := by
      simp only [oddCount, Nat.pow_add, Nat.mul_add, Nat.add_mul]
      ac_rfl

/-- A trace heavy at every boundary pays at most five eighteenth
of its tripling coefficient per odd step in affine offset. -/
theorem Trace.offset_le_five_odd_of_heavy {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hfull : 2 ^ time rs ≤ 3 ^ oddCount rs) :
    18 * offset rs ≤ (5 * oddCount rs) * 3 ^ oddCount rs := by
  induction h with
  | nil => decide
  | @step x y v u W rs _ hrun ih =>
    have hprev : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have hunit (hv : v = 1) : 4 * 2 ^ time rs ≤ 3 * 3 ^ oddCount rs := by
      have hpow : 4 ≤ 2 ^ (v + W) := by
        change 2 ^ 2 ≤ 2 ^ (v + W)
        have hw := hrun.one_le_W
        exact Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.le_trans (Nat.mul_le_mul_right _ hpow) (by
        simpa only [time, oddCount, Nat.pow_add, hv, Nat.pow_one] using hfull)
    have hlast := last_charge (v := v) (extra := 0) hprev (fun hv => Or.inr (hunit hv))
    simpa only [Nat.add_zero] using
      extend_charge ⟨v, W⟩ rs (ih hproper.2 hprev) hlast

/-- At a first crossing, only the last excursion can need an extra
eighteenth of the tripling coefficient. -/
theorem Trace.offset_le_five_odd_add_one {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs) :
    18 * offset rs ≤ (5 * oddCount rs + 1) * 3 ^ oddCount rs := by
  cases h with
  | nil => decide
  | @step x y v u W rs hpre _ =>
    have hprev : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have hlast := last_charge (v := v) (extra := 1) hprev (fun _ => Or.inl rfl)
    exact extend_charge ⟨v, W⟩ rs (hpre.offset_le_five_odd_of_heavy hproper.2 hprev) hlast

private def boundaryCredit (A B : Nat) : Nat :=
  if 9 * A < 10 * B then 5 else 0

private theorem credit_le (A B : Nat) : boundaryCredit A B ≤ 5 := by
  unfold boundaryCredit
  split <;> decide

private theorem charge_three_or_more {v : Nat} (hv : 3 ≤ v) :
    300 * (3 ^ v - 2 ^ v) + 5 * 3 ^ v ≤ (81 * v) * 3 ^ v := by
  by_cases he : v = 3
  · subst v
    decide
  · calc
      _ ≤ 300 * 3 ^ v + 5 * 3 ^ v :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le ..)) _
      _ ≤ _ := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right _ (by omega)

private theorem terminal_charge (v : Nat) :
    300 * (3 ^ v - 2 ^ v) ≤ (81 * v + 19) * 3 ^ v := by
  by_cases hv : 3 ≤ v
  · exact Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (charge_three_or_more hv)
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · have he : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases he with rfl | rfl | rfl <;> decide

private theorem pay_credit {v W A B : Nat} (hv : 0 < v) (hW : 1 ≤ W) (hprev : B ≤ A)
    (hfull : 2 ^ (v + W) * B ≤ 3 ^ v * A) :
    300 * (B * (3 ^ v - 2 ^ v)) + boundaryCredit (3 ^ v * A) (2 ^ (v + W) * B) * (3 ^ v * A) ≤
      (81 * v + boundaryCredit A B) * (3 ^ v * A) := by
  have pay (h : 300 * (B * (3 ^ v - 2 ^ v)) + 5 * (3 ^ v * A) ≤ (81 * v) * (3 ^ v * A)) :=
    Nat.le_trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (credit_le (3 ^ v * A) (2 ^ (v + W) * B))) _)
      (Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.le_add_right (81 * v) (boundaryCredit A B))))
  by_cases h1 : v = 1
  · subst v
    apply pay
    have hpow : 4 ≤ 2 ^ (1 + W) := by
      change 2 ^ 2 ≤ 2 ^ (1 + W)
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hsmall : 4 * B ≤ 3 * A :=
      Nat.le_trans (Nat.mul_le_mul_right _ hpow) hfull
    change 300 * (B * 1) + 5 * (3 * A) ≤ 81 * (3 * A)
    omega
  by_cases h2 : v = 2
  · subst v
    by_cases hW1 : W = 1
    · subst W
      have hafter : boundaryCredit (9 * A) (8 * B) = 0 := if_neg (by omega)
      change 300 * (B * 5) + boundaryCredit (9 * A) (8 * B) * (9 * A) ≤
        (162 + boundaryCredit A B) * (9 * A)
      rw [hafter, Nat.zero_mul, Nat.add_zero]
      by_cases hhigh : 9 * A < 10 * B
      · rw [boundaryCredit, if_pos hhigh]
        omega
      · rw [boundaryCredit, if_neg hhigh]
        omega
    · apply pay
      have hpow : 16 ≤ 2 ^ (2 + W) := by
        change 2 ^ 4 ≤ 2 ^ (2 + W)
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have hsmall : 16 * B ≤ 9 * A :=
        Nat.le_trans (Nat.mul_le_mul_right _ hpow) hfull
      change 300 * (B * 5) + 5 * (9 * A) ≤ 162 * (9 * A)
      omega
  · apply pay
    calc
      _ = B * (300 * (3 ^ v - 2 ^ v)) + A * (5 * 3 ^ v) := by ac_rfl
      _ ≤ A * (300 * (3 ^ v - 2 ^ v)) + A * (5 * 3 ^ v) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hprev) _
      _ = A * (300 * (3 ^ v - 2 ^ v) + 5 * 3 ^ v) := (Nat.mul_add ..).symm
      _ ≤ A * ((81 * v) * 3 ^ v) := Nat.mul_le_mul_left _ (charge_three_or_more (by omega))
      _ = _ := by ac_rfl

private theorem append_credit (r : Run) (rs : List Run) {p q extra : Nat}
    (hprev : 300 * offset rs + p * 3 ^ oddCount rs ≤ (81 * oddCount rs + 5) * 3 ^ oddCount rs)
    (hlast : 300 * (2 ^ time rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps)) +
        q * (3 ^ r.oddSteps * 3 ^ oddCount rs) ≤
      (81 * r.oddSteps + p + extra) * (3 ^ r.oddSteps * 3 ^ oddCount rs)) :
    300 * offset (r :: rs) + q * 3 ^ oddCount (r :: rs) ≤
      (81 * oddCount (r :: rs) + 5 + extra) * 3 ^ oddCount (r :: rs) := by
  let A := 3 ^ r.oddSteps * 3 ^ oddCount rs
  have hscaled : 300 * (3 ^ r.oddSteps * offset rs) + p * A ≤ (81 * oddCount rs + 5) * A := by
    calc
      _ = 3 ^ r.oddSteps * (300 * offset rs + p * 3 ^ oddCount rs) := by
        dsimp only [A]
        rw [Nat.mul_add]
        ac_rfl
      _ ≤ 3 ^ r.oddSteps * ((81 * oddCount rs + 5) * 3 ^ oddCount rs) :=
        Nat.mul_le_mul_left _ hprev
      _ = _ := by dsimp only [A]; ac_rfl
  apply Nat.le_of_add_le_add_right (b := p * A)
  calc
    _ = (300 * (3 ^ r.oddSteps * offset rs) + p * A) +
        (300 * (2 ^ time rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps)) + q * A) := by
      simp only [offset, oddCount, Nat.pow_add, Nat.mul_add, A]
      ac_rfl
    _ ≤ (81 * oddCount rs + 5) * A + (81 * r.oddSteps + p + extra) * A :=
      Nat.add_le_add hscaled hlast
    _ = _ := by
      simp only [oddCount, Nat.pow_add, Nat.mul_add, Nat.add_mul, A]
      ac_rfl

private theorem Trace.heavy_credit_bound {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hfull : 2 ^ time rs ≤ 3 ^ oddCount rs) :
    300 * offset rs + boundaryCredit (3 ^ oddCount rs) (2 ^ time rs) * 3 ^ oddCount rs ≤
      (81 * oddCount rs + 5) * 3 ^ oddCount rs := by
  induction h with
  | nil => decide
  | @step x y v u W rs _ hrun ih =>
    have hprev : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have hnext : 2 ^ (v + W) * 2 ^ time rs ≤ 3 ^ v * 3 ^ oddCount rs := by
      simpa only [time, oddCount, Nat.pow_add] using hfull
    have hpaid := pay_credit hrun.2.2.2.1 hrun.one_le_W hprev hnext
    have happend := append_credit ⟨v, W⟩ rs (extra := 0)
      (q := boundaryCredit (3 ^ v * 3 ^ oddCount rs) (2 ^ (v + W) * 2 ^ time rs))
      (ih hproper.2 hprev) (by simpa only [Nat.add_zero] using hpaid)
    simpa only [Nat.add_zero, oddCount, time, Nat.pow_add] using happend

/-- The high-weight boundary credit reduces the asymptotic offset
charge to 27 hundredths per odd step. The terminal run has a
fixed extra allowance. -/
theorem Trace.offset_le_credited_odd {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs) :
    300 * offset rs ≤ (81 * oddCount rs + 24) * 3 ^ oddCount rs := by
  cases h with
  | nil => decide
  | @step x y v u W rs hpre _ =>
    have hprev : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    let A := 3 ^ v * 3 ^ oddCount rs
    let p := boundaryCredit (3 ^ oddCount rs) (2 ^ time rs)
    have hlast : 300 * (2 ^ time rs * (3 ^ v - 2 ^ v)) + 0 * A ≤ (81 * v + p + 19) * A := by
      rw [Nat.zero_mul, Nat.add_zero]
      calc
        _ = 2 ^ time rs * (300 * (3 ^ v - 2 ^ v)) := Nat.mul_left_comm ..
        _ ≤ 3 ^ oddCount rs * ((81 * v + 19) * 3 ^ v) :=
          Nat.mul_le_mul hprev (terminal_charge v)
        _ = (81 * v + 19) * A := by dsimp only [A]; ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    simpa only [Nat.zero_mul, Nat.add_zero, Nat.add_assoc] using
      append_credit ⟨v, W⟩ rs (extra := 19) (hpre.heavy_credit_bound hproper.2 hprev) hlast

end Collatz.ExcursionBudget
