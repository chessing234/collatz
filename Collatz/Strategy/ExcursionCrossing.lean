import Collatz.Strategy.ExcursionMap

/-!
# Weighted first coefficient crossings for excursion chains

Use the shifted coordinate `x = n + 1`. An excursion with run length `v`
and extra halvings `W` updates the affine identity `B x = A (n + 1) + C`.
The new coefficients are `A' = A 3^v`, `B' = B 2^(v+W)), and
`C' = 3^v C + B 2^v (2^W - 1)`.

The new contribution to `2 C'` is at most `B'` when `W = 1` and at most
`2 B'` otherwise. Charging this cost at each completed excursion gives
a bound through the first crossing of any rational coefficient ratio.
-/

namespace Collatz.ExcursionCrossing

open Collatz.ExcursionMap

/-- Twice the upper bound for an excursion's correction relative to its new
denominator. A single extra halving has exactly half the full charge. -/
def charge (W : Nat) : Nat :=
  if W = 1 then 1 else 2

private def offset (B v W : Nat) : Nat :=
  B * 2 ^ v * (2 ^ W - 1)

private theorem offset_bound (B v W : Nat) :
    2 * offset B v W ≤ charge W * (B * 2 ^ (v + W)) := by
  have h : 2 * (2 ^ W - 1) ≤ charge W * 2 ^ W := by
    by_cases hW : W = 1
    · subst W
      decide
    · simpa only [charge, if_neg hW] using
        Nat.mul_le_mul_left 2 (Nat.sub_le (2 ^ W) 1)
  calc
    _ = (B * 2 ^ v) * (2 * (2 ^ W - 1)) := by unfold offset; ac_rfl
    _ ≤ (B * 2 ^ v) * (charge W * 2 ^ W) := Nat.mul_le_mul_left _ h
    _ = _ := by rw [Nat.pow_add]; ac_rfl

private theorem excursion_affine {x v u W y : Nat} (h : IsExcursion x v u W y) :
    2 ^ (v + W) * (y + 1) = 3 ^ v * (x + 1) + offset 1 v W := by
  have hlocal : 2 ^ W * (y + 1) = 3 ^ v * u + (2 ^ W - 1) := by
    rw [Nat.mul_add, Nat.mul_one, h.2.2.2.2.2.2]
    have := Nat.two_pow_pos W
    omega
  rw [offset, Nat.one_mul, h.2.2.2.2.2.1, Nat.pow_add, Nat.mul_assoc, hlocal, Nat.mul_add]
  congr 1
  ac_rfl

/-- An excursion prefix in which every completed coefficient ratio `B/A`
is at most `p/q`. The final index is the sum of the excursion charges. -/
inductive CappedTrace (p q n : Nat) : Nat → Nat → Nat → Nat → Nat → Prop where
  | start : CappedTrace p q n n 1 1 0 0
  | step {x A B C cost v u W y : Nat} :
      CappedTrace p q n x A B C cost →
      IsExcursion x v u W y →
      q * (B * 2 ^ (v + W)) ≤ p * (A * 3 ^ v) →
      CappedTrace p q n y (A * 3 ^ v) (B * 2 ^ (v + W))
        (C * 3 ^ v + offset B v W) (cost + charge W)

private theorem extend_affine {n x A B C v u W y : Nat}
    (h : B * (x + 1) = A * (n + 1) + C) (hstep : IsExcursion x v u W y) :
    (B * 2 ^ (v + W)) * (y + 1) =
      (A * 3 ^ v) * (n + 1) + (C * 3 ^ v + offset B v W) := by
  calc
    _ = B * (2 ^ (v + W) * (y + 1)) := by rw [Nat.mul_assoc]
    _ = 3 ^ v * (B * (x + 1)) + offset B v W := by
      rw [excursion_affine hstep, Nat.mul_add]
      simp only [offset, Nat.one_mul]
      congr 1 <;> ac_rfl
    _ = _ := by
      rw [h, Nat.mul_add, Nat.add_assoc]
      congr 1
      · ac_rfl
      · congr 1
        ac_rfl

/-- Exact shifted-coordinate affine identity for a capped prefix. -/
theorem CappedTrace.affine {p q n x A B C cost : Nat}
    (h : CappedTrace p q n x A B C cost) :
    B * (x + 1) = A * (n + 1) + C := by
  induction h with
  | start => simp
  | step _ hstep _ ih => exact extend_affine ih hstep

/-- The cap bounds twice the accumulated offset by the total charge times
the capped coefficient. -/
theorem CappedTrace.offset_le {p q n x A B C cost : Nat}
    (h : CappedTrace p q n x A B C cost) :
    2 * q * C ≤ p * A * cost := by
  induction h with
  | start => simp
  | @step x A B C cost v u W y _ _ hcap ih =>
    have hprev := Nat.mul_le_mul_right (3 ^ v) ih
    have hweighted : q * (charge W * (B * 2 ^ (v + W))) ≤
        p * (A * 3 ^ v) * charge W := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_right (charge W) hcap
    have hnew := Nat.le_trans (Nat.mul_le_mul_left q (offset_bound B v W)) hweighted
    rw [Nat.mul_add, Nat.mul_add]
    apply Nat.add_le_add
    · simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprev
    · simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnew

/-- A capped prefix followed by a strict crossing of `p/q` drops below its
start when `p·cost ≤ 2·(p-q)·(n+1)`, including the crossing excursion in cost.
The conclusion concerns the endpoint of the crossing, even if an earlier
excursion already went below the start. -/
theorem drop_at_crossing {p q n x A B C cost v u W y : Nat}
    (h : CappedTrace p q n x A B C cost) (hstep : IsExcursion x v u W y)
    (hq : 0 < q)
    (hcross : p * (A * 3 ^ v) < q * (B * 2 ^ (v + W)))
    (hbudget : p * (cost + charge W) + 2 * q * (n + 1) ≤ 2 * p * (n + 1)) :
    y < n := by
  let A' := A * 3 ^ v
  let B' := B * 2 ^ (v + W)
  let C' := C * 3 ^ v + offset B v W
  have hcross' : p * A' < q * B' := hcross
  have hland : B' * (y + 1) = A' * (n + 1) + C' := extend_affine h.affine hstep
  have hprev : 2 * q * (C * 3 ^ v) ≤ q * B' * cost := calc
    _ = (2 * q * C) * 3 ^ v := by ac_rfl
    _ ≤ (p * A * cost) * 3 ^ v := Nat.mul_le_mul_right _ h.offset_le
    _ = p * A' * cost := by dsimp [A']; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_of_lt hcross')
  have hlast : 2 * q * offset B v W ≤ q * B' * charge W := by
    simpa only [B', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left q (offset_bound B v W)
  have hscaled : 2 * q * C' ≤ q * (B' * (cost + charge W)) := by
    dsimp [C']
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
    simpa only [Nat.mul_assoc] using Nat.add_le_add hprev hlast
  have hmass : 2 * C' ≤ B' * (cost + charge W) := by
    apply Nat.le_of_mul_le_mul_left _ hq
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hlinear : 2 * p * (A' * (n + 1)) < 2 * q * B' * (n + 1) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_right hcross' (Nat.succ_pos n)) (by decide : 0 < 2)
  have hdrop : 2 * p * (B' * (y + 1)) < 2 * p * (B' * (n + 1)) := calc
    _ = 2 * p * (A' * (n + 1)) + p * (2 * C') := by
      rw [hland, Nat.mul_add]
      ac_rfl
    _ < 2 * q * B' * (n + 1) + p * (B' * (cost + charge W)) :=
      Nat.add_lt_add_of_lt_of_le hlinear (Nat.mul_le_mul_left p hmass)
    _ = B' * (p * (cost + charge W) + 2 * q * (n + 1)) := by
      rw [Nat.mul_add B' (p * (cost + charge W)) (2 * q * (n + 1))]
      ac_rfl
    _ ≤ B' * (2 * p * (n + 1)) := Nat.mul_le_mul_left _ hbudget
    _ = _ := by ac_rfl
  have hinner := Nat.lt_of_mul_lt_mul_left hdrop
  have hsucc := Nat.lt_of_mul_lt_mul_left hinner
  omega

/-- At the first strict factor-two crossing it suffices that the total
charge is at most `n+1`. In particular any crossing within `k` excursions
with `2k ≤ n+1` meets the bound, and every `W = 1` saves one unit. -/
theorem drop_at_doubling {n x A B C cost v u W y : Nat}
    (h : CappedTrace 2 1 n x A B C cost) (hstep : IsExcursion x v u W y)
    (hcross : 2 * (A * 3 ^ v) < B * 2 ^ (v + W))
    (hbudget : cost + charge W ≤ n + 1) :
    y < n :=
  drop_at_crossing h hstep (by decide) (by simpa using hcross) (by omega)

/-- The capped trace lands on the accelerated orbit of its start. -/
theorem CappedTrace.reaches {p q n x A B C cost : Nat}
    (h : CappedTrace p q n x A B C cost) :
    ∃ k, Collatz.acceleratedOrbit k n = x := by
  induction h with
  | start => exact ⟨0, rfl⟩
  | @step x A B C cost v u W y _ hstep _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨v + W + k, by rw [← Collatz.acceleratedOrbit_add, hk, landing_eq hstep]⟩

/-- An orbit minimum cannot cross the cap while the total charge fits its
budget. This propagates the cap forward by one excursion. -/
theorem CappedTrace.next_cap_of_neverDrops {p q n x A B C cost v u W y : Nat}
    (h : CappedTrace p q n x A B C cost) (hstep : IsExcursion x v u W y)
    (hnever : Collatz.NeverDrops.NeverDrops n) (hq : 0 < q)
    (hbudget : p * (cost + charge W) + 2 * q * (n + 1) ≤ 2 * p * (n + 1)) :
    q * (B * 2 ^ (v + W)) ≤ p * (A * 3 ^ v) := by
  apply Nat.le_of_not_gt
  intro hcross
  have hdrop := drop_at_crossing h hstep hq hcross hbudget
  obtain ⟨k, hk⟩ := h.reaches
  have hstay := hnever (v + W + k)
  rw [← Collatz.acceleratedOrbit_add, hk, landing_eq hstep] at hstay
  exact Nat.not_lt_of_ge hstay hdrop

/-- An example that uses the discount. The first doubling crossing for 27
lands at 5 after 16 excursions. The total charge is 22, below 28, while
charging two for every excursion would cost 32. -/
theorem twenty_seven_crossing :
    ∃ x A B C cost v u W,
      CappedTrace 2 1 27 x A B C cost ∧ IsExcursion x v u W 5 ∧
      2 * (A * 3 ^ v) < B * 2 ^ (v + W) ∧ cost + charge W = 22 ∧ 5 < 27 := by
  have t0 := CappedTrace.start (p := 2) (q := 1) (n := 27)
  have t1 := CappedTrace.step t0 (show IsExcursion 27 2 7 1 31 by unfold IsExcursion; decide) (by decide)
  have t2 := CappedTrace.step t1 (show IsExcursion 31 5 1 1 121 by unfold IsExcursion; decide) (by decide)
  have t3 := CappedTrace.step t2 (show IsExcursion 121 1 61 1 91 by unfold IsExcursion; decide) (by decide)
  have t4 := CappedTrace.step t3 (show IsExcursion 91 2 23 1 103 by unfold IsExcursion; decide) (by decide)
  have t5 := CappedTrace.step t4 (show IsExcursion 103 3 13 1 175 by unfold IsExcursion; decide) (by decide)
  have t6 := CappedTrace.step t5 (show IsExcursion 175 4 11 1 445 by unfold IsExcursion; decide) (by decide)
  have t7 := CappedTrace.step t6 (show IsExcursion 445 1 223 2 167 by unfold IsExcursion; decide) (by decide)
  have t8 := CappedTrace.step t7 (show IsExcursion 167 3 21 1 283 by unfold IsExcursion; decide) (by decide)
  have t9 := CappedTrace.step t8 (show IsExcursion 283 2 71 1 319 by unfold IsExcursion; decide) (by decide)
  have t10 := CappedTrace.step t9 (show IsExcursion 319 6 5 2 911 by unfold IsExcursion; decide) (by decide)
  have t11 := CappedTrace.step t10 (show IsExcursion 911 4 57 3 577 by unfold IsExcursion; decide) (by decide)
  have t12 := CappedTrace.step t11 (show IsExcursion 577 1 289 1 433 by unfold IsExcursion; decide) (by decide)
  have t13 := CappedTrace.step t12 (show IsExcursion 433 1 217 1 325 by unfold IsExcursion; decide) (by decide)
  have t14 := CappedTrace.step t13 (show IsExcursion 325 1 163 3 61 by unfold IsExcursion; decide) (by decide)
  have t15 := CappedTrace.step t14 (show IsExcursion 61 1 31 2 23 by unfold IsExcursion; decide) (by decide)
  have last : IsExcursion 23 3 3 4 5 := by unfold IsExcursion; decide
  exact ⟨23, _, _, _, _, 3, 3, 4, t15, last, by decide, by decide,
    drop_at_doubling t15 last (by decide) (by decide)⟩

end Collatz.ExcursionCrossing
