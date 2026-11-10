import Collatz.Strategy.ExcursionMap

/-!
# Switching shifted coordinates along an excursion trace

For a start floor `n`, normalize each landing `x` by either `x/n` or
`(x+1)/(n+1)`. The choice can change at every excursion. Each transition
has a departure-based bound and, when its denominator is positive, an
arrival-based bound. Both telescope with the same normalization.
-/

namespace Collatz.ExcursionSwitchFloor

open Collatz.ExcursionMap

/-- Nonnegative upper bound for the affine offset when changing from the
coordinate `x+s` to `y+t`. The actual offset can be negative. -/
def shiftOffset (v W s t : Nat) : Nat :=
  3 ^ v * (1 - s) + 2 ^ (v + W) * t - 2 ^ v

private theorem shifted_affine_le {x y v u W s t : Nat}
    (h : IsExcursion x v u W y) (hs : s ≤ 1) :
    2 ^ (v + W) * (y + t) ≤ 3 ^ v * (x + s) + shiftOffset v W s t := by
  have hraw : 2 ^ (v + W) * y + 2 ^ v = 3 ^ v * (x + 1) := calc
    _ = 2 ^ v * (2 ^ W * y + 1) := by
      rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
    _ = 2 ^ v * (3 ^ v * u) := by rw [h.2.2.2.2.2.2]
    _ = _ := by rw [h.2.2.2.2.2.1]; ac_rfl
  have hsplit : 3 ^ v * (x + 1) = 3 ^ v * (x + s) + 3 ^ v * (1 - s) := by
    rw [← Nat.mul_add, show x + s + (1 - s) = x + 1 by omega]
  rw [hsplit] at hraw
  rw [Nat.mul_add, shiftOffset]
  omega

/-- Two safe bounds for one coordinate transition. The arrival bound
requires its explicit positive denominator. -/
inductive Factor (n v W s t : Nat) : Nat → Nat → Prop where
  | departure : Factor n v W s t
      (3 ^ v * (n + s) + shiftOffset v W s t) (3 ^ v * (n + t))
  | arrival (h : shiftOffset v W s t < 2 ^ (v + W) * (n + t)) :
      Factor n v W s t
        (2 ^ (v + W) * (n + s)) (2 ^ (v + W) * (n + t) - shiftOffset v W s t)

/-- Either factor bounds the inverse coefficient times the ratio of
normalized states, provided both states are above the start floor. -/
theorem Factor.sound {n x y v u W s t num den : Nat} (f : Factor n v W s t num den)
    (h : IsExcursion x v u W y) (hs : s ≤ 1) (hx : n ≤ x) (hy : n ≤ y) :
    2 ^ (v + W) * den * (n + s) * (y + t) ≤ 3 ^ v * num * (n + t) * (x + s) := by
  let A := 3 ^ v
  let B := 2 ^ (v + W)
  let E := shiftOffset v W s t
  have hlocal : B * (y + t) ≤ A * (x + s) + E := shifted_affine_le h hs
  cases f with
  | departure =>
    have hbound : B * (y + t) * (n + s) ≤ (A * (n + s) + E) * (x + s) := calc
      _ ≤ (A * (x + s) + E) * (n + s) := Nat.mul_le_mul_right _ hlocal
      _ = A * (n + s) * (x + s) + E * (n + s) := by
        rw [Nat.add_mul]
        congr 1
        ac_rfl
      _ ≤ A * (n + s) * (x + s) + E * (x + s) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left E (Nat.add_le_add_right hx s)) _
      _ = _ := by rw [Nat.add_mul]
    change B * (A * (n + t)) * (n + s) * (y + t) ≤
      A * (A * (n + s) + E) * (n + t) * (x + s)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left (A * (n + t)) hbound
  | arrival hpos =>
    let D := B * (n + t) - E
    have hsum : D + E = B * (n + t) := Nat.sub_add_cancel (Nat.le_of_lt hpos)
    have hbound : D * (y + t) + E * (y + t) ≤ A * (x + s) * (n + t) + E * (n + t) := calc
      _ = B * (y + t) * (n + t) := by rw [← Nat.add_mul, hsum]; ac_rfl
      _ ≤ (A * (x + s) + E) * (n + t) := Nat.mul_le_mul_right _ hlocal
      _ = _ := by rw [Nat.add_mul]
    have hcharge := Nat.mul_le_mul_left E (Nat.add_le_add_right hy t)
    have hsimple : D * (y + t) ≤ A * (x + s) * (n + t) := by omega
    change B * D * (n + s) * (y + t) ≤ A * (B * (n + s)) * (n + t) * (x + s)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left (B * (n + s)) hsimple

/-- A finite excursion trace decorated with coordinate shifts and with
either valid local factor at each step. The indices store the landing,
shift, elapsed time, affine numerator and denominator, and factor product. -/
inductive Trace (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | start {s : Nat} : s ≤ 1 → Trace n n s 0 1 1 1 1
  | step {x y s t elapsed A B U D v u W num den : Nat} :
      Trace n x s elapsed A B U D →
      IsExcursion x v u W y →
      t ≤ 1 →
      Factor n v W s t num den →
      Trace n y t (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W)) (U * num) (D * den)

theorem Trace.shift_le {n x s elapsed A B U D : Nat} (h : Trace n x s elapsed A B U D) :
    s ≤ 1 := by
  cases h with
  | start hs => exact hs
  | step _ _ ht _ => exact ht

theorem Trace.landing {n x s elapsed A B U D : Nat} (h : Trace n x s elapsed A B U D) :
    Collatz.acceleratedOrbit elapsed n = x := by
  induction h with
  | start => rfl
  | step _ hstep _ _ ih => rw [← Collatz.acceleratedOrbit_add, ih, landing_eq hstep]

/-- Under a floor hypothesis, the decorated trace bounds the inverse
coefficient by the product of its chosen factors. -/
theorem Trace.floor_bound {n x s elapsed A B U D H : Nat}
    (h : Trace n x s elapsed A B U D) (hn : 0 < n) (htime : elapsed ≤ H)
    (hfloor : ∀ k, k ≤ H → n ≤ Collatz.acceleratedOrbit k n) :
    B * D * (x + s) ≤ A * U * (n + s) := by
  induction h with
  | start => simp
  | @step x y s t elapsed A B U D v u W num den hprev hstep _ f ih =>
    have hbefore : elapsed ≤ H := by omega
    have hx := hfloor elapsed hbefore
    rw [hprev.landing] at hx
    have hy := hfloor (v + W + elapsed) htime
    rw [← Collatz.acceleratedOrbit_add, hprev.landing, landing_eq hstep] at hy
    have hstepBound := f.sound hstep hprev.shift_le hx hy
    have hscaled :
        (B * 2 ^ (v + W)) * (D * den) * (y + t) * (n + s) ≤
          (A * 3 ^ v) * (U * num) * (n + t) * (n + s) := calc
      _ = (B * D) * (2 ^ (v + W) * den * (n + s) * (y + t)) := by ac_rfl
      _ ≤ (B * D) * (3 ^ v * num * (n + t) * (x + s)) :=
        Nat.mul_le_mul_left _ hstepBound
      _ = (3 ^ v * num * (n + t)) * (B * D * (x + s)) := by ac_rfl
      _ ≤ (3 ^ v * num * (n + t)) * (A * U * (n + s)) :=
        Nat.mul_le_mul_left _ (ih hbefore)
      _ = _ := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hscaled (Nat.add_pos_left hn _)

/-- If the inverse coefficient beats the product of the selected factors,
the accelerated orbit dropped below its start within the trace. -/
theorem Trace.drop_of_crossing {n x s elapsed A B U D : Nat}
    (h : Trace n x s elapsed A B U D) (hn : 0 < n) (hcross : A * U < B * D) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n := by
  apply Classical.byContradiction
  intro hnone
  have hfloor (k : Nat) (hk : k ≤ elapsed) : n ≤ Collatz.acceleratedOrbit k n := by
    apply Nat.le_of_not_gt
    intro hdrop
    exact hnone ⟨k, hk, hdrop⟩
  have hx := hfloor elapsed (Nat.le_refl _)
  rw [h.landing] at hx
  have hscaled : B * D * (n + s) ≤ A * U * (n + s) :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hx s))
      (h.floor_bound hn (Nat.le_refl _) hfloor)
  exact (Nat.not_lt_of_ge hscaled)
    (Nat.mul_lt_mul_of_pos_right hcross (Nat.add_pos_left hn _))

/-- Compute the smaller available factor by integer cross multiplication. -/
def chooseFactor (n v W s t : Nat) : Nat × Nat :=
  let a := 3 ^ v
  let b := 2 ^ (v + W)
  let e := shiftOffset v W s t
  let departure := (a * (n + s) + e, a * (n + t))
  if e < b * (n + t) then
    let arrival := (b * (n + s), b * (n + t) - e)
    if arrival.1 * departure.2 ≤ departure.1 * arrival.2 then arrival else departure
  else departure

theorem chooseFactor_sound (n v W s t : Nat) :
    Factor n v W s t (chooseFactor n v W s t).1 (chooseFactor n v W s t).2 := by
  unfold chooseFactor
  dsimp only
  split
  · rename_i hpositive
    split
    · exact .arrival hpositive
    · exact .departure
  · exact .departure

/-- A computed factor product with its checked trace as evidence. -/
structure Certificate (n x s elapsed A B : Nat) where
  num : Nat
  den : Nat
  trace : Trace n x s elapsed A B num den

def Certificate.extend {n x y s t elapsed A B v u W : Nat}
    (c : Certificate n x s elapsed A B) (hstep : IsExcursion x v u W y) (ht : t ≤ 1) :
    Certificate n y t (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W)) :=
  ⟨c.num * (chooseFactor n v W s t).1, c.den * (chooseFactor n v W s t).2,
    .step c.trace hstep ht (chooseFactor_sound n v W s t)⟩

def Certificate.better {n x s elapsed A B : Nat}
    (left right : Certificate n x s elapsed A B) : Certificate n x s elapsed A B :=
  if left.num * right.den ≤ right.num * left.den then left else right

/-- The dynamic program retains one certified product for each coordinate. -/
structure Table (n x elapsed A B : Nat) where
  unshifted : Certificate n x 0 elapsed A B
  shifted : Certificate n x 1 elapsed A B

def Table.start (n : Nat) : Table n n 0 1 1 :=
  ⟨⟨1, 1, .start (by decide)⟩, ⟨1, 1, .start (by decide)⟩⟩

def Table.advance {n x y elapsed A B v u W : Nat} (table : Table n x elapsed A B)
    (hstep : IsExcursion x v u W y) :
    Table n y (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W)) where
  unshifted := (table.unshifted.extend hstep (by decide)).better
    (table.shifted.extend hstep (by decide))
  shifted := (table.unshifted.extend hstep (by decide)).better
    (table.shifted.extend hstep (by decide))

/-- Either computed product can certify a drop within the trace. -/
theorem Table.drop_by {n x elapsed A B : Nat} (table : Table n x elapsed A B) (hn : 0 < n)
    (hcross : A * table.unshifted.num < B * table.unshifted.den ∨
      A * table.shifted.num < B * table.shifted.den) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n := by
  rcases hcross with h | h
  · exact table.unshifted.trace.drop_of_crossing hn h
  · exact table.shifted.trace.drop_of_crossing hn h

/-- The computed switching certificate detects a descent from 63 by
accelerated time 54. -/
theorem sixty_three_switch_drop :
    ∃ k, k ≤ 54 ∧ Collatz.acceleratedOrbit k 63 < 63 := by
  let t0 := Table.start 63
  let t1 := t0.advance (show IsExcursion 63 6 1 3 91 by unfold IsExcursion; decide)
  let t2 := t1.advance (show IsExcursion 91 2 23 1 103 by unfold IsExcursion; decide)
  let t3 := t2.advance (show IsExcursion 103 3 13 1 175 by unfold IsExcursion; decide)
  let t4 := t3.advance (show IsExcursion 175 4 11 1 445 by unfold IsExcursion; decide)
  let t5 := t4.advance (show IsExcursion 445 1 223 2 167 by unfold IsExcursion; decide)
  let t6 := t5.advance (show IsExcursion 167 3 21 1 283 by unfold IsExcursion; decide)
  let t7 := t6.advance (show IsExcursion 283 2 71 1 319 by unfold IsExcursion; decide)
  let t8 := t7.advance (show IsExcursion 319 6 5 2 911 by unfold IsExcursion; decide)
  let t9 := t8.advance (show IsExcursion 911 4 57 3 577 by unfold IsExcursion; decide)
  let t10 := t9.advance (show IsExcursion 577 1 289 1 433 by unfold IsExcursion; decide)
  let t11 := t10.advance (show IsExcursion 433 1 217 1 325 by unfold IsExcursion; decide)
  let t12 := t11.advance (show IsExcursion 325 1 163 3 61 by unfold IsExcursion; decide)
  exact t12.drop_by (by decide) (by decide)

end Collatz.ExcursionSwitchFloor
