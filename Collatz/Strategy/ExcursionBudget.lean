import Collatz.Strategy.ExcursionMap

/-!
# Weighted descent at an excursion crossing

The positive affine offset of an odd run of length `v` is `3^v - 2^v`.
Dividing by its coefficient gives `1 - (2/3)^v`. When composing runs, the
normalized offset of this run is multiplied by the inverse slope of the
prefix *before* the run. A bound on proper prefixes therefore pays for the
entire offset, including the crossing run itself.
-/

namespace Collatz.ExcursionBudget

open Collatz.ExcursionMap

/-- The odd run length and the extra halving count of an excursion. -/
structure Run where
  oddSteps : Nat
  halvings : Nat

/-- Runs are stored in reverse chronological order to expose the last run. -/
inductive Trace (n : Nat) : Nat → List Run → Prop where
  | nil : Trace n n []
  | step {x y v u W : Nat} {rs : List Run} :
      Trace n x rs → IsExcursion x v u W y → Trace n y (⟨v, W⟩ :: rs)

def oddCount : List Run → Nat
  | [] => 0
  | r :: rs => r.oddSteps + oddCount rs

def time : List Run → Nat
  | [] => 0
  | r :: rs => (r.oddSteps + r.halvings) + time rs

def offset : List Run → Nat
  | [] => 0
  | r :: rs => 3 ^ r.oddSteps * offset rs + 2 ^ time rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps)

def weight (charge : Nat → Nat) : List Run → Nat
  | [] => 0
  | r :: rs => charge r.oddSteps + weight charge rs

/-- For every proper prefix, the inverse slope is at most `p / d`. -/
def ProperPrefixBound (p d : Nat) : List Run → Prop
  | [] => True
  | _ :: rs => d * 2 ^ time rs ≤ p * 3 ^ oddCount rs ∧ ProperPrefixBound p d rs

theorem single_affine {x v u W y : Nat} (h : IsExcursion x v u W y) :
    3 ^ v * x + (3 ^ v - 2 ^ v) = 2 ^ (v + W) * y := by
  have hmul : 3 ^ v * (x + 1) = 2 ^ v * (2 ^ W * y + 1) := by
    calc
      _ = 3 ^ v * (2 ^ v * u) := by rw [h.2.2.2.2.2.1]
      _ = 2 ^ v * (3 ^ v * u) := Nat.mul_left_comm ..
      _ = _ := by rw [h.2.2.2.2.2.2]
  have hpow : (2 : Nat) ^ v ≤ 3 ^ v := Nat.pow_le_pow_left (by decide) _
  simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add] at hmul
  omega

theorem Trace.affine {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    3 ^ oddCount rs * n + offset rs = 2 ^ time rs * e := by
  induction h with
  | nil => simp [oddCount, offset, time]
  | @step x y v u W rs _ hrun ih =>
    have hstep := congrArg (2 ^ time rs * ·) (single_affine hrun)
    calc
      _ = 3 ^ v * (3 ^ oddCount rs * n + offset rs) +
          2 ^ time rs * (3 ^ v - 2 ^ v) := by
        simp [oddCount, offset, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
      _ = 2 ^ time rs * (3 ^ v * x + (3 ^ v - 2 ^ v)) := by
        rw [ih, Nat.mul_left_comm (3 ^ v), ← Nat.mul_add]
      _ = _ := by
        rw [hstep]
        simp [time, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]

theorem Trace.landing {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    Collatz.acceleratedOrbit (time rs) n = e := by
  induction h with
  | nil => rfl
  | step _ hrun ih =>
    rw [time, ← Collatz.acceleratedOrbit_add, ih, landing_eq hrun]

/-- A bound on normalized offsets obtained by charging each run separately. -/
theorem offset_le_weight {p d scale : Nat} {charge : Nat → Nat}
    (hcharge : ∀ v, scale * (3 ^ v - 2 ^ v) ≤ charge v * 3 ^ v)
    {rs : List Run} (hp : ProperPrefixBound p d rs) :
    d * scale * offset rs ≤ p * (3 ^ oddCount rs * weight charge rs) := by
  induction rs with
  | nil => simp [offset, weight]
  | cons r rs ih =>
    obtain ⟨hprev, hp⟩ := hp
    calc
      _ = 3 ^ r.oddSteps * (d * scale * offset rs) +
          (d * 2 ^ time rs) * (scale * (3 ^ r.oddSteps - 2 ^ r.oddSteps)) := by
        simp [offset, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3 ^ r.oddSteps * (p * (3 ^ oddCount rs * weight charge rs)) +
          (p * 3 ^ oddCount rs) * (charge r.oddSteps * 3 ^ r.oddSteps) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (ih hp)) (Nat.mul_le_mul hprev (hcharge _))
      _ = _ := by
        simp [oddCount, weight, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.add_comm]

/-- If the weighted error fits in the slope gap, the crossing gives a descent. -/
theorem drop_of_weighted_crossing {p d scale n e : Nat} {rs : List Run}
    {charge : Nat → Nat} (h : Trace n e rs) (hn : 0 < n) (hs : 0 < scale)
    (hcharge : ∀ v, scale * (3 ^ v - 2 ^ v) ≤ charge v * 3 ^ v)
    (hp : ProperPrefixBound p d rs) (hcross : p * 3 ^ oddCount rs < d * 2 ^ time rs)
    (hbudget : d * scale * n + p * weight charge rs ≤ p * scale * n) : e < n := by
  have hbound := offset_le_weight hcharge hp
  have hlt : (d * scale * 2 ^ time rs) * e < (d * scale * 2 ^ time rs) * n := by
    calc
      _ = (d * scale) * (2 ^ time rs * e) := Nat.mul_assoc ..
      _ = 3 ^ oddCount rs * (d * scale * n) + d * scale * offset rs := by
        rw [← h.affine, Nat.mul_add]
        ac_rfl
      _ ≤ 3 ^ oddCount rs * (d * scale * n + p * weight charge rs) := by
        rw [Nat.mul_add, Nat.mul_left_comm (3 ^ oddCount rs) p]
        exact Nat.add_le_add_left hbound _
      _ ≤ 3 ^ oddCount rs * (p * scale * n) := Nat.mul_le_mul_left _ hbudget
      _ = (p * 3 ^ oddCount rs) * (scale * n) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ < (d * 2 ^ time rs) * (scale * n) :=
        Nat.mul_lt_mul_of_pos_right hcross (Nat.mul_pos hs hn)
      _ = _ := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- Nine times the normalized offset, rounded up to nine for long runs.
Lengths one and two have exact charges three and five. -/
def ninths : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 9

theorem ninths_bound (v : Nat) : 9 * (3 ^ v - 2 ^ v) ≤ ninths v * 3 ^ v := by
  match v with
  | 0 | 1 | 2 => decide
  | v + 3 => exact Nat.mul_le_mul_left _ (Nat.sub_le ..)

/-- No fixed bound on the number of excursions is needed at a first crossing
below half the initial multiplier. The source pays for the weighted length. -/
theorem drop_of_first_half {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : 0 < n) (hp : ProperPrefixBound 2 1 rs)
    (hcross : 2 * 3 ^ oddCount rs < 2 ^ time rs)
    (hbudget : 2 * weight ninths rs ≤ 9 * n) : e < n :=
  drop_of_weighted_crossing h hn (by decide) ninths_bound hp (by simpa using hcross) (by omega)

/-- For a fixed ratio, every prefix stays on its initial side as long as
the orbit stays above its starting value and the total charge fits. -/
theorem prefix_bound_of_no_drop {p d scale n e : Nat} {rs : List Run}
    {charge : Nat → Nat} (h : Trace n e rs) (hn : 0 < n) (hs : 0 < scale)
    (hcharge : ∀ v, scale * (3 ^ v - 2 ^ v) ≤ charge v * 3 ^ v)
    (hbudget : d * scale * n + p * weight charge rs ≤ p * scale * n)
    (hmin : ∀ j ≤ time rs, n ≤ Collatz.acceleratedOrbit j n) :
    d * 2 ^ time rs ≤ p * 3 ^ oddCount rs ∧ ProperPrefixBound p d rs := by
  induction h with
  | nil =>
    have h := Nat.le_of_mul_le_mul_right (by simpa [weight, Nat.mul_assoc] using hbudget :
        d * (scale * n) ≤ p * (scale * n)) (Nat.mul_pos hs hn)
    simpa [time, oddCount, ProperPrefixBound] using h
  | @step x y v u W rs hprev hrun ih =>
    have hsub : weight charge rs ≤ weight charge (⟨v, W⟩ :: rs) := by simp [weight]
    have hprevBudget := Nat.le_trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left p hsub) (d * scale * n)) hbudget
    have htime : time rs ≤ time (⟨v, W⟩ :: rs) := by simp [time]
    have hp : ProperPrefixBound p d (⟨v, W⟩ :: rs) :=
      ih hprevBudget (fun j hj => hmin j (Nat.le_trans hj htime))
    refine ⟨?_, hp⟩
    apply Nat.le_of_not_gt
    intro hc
    have htrace := Trace.step hprev hrun
    have hdrop := drop_of_weighted_crossing htrace hn hs hcharge hp hc hbudget
    have hkeep := hmin _ (Nat.le_refl _)
    rw [htrace.landing] at hkeep
    omega

/-- A finite necessary condition for staying at or above the source.
Each long run is charged at most one, irrespective of its odd length. -/
theorem slope_bound_of_no_drop {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : 0 < n)
    (hmin : ∀ j ≤ time rs, n ≤ Collatz.acceleratedOrbit j n) :
    (9 * n - weight ninths rs) * 2 ^ time rs ≤ 9 * n * 3 ^ oddCount rs := by
  by_cases hcost : weight ninths rs ≤ 9 * n
  · have hsum : (9 * n - weight ninths rs) + weight ninths rs = 9 * n :=
      Nat.sub_add_cancel hcost
    have hbudget : (9 * n - weight ninths rs) * 9 * n + 9 * n * weight ninths rs ≤
        9 * n * 9 * n := by
      apply Nat.le_of_eq
      calc
        _ = ((9 * n - weight ninths rs) + weight ninths rs) * (9 * n) := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (9 * n) (weight ninths rs)]
        _ = 9 * n * (9 * n) := by rw [hsum]
        _ = 9 * n * 9 * n := (Nat.mul_assoc ..).symm
    exact (prefix_bound_of_no_drop h hn (by decide) ninths_bound hbudget hmin).1
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hcost), Nat.zero_mul]
    exact Nat.zero_le _

end Collatz.ExcursionBudget
