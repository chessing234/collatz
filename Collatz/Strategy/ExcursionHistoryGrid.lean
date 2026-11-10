import Collatz.Strategy.ExcursionMixedGrid

/-!
# Recovering excursion sources from the preceding history

The affine equation of a prefix fixes its endpoint modulo a power of three.
The odd-run length of the next excursion fixes a dyadic residue at the same
endpoint. The joint modulus grows with the odd-step count of the whole
prefix. After the elapsed shortcut time exceeds the binary size of the
source, the endpoint is itself below that modulus.
-/

namespace Collatz.ExcursionHistoryGrid

open Collatz.ExcursionBudget Collatz.ExcursionMixedGrid Collatz.LiftExponent
open Collatz.ExcursionMap Collatz.ExcursionLattice

/-- The full preceding trace supplies the incoming ternary residue. -/
theorem history_residue {n x : Nat} {rs : List Run} (h : Trace n x rs) :
    (2 ^ time rs * x) % 3 ^ ExcursionBudget.oddCount rs = offset rs % 3 ^ ExcursionBudget.oddCount rs := by
  rw [← h.affine, Nat.mul_add_mod_self_left]

/-- A full-history candidate also satisfies the last excursion's incoming
congruence. Earlier excursions cannot relax this constraint. -/
theorem history_implies_incoming {v W b : Nat} {rs : List Run}
    (hc : (2 ^ time (⟨v, W⟩ :: rs) * b) % 3 ^ ExcursionBudget.oddCount (⟨v, W⟩ :: rs) =
      offset (⟨v, W⟩ :: rs) % 3 ^ ExcursionBudget.oddCount (⟨v, W⟩ :: rs)) :
    3 ^ v ∣ 2 ^ W * b + 1 := by
  let A := 3 ^ v
  let B := 2 ^ time rs
  let D := 2 ^ (v + W)
  let E := 2 ^ v
  have hd : A ∣ 3 ^ ExcursionBudget.oddCount (⟨v, W⟩ :: rs) := by
    change 3 ^ v ∣ 3 ^ (v + ExcursionBudget.oddCount rs)
    rw [Nat.pow_add]
    exact Nat.dvd_mul_right _ _
  have hlocal := congrArg (· % A) hc
  rw [Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd] at hlocal
  change (2 ^ ((v + W) + time rs) * b) % A =
    (A * offset rs + B * (A - E)) % A at hlocal
  rw [Nat.mul_add_mod_self_left, Nat.pow_add] at hlocal
  have hmod : (B * (D * b)) % A = (B * (A - E)) % A := by
    simpa only [D, B, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlocal
  have hE : E ≤ A := Nat.pow_le_pow_left (by decide) _
  have hadd : (B * (D * b) + B * E) % A = 0 := by
    calc
      _ = ((B * (D * b)) % A + (B * E) % A) % A := Nat.add_mod ..
      _ = (B * (A - E) + B * E) % A := by rw [hmod, ← Nat.add_mod]
      _ = (B * A) % A := by rw [← Nat.mul_add, Nat.sub_add_cancel hE]
      _ = 0 := by simp
  apply cancel_dyadic (W := time rs + v)
  apply Nat.dvd_of_mod_eq_zero
  have heq : 2 ^ (time rs + v) * (2 ^ W * b + 1) = B * (D * b) + B * E := by
    simp only [Nat.pow_add, Nat.mul_add, Nat.mul_one, B, D, E]
    ac_rfl
  rw [heq, hadd]

/-- A full-history floor lies above every admissible one-excursion floor
from the first joint period. -/
theorem incoming_floor_le_history {m x b v p W : Nat} {rs : List Run}
    (hm : m ≤ x) (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v)
    (hc : (2 ^ time (⟨p, W⟩ :: rs) * x) % 3 ^ ExcursionBudget.oddCount (⟨p, W⟩ :: rs) =
      offset (⟨p, W⟩ :: rs) % 3 ^ ExcursionBudget.oddCount (⟨p, W⟩ :: rs))
    (hin : 3 ^ p ∣ 2 ^ W * b + 1) (hwindow : b < m + 2 ^ (v + 1) * 3 ^ p) :
    b ≤ x :=
  mixed_floor hm hx hb (history_implies_incoming hc) hin hwindow

/-- Matching residues give a divisor of the difference in either order. -/
theorem dvd_sub_of_residue {a b d : Nat} (h : a % d = b % d) :
    d ∣ b - a := by
  refine ⟨b / d - a / d, ?_⟩
  have ha := Nat.mod_add_div a d
  have hb := Nat.mod_add_div b d
  rw [Nat.mul_sub_left_distrib]
  omega

/-- A candidate in the first full-history residue period above a floor
bounds the actual next source below. -/
theorem history_floor {n x m b v : Nat} {rs : List Run} (h : Trace n x rs)
    (hm : m ≤ x) (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v)
    (hcert : (2 ^ time rs * b) % 3 ^ ExcursionBudget.oddCount rs = offset rs % 3 ^ ExcursionBudget.oddCount rs)
    (hwindow : b < m + 2 ^ (v + 1) * 3 ^ ExcursionBudget.oddCount rs) : b ≤ x := by
  by_cases hxb : x < b
  · have hsub := dvd_sub_of_residue ((history_residue h).trans hcert.symm)
    rw [← Nat.mul_sub_left_distrib] at hsub
    have hperiod := mixed_period_dvd_difference hx hb (Nat.le_of_lt hxb) hsub
    have hle := Nat.le_of_dvd (by omega : 0 < b - x) hperiod
    omega
  · exact Nat.le_of_not_gt hxb

/-- The affine offset is bounded by the product of the two coefficients. -/
theorem offset_le_coefficients {n x : Nat} {rs : List Run} (h : Trace n x rs) :
    offset rs ≤ 2 ^ time rs * 3 ^ ExcursionBudget.oddCount rs := by
  induction h with
  | nil => simp [offset, time, ExcursionBudget.oddCount]
  | @step x y v u W rs _ hrun ih =>
    let A := 3 ^ ExcursionBudget.oddCount rs
    let B := 2 ^ time rs
    let a := 3 ^ v
    have hA : 0 < A := Nat.pow_pos (by decide)
    have hb : 2 ≤ 2 ^ (v + W) := by
      have hv : 0 < v := hrun.2.2.2.1
      exact Nat.le_trans (by decide : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hc : B * (a - 2 ^ v) ≤ a * (B * A) := by
      calc
        _ ≤ B * a := Nat.mul_le_mul_left _ (Nat.sub_le ..)
        _ ≤ (B * a) * A := Nat.le_mul_of_pos_right _ hA
        _ = _ := by ac_rfl
    change a * offset rs + B * (a - 2 ^ v) ≤
      2 ^ ((v + W) + time rs) * 3 ^ (v + ExcursionBudget.oddCount rs)
    calc
      _ ≤ a * (B * A) + a * (B * A) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ih) hc
      _ = 2 * (a * (B * A)) := by rw [Nat.two_mul]
      _ ≤ 2 ^ (v + W) * (a * (B * A)) := Nat.mul_le_mul_right _ hb
      _ = _ := by
        simp only [Nat.pow_add, A, B, a]
        ac_rfl

/-- If the denominator of the preceding trace exceeds the original source,
the landing is below every joint period for its next odd-run length. -/
theorem source_lt_period {n x v : Nat} {rs : List Run} (h : Trace n x rs)
    (hn : n < 2 ^ time rs) : x < 2 ^ (v + 1) * 3 ^ ExcursionBudget.oddCount rs := by
  let A := 3 ^ ExcursionBudget.oddCount rs
  let B := 2 ^ time rs
  have ha : 0 < A := Nat.pow_pos (by decide)
  have hscaled : B * x < B * (2 * A) := by
    calc
      _ = A * n + offset rs := h.affine.symm
      _ < A * B + B * A :=
        Nat.add_lt_add_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hn ha)
          (offset_le_coefficients h)
      _ = B * (2 * A) := by rw [Nat.two_mul, Nat.mul_add, Nat.mul_comm A B]
  have ht : 2 ≤ 2 ^ (v + 1) :=
    Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
  exact Nat.lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_left hscaled)
    (Nat.mul_le_mul_right _ ht)

/-- After the binary-size threshold, the unique candidate in the joint
period is the actual source. -/
theorem history_recovers_source {n x b v : Nat} {rs : List Run} (h : Trace n x rs)
    (hn : n < 2 ^ time rs) (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v)
    (hcert : (2 ^ time rs * b) % 3 ^ ExcursionBudget.oddCount rs = offset rs % 3 ^ ExcursionBudget.oddCount rs)
    (hwindow : b < 2 ^ (v + 1) * 3 ^ ExcursionBudget.oddCount rs) : b = x := by
  have hle := history_floor h (m := 0) (Nat.zero_le x) hx hb hcert (by simpa using hwindow)
  have hsub := dvd_sub_of_residue (hcert.trans (history_residue h).symm)
  rw [← Nat.mul_sub_left_distrib] at hsub
  have hperiod := mixed_period_dvd_difference hb hx hle hsub
  have hlt := source_lt_period (v := v) h hn
  have hd := Nat.eq_zero_of_dvd_of_lt hperiod (show x - b < _ by omega)
  omega

/-- Lower sources certified against the whole preceding trace. -/
inductive HistoryFloors (m : Nat) : List Run → List Visit → Prop where
  | nil : HistoryFloors m [] []
  | step {v W b : Nat} {rs : List Run} {bs : List Visit} :
      HistoryFloors m rs bs →
      m ≤ b → Val2 (b + 1) v →
      (2 ^ time rs * b) % 3 ^ ExcursionBudget.oddCount rs =
        offset rs % 3 ^ ExcursionBudget.oddCount rs →
      b < m + 2 ^ (v + 1) * 3 ^ ExcursionBudget.oddCount rs →
      HistoryFloors m (⟨v, W⟩ :: rs) (⟨v, b⟩ :: bs)

theorem HistoryFloors.compare {m n e : Nat} {rs : List Run} {bs : List Visit}
    (hc : HistoryFloors m rs bs) (ht : Trace n e rs)
    (hm : ∀ r ∈ visits n rs, m ≤ r.source) :
    ((visits n rs).map Visit.numerator).prod * (bs.map Visit.source).prod ≤
      ((visits n rs).map Visit.source).prod * (bs.map Visit.numerator).prod := by
  induction hc generalizing e with
  | nil => simp [visits]
  | step _ _ hval hcert hwindow ih =>
    cases ht with
    | step hp hrun =>
      rw [visits, hp.landing] at hm ⊢
      have hx := history_floor hp (hm _ List.mem_cons_self) (val2_succ_of hrun)
        hval hcert hwindow
      exact compare_cons hx (ih hp (fun r hr => hm r (List.mem_cons_of_mem _ hr)))

/-- A full-history product certificate gives a descent somewhere in the trace
for every realizing source above the chosen floor. -/
theorem descent_of_history_floors {m n e : Nat} {rs : List Run} {bs : List Visit}
    (ht : Trace n e rs) (hc : HistoryFloors m rs bs) (hm : 0 < m) (hmn : m ≤ n)
    (hgap : (bs.map Visit.numerator).prod < 2 ^ time rs * (bs.map Visit.source).prod) :
    ∃ j ≤ time rs, Collatz.acceleratedOrbit j n < n := by
  apply Classical.byContradiction
  intro hno
  have hfloor : ∀ r ∈ visits n rs, m ≤ r.source := by
    intro r hr
    obtain ⟨j, hj, heq⟩ := visit_time hr
    rw [heq]
    exact Nat.le_trans hmn (Nat.le_of_not_gt (fun hd => hno ⟨j, hj, hd⟩))
  have hkeep : n ≤ e := Nat.le_of_not_gt (fun hd =>
    hno ⟨time rs, Nat.le_refl _, ht.landing.symm ▸ hd⟩)
  exact Nat.not_lt_of_ge (trace_denominator_le ht (Nat.lt_of_lt_of_le hm hmn) hkeep
    (fun r hr => Nat.lt_of_lt_of_le hm (hfloor r hr)) (hc.compare ht hfloor)) hgap

end Collatz.ExcursionHistoryGrid
