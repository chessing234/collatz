import Collatz.Strategy.ExcursionChargeCore
import Collatz.Strategy.ExcursionBudget

/-!
# Optimal charges in finite excursion descent budgets

The arithmetic charge is the least valid integer bound at its scale.
These theorems strengthen a conditional descent test; they establish
neither universal coefficient crossings nor the Collatz conjecture.
-/

namespace Collatz.ExcursionCharge

open ExcursionBudget

/-- Each run fits below the total odd count of its finite trace. -/
theorem run_le_total {r : Run} {rs : List Run} (hr : r ∈ rs) :
    r.oddSteps ≤ ExcursionBudget.oddCount rs := by
  induction rs with
  | nil => simp at hr
  | cons q rs ih =>
    rcases List.mem_cons.mp hr with he | ht
    · subst r
      exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih ht) (Nat.le_add_left _ _)

/-- One common ternary scale removes rounding for every run of a finite trace. -/
theorem common_exact_scale (rs : List Run) :
    ∀ r ∈ rs, charge (3 ^ ExcursionBudget.oddCount rs) r.oddSteps * 3 ^ r.oddSteps =
      3 ^ ExcursionBudget.oddCount rs * (3 ^ r.oddSteps - 2 ^ r.oddSteps) := by
  intro r hr
  exact charge_ternary_exact (run_le_total hr)

/-- Optimal charges minimize the total weight among all valid per-run charges. -/
theorem weight_le_of_valid {s : Nat} {other : Nat → Nat}
    (ho : ∀ v, s * (3 ^ v - 2 ^ v) ≤ other v * 3 ^ v) (rs : List Run) :
    weight (charge s) rs ≤ weight other rs := by
  induction rs with
  | nil => simp [weight]
  | cons r rs ih =>
    exact Nat.add_le_add ((charge_le_iff s r.oddSteps (other r.oddSteps)).mpr (ho _)) ih

/-- Refinement improves the whole finite error budget, not just a single run. -/
theorem weight_refine (m s : Nat) (rs : List Run) :
    weight (charge (m * s)) rs ≤ m * weight (charge s) rs := by
  induction rs with
  | nil => simp [weight]
  | cons r rs ih =>
    simpa only [weight, Nat.mul_add] using
      Nat.add_le_add (charge_refine m s r.oddSteps) ih

/-- Every old budget remains valid after refinement by an integer multiple. -/
theorem budget_refine {p d s n : Nat} {rs : List Run}
    (hb : d * s * n + p * weight (charge s) rs ≤ p * s * n) (m : Nat) :
    d * (m * s) * n + p * weight (charge (m * s)) rs ≤ p * (m * s) * n := by
  calc
    _ ≤ d * (m * s) * n + p * (m * weight (charge s) rs) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left p (weight_refine m s rs)) _
    _ = m * (d * s * n + p * weight (charge s) rs) := by
      simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ m * (p * s * n) := Nat.mul_le_mul_left m hb
    _ = _ := by ac_rfl

/-- The old ninths charge is valid but not always minimal. -/
theorem charge_nine_le_ninths (v : Nat) : charge 9 v ≤ ninths v :=
  (charge_le_iff 9 v (ninths v)).mpr (ninths_bound v)

theorem weight_nine_le_ninths (rs : List Run) :
    weight (charge 9) rs ≤ weight ninths rs :=
  weight_le_of_valid ninths_bound rs

/-- Arbitrary-length descent with optimal charges; all crossing hypotheses remain explicit. -/
theorem drop_of_crossing {p d s n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : 0 < n) (hs : 0 < s)
    (hp : ProperPrefixBound p d rs)
    (hc : p * 3 ^ ExcursionBudget.oddCount rs < d * 2 ^ time rs)
    (hb : d * s * n + p * weight (charge s) rs ≤ p * s * n) : e < n :=
  drop_of_weighted_crossing h hn hs (charge_bound s) hp hc hb

/-- The improved ninths budget specializes to the existing first-half crossing. -/
theorem drop_of_first_half {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : 0 < n) (hp : ProperPrefixBound 2 1 rs)
    (hc : 2 * 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs)
    (hb : 2 * weight (charge 9) rs ≤ 9 * n) : e < n := by
  apply drop_of_crossing h hn (by decide : 0 < 9) hp (by simpa using hc)
  omega

/-- A genuine trace: `7 → 13 → 5`, stored in reverse chronological order. -/
def sevenRuns : List Run := [⟨1, 2⟩, ⟨3, 1⟩]

theorem seven_trace : Trace 7 5 sevenRuns := by
  apply Trace.step (v := 1) (u := 7) (W := 2) (x := 13)
  · exact Trace.step Trace.nil (by
      unfold ExcursionMap.IsExcursion
      decide : ExcursionMap.IsExcursion 7 3 1 1 13)
  · unfold ExcursionMap.IsExcursion
    decide

/-- At threshold `5/6`, the optimal budget passes while the old budget fails.
This compares the same trace, scale, and coefficient threshold. -/
theorem seven_strict_budget :
    ProperPrefixBound 6 5 sevenRuns ∧
    6 * 3 ^ ExcursionBudget.oddCount sevenRuns < 5 * 2 ^ time sevenRuns ∧
    5 * 9 * 7 + 6 * weight (charge 9) sevenRuns ≤ 6 * 9 * 7 ∧
    ¬ (5 * 9 * 7 + 6 * weight ninths sevenRuns ≤ 6 * 9 * 7) := by
  simp only [sevenRuns, ProperPrefixBound]
  decide

/-- The strengthened general theorem, rather than a direct numerical comparison,
certifies the endpoint of the genuine example trace. -/
theorem seven_drop_from_budget : (5 : Nat) < 7 := by
  obtain ⟨hp, hc, hb, _⟩ := seven_strict_budget
  exact drop_of_crossing seven_trace (by decide) (by decide : 0 < 9) hp hc hb

end Collatz.ExcursionCharge
