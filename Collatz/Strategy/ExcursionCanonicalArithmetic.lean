import Collatz.Strategy.BackwardRun
import Collatz.Strategy.ExcursionCanonicalCrossing
import Collatz.Strategy.ExcursionRealization

/-!
# An exact arithmetic target for first-crossing descent

The offset divided by the coefficient gap is the last source
that could fail to descend. If any genuine nontrivial source
of a contracting word fails, the canonical source also fails.
The canonical source one is handled by the trivial orbit.
-/

namespace Collatz.ExcursionRays

open Collatz.ExcursionBudget

/-- The greatest possible failing source for a contracting affine
profile, before imposing its residue constraint. -/
def failureCutoff (rs : List Run) : Nat :=
  offset rs / (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs)

theorem fails_iff_source_le_cutoff {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hcross : 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) :
    n ≤ e ↔ n ≤ failureCutoff rs := by
  let A := 3 ^ ExcursionBudget.oddCount rs
  let B := 2 ^ time rs
  let D := B - A
  have hD : 0 < D := Nat.sub_pos_iff_lt.mpr hcross
  have hB : 0 < B := Nat.two_pow_pos _
  have hsplit : A * n + n * D = B * n := by
    rw [Nat.mul_comm n D, ← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hcross)]
  have ha : A * n + offset rs = B * e := h.affine
  change n ≤ e ↔ n ≤ offset rs / D
  rw [Nat.le_div_iff_mul_le hD]
  constructor
  · intro hne
    have hm := Nat.mul_le_mul_left B hne
    omega
  · intro hm
    apply Nat.le_of_mul_le_mul_left _ hB
    rw [← ha, ← hsplit]
    exact Nat.add_le_add_left hm _

private theorem source_odd_of_nonempty {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hne : rs ≠ []) : n % 2 = 1 := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | @step x y v u W rs hpre hrun ih =>
    by_cases he : rs = []
    · subst rs
      cases hpre
      exact hrun.1
    · exact ih he

private theorem cutoff_of_canonical_source_one {rs : List Run} (hvalid : PositiveProfile rs)
    (hcross : 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) (hsource : canonicalSource rs = 1) :
    failureCutoff rs = 1 := by
  have h := canonical_trace_of_positive_profile hvalid
  have hbound := BackwardRun.accOrbit_small (time rs) 1 (by decide) (by decide)
  have hland := h.landing
  rw [hsource] at hland
  rw [hland] at hbound
  have hodd := (canonical_source_spec rs).2.1
  have he : canonicalLanding rs = 1 := by omega
  have ha := h.affine
  rw [hsource, he, Nat.mul_one, Nat.mul_one] at ha
  have hd : 2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs = offset rs := by omega
  unfold failureCutoff
  rw [← hd, Nat.div_self (Nat.sub_pos_iff_lt.mpr hcross)]

/-- An endpoint failure at some source greater than one exists
exactly when the canonical source is greater than one and fits
under the affine cutoff. -/
theorem nontrivial_failure_iff_canonical {rs : List Run} (hvalid : PositiveProfile rs)
    (hcross : 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) :
    (∃ n e, 1 < n ∧ Trace n e rs ∧ n ≤ e) ↔
      1 < canonicalSource rs ∧ canonicalSource rs ≤ failureCutoff rs := by
  have hcanon := canonical_trace_of_positive_profile hvalid
  constructor
  · rintro ⟨n, e, hn, ht, hkeep⟩
    have hcut := (fails_iff_source_le_cutoff ht hcross).mp hkeep
    cases rs with
    | nil => simp [ExcursionBudget.oddCount, time] at hcross
    | cons r rs =>
      have hm := (realizes_iff_canonical_source hvalid).mp ⟨e, ht⟩
      have hle : canonicalSource (r :: rs) ≤ n := hm ▸ Nat.mod_le n _
      refine ⟨?_, Nat.le_trans hle hcut⟩
      apply Nat.lt_of_not_ge
      intro hsmall
      have hodd := source_odd_of_nonempty hcanon (by simp)
      have he : canonicalSource (r :: rs) = 1 := by omega
      have hcutoff := cutoff_of_canonical_source_one hvalid hcross he
      omega
  · rintro ⟨hn, hcut⟩
    exact ⟨_, _, hn, hcanon, (fails_iff_source_le_cutoff hcanon hcross).mpr hcut⟩

private def properHeavyCheck : List Run → Bool
  | [] => true
  | _ :: rs => decide (2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs) && properHeavyCheck rs

private theorem properHeavyCheck_spec (rs : List Run) :
    properHeavyCheck rs = true ↔ ProperPrefixBound 1 1 rs := by
  induction rs with
  | nil => simp [properHeavyCheck, ProperPrefixBound]
  | cons r rs ih =>
    simp only [properHeavyCheck, Bool.and_eq_true, decide_eq_true_eq, ih,
      ProperPrefixBound, Nat.one_mul]

/-- Decide whether a proposed profile can fail at its first
coefficient crossing from some source greater than one. -/
def firstCrossingFailure (rs : List Run) : Bool :=
  rs.all (fun r => decide (0 < r.oddSteps ∧ 0 < r.halvings)) &&
    properHeavyCheck rs &&
    decide (3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) &&
    decide (1 < canonicalSource rs ∧ canonicalSource rs ≤ failureCutoff rs)

theorem firstCrossingFailure_spec (rs : List Run) :
    firstCrossingFailure rs = true ↔
      ProperPrefixBound 1 1 rs ∧ 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs ∧
        ∃ n e, 1 < n ∧ Trace n e rs ∧ n ≤ e := by
  simp only [firstCrossingFailure, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, properHeavyCheck_spec]
  constructor
  · rintro ⟨⟨⟨hv, hp⟩, hc⟩, hsrc⟩
    exact ⟨hp, hc, (nontrivial_failure_iff_canonical hv hc).mpr hsrc⟩
  · rintro ⟨hp, hc, n, e, hn, ht, hkeep⟩
    have hv : PositiveProfile rs := ht.runs_positive
    exact ⟨⟨⟨hv, hp⟩, hc⟩, (nontrivial_failure_iff_canonical hv hc).mp ⟨n, e, hn, ht, hkeep⟩⟩

/-- The arithmetic comparison still needed at the first
coefficient crossing of each positive profile. -/
def CanonicalOffsetDescent : Prop :=
  ∀ rs : List Run, PositiveProfile rs → ProperPrefixBound 1 1 rs →
    3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs → 1 < canonicalSource rs →
    failureCutoff rs < canonicalSource rs

/-- Checking only the canonical source is exactly sufficient for
first-crossing endpoint descent at all positive nontrivial sources. -/
theorem canonical_offset_descent_iff :
    CanonicalOffsetDescent ↔
      ∀ {n e : Nat} {rs : List Run}, 1 < n → Trace n e rs →
        ProperPrefixBound 1 1 rs → 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs → e < n := by
  constructor
  · intro hc n e rs hn ht hp hcross
    apply Nat.lt_of_not_ge
    intro hkeep
    have hv : PositiveProfile rs := ht.runs_positive
    obtain ⟨hn0, hcut⟩ := (nontrivial_failure_iff_canonical hv hcross).mp ⟨n, e, hn, ht, hkeep⟩
    exact Nat.not_le_of_gt (hc rs hv hp hcross hn0) hcut
  · intro h rs hv hp hcross hn
    apply Nat.lt_of_not_ge
    intro hcut
    have ht := canonical_trace_of_positive_profile hv
    exact Nat.not_le_of_gt (h hn ht hp hcross) ((fails_iff_source_le_cutoff ht hcross).mpr hcut)

/-- A canonical arithmetic proof and universal coverage would
settle the conjecture without a separate analytic power-gap input. -/
theorem collatz_of_coverage_and_canonical_offset (coverage : HasExcursionCoefficientCrossings)
    (canonical : CanonicalOffsetDescent) : CollatzConjecture := by
  apply Collatz.ExcursionMap.collatz_of_three_mod_four
  intro n hn hmod
  obtain ⟨e, rs, ht, hcross⟩ := coverage n hn hmod
  rcases ht.first_crossing_or_heavy with hh | ⟨f, earlier, hpre, hp, hc, _⟩
  · exact False.elim (Nat.not_le_of_gt hcross hh.1)
  · exact ⟨time earlier, hpre.landing.symm ▸ (canonical_offset_descent_iff.mp canonical hn hpre hp hc)⟩

end Collatz.ExcursionRays
