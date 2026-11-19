import Collatz.Strategy.ExcursionPowerGap
import Collatz.Strategy.ExcursionRays

/-!
# Only canonical sources can miss the final descent

For a contracting excursion word the last halving run sharpens
the affine offset bound. A sufficient integer power gap gives
descent at every source at least as large as the tripling
coefficient. Any possible failure is therefore canonical.
-/

namespace Collatz.ExcursionBudget

open Collatz.ExcursionPowerGap

/-- The endpoint gap beats the last-run offset at sources at
least the tripling coefficient. -/
theorem Trace.endpoint_drop_of_coefficient_and_gap {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hcoef : 3 ^ oddCount rs < 2 ^ time rs)
    (hsize : 3 ^ oddCount rs ≤ n)
    (hgap : 3 ^ oddCount rs ≤ 2 ^ (oddCount rs + 1) * (2 ^ time rs - 3 ^ oddCount rs)) :
    e < n := by
  by_cases hlow : n < 2 ^ time rs
  · have hcut : n < 2 ^ time rs * 1 := by simpa only [Nat.mul_one] using hlow
    have he : e < 3 ^ oddCount rs := by
      simpa only [Nat.mul_one] using Collatz.ExcursionRays.endpoint_lt_of_source_lt_multiple h hcut
    exact Nat.lt_of_lt_of_le he hsize
  · have hlarge := Nat.le_of_not_gt hlow
    cases h with
    | nil => simp [oddCount, time] at hcoef
    | @step x y v u W rs hpre hrun =>
      apply Collatz.ExcursionRays.drop_of_terminal_gap_and_size (.step hpre hrun) hlarge
      rw [Nat.pow_succ, Nat.mul_assoc] at hgap
      refine Nat.le_trans hgap (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hrun.one_le_W

/-- A genuine coefficient crossing uses at least one odd step. -/
theorem Trace.odd_count_pos_of_crossing {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hcoef : 3 ^ oddCount rs < 2 ^ time rs) : 0 < oddCount rs := by
  cases h with
  | nil => simp [oddCount, time] at hcoef
  | step _ hrun =>
    have hv := hrun.2.2.2.1
    simp only [oddCount]
    omega

/-- For fewer than 6,291 odd steps, failure at the last landing
requires a source strictly below the tripling coefficient. -/
theorem Trace.endpoint_drop_of_coefficient_of_odd_lt {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hcoef : 3 ^ oddCount rs < 2 ^ time rs)
    (hodd : oddCount rs < 6291) (hsource : 3 ^ oddCount rs ≤ n) :
    e < n :=
  h.endpoint_drop_of_coefficient_and_gap hcoef hsource
    (endpoint_gap_of_odd_lt (h.odd_count_pos_of_crossing hcoef) hodd hcoef)

/-- The large-exponent estimate extends the final-landing conclusion
to all sources at least the tripling coefficient. -/
theorem Trace.endpoint_drop_of_coefficient (tail : LargeEndpointGap)
    {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hcoef : 3 ^ oddCount rs < 2 ^ time rs) (hsource : 3 ^ oddCount rs ≤ n) :
    e < n :=
  h.endpoint_drop_of_coefficient_and_gap hcoef hsource
    (endpoint_gap_of_tail tail (h.odd_count_pos_of_crossing hcoef) hcoef)

/-- A finite trace either has no coefficient crossing, or contains
a first crossing with every proper prefix still heavy. -/
theorem Trace.first_crossing_or_heavy {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    (2 ^ time rs ≤ 3 ^ oddCount rs ∧ ProperPrefixBound 1 1 rs) ∨
      ∃ f earlier, Trace n f earlier ∧ ProperPrefixBound 1 1 earlier ∧
        3 ^ oddCount earlier < 2 ^ time earlier ∧ time earlier ≤ time rs := by
  induction h with
  | nil =>
    exact Or.inl ⟨by decide, trivial⟩
  | @step x y v u W rs hpre hrun ih =>
    rcases ih with hheavy | ⟨f, earlier, ht, hp, hc, htime⟩
    · have hp : ProperPrefixBound 1 1 (⟨v, W⟩ :: rs) := by
        refine ⟨?_, hheavy.2⟩
        simpa only [Nat.one_mul] using hheavy.1
      by_cases hcoef : 3 ^ oddCount (⟨v, W⟩ :: rs) < 2 ^ time (⟨v, W⟩ :: rs)
      · exact Or.inr ⟨y, _, .step hpre hrun, hp, hcoef, Nat.le_refl _⟩
      · exact Or.inl ⟨Nat.le_of_not_gt hcoef, hp⟩
    · exact Or.inr ⟨f, earlier, ht, hp, hc, Nat.le_trans htime (Nat.le_add_left _ _)⟩

/-- The outstanding coverage condition for this approach. -/
def HasExcursionCoefficientCrossings : Prop :=
  ∀ n : Nat, 1 < n → n % 4 = 3 →
    ∃ e rs, Trace n e rs ∧ 3 ^ oddCount rs < 2 ^ time rs

/-- The outstanding final-landing condition, restricted to sources
below the tripling coefficient of a first-crossing word. -/
def CanonicalFirstCrossingDrop : Prop :=
  ∀ {n e : Nat} {rs : List Run}, 1 < n → Trace n e rs →
    ProperPrefixBound 1 1 rs → 3 ^ oddCount rs < 2 ^ time rs →
    n < 3 ^ oddCount rs → e < n

/-- Universal coefficient coverage and canonical first-crossing
descent suffice for Collatz, given the analytic power-gap tail. -/
theorem collatz_of_canonical_first_crossings (tail : LargeEndpointGap)
    (coverage : HasExcursionCoefficientCrossings) (canonical : CanonicalFirstCrossingDrop) :
    CollatzConjecture := by
  apply Collatz.ExcursionMap.collatz_of_three_mod_four
  intro n hn hmod
  obtain ⟨e, rs, htrace, hcoef⟩ := coverage n hn hmod
  rcases htrace.first_crossing_or_heavy with hheavy | ⟨f, first, ht, hp, hc, _⟩
  · exact False.elim ((Nat.not_le_of_gt hcoef) hheavy.1)
  · have hdrop : f < n := by
      by_cases hsource : n < 3 ^ oddCount first
      · exact canonical hn ht hp hc hsource
      · exact ht.endpoint_drop_of_coefficient tail hc (Nat.le_of_not_gt hsource)
    exact ⟨time first, ht.landing.symm ▸ hdrop⟩

end Collatz.ExcursionBudget
