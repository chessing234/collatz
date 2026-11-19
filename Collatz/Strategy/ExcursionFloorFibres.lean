import Collatz.Strategy.ExcursionFloorMonotonicity
import Collatz.Strategy.ExcursionCrossingEquivalence
import Collatz.Strategy.ExcursionBudget

/-!
# At most one small realization of a crossing word

The odd exit of an excursion word doubles the spacing between its
source integers. If twice the coefficient gap exceeds the number
of excursions, any realization other than the least one is above
the explicit descent certificate cutoff. A common factor in the
total exponents makes this gap condition automatic.
-/

namespace Collatz.ExcursionBudget

open Collatz.ExcursionAnchor
open Collatz.ExcursionMap

private def chronologicalRuns (rs : List Run) : List (Nat × Nat) :=
  rs.reverse.map fun r => (r.oddSteps, r.halvings)

/-- A genuine excursion trace has two positive run lengths at
every letter. -/
theorem Trace.runs_positive {n x : Nat} {rs : List Run} (h : Trace n x rs) :
    ∀ r ∈ rs, 0 < r.oddSteps ∧ 0 < r.halvings := by
  induction h with
  | nil => simp
  | step _ hrun ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hrun.2.2.2.1, hrun.one_le_W⟩
    · exact ih r hr

private theorem Trace.chronological_positive {n x : Nat} {rs : List Run} (h : Trace n x rs) :
    ∀ r ∈ chronologicalRuns rs, 0 < r.1 ∧ 0 < r.2 := by
  intro r hr
  obtain ⟨run, hrun, rfl⟩ := List.mem_map.mp hr
  exact h.runs_positive run (List.mem_reverse.mp hrun)

theorem Trace.length_le_oddCount {n x : Nat} {rs : List Run} (h : Trace n x rs) :
    rs.length ≤ oddCount rs := by
  induction h with
  | nil => decide
  | @step x y v u W rs hpre hrun ih =>
    have hv := hrun.2.2.2.1
    simp only [List.length_cons, oddCount]
    omega

private theorem Trace.exit_odd {n x : Nat} {rs : List Run} (h : Trace n x rs) (hne : rs ≠ []) :
    x % 2 = 1 := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | step _ hrun => exact hrun.2.2.1

private theorem Trace.toOrbitWord {n x : Nat} {rs : List Run} (h : Trace n x rs) (floor : Nat) :
    OrbitWord floor n (wordAt floor (chronologicalRuns rs)) x (time rs)
      (3 ^ oddCount rs) (2 ^ time rs) := by
  induction h with
  | nil => exact .nil
  | @step x y v u W rs hpre hrun ih =>
    have hsingle : OrbitWord floor x [Edge.ofRun floor v W] y (v + W) (3 ^ v) (2 ^ (v + W)) := by
      have h := OrbitWord.cons (floor := floor) hrun (.nil (x := y))
      simpa using h
    have h := ih.append hsingle
    have hword : wordAt floor (chronologicalRuns (⟨v, W⟩ :: rs)) =
        wordAt floor (chronologicalRuns rs) ++ [Edge.ofRun floor v W] := by
      simp [chronologicalRuns, wordAt, List.reverse_cons]
    rw [hword, time, oddCount, Nat.pow_add, Nat.pow_add]
    simpa [Nat.add_comm, Nat.mul_comm] using h

/-- Distinct starts with the same genuine excursion word differ by a
multiple of twice its homogeneous denominator. -/
theorem Trace.same_word_source_dvd {n m x y : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) :
    2 * 2 ^ time rs ∣ m - n := by
  let A := 3 ^ oddCount rs
  let B := 2 ^ time rs
  have hx := h₁.exit_odd hne
  have hy := h₂.exit_odd hne
  have heven : 2 ∣ y - x := by omega
  have hdiff : A * (m - n) = B * (y - x) := by
    have h₁' := h₁.affine
    have h₂' := h₂.affine
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    change 3 ^ oddCount rs * m - 3 ^ oddCount rs * n =
      2 ^ time rs * y - 2 ^ time rs * x
    rw [← h₂', ← h₁', Nat.add_sub_add_right]
  have hd := Nat.mul_dvd_mul_left B heven
  rw [Nat.mul_comm B 2, ← hdiff] at hd
  have hpow : 2 * B = 2 ^ (time rs + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hcop : Nat.Coprime (2 * B) A := by
    rw [hpow]
    exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)
  exact hcop.dvd_of_dvd_mul_left hd

private theorem Trace.drop_of_gap_margin {n x : Nat} {rs : List Run} (h : Trace n x rs)
    (hmargin : 2 ^ time rs * rs.length < (2 ^ time rs - 3 ^ oddCount rs) * n) :
    ∃ k, k ≤ time rs ∧ Collatz.acceleratedOrbit k n < n := by
  have hlen : (chronologicalRuns rs).length = rs.length := by simp [chronologicalRuns]
  obtain ⟨best, hbest, hcross⟩ :=
    localMinimum_crosses_above_gap_size h.chronological_positive (by rwa [hlen])
  have hn : 0 < n := by
    cases n with
    | zero => simp at hmargin
    | succ n => omega
  exact (h.toOrbitWord n).drop_of_localMinimum hn hbest hcross

/-- When the coefficient gap is large enough, a word can leave
only its least genuine realization without a crossing certificate. -/
theorem Trace.larger_realization_descends {n m x y : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) (hnm : n < m)
    (hgap : rs.length < 2 * (2 ^ time rs - 3 ^ oddCount rs)) :
    ∃ k, k ≤ time rs ∧ Collatz.acceleratedOrbit k m < m := by
  let A := 3 ^ oddCount rs
  let B := 2 ^ time rs
  have hB : 0 < B := Nat.two_pow_pos _
  have hdiv := h₁.same_word_source_dvd h₂ hne
  have hdist : 2 * B ≤ m - n := Nat.le_of_dvd (by omega) hdiv
  have hupper : 2 * B ≤ m := by omega
  have hmargin : B * rs.length < (B - A) * m := by
    calc
      _ < B * (2 * (B - A)) := Nat.mul_lt_mul_of_pos_left hgap hB
      _ = (B - A) * (2 * B) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ hupper
  exact h₂.drop_of_gap_margin hmargin

/-- The index of any unresolved realization is bounded by its length
and coefficient gap. The index counts full source periods from an
earlier realization. -/
theorem Trace.index_bound_of_no_drop {n m x y : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) (hnm : n ≤ m)
    (hno : ¬ ∃ j, j ≤ time rs ∧ Collatz.acceleratedOrbit j m < m) :
    ∃ index : Nat, m - n = (2 * 2 ^ time rs) * index ∧
      (2 * (2 ^ time rs - 3 ^ oddCount rs)) * index ≤ rs.length := by
  let B := 2 ^ time rs
  let gap := B - 3 ^ oddCount rs
  obtain ⟨index, hi⟩ := h₁.same_word_source_dvd h₂ hne
  change m - n = (2 * B) * index at hi
  have hplus : n + (2 * B) * index = m := by
    rw [← hi, Nat.add_sub_of_le hnm]
  have hsize : (2 * B) * index ≤ m := by omega
  have hnot : ¬ B * rs.length < gap * m := fun h => hno (h₂.drop_of_gap_margin h)
  have hbudget := Nat.le_of_not_gt hnot
  have hscale := Nat.mul_le_mul_left gap hsize
  have hfull : B * ((2 * gap) * index) ≤ B * rs.length := by
    calc
      _ = gap * ((2 * B) * index) := by ac_rfl
      _ ≤ gap * m := hscale
      _ ≤ _ := hbudget
  exact ⟨index, hi, (Nat.mul_le_mul_left_iff (Nat.two_pow_pos (time rs))).mp hfull⟩


private theorem two_gap_gt_exponent {u v d : Nat} (hd : 1 < d)
    (hcross : (3 ^ u) ^ d < (2 ^ v) ^ d) :
    d * u < 2 * ((2 ^ v) ^ d - (3 ^ u) ^ d) := by
  let X := 3 ^ u
  let Y := 2 ^ v
  have hXY : X < Y := by
    apply Nat.lt_of_not_ge
    intro h
    exact (Nat.not_le_of_gt hcross) (Nat.pow_le_pow_left h d)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hterm : X ^ k ≤ Y ^ (k + 1) - X ^ (k + 1) := by
    have hpower : X ^ k ≤ Y ^ k := Nat.pow_le_pow_left (Nat.le_of_lt hXY) _
    have hsum : X ^ (k + 1) + X ^ k ≤ Y ^ (k + 1) := by
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        _ = X ^ k * (X + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ _ := Nat.mul_le_mul hpower hXY
    omega
  have hsmall : u * k < X ^ k := by
    change u * k < (3 ^ u) ^ k
    rw [← Nat.pow_mul]
    exact Nat.lt_of_lt_of_le (Collatz.Arith.lt_two_pow_self _)
      (Collatz.Arith.two_pow_le_three_pow _)
  have hlength : (k + 1) * u ≤ 2 * (u * k) := by
    have h := Nat.mul_le_mul_right u (show k + 1 ≤ 2 * k by omega)
    rwa [Nat.mul_assoc, Nat.mul_comm k u] at h
  change (k + 1) * u < 2 * (Y ^ (k + 1) - X ^ (k + 1))
  omega

/-- A common divisor of the total odd and accelerated step counts
forces the gap condition for every nonminimal realization. -/
theorem Trace.larger_realization_descends_of_common_exponent {n m x y d : Nat} {rs : List Run}
    (h₁ : Trace n x rs) (h₂ : Trace m y rs) (hne : rs ≠ []) (hnm : n < m)
    (hd : 1 < d) (hOdd : d ∣ oddCount rs) (hTime : d ∣ time rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) :
    ∃ k, k ≤ time rs ∧ Collatz.acceleratedOrbit k m < m := by
  obtain ⟨u, hu⟩ := hOdd
  obtain ⟨v, hv⟩ := hTime
  have hA : 3 ^ oddCount rs = (3 ^ u) ^ d := by rw [hu, Nat.mul_comm d u, Nat.pow_mul]
  have hB : 2 ^ time rs = (2 ^ v) ^ d := by rw [hv, Nat.mul_comm d v, Nat.pow_mul]
  have hpow : (3 ^ u) ^ d < (2 ^ v) ^ d := by rwa [← hA, ← hB]
  have hgap := two_gap_gt_exponent hd hpow
  rw [← hu, ← hA, ← hB] at hgap
  exact h₁.larger_realization_descends h₂ hne hnm (Nat.lt_of_le_of_lt h₁.length_le_oddCount hgap)

private def runs11 : List Run := [⟨1, 2⟩, ⟨2, 1⟩]

/-- The first crossing from 11 and its lift by one source period
share both excursions. Their total exponents have common divisor
three, so the larger start descends by the lifted certificate. -/
theorem lifted_descent_139 :
    ∃ k, k ≤ 6 ∧ Collatz.acceleratedOrbit k 139 < 139 := by
  have h11 : Trace 11 5 runs11 :=
    .step (.step .nil (show IsExcursion 11 2 3 1 13 by unfold IsExcursion; decide))
      (show IsExcursion 13 1 7 2 5 by unfold IsExcursion; decide)
  have h139 : Trace 139 59 runs11 :=
    .step (.step .nil (show IsExcursion 139 2 35 1 157 by unfold IsExcursion; decide))
      (show IsExcursion 157 1 79 2 59 by unfold IsExcursion; decide)
  exact h11.larger_realization_descends_of_common_exponent (d := 3) h139
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Collatz.ExcursionBudget
