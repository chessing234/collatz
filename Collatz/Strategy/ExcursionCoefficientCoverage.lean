import Collatz.Exploration.HalvingBlocks
import Collatz.Strategy.ExcursionCanonicalCrossing
import Collatz.Strategy.ExcursionCrossingEquivalence
import Collatz.Strategy.FirstLightBasics
import Collatz.Strategy.OrbitCapacity
import Collatz.Strategy.TwoRunOrder

/-!
# Coefficient coverage is equivalent to ruling out divergent orbits

A coefficient crossing at any shortcut step extends to a crossing
at an excursion boundary, since an excursion's smallest coefficient
occurs at one of its two ends. Repeated shortcut states supply a
contracting period. Conversely, if every odd state has a crossing,
concatenating them gives arbitrarily late multipliers at most one.
That contradicts multiplier escape on an injective orbit.
-/

namespace Collatz.ExcursionBudget

open Collatz.ExcursionMap

private theorem even_count_zero {x r : Nat}
    (h : ∀ i, i < r → acceleratedOrbit i x % 2 = 0) : Collatz.oddCount x r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Density.oddCount_succ_last, ih (fun i hi => h i (by omega)), h r (by omega)]

private theorem excursion_count_before {x v u W y j : Nat} (h : IsExcursion x v u W y)
    (hj : j ≤ v) : Collatz.oddCount x j = j := by
  have hf : OddRuns.OddRun x v := (OddRuns.oddRun_iff v x).mpr ⟨u, h.2.2.2.2.2.1⟩
  exact TwoRunOrder.oddCount_oddRun (fun i hi => hf i (Nat.lt_of_lt_of_le hi hj))

private theorem excursion_count_after {x v u W y r : Nat} (h : IsExcursion x v u W y)
    (hr : r ≤ W) : Collatz.oddCount x (v + r) = v := by
  have hp : acceleratedOrbit v x = 2 ^ W * y := by
    rw [peak_eq h, h.2.2.2.2.2.2, Nat.add_sub_cancel]
  have he := even_orbit_of_val2 h.2.2.1 hp
  have hzero := even_count_zero (fun i hi => he i (Nat.lt_of_lt_of_le hi hr))
  rw [AccumulatorArith.oddCount_add, excursion_count_before h (Nat.le_refl _), hzero, Nat.add_zero]

/-- Excursion odd counts agree with the shortcut odd counts at their
boundary times. -/
theorem Trace.shortcut_odd_count {n y : Nat} {rs : List Run} (h : Trace n y rs) :
    Collatz.oddCount n (time rs) = oddCount rs := by
  induction h with
  | nil => rfl
  | @step x y v u W rs hpre hrun ih =>
    simp only [time, oddCount]
    rw [Nat.add_comm (v + W), AccumulatorArith.oddCount_add, hpre.landing, ih,
      excursion_count_after hrun (Nat.le_refl _), Nat.add_comm]

private theorem excursion_inner_heavy {A B x v u W y j : Nat} (h : IsExcursion x v u W y)
    (hstart : B ≤ A) (hend : B * 2 ^ (v + W) ≤ A * 3 ^ v) (hj : j ≤ v + W) :
    B * 2 ^ j ≤ A * 3 ^ Collatz.oddCount x j := by
  by_cases hle : j ≤ v
  · rw [excursion_count_before h hle]
    exact Nat.mul_le_mul hstart (Collatz.Arith.two_pow_le_three_pow j)
  · let r := j - v
    have hr : r ≤ W := by dsimp [r]; omega
    have hsplit : v + r = j := by dsimp [r]; omega
    rw [← hsplit, excursion_count_after h hr]
    exact Nat.le_trans
      (Nat.mul_le_mul_left B (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))) hend

/-- If every complete excursion prefix is heavy, all intervening
shortcut prefixes are heavy as well. -/
theorem Trace.shortcut_heavy_of_boundary_heavy {n y : Nat} {rs : List Run}
    (h : Trace n y rs) (hfull : 2 ^ time rs ≤ 3 ^ oddCount rs) (hproper : ProperPrefixBound 1 1 rs) :
    ∀ k, k ≤ time rs → 2 ^ k ≤ 3 ^ Collatz.oddCount n k := by
  induction h with
  | nil =>
    intro k hk
    have he : k = 0 := by simpa [time] using hk
    subst k
    change 1 ≤ 1
    exact Nat.le_refl _
  | @step x y v u W rs hpre hrun ih =>
    intro k hk
    have hpreFull : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    by_cases hle : k ≤ time rs
    · exact ih hpreFull hproper.2 k hle
    · let j := k - time rs
      have hsplit : time rs + j = k := by dsimp [j]; omega
      have hj : j ≤ v + W := by
        simp only [time] at hk
        dsimp [j]
        omega
      have hend : 2 ^ time rs * 2 ^ (v + W) ≤ 3 ^ oddCount rs * 3 ^ v := by
        simpa only [time, oddCount, Nat.pow_add, Nat.mul_comm] using hfull
      have hlocal := excursion_inner_heavy hrun hpreFull hend hj
      rw [← hsplit, Nat.pow_add, AccumulatorArith.oddCount_add, hpre.landing,
        hpre.shortcut_odd_count, Nat.pow_add]
      exact hlocal

/-- The first shortcut crossing of a first-crossing excursion word
occurs during its terminal halving run. It has the same odd count
as the whole word, and its value is at least the final landing. -/
theorem Trace.first_light_of_first_crossing {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) :
    ∃ k, k ≤ time rs ∧ FirstLightDescent.FirstLight n k ∧
      Collatz.oddCount n k = oddCount rs ∧ e ≤ acceleratedOrbit k n := by
  have hl : 3 ^ Collatz.oddCount n (time rs) < 2 ^ time rs := by
    rwa [h.shortcut_odd_count]
  obtain ⟨k, hk, hfirst⟩ := FirstLightDescent.least_light_prefix n (time rs) hl
  refine ⟨k, hk, hfirst, ?_⟩
  cases h with
  | nil => simp [time, oddCount] at hcross
  | @step x _ v u W rs hpre hrun =>
    have hfull : 2 ^ time rs ≤ 3 ^ oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have hbefore : time rs < k := by
      apply Nat.lt_of_not_ge
      intro hle
      exact Nat.not_le_of_gt hfirst.1
        (hpre.shortcut_heavy_of_boundary_heavy hfull hproper.2 k hle)
    let j := k - time rs
    have hj : time rs + j = k := Nat.add_sub_of_le (Nat.le_of_lt hbefore)
    have hcount : Collatz.oddCount n k =
        oddCount rs + Collatz.oddCount x j := by
      rw [← hj, AccumulatorArith.oddCount_add, hpre.landing, hpre.shortcut_odd_count]
    have hpeak_before : v < j := by
      apply Nat.lt_of_not_ge
      intro hle
      have hheavy : 2 ^ k ≤ 3 ^ Collatz.oddCount n k := by
        calc
          _ = 2 ^ time rs * 2 ^ j := by rw [← hj, Nat.pow_add]
          _ ≤ 3 ^ oddCount rs * 3 ^ j :=
            Nat.mul_le_mul hfull (Collatz.Arith.two_pow_le_three_pow j)
          _ = _ := by rw [hcount, excursion_count_before hrun hle, Nat.pow_add]
      exact Nat.not_le_of_gt hfirst.1 hheavy
    let r := j - v
    have hr : r ≤ W := by
      simp only [time] at hk
      dsimp [r, j]
      omega
    have hpart : v + r = j := Nat.add_sub_of_le (Nat.le_of_lt hpeak_before)
    constructor
    · rw [hcount, ← hpart, excursion_count_after hrun hr]
      simp only [oddCount, Nat.add_comm]
    · have hpeak : acceleratedOrbit v x = 2 ^ W * e := by
        rw [peak_eq hrun, hrun.2.2.2.2.2.2, Nat.add_sub_cancel]
      have hland : acceleratedOrbit k n = acceleratedOrbit r (2 ^ W * e) := by
        rw [← hj, Nat.add_comm (time rs), ← acceleratedOrbit_add, hpre.landing,
          ← hpart, Nat.add_comm v, ← acceleratedOrbit_add, hpeak]
      have hsplit : 2 ^ W * e = 2 ^ r * (2 ^ (W - r) * e) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hr]
      rw [hland, hsplit, Collatz.Exploration.HalvingBlocks.accelerated_halving]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

/-- An odd source has a genuine trace of any prescribed number of
excursions. Each excursion takes at least two shortcut steps. -/
theorem trace_of_length (n : Nat) (hn : n % 2 = 1) (j : Nat) :
    ∃ y rs, Trace n y rs ∧ rs.length = j ∧ 2 * j ≤ time rs ∧ y % 2 = 1 := by
  induction j with
  | zero => exact ⟨n, [], .nil, rfl, Nat.zero_le _, hn⟩
  | succ j ih =>
    obtain ⟨x, rs, ht, hlen, htime, hx⟩ := ih
    obtain ⟨v, u, W, y, hstep⟩ := exists_excursion hx
    have hv := hstep.2.2.2.1
    have hw := hstep.one_le_W
    refine ⟨y, _, .step ht hstep, by simp [hlen], ?_, hstep.2.2.1⟩
    simp only [time]
    omega

/-- Any shortcut coefficient crossing from an odd start yields an
excursion coefficient crossing. -/
theorem crossing_of_shortcut_crossing {n k : Nat} (hn : n % 2 = 1)
    (hcross : 3 ^ Collatz.oddCount n k < 2 ^ k) :
    ∃ y rs, Trace n y rs ∧ 3 ^ oddCount rs < 2 ^ time rs := by
  obtain ⟨y, rs, htrace, _, htime, _⟩ := trace_of_length n hn k
  have hk : k ≤ time rs := by omega
  rcases htrace.first_crossing_or_heavy with hheavy | ⟨e, first, hfirst, _, hcoef, _⟩
  · exact False.elim ((Nat.not_le_of_gt hcross)
      (htrace.shortcut_heavy_of_boundary_heavy hheavy.1 hheavy.2 k hk))
  · exact ⟨e, first, hfirst, hcoef⟩

private def slope (n k : Nat) : Rat :=
  ((3 ^ Collatz.oddCount n k : Nat) : Rat) / ((2 ^ k : Nat) : Rat)

private theorem slope_pos (n k : Nat) : 0 < slope n k := by
  unfold slope
  rw [Rat.div_def]
  exact Rat.mul_pos (Rat.natCast_pos.mpr (Nat.pow_pos (by decide)))
    (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.two_pow_pos k)))

private theorem slope_lt_one_iff {n k : Nat} :
    slope n k < 1 ↔ 3 ^ Collatz.oddCount n k < 2 ^ k := by
  unfold slope
  rw [Rat.div_lt_iff (Rat.natCast_pos.mpr (Nat.two_pow_pos k)), Rat.one_mul,
    Rat.natCast_lt_natCast]

private theorem one_lt_slope_iff {n k : Nat} :
    1 < slope n k ↔ 2 ^ k < 3 ^ Collatz.oddCount n k := by
  unfold slope
  rw [Rat.lt_div_iff (Rat.natCast_pos.mpr (Nat.two_pow_pos k)), Rat.one_mul,
    Rat.natCast_lt_natCast]

private theorem slope_add (n j k : Nat) :
    slope n (j + k) = slope n j * slope (acceleratedOrbit j n) k := by
  simp only [slope, AccumulatorArith.oddCount_add, Nat.pow_add, Rat.natCast_mul,
    Rat.div_def, Rat.inv_mul_rev]
  grind

private theorem slope_period_power {x L : Nat} (h : acceleratedOrbit L x = x) (j : Nat) :
    slope x (L * j) = slope x L ^ j := by
  induction j with
  | zero =>
    have he : L * 0 = 0 := Nat.mul_zero _
    rw [he, Rat.pow_zero]
    exact (by decide +kernel : (1 : Rat) / 1 = 1)
  | succ j ih =>
    rw [Nat.mul_succ, Nat.add_comm (L * j), slope_add, h, ih, Rat.pow_succ, Rat.mul_comm]

/-- A repeated shortcut state supplies a contracting period, which
eventually outweighs the coefficient of the initial segment. -/
theorem shortcut_crossing_of_repeat {n i j : Nat} (hn : 0 < n) (hij : i < j)
    (hrep : acceleratedOrbit i n = acceleratedOrbit j n) :
    ∃ k, 3 ^ Collatz.oddCount n k < 2 ^ k := by
  let x := acceleratedOrbit i n
  let L := j - i
  have htime : L + i = j := by dsimp [L]; omega
  have hperiod : acceleratedOrbit L x = x := by
    change acceleratedOrbit L (acceleratedOrbit i n) = acceleratedOrbit i n
    rw [acceleratedOrbit_add, htime, hrep]
  have hcycle : AccCycle.AccIsCycleOf x L := ⟨by dsimp [L]; omega, hperiod⟩
  have hx : 0 < x := acceleratedOrbit_positive hn i
  have hsmall := (slope_lt_one_iff).mpr (AccCycle.accCycle_bounds hx hcycle).2.2
  obtain ⟨q, hq⟩ := Collatz.ExcursionAnchor.eventually_scaled_lt_one (slope_pos x L)
    hsmall (slope n i)
  refine ⟨i + L * q, (slope_lt_one_iff).mp ?_⟩
  rw [slope_add, slope_period_power hperiod q]
  exact hq

private theorem coverage_all_odd (coverage : HasExcursionCoefficientCrossings)
    {n : Nat} (hn : n % 2 = 1) :
    ∃ y rs, Trace n y rs ∧ 3 ^ oddCount rs < 2 ^ time rs := by
  by_cases hmod : n % 4 = 3
  · exact coverage n (by omega) hmod
  · obtain ⟨v, u, W, y, h⟩ := exists_excursion hn
    have hv : v = 1 := (v_eq_one_iff h).mpr (by omega)
    subst v
    have hw := h.one_le_W
    have hcoef : 3 ^ oddCount [⟨1, W⟩] < 2 ^ time [⟨1, W⟩] := by
      change 3 ^ 1 < 2 ^ (1 + W + 0)
      exact Nat.lt_of_lt_of_le (by decide : 3 ^ 1 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact ⟨y, _, .step .nil h, hcoef⟩

private theorem arbitrarily_late_small_slope (coverage : HasExcursionCoefficientCrossings)
    {n : Nat} (hn : n % 2 = 1) (H : Nat) :
    ∃ k, H ≤ k ∧ acceleratedOrbit k n % 2 = 1 ∧ slope n k ≤ 1 := by
  induction H with
  | zero =>
    refine ⟨0, Nat.zero_le _, hn, ?_⟩
    exact (by decide +kernel : (1 : Rat) / 1 ≤ 1)
  | succ H ih =>
    obtain ⟨k, hk, hodd, hsmall⟩ := ih
    obtain ⟨y, rs, ht, hc⟩ := coverage_all_odd coverage hodd
    have hr : rs ≠ [] := by
      intro he
      subst rs
      simp [time, oddCount] at hc
    have htime : 0 < time rs := by
      cases ht with
      | nil => exact False.elim (hr rfl)
      | step _ hstep =>
        have hv := hstep.2.2.2.1
        simp only [time]
        omega
    have hy : y % 2 = 1 := by
      cases ht with
      | nil => exact False.elim (hr rfl)
      | step _ hstep => exact hstep.2.2.1
    have hlocal : slope (acceleratedOrbit k n) (time rs) < 1 := by
      apply slope_lt_one_iff.mpr
      rwa [ht.shortcut_odd_count]
    refine ⟨k + time rs, by omega, ?_, ?_⟩
    · rw [Nat.add_comm, ← acceleratedOrbit_add, ht.landing]
      exact hy
    · rw [slope_add]
      have hnonneg := Rat.le_of_lt (slope_pos (acceleratedOrbit k n) (time rs))
      have hs := Rat.mul_le_mul_of_nonneg_right hsmall hnonneg
      rw [Rat.one_mul] at hs
      exact Rat.le_trans hs (Rat.le_of_lt hlocal)

/-- Universal excursion coefficient coverage is exactly the absence
of an injective shortcut orbit from a positive odd start. -/
theorem excursion_coverage_iff_no_injective_odd :
    HasExcursionCoefficientCrossings ↔
      ∀ n : Nat, n % 2 = 1 →
        ¬ (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) := by
  constructor
  · intro coverage n hn hinj
    have hp : 0 < n := by omega
    obtain ⟨H, hH⟩ := OrbitCapacity.multiplier_escapes hp hinj 1
    obtain ⟨k, hk, _, hsmall⟩ := arbitrarily_late_small_slope coverage hn H
    have h := hH k hk
    rw [Nat.one_mul] at h
    exact ((Rat.not_lt).mpr hsmall) (one_lt_slope_iff.mpr h)
  · intro hno n hn hmod
    have hodd : n % 2 = 1 := by omega
    have hex : ∃ i j : Nat, i ≠ j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
      apply Classical.byContradiction
      intro h
      apply hno n hodd
      intro i j he
      apply Classical.byContradiction
      intro hne
      exact h ⟨i, j, hne, he⟩
    obtain ⟨i, j, hne, he⟩ := hex
    have hp : 0 < n := by omega
    have hc : ∃ k, 3 ^ Collatz.oddCount n k < 2 ^ k := by
      by_cases hij : i < j
      · exact shortcut_crossing_of_repeat hp hij he
      · exact shortcut_crossing_of_repeat hp (by omega : j < i) he.symm
    obtain ⟨k, hk⟩ := hc
    exact crossing_of_shortcut_crossing hodd hk

end Collatz.ExcursionBudget
