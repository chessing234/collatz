import Collatz.Strategy.PeakSuffixTable
import Collatz.Strategy.TwoRunOrder
import Collatz.Strategy.BoundedEvenDefect

/-!
# Ternary divisibility constrains meetings during an odd prefix

A smaller source joining a full odd prefix must use more extra odd
steps than the target start's ternary valuation. The affine offset
after stripping the long ternary part would otherwise give a
nonnegative preimage too small to carry the required odd steps.
-/

namespace Collatz.OddPrefixValuation

open Collatz.AffineExact Collatz.OddRuns Collatz.SynchronousClasses

private theorem affineC_le_full_odd (x i : Nat) : affineC i x + 2 ^ i ≤ 3 ^ i := by
  have ha := oddCount_le_self x i
  calc
    _ ≤ 2 ^ (i - oddCount x i) * 3 ^ oddCount x i := affineC_le x i
    _ ≤ 3 ^ (i - oddCount x i) * 3 ^ oddCount x i :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by rw [← Nat.pow_add, Nat.sub_add_cancel ha]

private theorem full_odd_fiber {i n z : Nat} (hodd : OddRun n i)
    (h : acceleratedOrbit i z = acceleratedOrbit i n) :
    ∃ c, c < 3 ^ (i - oddCount z i) ∧ z = 3 ^ (i - oddCount z i) * n + c := by
  let b := oddCount z i
  let C := affineC i n - affineC i z
  have hC₁ := TwoRunOrder.affineC_oddRun i n hodd
  have hC₂ := affineC_le_full_odd z i
  have hC : affineC i z + C = affineC i n := by dsimp only [C]; omega
  have hz := affine_exact z i
  have hn := affine_exact n i
  rw [h] at hz
  rw [TwoRunOrder.oddCount_oddRun hodd] at hn
  have heq : 3 ^ b * z = 3 ^ i * n + C := by
    change 2 ^ i * acceleratedOrbit i n = 3 ^ b * z + affineC i z at hz
    omega
  have hp : 3 ^ i = 3 ^ b * 3 ^ (i - b) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (oddCount_le_self z i)]
  have hd : 3 ^ b ∣ C := by
    have hs : 3 ^ b ∣ 3 ^ i * n := by rw [hp, Nat.mul_assoc]; exact Nat.dvd_mul_right _ _
    have ht : 3 ^ b ∣ 3 ^ i * n + C := by rw [← heq]; exact Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_iff_right hs).mpr ht
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < 3 ^ b := Nat.pow_pos (by decide)
  have hbound : c < 3 ^ (i - b) := by
    apply Nat.lt_of_mul_lt_mul_left (a := 3 ^ b)
    rw [← hc, ← hp]
    dsimp only [C]
    have h2 := Nat.two_pow_pos i
    omega
  refine ⟨c, hbound, Nat.mul_left_cancel hpos ?_⟩
  rw [heq, hp, hc, Nat.mul_add, Nat.mul_assoc]

/-- The smaller source must spend more odd steps than the original
run by an amount exceeding any power of three dividing the start. -/
theorem excess_odd_steps_exceed_valuation {i s n m : Nat} (hodd : OddRun n i)
    (hsmall : m < n) (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    ¬ 3 ^ (oddCount m (i + s) - i) ∣ n := by
  intro hdiv
  let z := acceleratedOrbit s m
  let a := oddCount m s
  let b := oddCount z i
  let g := 3 ^ (i - b)
  have htail : acceleratedOrbit i z = acceleratedOrbit i n := by
    simpa only [z, acceleratedOrbit_add] using hmeet
  obtain ⟨c, hcg, hzc⟩ := full_odd_fiber hodd htail
  change c < g at hcg
  change z = g * n + c at hzc
  have hcount : oddCount m (i + s) = a + b := by
    rw [Nat.add_comm i s, AccumulatorArith.oddCount_add]
  have hscale : 3 ^ a ∣ g * n := by
    rw [hcount] at hdiv
    have hd := Nat.mul_dvd_mul (Nat.dvd_refl g) hdiv
    dsimp only [g] at hd
    rw [← Nat.pow_add] at hd
    exact Nat.dvd_trans (Nat.pow_dvd_pow 3 (by omega)) hd
  obtain ⟨q, hq⟩ := hscale
  have htarget : z = 3 ^ a * q + c := by rw [hzc, hq]
  let D := 2 ^ s
  let r := m % D
  have hr : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit : D * (m / D) + r = m := Nat.div_add_mod _ _
  have hprofile : oddCount r s = a := (Density.oddCount_mod m s).symm
  have himage := (orbit_target_iff hr).mp (congrArg (acceleratedOrbit s) hsplit)
  change z % 3 ^ oddCount r s = acceleratedOrbit s r ∧ z / 3 ^ oddCount r s = m / D at himage
  rw [hprofile] at himage
  have hpos : 0 < 3 ^ a := Nat.pow_pos (by decide)
  have hquot : m / D = q + c / 3 ^ a := by
    rw [← himage.2, htarget, Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.add_comm]
  have hlow : D * q ≤ m := by
    have h := Nat.mul_le_mul_left D (Nat.le_add_right q (c / 3 ^ a))
    rw [← hquot] at h
    omega
  have hgain : D * g < 3 ^ a := by
    have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_le_of_lt hlow hsmall) hpos
    rw [Nat.mul_left_comm, ← hq, ← Nat.mul_assoc] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hcSmall : D * c < 3 ^ a :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hcg (Nat.two_pow_pos _)) hgain
  have hc : c < 3 ^ a :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)) hcSmall
  have hrc : acceleratedOrbit s r = c := by
    rw [← himage.1, htarget, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  have hres := affine_exact r s
  rw [hrc, hprofile] at hres
  have hrz : r = 0 := by
    by_cases hp : 0 < r
    · have hb := Nat.le_mul_of_pos_right (3 ^ a) hp
      change 2 ^ s * c < 3 ^ a at hcSmall
      omega
    · omega
  rw [Nat.div_eq_of_lt hc, Nat.add_zero] at hquot
  have hm : m = 2 ^ s * q := by rw [hquot, hrz, Nat.add_zero] at hsplit; exact hsplit.symm
  have hzq : z = q := by
    change acceleratedOrbit s m = q
    rw [hm, orbit_halvings]
  have hzge : n ≤ z := by
    rw [hzc]
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide) : 0 < g))
      (Nat.le_add_right _ _)
  have hzle : z ≤ m := by
    rw [hzq, hm]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)
  omega

/-- A smaller source reaching an odd-prefix endpoint must use
strictly more odd steps than that prefix. -/
theorem odd_count_gt_of_smaller_meeting {i s n m : Nat} (hodd : OddRun n i)
    (hsmall : m < n) (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    i < oddCount m (i + s) := by
  apply Nat.lt_of_not_ge
  intro hbad
  apply excess_odd_steps_exceed_valuation hodd hsmall hmeet
  rw [Nat.sub_eq_zero_of_le hbad, Nat.pow_zero]
  exact Nat.one_dvd _

/-- A sufficient ternary divisor excludes all smaller sources
with the given time overhead during the initial odd run. -/
theorem no_smaller_meeting_with_overhead {i s n m : Nat} (hodd : OddRun n i)
    (hdiv : 3 ^ s ∣ n) (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    n ≤ m := by
  apply Nat.le_of_not_gt
  intro hsmall
  have hc := oddCount_le_self m (i + s)
  exact excess_odd_steps_exceed_valuation hodd hsmall hmeet
    (Nat.dvd_trans (Nat.pow_dvd_pow 3 (by omega)) hdiv)

private theorem odd_prefix_grows {j i n : Nat} (hj : j ≤ i) (hodd : OddRun n i) :
    acceleratedOrbit j n ≤ acceleratedOrbit i n := by
  induction i with
  | zero =>
    rw [Nat.eq_zero_of_le_zero hj]
    exact Nat.le_refl _
  | succ i ih =>
    by_cases he : j = i + 1
    · rw [he]
      exact Nat.le_refl _
    · have hprev := ih (by omega) (fun a ha => hodd a (by omega))
      have hstep : acceleratedOrbit i n ≤ acceleratedOrbit (i + 1) n := by
        rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by
          have := hodd i (Nat.lt_succ_self _)
          omega)]
        omega
      exact Nat.le_trans hprev hstep

/-- A multiple of 3^s has no smaller partner meeting anywhere in
its full odd run with an overhead of at most s steps. -/
theorem no_smaller_meeting_during_run {i j s n m : Nat} (hodd : OddRun n i)
    (hdiv : 3 ^ s ∣ n) (hbudget : j ≤ i + s)
    (hmeet : acceleratedOrbit j m = acceleratedOrbit i n) : n ≤ m := by
  by_cases hij : i ≤ j
  · rw [← Nat.add_sub_of_le hij] at hmeet
    exact no_smaller_meeting_with_overhead hodd
      (Nat.dvd_trans (Nat.pow_dvd_pow 3 (by omega : j - i ≤ s)) hdiv) hmeet
  · apply Nat.le_of_not_gt
    intro hsmall
    obtain ⟨u, hu⟩ := (oddRun_iff j n).mp (fun t ht => hodd t (by omega))
    have hpos : 0 < u := by
      by_cases he : u = 0
      · rw [he, Nat.mul_zero] at hu
        omega
      · omega
    have hlt := PeakSuffixTable.prefix_image_lt hpos hu hsmall
    have hrun := DeviceSwap.run_climb j u n hpos hu
    have hstrict : acceleratedOrbit j m < acceleratedOrbit j n := by omega
    exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le hstrict (odd_prefix_grows (by omega) hodd))
      (Nat.le_of_eq hmeet.symm)

/-- A meeting late in the odd run can be pulled back to within
three times the smaller source's even count of the start. -/
theorem compress_meeting_during_run {i s n m : Nat} (hodd : OddRun n i)
    (hsmall : m < n) (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n)
    (hL : 3 * (i + s - oddCount m (i + s) - 1) ≤ i) :
    acceleratedOrbit (s + 3 * (i + s - oddCount m (i + s) - 1)) m =
      acceleratedOrbit (3 * (i + s - oddCount m (i + s) - 1)) n := by
  let e := i + s - oddCount m (i + s)
  let L := 3 * (e - 1)
  let J := s + L
  have hcount := odd_count_gt_of_smaller_meeting hodd hsmall hmeet
  have hdiv : 3 ^ i ∣ RunAlgebra.runA (i + s) m := by
    have hshift := RunAlgebra.shifted_affine_exact m (i + s)
    rw [hmeet] at hshift
    have htargetShift := RunAlgebra.shifted_affine_exact n i
    rw [TwoRunOrder.oddCount_oddRun hodd, BoundedEvenDefect.runA_zero_of_full_oddCount
      (TwoRunOrder.oddCount_oddRun hodd)] at htargetShift
    simp only [Nat.add_zero] at htargetShift
    have himage : 3 ^ i ∣ 2 ^ (i + s) * (acceleratedOrbit i n + 1) := by
      rw [Nat.pow_add, Nat.mul_right_comm, htargetShift, Nat.mul_right_comm, Nat.mul_assoc]
      exact Nat.dvd_mul_right _ _
    have hfirst : 3 ^ i ∣ 3 ^ oddCount m (i + s) * (m + 1) :=
      Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (Nat.le_of_lt hcount)) _
    rw [hshift] at himage
    exact (Nat.dvd_add_iff_right hfirst).mpr himage
  have hprefix : ∃ q, q ≤ J ∧ q ≤ i + s ∧
      oddCount (acceleratedOrbit q m) (i + s - q) = i + s - q := by
    rcases Nat.eq_zero_or_pos e with he | he
    · refine ⟨0, Nat.zero_le _, Nat.zero_le _, ?_⟩
      have hcap := oddCount_le_self m (i + s)
      have hfull : oddCount m (i + s) = i + s := by dsimp only [e] at he; omega
      simpa using hfull
    · obtain ⟨q, hq, hbound, hoddTail⟩ := BoundedEvenDefect.trailing_odds_at_precision
        he (Nat.le_add_right i s) (by dsimp only [e]; omega) hdiv
      exact ⟨q, by dsimp only [J, L]; omega, hq, hoddTail⟩
  obtain ⟨q, hq, _, htail⟩ := hprefix
  have hmOdd := BoundedEvenDefect.full_odd_suffix hq (by dsimp only [J, L]; omega) htail
  have hnOdd := BoundedEvenDefect.full_odd_suffix (s := 0) (Nat.zero_le L) hL
    (by simpa using TwoRunOrder.oddCount_oddRun hodd)
  have hmShift := RunAlgebra.shifted_affine_exact (acceleratedOrbit J m) (i - L)
  have hnShift := RunAlgebra.shifted_affine_exact (acceleratedOrbit L n) (i - L)
  have hlen : i + s - J = i - L := by dsimp only [J]; omega
  rw [hlen] at hmOdd
  rw [hmOdd, BoundedEvenDefect.runA_zero_of_full_oddCount hmOdd, Nat.add_zero,
    acceleratedOrbit_add, show i - L + J = i + s by dsimp only [J]; omega, hmeet] at hmShift
  rw [hnOdd, BoundedEvenDefect.runA_zero_of_full_oddCount hnOdd, Nat.add_zero,
    acceleratedOrbit_add, Nat.sub_add_cancel hL] at hnShift
  have heq := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 3) (n := i - L))
    (hmShift.symm.trans hnShift)
  exact Nat.add_right_cancel heq

/-- Ternary precision at a fixed original prefix is bounded by its
length and the competing even count. -/
theorem valuation_le_two_prefix_add_two_evens {i s t n m : Nat} (hodd : OddRun n i)
    (hdiv : 3 ^ t ∣ n) (hsmall : m < n)
    (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    t ≤ 2 * i + 2 * (i + s - oddCount m (i + s)) := by
  let j := i + s
  let a := oddCount m j
  let e := j - a
  have ha : i + t < a := by
    apply Nat.lt_of_not_ge
    intro hbad
    apply excess_odd_steps_exceed_valuation hodd hsmall hmeet
    exact Nat.dvd_trans (Nat.pow_dvd_pow 3 (by dsimp only [a, j] at hbad; omega)) hdiv
  have hsource := RunAlgebra.shifted_affine_exact m j
  have htarget := RunAlgebra.shifted_affine_exact n i
  rw [TwoRunOrder.oddCount_oddRun hodd, BoundedEvenDefect.runA_zero_of_full_oddCount
    (TwoRunOrder.oddCount_oddRun hodd)] at htarget
  simp only [Nat.add_zero] at htarget
  change 2 ^ j * (acceleratedOrbit j m + 1) = 3 ^ a * (m + 1) + RunAlgebra.runA j m at hsource
  rw [show acceleratedOrbit j m = acceleratedOrbit i n from hmeet] at hsource
  have hbalance : (2 ^ j * 3 ^ i) * (n + 1) =
      2 ^ i * (3 ^ a * (m + 1) + RunAlgebra.runA j m) := by
    calc
      _ = 2 ^ j * (2 ^ i * (acceleratedOrbit i n + 1)) := by rw [htarget]; ac_rfl
      _ = 2 ^ i * (2 ^ j * (acceleratedOrbit i n + 1)) := by ac_rfl
      _ = _ := by rw [hsource]
  have hbalanceInt := congrArg (fun n : Nat => (n : Int)) hbalance
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow,
    show ((2 : Nat) : Int) = 2 by rfl, show ((3 : Nat) : Int) = 3 by rfl,
    show ((1 : Nat) : Int) = 1 by rfl] at hbalanceInt
  have heq : (2 : Int) ^ j * (3 : Int) ^ i - (2 : Int) ^ i * (RunAlgebra.runA j m : Int) =
      (2 : Int) ^ i * ((3 : Int) ^ a * ((m : Int) + 1)) -
        ((2 : Int) ^ j * (3 : Int) ^ i) * (n : Int) := by
    simp only [Int.mul_add, Int.mul_one] at hbalanceInt ⊢
    omega
  have hfirst : (3 : Int) ^ (i + t) ∣
      (2 : Int) ^ i * ((3 : Int) ^ a * ((m : Int) + 1)) := by
    have hpow : (3 : Int) ^ (i + t) ∣ (3 : Int) ^ a := by
      simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
        (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 3 (Nat.le_of_lt ha)))
    exact Int.dvd_trans hpow (by refine ⟨(2 : Int) ^ i * ((m : Int) + 1), ?_⟩; ac_rfl)
  have hsecond : (3 : Int) ^ (i + t) ∣
      ((2 : Int) ^ j * (3 : Int) ^ i) * (n : Int) := by
    have hd : (3 : Int) ^ t ∣ (n : Int) := by
      simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using Int.ofNat_dvd.mpr hdiv
    obtain ⟨q, hq⟩ := hd
    rw [hq, Int.pow_add]
    exact ⟨(2 : Int) ^ j * q, by ac_rfl⟩
  have hcomp : (3 : Int) ^ (i + t) ∣
      (2 : Int) ^ j * (3 : Int) ^ i - (2 : Int) ^ i * (RunAlgebra.runA j m : Int) := by
    rw [heq]
    exact Int.dvd_sub hfirst hsecond
  apply Nat.le_of_not_gt
  intro hbad
  have hc := AffineExact.oddCount_le_self m j
  apply BoundedEvenDefect.avoids_odd_run_ratio e i m j (by dsimp only [e, a]; omega)
  have hprec : 2 * e + 3 * i + 1 ≤ i + t := by dsimp only [e, a, j]; omega
  have hp : (3 : Int) ^ (2 * e + 3 * i + 1) ∣ 3 ^ (i + t) := by
    simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
      Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 3 hprec)
  exact Int.dvd_trans hp hcomp

/-- After pulling the meeting back, its necessary even count grows
linearly with every ternary power dividing the original start. -/
theorem valuation_le_compressed_even_budget {i s t n m : Nat} (hodd : OddRun n i)
    (hdiv : 3 ^ t ∣ n) (hsmall : m < n)
    (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    t ≤ 2 * (3 * (i + s - oddCount m (i + s) - 1)) +
      2 * (i + s - oddCount m (i + s)) := by
  let e := i + s - oddCount m (i + s)
  let L := 3 * (e - 1)
  change t ≤ 2 * L + 2 * e
  by_cases hi : i ≤ L
  · have h := valuation_le_two_prefix_add_two_evens hodd hdiv hsmall hmeet
    change t ≤ 2 * i + 2 * e at h
    omega
  · have hL : L ≤ i := by omega
    have hcompressed := compress_meeting_during_run hodd hsmall hmeet hL
    have hmeet' : acceleratedOrbit (L + s) m = acceleratedOrbit L n := by
      simpa only [Nat.add_comm L s] using hcompressed
    have hodd' : OddRun n L := fun k hk => hodd k (by omega)
    have hb := valuation_le_two_prefix_add_two_evens hodd' hdiv hsmall hmeet'
    have hsplit := AccumulatorArith.oddCount_add m (L + s) (i + s - (L + s))
    rw [Nat.add_sub_of_le (by omega : L + s ≤ i + s)] at hsplit
    have hcap := AffineExact.oddCount_le_self (acceleratedOrbit (L + s) m) (i + s - (L + s))
    dsimp only [e]
    omega

/-- A positive ternary valuation requires at least its linear
share of the smaller path's even steps, independently of time. -/
theorem valuation_add_six_le_eight_evens {i s t n m : Nat} (ht : 0 < t)
    (hodd : OddRun n i) (hdiv : 3 ^ t ∣ n) (hsmall : m < n)
    (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    t + 6 ≤ 8 * (i + s - oddCount m (i + s)) := by
  have hb := valuation_le_compressed_even_budget hodd hdiv hsmall hmeet
  omega

end Collatz.OddPrefixValuation
