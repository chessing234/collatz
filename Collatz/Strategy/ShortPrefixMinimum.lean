import Collatz.Strategy.LongRunPeakRigidity

/-!
# The exact equal-time minimum from short inverse fibers

A certified exponent drop confines all even steps in the smaller
source's prefix to its first 4d-3 positions. Its long remaining odd
run is forced, so the entire fiber can be replaced by one short
inverse fiber.
-/

namespace Collatz.ShortPrefixMinimum

open Collatz.SynchronousClasses Collatz.BoundedEvenDefect
  Collatz.LongRunPeakRigidity Collatz.RunAlgebra

def shortPrefixLength (d : Nat) : Nat := 4 * d - 3

private theorem full_odd_suffix {s J v x : Nat} (hs : s ≤ J) (hJ : J ≤ v)
    (h : oddCount (acceleratedOrbit s x) (v - s) = v - s) :
    oddCount (acceleratedOrbit J x) (v - J) = v - J := by
  have hlen : J - s + (v - J) = v - s := by omega
  have hsplit := AccumulatorArith.oddCount_add (acceleratedOrbit s x) (J - s) (v - J)
  rw [hlen, h, acceleratedOrbit_add, Nat.sub_add_cancel hs] at hsplit
  have hfirst := AffineExact.oddCount_le_self (acceleratedOrbit s x) (J - s)
  have hlast := AffineExact.oddCount_le_self (acceleratedOrbit J x) (v - J)
  omega

/-- An exact scaled peak determines the image at the much shorter
prefix where its final all-odd run begins. -/
theorem short_fiber_of_scaled_peak {v d x u : Nat} (hd : 0 < d) (hdv : d < v)
    (hJ : shortPrefixLength d ≤ v) (hu : 0 < u) (hx : x < 2 ^ v * u)
    (hpeak : acceleratedOrbit v x + 1 = 3 ^ (v - d) * u) :
    acceleratedOrbit (shortPrefixLength d) x + 1 =
      2 ^ (v - shortPrefixLength d) * 3 ^ (shortPrefixLength d - d) * u := by
  let J := shortPrefixLength d
  have hJd : d ≤ J := by dsimp [J, shortPrefixLength]; omega
  have hcast : (acceleratedOrbit v x : Int) + 1 = ((3 ^ (v - d) * u : Nat) : Int) := by
    simpa only [Int.natCast_add, show ((1 : Nat) : Int) = 1 by rfl] using
      congrArg (fun n : Nat => (n : Int)) hpeak
  have hcount := odd_count_near_peak hu hx hdv
    (show (1 : Int).natAbs ≤ 3 ^ (v - d - 1) from Nat.pow_pos (by decide)) hcast
  have hdiv : 3 ^ (v - d) ∣ runA v x := by
    have hterm : 3 ^ (v - d) ∣ 3 ^ oddCount x v * (x + 1) :=
      Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 hcount) _
    have hsum : 3 ^ (v - d) ∣ 2 ^ v * (acceleratedOrbit v x + 1) := by
      rw [hpeak, Nat.mul_left_comm]
      exact Nat.dvd_mul_right _ _
    rw [shifted_affine_exact] at hsum
    exact (Nat.dvd_add_iff_right hterm).mpr hsum
  obtain ⟨s, _, hsJ, hsodd⟩ := trailing_odds_of_divisible_defect hd hcount hdiv
  have hodd := full_odd_suffix hsJ hJ hsodd
  let t := v - J
  have htail : acceleratedOrbit t (acceleratedOrbit J x) = acceleratedOrbit v x := by
    rw [acceleratedOrbit_add, Nat.sub_add_cancel hJ]
  have hshift := shifted_affine_exact (acceleratedOrbit J x) t
  change oddCount (acceleratedOrbit J x) t = t at hodd
  rw [htail, hodd, runA_zero_of_full_oddCount hodd, Nat.add_zero, hpeak,
    show 3 ^ (v - d) = 3 ^ t * 3 ^ (J - d) by
      rw [← Nat.pow_add, show t + (J - d) = v - d by dsimp only [t]; omega]] at hshift
  simp only [Nat.add_zero] at hshift
  apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 3) (n := t))
  change 3 ^ t * (acceleratedOrbit J x + 1) = 3 ^ t * (2 ^ t * 3 ^ (J - d) * u)
  rw [← hshift]
  ac_rfl

private def paddedStart (v u d : Nat) : Nat := 2 ^ d * (2 ^ (v - d) * u - 1)

private theorem padded_lt {v u d : Nat} (hu : 0 < u) (hd : 0 < d) (hdv : d ≤ v) :
    paddedStart v u d < 2 ^ v * u - 1 := by
  simpa only [paddedStart, Nat.sub_add_cancel hdv] using
    PeakContraction.padded_start_lt (e := v - d) hu hd

private theorem padded_peak {v u d : Nat} (hu : 0 < u) (hdv : d ≤ v) :
    acceleratedOrbit v (paddedStart v u d) + 1 = 3 ^ (v - d) * u := by
  calc
    _ = acceleratedOrbit ((v - d) + d) (paddedStart v u d) + 1 := by
      rw [Nat.sub_add_cancel hdv]
    _ = _ := by
      rw [paddedStart, ← acceleratedOrbit_add, orbit_halvings]
      exact DeviceSwap.run_climb (v - d) u _ hu (Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) hu))

private theorem padded_meets {k v u d : Nat} (hu : 0 < u) (hdv : d ≤ v)
    (h : acceleratedOrbit k (3 ^ (v - d) * u - 1) = acceleratedOrbit k (3 ^ v * u - 1)) :
    acceleratedOrbit (v + k) (paddedStart v u d) = acceleratedOrbit (v + k) (2 ^ v * u - 1) := by
  have hsplit : v - d + d = v := Nat.sub_add_cancel hdv
  have hmeet : acceleratedOrbit k (3 ^ (v - d + d) * u - 1) =
      acceleratedOrbit k (3 ^ (v - d) * u - 1) := by rw [hsplit]; exact h.symm
  have hsync := PeakContraction.synchronized_drop hu hmeet
  rw [hsplit, Nat.add_comm k v] at hsync
  exact hsync.symm

private theorem equal_later {x y J L : Nat} (hJ : J ≤ L)
    (h : acceleratedOrbit J x = acceleratedOrbit J y) : acceleratedOrbit L x = acceleratedOrbit L y := by
  have he := congrArg (acceleratedOrbit (L - J)) h
  rwa [acceleratedOrbit_add, acceleratedOrbit_add, Nat.sub_add_cancel hJ] at he

private def candidates (k v u : Nat) : List Nat :=
  (List.range k).filterMap (fun i =>
    let d := i + 1
    if scaledPeakCertificate k v u d then
      some (leastAt (shortPrefixLength d) (paddedStart v u d))
    else none)

/-- Compute the least synchronous partner from short inverse fibers
for the certified drops, keeping the original source as a fallback. -/
def minimumFromPeaks (k v u : Nat) : Nat :=
  ((2 ^ v * u - 1) :: candidates k v u).min (by simp)

theorem minimumFromPeaks_correct {k v u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : u % 2 = 1) :
    minimumFromPeaks k v u = leastAt (v + k) (2 ^ v * u - 1) := by
  let n := 2 ^ v * u - 1
  let m := leastAt (v + k) n
  let xs := n :: candidates k v u
  let result := minimumFromPeaks k v u
  have hV : 6 * k + 2 ≤ v := hv
  have hbase : 2 * k + 2 ≤ v := by omega
  have huPos : 0 < u := by omega
  have hn : n + 1 = 2 ^ v * u := Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) huPos)
  have hrep : result ∈ xs := List.min_mem (l := xs) (by simp [xs])
  have hless (x : Nat) (hx : x ∈ xs) : result ≤ x := List.min_le_of_mem hx
  change result = m
  apply Nat.le_antisymm
  · by_cases hm : m < n
    · obtain ⟨d, hpos, hd, hpeak⟩ :=
        scaled_peak_at_cutoff hv huPos hn hm (leastAt_meets (v + k) n)
      let J := shortPrefixLength d
      let p := paddedStart v u d
      have hJ : J ≤ v := by dsimp [J, shortPrefixLength]; omega
      have hpd : p < n := padded_lt huPos hpos (by omega)
      have htrue := DeviceSwap.run_climb v u n huPos hn
      have hmeet : acceleratedOrbit k (3 ^ (v - d) * u - 1) =
          acceleratedOrbit k (3 ^ v * u - 1) := by
        rw [← hpeak, show 3 ^ v * u - 1 = acceleratedOrbit v n by omega,
          acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k v]
        exact leastAt_meets (v + k) n
      have hc := (scaledPeakCertificate_iff hbase hpos hd hu).mpr hmeet
      have hmem : leastAt J p ∈ candidates k v u := by
        apply List.mem_filterMap.mpr
        refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
        dsimp only
        rw [show d - 1 + 1 = d by omega, if_pos hc]
      have hbefore := short_fiber_of_scaled_peak hpos (by omega) hJ huPos
        (by omega : m < 2 ^ v * u)
        (show acceleratedOrbit v m + 1 = 3 ^ (v - d) * u by
          rw [hpeak, Nat.sub_add_cancel (Nat.mul_pos (Nat.pow_pos (by decide)) huPos)])
      have hp := short_fiber_of_scaled_peak hpos (by omega) hJ huPos
        (by omega : p < 2 ^ v * u) (padded_peak huPos (by omega))
      have hsame : acceleratedOrbit J p = acceleratedOrbit J m :=
        Nat.add_right_cancel (hp.trans hbefore.symm)
      exact Nat.le_trans (hless _ (List.mem_cons_of_mem _ hmem)) (leastAt_le hsame)
    · exact Nat.le_trans (hless n (List.mem_cons_self ..)) (by omega)
  · rcases List.mem_cons.mp hrep with he | hmem
    · rw [he]
      exact leastAt_le rfl
    · obtain ⟨i, hi, hcase⟩ := List.mem_filterMap.mp hmem
      have hd : i + 1 ≤ k := Nat.succ_le_of_lt (List.mem_range.mp hi)
      by_cases hc : scaledPeakCertificate k v u (i + 1) = true
      · dsimp only at hcase
        rw [if_pos hc] at hcase
        have he := Option.some.inj hcase
        rw [← he]
        have hmeet := (scaledPeakCertificate_iff hbase (Nat.succ_pos _) hd hu).mp hc
        have hshort : shortPrefixLength (i + 1) ≤ v + k := by unfold shortPrefixLength; omega
        have hsync := (equal_later hshort (leastAt_meets _ _)).trans
          (padded_meets huPos (by omega) hmeet)
        exact leastAt_le hsync.symm
      · dsimp only at hcase
        rw [if_neg hc] at hcase
        contradiction

end Collatz.ShortPrefixMinimum
