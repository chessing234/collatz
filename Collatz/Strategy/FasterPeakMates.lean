import Collatz.Strategy.LongRunPeakRigidity
import Collatz.Strategy.CouplingDead

/-!
# Smaller partners that reach the meeting point earlier

Advancing the original run by r extra steps gives a smaller source
an r-step time lead at the meeting. Rigidity still determines the
shorter prefix's endpoint. Its maximum possible image gives an
exact capacity inequality, and an odd run with optional initial
halvings realizes every certificate that satisfies it.
-/

namespace Collatz.FasterPeakMates

open Collatz.LongRunPeakRigidity

private theorem height_condition {v r d u : Nat} (hv : r + d ≤ v) (hu : 0 < u) :
    3 ^ (v - d) * u ≤ (2 ^ r * u) * 3 ^ (v - r) ↔ 3 ^ r ≤ 2 ^ r * 3 ^ d := by
  let G := 3 ^ (v - r - d) * u
  have hl : 3 ^ (v - d) * u = G * 3 ^ r := by
    rw [show v - d = (v - r - d) + r by omega, Nat.pow_add]
    dsimp only [G]
    ac_rfl
  have hr : (2 ^ r * u) * 3 ^ (v - r) = G * (2 ^ r * 3 ^ d) := by
    rw [show v - r = (v - r - d) + d by omega, Nat.pow_add]
    dsimp only [G]
    ac_rfl
  rw [hl, hr, Nat.mul_le_mul_left_iff (Nat.mul_pos (Nat.pow_pos (by decide)) hu : 0 < G)]

private theorem peak_source {v r d u : Nat} (hv : r + d + 1 ≤ v) (hu : 0 < u)
    (hd : 0 < d) (hgain : 3 ^ r < 2 ^ r * 3 ^ d) :
    ∃ m, 0 < m ∧ m < 2 ^ v * u - 1 ∧
      acceleratedOrbit (v - r) m = 3 ^ (v - d) * u - 1 := by
  by_cases hrd : r ≤ d
  · let m := 2 ^ (d - r) * (2 ^ (v - d) * u - 1)
    have hm : 0 < m := by
      have h2 : 2 ≤ 2 ^ (v - d) := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ v - d by omega)
      exact Nat.mul_pos (Nat.two_pow_pos _) (by
        have h := Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ (v - d)) hu)
        omega)
    have hshift : m + 2 ^ (d - r) = 2 ^ (v - r) * u := by
      calc
        _ = 2 ^ (d - r) * ((2 ^ (v - d) * u - 1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = _ := by
          rw [Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) hu),
            ← Nat.mul_assoc, ← Nat.pow_add, show d - r + (v - d) = v - r by omega]
    have hsmall : m < 2 ^ v * u - 1 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · simpa only [m, hr, Nat.sub_zero, Nat.sub_add_cancel (by omega : d ≤ v)] using
          PeakContraction.padded_start_lt (e := v - d) hu hd
      · have hpow : 2 ^ (v - r) < 2 ^ v :=
          (Nat.pow_lt_pow_iff_right (by decide)).mpr (by omega)
        have hcap := Nat.mul_lt_mul_of_pos_right hpow hu
        have hpos := Nat.two_pow_pos (d - r)
        omega
    refine ⟨m, hm, hsmall, ?_⟩
    have hrun := DeviceSwap.run_climb (v - d) u (2 ^ (v - d) * u - 1) hu
      (Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) hu))
    dsimp only [m]
    rw [show v - r = (v - d) + (d - r) by omega, ← acceleratedOrbit_add,
      SynchronousClasses.orbit_halvings]
    omega
  · let U := 3 ^ (r - d) * u
    let m := 2 ^ (v - r) * U - 1
    have hpow : 3 ^ (r - d) * 3 ^ d = 3 ^ r := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega : d ≤ r)]
    have hrelative : 3 ^ (r - d) < 2 ^ r :=
      Nat.lt_of_mul_lt_mul_right (by rwa [hpow])
    have hU : 0 < U := Nat.mul_pos (Nat.pow_pos (by decide)) hu
    have h2 : 2 ≤ 2 ^ (v - r) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ v - r by omega)
    have hm : 0 < m := by
      have h := Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ (v - r)) hU)
      dsimp only [m]
      omega
    have hsize : 2 ^ (v - r) * U < 2 ^ v * u := by
      calc
        _ < 2 ^ (v - r) * (2 ^ r * u) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hrelative hu) (Nat.two_pow_pos _)
        _ = _ := by rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (by omega : r ≤ v)]
    have hrun := DeviceSwap.run_climb (v - r) U m hU
      (Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) hU))
    have hend : 3 ^ (v - r) * U = 3 ^ (v - d) * u := by
      dsimp only [U]
      rw [← Nat.mul_assoc, ← Nat.pow_add, show v - r + (r - d) = v - d by omega]
    rw [hend] at hrun
    exact ⟨m, hm, by dsimp only [m]; omega, by omega⟩

/-- A smaller source can reach the meeting point r steps earlier
exactly when some certified drop can support the shorter prefix. -/
theorem faster_iff_scaled {k v r n u : Nat}
    (hv : requiredRunLength k v u + r ≤ v) (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ v * u) :
    (∃ m, 0 < m ∧ m < n ∧
      acceleratedOrbit (v - r + k) m = acceleratedOrbit (v + k) n) ↔
      ∃ d, 0 < d ∧ d ≤ k ∧ 3 ^ r < 2 ^ r * 3 ^ d ∧
        scaledPeakCertificate k v u d = true := by
  have huPos : 0 < u := by omega
  rw [requiredRunLength_eq k v u huPos] at hv
  have hbase : 2 * k + 2 + r ≤ v := by unfold adaptiveRigidityCutoff at hv; omega
  have hrun := DeviceSwap.run_climb v u n huPos hfac
  have hpeak : acceleratedOrbit v n = 3 ^ v * u - 1 := by omega
  constructor
  · rintro ⟨m, _, hsmall, hfinal⟩
    obtain ⟨d, hd, hdCap, hscaled⟩ := scaled_peak_after_shortened_prefix hv huPos hfac hsmall hfinal
    have hcap : m < (2 ^ r * u) * 2 ^ (v - r) := by
      rw [Nat.mul_right_comm, ← Nat.pow_add, Nat.add_sub_of_le (by omega : r ≤ v)]
      omega
    have hupper := Nat.lt_of_lt_of_le (OrbitCapacity.image_lt hcap)
      (Nat.mul_le_mul_left (2 ^ r * u)
        (Nat.pow_le_pow_right (by decide) (AffineExact.oddCount_le_self m (v - r))))
    have hheight : 3 ^ (v - d) * u ≤ (2 ^ r * u) * 3 ^ (v - r) := by
      rw [hscaled] at hupper
      omega
    have hle := (height_condition (by omega : r + d ≤ v) huPos).mp hheight
    have hstrict : 3 ^ r < 2 ^ r * 3 ^ d := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · simpa only [hr, Nat.pow_zero, Nat.one_mul] using Nat.one_lt_pow (Nat.ne_of_gt hd) (by decide : 1 < 3)
      · refine Nat.lt_of_le_of_ne hle ?_
        intro he
        have htwo : 2 ∣ 2 ^ r := Nat.pow_dvd_pow 2 (by omega : 1 ≤ r)
        have hdiv : 2 ∣ 3 ^ r := he ▸ Nat.dvd_mul_right_of_dvd htwo (3 ^ d)
        exact CouplingDead.not_two_dvd_three_pow r hdiv
    have hmeet : acceleratedOrbit k (3 ^ (v - d) * u - 1) =
        acceleratedOrbit k (3 ^ v * u - 1) := by
      rw [← hscaled, ← hpeak, acceleratedOrbit_add, acceleratedOrbit_add,
        Nat.add_comm k (v - r), Nat.add_comm k v]
      exact hfinal
    exact ⟨d, hd, by omega, hstrict,
      (scaledPeakCertificate_iff (by omega) hd (by omega) hu).mpr hmeet⟩
  · rintro ⟨d, hd, hdk, hgain, hc⟩
    obtain ⟨m, hm, hsmall, hscaled⟩ := peak_source (v := v) (by omega) huPos hd hgain
    have hmeet := (scaledPeakCertificate_iff (by omega) hd hdk hu).mp hc
    refine ⟨m, hm, by omega, ?_⟩
    rw [← hscaled, ← hpeak] at hmeet
    simpa only [acceleratedOrbit_add, Nat.add_comm k] using hmeet

private theorem lead_lt_triple_drop {r d : Nat} (h : 3 ^ r < 2 ^ r * 3 ^ d) : r < 3 * d := by
  apply Nat.lt_of_not_ge
  intro hlarge
  let s := r - 3 * d
  have hsplit : r = 3 * d + s := (Nat.add_sub_of_le hlarge).symm
  have hle : 2 ^ r * 3 ^ d ≤ 3 ^ r := by
    rw [hsplit, Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul, Nat.mul_right_comm,
      ← Nat.mul_pow]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)
  exact Nat.not_le_of_gt h hle

/-- Reject time leads outside the certificate range before computing
any powers depending on the lead. -/
def fasterPeakCheck (k v u r : Nat) : Bool :=
  if r < 3 * k then
    (List.range k).any fun i =>
      decide (3 ^ r < 2 ^ r * 3 ^ (i + 1)) && scaledPeakCertificate k v u (i + 1)
  else false

theorem fasterPeakCheck_correct {k v r n u : Nat}
    (hv : requiredRunLength k v u + r ≤ v) (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ v * u) :
    (∃ m, 0 < m ∧ m < n ∧
      acceleratedOrbit (v - r + k) m = acceleratedOrbit (v + k) n) ↔
      fasterPeakCheck k v u r = true := by
  rw [faster_iff_scaled hv hu hfac, fasterPeakCheck]
  constructor
  · rintro ⟨d, hd, hdk, hgain, hc⟩
    have hlead := lead_lt_triple_drop hgain
    rw [if_pos (by omega), List.any_eq_true]
    refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [show d - 1 + 1 = d by omega, decide_eq_true hgain, hc]
    rfl
  · by_cases hlead : r < 3 * k
    · rw [if_pos hlead, List.any_eq_true]
      rintro ⟨i, hi, hc⟩
      rw [Bool.and_eq_true] at hc
      exact ⟨i + 1, Nat.succ_pos _, Nat.succ_le_of_lt (List.mem_range.mp hi),
        of_decide_eq_true hc.1, hc.2⟩
    · simp [hlead]

end Collatz.FasterPeakMates
