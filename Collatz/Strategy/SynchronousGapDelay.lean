import Collatz.Strategy.PeakSuffixTable
import Collatz.Strategy.LiftExponent
import Collatz.Strategy.MixedProgressionAncestors

/-!
# Arbitrary meeting delays after a fixed initial odd run

When the shifted peak is minus one modulo the suffix period, the
suffix begins with one halving and then stays odd. The exact least
source of that suffix preserves the minimum of the whole prefix.
-/

namespace Collatz.SynchronousGapDelay

open Collatz.SynchronousClasses Collatz.SynchronousExcursion Collatz.PeakSuffixTable

/-- A shifted peak one below a multiple of the suffix period keeps
the original minimum throughout that suffix. -/
theorem leastAt_single_gap {v k n u : Nat} (hv : 0 < v) (hk : 0 < k)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u)
    (hdiv : 2 ^ k ∣ 3 ^ v * u + 1) : leastAt (v + k) n = n := by
  let A := 3 ^ v * u
  have hA : 0 < A := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  obtain ⟨U, hU⟩ := hdiv
  change A + 1 = 2 ^ (j + 1) * U at hU
  have hpos : 0 < U := by
    apply Nat.pos_of_ne_zero
    intro he
    rw [he, Nat.mul_zero] at hU
    omega
  have hA3 : A % 3 = 0 := Nat.mod_eq_zero_of_dvd
    (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (show 1 ≤ v by omega)) _)
  have hU3 : ¬ 3 ∣ U := by
    intro hbad
    have hmod := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd hbad (2 ^ (j + 1)))
    rw [← hU] at hmod
    omega
  have hpeakMin : leastAt (j + 1) (A - 1) = A - 1 := by
    rw [show A - 1 = 2 ^ (j + 1) * U - 2 by omega, leastAt_leading_halving hpos, if_neg hU3]
  have hpeak := DeviceSwap.run_climb v u n hu hfac
  have hval : acceleratedOrbit v n = A - 1 := by omega
  let m := leastAt (v + (j + 1)) n
  apply Nat.le_antisymm (leastAt_le rfl)
  apply Nat.le_of_not_gt
  intro hsmall
  change m < n at hsmall
  have hlt := prefix_image_lt hu hfac hsmall
  have hmeet : acceleratedOrbit (j + 1) (A - 1) =
      acceleratedOrbit (j + 1) (acceleratedOrbit v m) := by
    rw [← hval, acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm (j + 1)]
    exact (leastAt_meets (v + (j + 1)) n).symm
  have hle := leastAt_le hmeet
  rw [hpeakMin] at hle
  exact Nat.not_le_of_gt hlt hle

/-- For any fixed positive initial run length and any prescribed suffix
length at least three, a whole progression of odd cofactors gives the
same minimum through that suffix. -/
theorem delay_progression (v k : Nat) (hv : 0 < v) (hk : 3 ≤ k) :
    ∃ u₀, 0 < u₀ ∧ ∀ t, let u := u₀ + 2 ^ k * t
      u % 2 = 1 ∧ leastAt (v + k) (2 ^ v * u - 1) = 2 ^ v * u - 1 := by
  let M := 2 ^ k
  let P := 2 ^ (k - 2)
  let u₀ := 3 ^ (P * v - v) * (M - 1)
  have hM : 1 < M := by
    simpa only [Nat.pow_zero] using
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (show 0 < k by omega)
  have hP : 0 < P := Nat.two_pow_pos _
  have hu₀ : 0 < u₀ := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hexp : v + (P * v - v) = P * v :=
    Nat.add_sub_cancel' (Nat.le_mul_of_pos_left _ hP)
  have hp : 3 ^ (P * v) % M = 1 := by
    rw [Nat.pow_mul, Nat.pow_mod, LiftExponent.three_pow_one_mod hk,
      Nat.one_pow, Nat.mod_eq_of_lt hM]
  have hbase : (3 ^ v * u₀) % M = M - 1 := by
    rw [show 3 ^ v * u₀ = 3 ^ (P * v) * (M - 1) by
      dsimp only [u₀]; rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]]
    rw [Nat.mul_mod, hp, Nat.mod_eq_of_lt (by omega : M - 1 < M), Nat.one_mul,
      Nat.mod_eq_of_lt (by omega : M - 1 < M)]
  refine ⟨u₀, hu₀, fun t => ?_⟩
  let u := u₀ + M * t
  have hu : 0 < u := by omega
  have hdiv : M ∣ 3 ^ v * u + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [show 3 ^ v * u + 1 = (3 ^ v * u₀ + 1) + M * (3 ^ v * t) by
      dsimp only [u]; rw [Nat.mul_add, Nat.add_right_comm]; congr 1; ac_rfl]
    rw [Nat.add_mul_mod_self_left, Nat.add_mod, hbase, Nat.mod_eq_of_lt hM,
      Nat.sub_add_cancel (by omega : 1 ≤ M), Nat.mod_self]
  have htwo : 2 ∣ M := Nat.pow_dvd_pow 2 (show 1 ≤ k by omega)
  have hpar := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans htwo hdiv)
  rw [Nat.add_mod, Nat.mul_mod (3 ^ v), Arith.three_pow_odd] at hpar
  have hodd : u % 2 = 1 := by omega
  have hfac : 2 ^ v * u - 1 + 1 = 2 ^ v * u :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos _) hu)
  exact ⟨hodd, leastAt_single_gap hv (by omega) hu hfac hdiv⟩

/-- Every unit target has arbitrarily large ancestors with a prescribed
initial odd-run length and a prescribed delay before a smaller
equal-time partner can appear. -/
theorem ancestor_with_delay {z : Nat} (hz : z % 3 ≠ 0)
    (v k H : Nat) (hv : 0 < v) (hk : 3 ≤ k) :
    ∃ u L, H < u ∧ u % 2 = 1 ∧
      acceleratedOrbit L (2 ^ v * u - 1) = z ∧
      leastAt (v + k) (2 ^ v * u - 1) = 2 ^ v * u - 1 := by
  obtain ⟨u₀, hu₀, hdelays⟩ := delay_progression v k hv hk
  obtain ⟨q, L, hq, htarget⟩ :=
    MixedProgressionAncestors.ancestor_in_progression hz (v + k) 0 (2 ^ v * u₀ - 1) H
  let u := u₀ + 2 ^ k * q
  have hform : (2 ^ (v + k) * 3 ^ 0) * q + (2 ^ v * u₀ - 1) =
      2 ^ v * u - 1 := by
    dsimp only [u]
    rw [Nat.pow_zero, Nat.mul_one, Nat.pow_add, Nat.mul_assoc, Nat.mul_add]
    have hp := Nat.mul_pos (Nat.two_pow_pos v) hu₀
    omega
  have hq' : q ≤ 2 ^ k * q := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  have hu : H < u := by omega
  rw [hform] at htarget
  exact ⟨u, L, hu, (hdelays q).1, htarget, (hdelays q).2⟩

end Collatz.SynchronousGapDelay
