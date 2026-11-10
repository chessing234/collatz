import Collatz.Strategy.InverseFiberTransport
import Collatz.Strategy.SuffixResidueObstruction
import Collatz.Strategy.SynchronousExcursion

/-!
# Finite inverse-suffix tables for long odd runs

For a fixed suffix depth, the candidate peaks in a smaller source
can be classified at finitely many dyadic and ternary base points.
Each candidate then reduces to a short ternary residue test on
the prefix, independently of the length of the initial odd run.
-/

namespace Collatz.PeakSuffixTable

open Collatz.SynchronousClasses Collatz.InverseFiberTransport
  Collatz.SuffixResidueObstruction Collatz.OrbitCapacity

/-- Each row either stays at or above the true peak under translation,
or is described by its odd-count gap and constant displacement. -/
def Covers (k : Nat) (offsets : List (Nat × Nat)) : Prop :=
  ∀ r : Fin (2 ^ k),
    let A := 3 ^ k * (r.val + 1)
    let a := oddCount (A - 1) k
    A % 8 = 3 → ∀ w ∈ fiber k (acceleratedOrbit k (A - 1)),
      (A - 1 ≤ w ∧ oddCount w k ≤ a) ∨
        ∃ dc ∈ offsets, oddCount w k = a + dc.1 ∧ 3 ^ dc.1 * (w + dc.2) = A

instance (k : Nat) (offsets : List (Nat × Nat)) : Decidable (Covers k offsets) := by
  unfold Covers
  infer_instance

/-- A finite table classifies every strictly lower inverse peak in
the corresponding mixed dyadic and ternary progressions. -/
theorem lower_peak_of_table {k A x : Nat} {offsets : List (Nat × Nat)}
    (hk : 3 ≤ k) (hcover : Covers k offsets)
    (hmod : A % 8 = 3) (hdiv : 3 ^ k ∣ A)
    (hlt : x < A - 1) (hmeet : acceleratedOrbit k x = acceleratedOrbit k (A - 1)) :
    ∃ dc ∈ offsets, 3 ^ dc.1 * (x + dc.2) = A := by
  let D := 2 ^ k
  let M := 3 ^ k
  let q := (A / M - 1) / D
  let r : Fin D := ⟨(A / M - 1) % D, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let B := M * (r.val + 1)
  have hApos : 0 < A := by omega
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hB : 0 < B := Nat.mul_pos hM (Nat.succ_pos _)
  have hmul : M * (A / M) = A := Nat.mul_div_cancel' hdiv
  have hpos : 0 < A / M := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, Nat.mul_zero] at hmul
    omega
  have hs : D * q + r.val = A / M - 1 := Nat.div_add_mod _ _
  have hsplit : A = D * (M * q) + B := by
    have hq : A / M = D * q + (r.val + 1) := by omega
    rw [← hmul, hq, Nat.mul_add, Nat.mul_left_comm M]
  have hD8 : 8 ∣ D := Nat.pow_dvd_pow 2 hk
  have hBmod : B % 8 = 3 := by
    have hdiv8 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd hD8 (M * q))
    rw [hsplit, Nat.add_mod, hdiv8, Nat.zero_add, Nat.mod_mod] at hmod
    exact hmod
  let a := oddCount (B - 1) k
  let s := 3 ^ a * q
  have hpeak : A - 1 = D * (M * q) + (B - 1) := by omega
  have htarget : acceleratedOrbit k (A - 1) = acceleratedOrbit k (B - 1) + M * s := by
    rw [hpeak]
    change acceleratedOrbit k (2 ^ k * (M * q) + (B - 1)) = _
    rw [Congruence.accOrbit_pow_two_mul_add]
    change 3 ^ a * (M * q) + _ = _ + M * (3 ^ a * q)
    ac_rfl
  have hmem : x ∈ fiber k (acceleratedOrbit k (B - 1) + 3 ^ k * s) :=
    mem_fiber.mpr (hmeet.trans htarget)
  obtain ⟨w, hw, hx⟩ := mem_fiber_translate.mp hmem
  have htranslate : x = w + D * (3 ^ (k - oddCount w k) * s) := hx
  rcases hcover r hBmod w hw with ⟨hbase, hcount⟩ | ⟨⟨d, c⟩, hdc, hcount, hval⟩
  · have hp : M ≤ 3 ^ (k - oddCount w k) * 3 ^ a := by
      change oddCount w k ≤ a at hcount
      have hle := AffineExact.oddCount_le_self w k
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hge : D * (M * q) ≤ D * (3 ^ (k - oddCount w k) * s) := by
      simpa only [s, Nat.mul_assoc] using Nat.mul_le_mul_left D (Nat.mul_le_mul_right q hp)
    change B - 1 ≤ w at hbase
    omega
  · refine ⟨(d, c), hdc, ?_⟩
    change oddCount w k = a + d at hcount
    change 3 ^ d * (w + c) = B at hval
    have hb := AffineExact.oddCount_le_self w k
    have hexp : d + (k - oddCount w k) + a = k := by omega
    have hscale : 3 ^ d * (D * (3 ^ (k - oddCount w k) * s)) = D * (M * q) := by
      calc
        _ = D * ((3 ^ d * 3 ^ (k - oddCount w k) * 3 ^ a) * q) := by dsimp only [s]; ac_rfl
        _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add, hexp]
    change 3 ^ d * (x + c) = A
    rw [htranslate, Nat.add_right_comm, Nat.mul_add, hval, hscale, hsplit, Nat.add_comm]

private def sevenOffsets : List (Nat × Nat) :=
  [(0, 2), (0, 3), (0, 6), (0, 7), (0, 11), (1, 0),
    (1, 3), (1, 4), (1, 5), (1, 9), (2, 2)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem seven_covers : Covers 7 sevenOffsets := by decide

private theorem seven_rejects :
    ∀ dc ∈ sevenOffsets, dc.1 ≤ 2 ∧ dc.2 ≤ 27 ∧
      ∃ p ∈ [1, 2, 3], Reject dc.1 dc.2 p := by decide

/-- After a run of at least seven odd steps, a shifted peak congruent
to three modulo eight gives no smaller equal-time partner through
seven suffix steps. -/
theorem leastAt_seven_after_mod_eight {v n u : Nat} (hv : 7 ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u)
    (hmod : (3 ^ v * u) % 8 = 3) : leastAt (v + 7) n = n := by
  let A := 3 ^ v * u
  let m := leastAt (v + 7) n
  have hpeak : acceleratedOrbit v n + 1 = A := DeviceSwap.run_climb v u n hu hfac
  apply Nat.le_antisymm (leastAt_le rfl)
  apply Nat.le_of_not_gt
  intro hsmall
  change m < n at hsmall
  have hm : m < 2 ^ v * u := by omega
  have himage := image_lt (k := v) (c := u) (x := m)
    (by simpa only [Nat.mul_comm] using hm)
  have hbound : acceleratedOrbit v m < A := by
    have ha := AffineExact.oddCount_le_self m v
    exact Nat.lt_of_lt_of_le himage (by
      rw [Nat.mul_comm u]
      exact Nat.mul_le_mul_right u (Nat.pow_le_pow_right (by decide) ha))
  have hlt : acceleratedOrbit v m < A - 1 := by
    apply Nat.lt_of_le_of_ne (by omega)
    intro he
    have hme : acceleratedOrbit v n = acceleratedOrbit v m := by omega
    have hmin := leastAt_le hme
    have hn : n = u * 2 ^ v - 1 := by rw [Nat.mul_comm]; omega
    rw [show leastAt v n = n by rw [hn]; exact leastAt_last_in_period v u hu] at hmin
    exact Nat.not_le_of_gt hsmall hmin
  have hmeet : acceleratedOrbit 7 (acceleratedOrbit v m) = acceleratedOrbit 7 (A - 1) := by
    have hpn : A - 1 = acceleratedOrbit v n := by omega
    rw [hpn, acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm 7]
    exact leastAt_meets (v + 7) n
  have hdvd : 3 ^ 7 ∣ A := Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 hv) _
  obtain ⟨⟨d, c⟩, hdc, he⟩ := lower_peak_of_table (by decide) seven_covers hmod hdvd hlt hmeet
  obtain ⟨hd, hc, p, hp, hr⟩ := seven_rejects (d, c) hdc
  have hp' : p ≤ 3 := by simp at hp; omega
  have hsize : c ≤ 3 ^ (v - d - 1) := by
    exact Nat.le_trans hc (Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ v - d - 1 by omega))
  exact reject_peak hu hm (by omega) (by omega) hsize hr he

end Collatz.PeakSuffixTable
