import Collatz.Strategy.OrbitMinimumSpacing
import Collatz.Strategy.ShiftedAffine

/-!
# Simultaneous coefficient and value gaps

Pack minima of the integer part of the cumulative multiplier,
scaled by the original start. On a high injective tail, this
coordinate and the actual orbit value differ by a bounded factor.
A gap in the integer coordinate gives both a strict future
coefficient margin and a gap in the actual values.
-/

namespace Collatz.OrbitCoefficientSpacing

set_option exponentiation.threshold 512

open Collatz.OrbitCapacity Collatz.OrbitWindowBootstrap
open Collatz.OrbitMinimumSpacing Collatz.ExcursionSparseProduct

/-- The integer part of the affine multiplier times the source. -/
def coefficientFloor (n k : Nat) : Nat :=
  (n * 3 ^ oddCount n k) / 2 ^ k

theorem floor_le_state (n k : Nat) : coefficientFloor n k ≤ acceleratedOrbit k n := by
  apply Nat.div_le_of_le_mul
  have h := AffineExact.affine_exact n k
  rw [Nat.mul_comm n]
  omega

private theorem state_lt_twice_floor {n : Nat}
    (henv : ∀ k, 2 ^ k * acceleratedOrbit k n ≤ 2 * (n * 3 ^ oddCount n k)) (k : Nat) :
    acceleratedOrbit k n < 2 * (coefficientFloor n k + 1) := by
  let z := coefficientFloor n k
  let B := 2 ^ k
  have hceil : n * 3 ^ oddCount n k < (z + 1) * B :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mp (Nat.lt_succ_self z)
  apply Nat.lt_of_mul_lt_mul_left (a := B)
  calc
    _ ≤ 2 * (n * 3 ^ oddCount n k) := henv k
    _ < 2 * ((z + 1) * B) := Nat.mul_lt_mul_of_pos_left hceil (by decide)
    _ = _ := by ac_rfl

private theorem floor_escapes {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∀ R, ∃ H, ∀ k, H ≤ k → R < coefficientFloor n k := by
  intro R
  obtain ⟨H, hH⟩ := multiplier_escapes hn hinj (R + 1)
  refine ⟨H, ?_⟩
  intro k hk
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self R)
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr
  exact Nat.le_trans (Nat.le_of_lt (hH k hk)) (Nat.le_mul_of_pos_left _ hn)

/-- A gap in cumulative coefficient floors gives a strict relative
multiplier and at least the same gap in the actual orbit. -/
theorem gap_transfers {n i k D : Nat} (hD : 0 < D)
    (hgap : coefficientFloor n i + D ≤ coefficientFloor n (i + k)) :
    2 ^ k < 3 ^ oddCount (acceleratedOrbit i n) k ∧
      (acceleratedOrbit i n + D) * 2 ^ k <
        (acceleratedOrbit i n + 1) * 3 ^ oddCount (acceleratedOrbit i n) k ∧
      acceleratedOrbit i n + D ≤ acceleratedOrbit k (acceleratedOrbit i n) := by
  let x := acceleratedOrbit i n
  let z := coefficientFloor n i
  let A := 3 ^ oddCount x k
  let B := 2 ^ k
  let R := 2 ^ i
  have hcut : (z + D) * 2 ^ (i + k) ≤ n * 3 ^ oddCount n (i + k) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos (i + k))).mp hgap
  have hceil : n * 3 ^ oddCount n i < (z + 1) * R :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i)).mp (Nat.lt_succ_self z)
  have hrelative : (z + D) * B < (z + 1) * A := by
    apply Nat.lt_of_mul_lt_mul_left (a := R)
    calc
      _ = (z + D) * 2 ^ (i + k) := by rw [Nat.pow_add]; change _ = (z + D) * (R * B); ac_rfl
      _ ≤ n * 3 ^ oddCount n (i + k) := hcut
      _ = A * (n * 3 ^ oddCount n i) := by
        rw [AccumulatorArith.oddCount_add, Nat.pow_add]
        change _ * (_ * A) = _
        ac_rfl
      _ < A * ((z + 1) * R) := Nat.mul_lt_mul_of_pos_left hceil (Nat.pow_pos (by decide))
      _ = _ := by ac_rfl
  have hcoeff : B < A := by
    apply Nat.lt_of_mul_lt_mul_left (a := z + 1)
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right B (Nat.add_le_add_left hD z)) hrelative
  refine ⟨hcoeff, ?_⟩
  have hx := floor_le_state n i
  let excess := x - z
  have hsum : z + excess = x := Nat.add_sub_of_le hx
  have hvalue : (x + D) * B < (x + 1) * A := by
    calc
      _ = (z + D) * B + excess * B := by
        rw [← hsum, Nat.add_right_comm z excess D, Nat.add_mul]
      _ < (z + 1) * A + excess * A :=
        Nat.add_lt_add_of_lt_of_le hrelative (Nat.mul_le_mul_left _ (Nat.le_of_lt hcoeff))
      _ = _ := by rw [← Nat.add_mul, Nat.add_right_comm z 1 excess, hsum]
  refine ⟨hvalue, ?_⟩
  have hshift := RunAlgebra.shifted_affine_exact x k
  have htail : (x + 1) * A ≤ (acceleratedOrbit k x + 1) * B := by
    rw [Nat.mul_comm (x + 1), Nat.mul_comm (acceleratedOrbit k x + 1)]
    change 3 ^ oddCount x k * (x + 1) ≤ 2 ^ k * (acceleratedOrbit k x + 1)
    omega
  have h := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le hvalue htail)
  change x + D ≤ acceleratedOrbit k x
  omega

private theorem packing_contradiction {C T D : Nat} (hT : C * (2 ^ 23) ^ 19 < T)
    (hD : 0 < D) (hcount : (T * D ^ 19) ^ 20 ≤ C * ((2 ^ 23) * (T * D ^ 20)) ^ 19) :
    False := by
  have hpos : 0 < T := Nat.lt_of_le_of_lt (Nat.zero_le _) hT
  have h := hcount
  simp only [Nat.mul_pow, ← Nat.pow_mul] at h
  have he : D ^ (19 * 20) = D ^ (20 * 19) := rfl
  rw [he, Nat.pow_succ T 19] at h
  have hmain : T * (T ^ 19 * D ^ (20 * 19)) ≤
      (C * (2 ^ 23) ^ 19) * (T ^ 19 * D ^ (20 * 19)) := by
    calc
      _ = (T ^ 19 * T) * D ^ (20 * 19) := by ac_rfl
      _ ≤ C * ((2 ^ 23) ^ 19 * (T ^ 19 * D ^ (20 * 19))) := h
      _ = _ := (Nat.mul_assoc ..).symm
  exact Nat.not_le_of_gt hT
    (Nat.le_of_mul_le_mul_right hmain (Nat.mul_pos (Nat.pow_pos hpos) (Nat.pow_pos hD)))

private theorem separated_of_envelope :
    ∃ L, 0 < L ∧ ∀ {n : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      (∀ k, 2 ^ k * acceleratedOrbit k n ≤ 2 * (n * 3 ^ oddCount n k)) →
      ∀ H, ∃ i D, H ≤ i ∧ 2 ≤ D ∧ acceleratedOrbit i n ≤ L * D ^ 20 ∧
        ∀ k, 0 < k →
          2 ^ k < 3 ^ oddCount (acceleratedOrbit i n) k ∧
          (acceleratedOrbit i n + D) * 2 ^ k <
            (acceleratedOrbit i n + 1) * 3 ^ oddCount (acceleratedOrbit i n) k ∧
          acceleratedOrbit i n + D ≤ acceleratedOrbit k (acceleratedOrbit i n) := by
  obtain ⟨C, hC⟩ := orbit_window_power
  let V := C * (2 ^ 23) ^ 19 + 1
  let T := 2 ^ (20 * V)
  have hT : C * (2 ^ 23) ^ 19 < T := by
    have hbase : C * (2 ^ 23) ^ 19 < V := Nat.lt_succ_self _
    have hsmall : V < 2 ^ V := Nat.lt_two_pow_self
    have hlarge : 2 ^ V ≤ T := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_trans hbase (Nat.lt_of_lt_of_le hsmall hlarge)
  let L := (2 ^ 23) * T
  refine ⟨L, Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _), ?_⟩
  intro n hn hinj henv H
  let z := coefficientFloor n
  obtain ⟨cut, hcut⟩ := floor_escapes hn hinj (2 ^ (20 * (V + 1)))
  obtain ⟨start, hstart, hmin⟩ := minimum_after z (max H cut)
  let x := z start
  have hxT : 2 ^ (20 * (V + 1)) ≤ x := Nat.le_of_lt (hcut start (by omega))
  have hx : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hxT
  let q := x.log2 / 20
  have hV : V + 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 20)).mpr
    have h := (Nat.le_log2 (Nat.ne_of_gt hx)).mpr hxT
    rw [Nat.mul_comm]
    exact h
  let d := q - V
  let D := 2 ^ d
  have hD : 2 ≤ D := by
    change 2 ^ 1 ≤ 2 ^ d
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    dsimp [d]
    omega
  let U := T * D ^ 20
  have hU : U = 2 ^ (20 * q) := by
    change 2 ^ (20 * V) * (2 ^ d) ^ 20 = _
    rw [← Nat.pow_mul, ← Nat.pow_add]
    have he : V + d = q := Nat.add_sub_of_le (Nat.le_trans (Nat.le_succ V) hV)
    rw [Nat.mul_comm d 20, ← Nat.mul_add, he]
  have hUpos : 0 < U := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (Nat.two_pow_pos _))
  have hlow : U ≤ x := by
    rw [hU]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self x.log2 20))
      (Nat.log2_self_le (Nat.ne_of_gt hx))
  have hupper : x ≤ 2 ^ 20 * U := by
    rw [hU, ← Nat.pow_add]
    apply Nat.le_trans (Nat.le_of_lt Nat.lt_log2_self)
    apply Nat.pow_le_pow_right (by decide)
    have hdiv := Nat.mod_add_div x.log2 20
    have hrem := Nat.mod_lt x.log2 (by decide : 0 < 20)
    change x.log2 + 1 ≤ 20 + 20 * (x.log2 / 20)
    omega
  let count := T * D ^ 19
  let width := (2 ^ 23) * U
  have hroom : x + count * D ≤ 2 * x := by
    have he : count * D = U := by
      change (T * D ^ 19) * D = T * D ^ 20
      rw [Nat.mul_assoc, ← Nat.pow_succ]
    rw [he]
    omega
  have hbounded (j : Nat) (hj : z j ≤ 2 * x) : acceleratedOrbit j n < width := by
    apply Nat.lt_of_lt_of_le (state_lt_twice_floor henv j)
    change 2 * (z j + 1) ≤ 8388608 * U
    change x ≤ 1048576 * U at hupper
    omega
  have hfound : ∃ i, start ≤ i ∧ z i ≤ 2 * x ∧ ∀ j, i < j → z i + D ≤ z j := by
    apply Classical.byContradiction
    intro hnone
    have hsmall (i : Nat) (hi : start ≤ i) (_ : FutureMinimum z i) (hb : z i ≤ 2 * x) :
        ∃ j, i < j ∧ z j < z i + D := by
      apply Classical.byContradiction
      intro h
      exact hnone ⟨i, hi, hb, fun j hj => Nat.le_of_not_gt (fun hg => h ⟨j, hj, hg⟩)⟩
    have hstartmin : FutureMinimum z start :=
      fun j hj => hmin j (Nat.le_trans hstart hj)
    obtain ⟨indices, hnd, hlen, hmembers⟩ :=
      minima_indices_of_small_gaps hsmall count (Nat.le_refl start) hstartmin hroom
    let xs := indices.map (fun j => acceleratedOrbit j n)
    have hxs : xs.Nodup := List.pairwise_map.mpr
      (hnd.imp (fun hne heq => hne (hinj _ _ heq)))
    have hl : xs.length = count := by simp [xs, hlen]
    have hc : count ^ 20 ≤ C * width ^ 19 := by
      rw [← hl]
      apply hC (a := 0) (X := width) (Nat.mul_pos (Nat.two_pow_pos _) hUpos)
        (no_merging_of_injective hinj) xs hxs
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      exact ⟨Nat.zero_le _, by simpa using hbounded j (hmembers j hj).2.2, j, rfl⟩
    exact packing_contradiction hT (Nat.two_pow_pos _) hc
  obtain ⟨i, hi, hb, hg⟩ := hfound
  refine ⟨i, D, by omega, hD, ?_, ?_⟩
  · have hw := Nat.le_of_lt (hbounded i hb)
    change acceleratedOrbit i n ≤ (2 ^ 23) * (T * D ^ 20) at hw
    simpa only [L, Nat.mul_assoc] using hw
  · intro k hk
    exact gap_transfers (Nat.two_pow_pos d) (hg (i + k) (by omega))

/-- Arbitrarily late states of an injective positive orbit have a
strictly expanding multiplier at every positive time and a value
gap on the twentieth-root scale to every later state. -/
theorem simultaneous_future_gaps :
    ∃ L, 0 < L ∧ ∀ {n : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      ∀ H, ∃ i D, H ≤ i ∧ 2 ≤ D ∧ acceleratedOrbit i n ≤ L * D ^ 20 ∧
        ∀ k, 0 < k →
          2 ^ k < 3 ^ oddCount (acceleratedOrbit i n) k ∧
          (acceleratedOrbit i n + D) * 2 ^ k <
            (acceleratedOrbit i n + 1) * 3 ^ oddCount (acceleratedOrbit i n) k ∧
          acceleratedOrbit i n + D ≤ acceleratedOrbit k (acceleratedOrbit i n) := by
  obtain ⟨L, hL, hseparated⟩ := separated_of_envelope
  obtain ⟨P, _, hP⟩ := uniform_segment_envelope
  refine ⟨L, hL, ?_⟩
  intro n hn hinj H
  obtain ⟨cut, hcut⟩ := injective_eventually_above _ hinj (cutoff P P)
  let start := max H cut
  let x := acceleratedOrbit start n
  have hx : 0 < x := acceleratedOrbit_positive hn start
  have hshift (k : Nat) : acceleratedOrbit k x = acceleratedOrbit (start + k) n := by
    rw [show x = acceleratedOrbit start n from rfl, acceleratedOrbit_add, Nat.add_comm k start]
  have hxinj (i j : Nat) (h : acceleratedOrbit i x = acceleratedOrbit j x) : i = j := by
    rw [hshift, hshift] at h
    exact Nat.add_left_cancel (hinj _ _ h)
  have henv (k : Nat) : 2 ^ k * acceleratedOrbit k x ≤ 2 * (x * 3 ^ oddCount x k) := by
    have hlow (i : Nat) (_ : i < k) : cutoff P (P + 0) ≤ acceleratedOrbit i x := by
      rw [Nat.add_zero, hshift]
      exact Nat.le_of_lt (hcut _ (by omega : cut ≤ start + i))
    have h := hP (q := 0) hx (no_merging_of_injective hxinj) (fun i j _ _ => hxinj i j) hlow
    change 1 * (2 ^ k * acceleratedOrbit k x) ≤ 2 * (x * 3 ^ oddCount x k) at h
    simpa only [Nat.one_mul] using h
  obtain ⟨i, D, _, hD, hbound, hgap⟩ := hseparated hx hxinj henv 0
  rw [hshift] at hbound hgap
  exact ⟨start + i, D, by omega, hD, hbound, hgap⟩

end Collatz.OrbitCoefficientSpacing
