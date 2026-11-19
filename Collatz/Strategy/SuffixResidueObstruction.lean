import Collatz.Strategy.ShiftedAffine
import Collatz.Strategy.OrbitCapacity
import Collatz.Strategy.AccumulatorArith

/-!
# Short ternary tests for prefixes near an odd-run peak

If a long prefix is almost entirely odd, a short final part already
contains enough odd steps to kill the homogeneous term modulo a
power of three. The shifted additive defect in that short part
then decides which nearby peak offsets are possible.
-/

namespace Collatz.SuffixResidueObstruction

open Collatz.RunAlgebra Collatz.OrbitCapacity

theorem runA_mod (k x : Nat) : runA k (x % 2 ^ k) = runA k x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    let r := x % 2 ^ (k + 1)
    have hm : r % 2 ^ k = x % 2 ^ k :=
      Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (Nat.le_succ k))
    have ha : oddCount r k = oddCount x k := by
      rw [Density.oddCount_mod r, hm, ← Density.oddCount_mod]
    have hb : oddCount r (k + 1) = oddCount x (k + 1) :=
      (Density.oddCount_mod x (k + 1)).symm
    have hpar : acceleratedOrbit k r % 2 = acceleratedOrbit k x % 2 := by
      rw [Density.oddCount_succ_last, Density.oddCount_succ_last, ha] at hb
      exact Nat.add_left_cancel hb
    have hacc : runA k r = runA k x := by rw [← ih r, hm, ih x]
    change runA (k + 1) r = runA (k + 1) x
    rw [runA, runA, hpar, hacc]

/-- No short residue profile with enough odd steps gives the required
shifted defect for a peak displaced by c. -/
def Reject (d c p : Nat) : Prop :=
  ∀ r : Fin (2 ^ (d + p)), p ≤ oddCount r.val (d + p) →
    (runA (d + p) r.val + 2 ^ (d + p) * c) % 3 ^ p ≠ 2 ^ (d + p) % 3 ^ p

instance (d c p : Nat) : Decidable (Reject d c p) := by
  unfold Reject
  infer_instance

/-- The last d+p steps of a prefix with at most d even steps suffice
to rule out a target whose displacement is incompatible modulo 3^p. -/
theorem reject_target {v d c p x : Nat} (hr : Reject d c p)
    (hlen : d + p ≤ v) (hodd : v - d ≤ oddCount x v) :
    ¬ 3 ^ p ∣ acceleratedOrbit v x + c := by
  intro hdvd
  let j := d + p
  let i := v - j
  let y := acceleratedOrbit i x
  let M := 3 ^ p
  have hij : i + j = v := Nat.sub_add_cancel hlen
  have hsplit := AccumulatorArith.oddCount_add x i j
  rw [hij] at hsplit
  change oddCount x v = oddCount x i + oddCount y j at hsplit
  have htail : p ≤ oddCount y j := by
    have hcap := AffineExact.oddCount_le_self x i
    change i + (d + p) = v at hij
    omega
  have hpow : M ∣ 3 ^ oddCount y j * (y + 1) :=
    Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 htail) _
  have hshift := shifted_affine_exact y j
  have hy : acceleratedOrbit j y = acceleratedOrbit v x := by
    change acceleratedOrbit j (acceleratedOrbit i x) = acceleratedOrbit v x
    rw [acceleratedOrbit_add, Nat.add_comm j i, hij]
  rw [hy] at hshift
  have hbalance : 2 ^ j * (acceleratedOrbit v x + c) + 2 ^ j =
      3 ^ oddCount y j * (y + 1) + (runA j y + 2 ^ j * c) := by
    rw [Nat.mul_add]
    have hleft : 2 ^ j * (acceleratedOrbit v x + 1) =
        2 ^ j * acceleratedOrbit v x + 2 ^ j := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmod₁ := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd hdvd (2 ^ j))
  have hmod₂ := Nat.mod_eq_zero_of_dvd hpow
  have hmod : (runA j y + 2 ^ j * c) % M = 2 ^ j % M := by
    have he := congrArg (· % M) hbalance
    rw [Nat.add_mod (2 ^ j * (acceleratedOrbit v x + c)), hmod₁, Nat.zero_add,
      Nat.mod_mod, Nat.add_mod (3 ^ oddCount y j * (y + 1)), hmod₂, Nat.zero_add,
      Nat.mod_mod] at he
    exact he.symm
  let r : Fin (2 ^ j) := ⟨y % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos j)⟩
  have hcount : oddCount r.val j = oddCount y j := (Density.oddCount_mod y j).symm
  have hacc : runA j r.val = runA j y := runA_mod j y
  exact hr r (hcount ▸ htail) (hacc ▸ hmod)

/-- A source below the start of the full odd run cannot reach a
rejected offset from a power-of-three fraction of that peak. -/
theorem reject_peak {v d c p x u : Nat} (hu : 0 < u)
    (hx : x < 2 ^ v * u) (hd : d < v) (hlen : d + p ≤ v)
    (hc : c ≤ 3 ^ (v - d - 1)) (hr : Reject d c p) :
    3 ^ d * (acceleratedOrbit v x + c) ≠ 3 ^ v * u := by
  intro heq
  have hs : 3 ^ v = 3 ^ d * 3 ^ (v - d) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hd)]
  rw [hs, Nat.mul_assoc] at heq
  have hy := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 3)) heq
  have ha : v - d ≤ oddCount x v := by
    apply Nat.le_of_not_gt
    intro hshort
    have himage := image_lt (k := v) (c := u) (x := x) (by simpa only [Nat.mul_comm] using hx)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 3)
      (show oddCount x v ≤ v - d - 1 by omega)
    let B := u * 3 ^ (v - d - 1)
    have hbound : acceleratedOrbit v x < B :=
      Nat.lt_of_lt_of_le himage (Nat.mul_le_mul_left u hp)
    have hcoef : c ≤ B := Nat.le_trans hc (Nat.le_mul_of_pos_left _ hu)
    have htriple : 3 ^ (v - d) * u = 3 * B := by
      rw [show v - d = (v - d - 1) + 1 by omega, Nat.pow_succ']
      dsimp [B]
      ac_rfl
    omega
  apply reject_target hr hlen ha
  rw [hy]
  exact Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega)) _

end Collatz.SuffixResidueObstruction
