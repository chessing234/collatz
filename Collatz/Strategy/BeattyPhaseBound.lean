import Collatz.Strategy.BeattyPhaseCertificate

/-!
# A uniform block bound for the normalized Beatty accumulator

The phase of a block starting at `j` is `2 ^ fexp j / 3 ^ j`.
A dyadic interval for that phase bounds all carry decisions in a block.
Checking the finite phase grid gives a uniform charge for blocks at
arbitrarily large indices.
-/

namespace Collatz.BeattyPhaseBound

open RealizableBound BeattyPhaseCertificate

private theorem fexp_eq_log2 (i : Nat) : (3 ^ i : Nat).log2 = fexp i :=
  (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.pow_pos (by decide)))).mpr (fexp_spec i)

/-- The lower end of a phase bucket gives a conservative carry test. -/
private theorem power_le_bucket_weight {D z j i : Nat}
    (hlo : (z - 1) * 3 ^ j < D * 2 ^ fexp j) :
    2 ^ fexp (j + i) ≤ 2 ^ fexp j * bucketWeight D z i := by
  unfold bucketWeight
  dsimp only
  rw [fexp_eq_log2]
  let P := 2 ^ fexp j
  let p := 2 ^ fexp i
  let Q := 3 ^ j
  let q := 3 ^ i
  have hupper : fexp (j + i) ≤ fexp j + (fexp i + 1) := by
    have hpow := Nat.mul_lt_mul_of_lt_of_le (lt_fexp j) (Nat.le_of_lt (lt_fexp i))
      (Nat.pow_pos (by decide))
    rw [← Nat.pow_add, ← Nat.pow_add] at hpow
    have hlog := (Nat.log2_lt (Nat.ne_of_gt (Nat.pow_pos (by decide)))).mpr hpow
    rw [fexp_eq_log2] at hlog
    omega
  change (z - 1) * Q < D * P at hlo
  change 2 ^ fexp (j + i) ≤ P * (if (z - 1) * (2 * p) < D * q then 2 * p else p)
  have hsplit : (2 : Nat) ^ (fexp j + (fexp i + 1)) = P * (2 * p) := by
    rw [Nat.pow_add, Nat.pow_succ']
  by_cases hcarry : (z - 1) * (2 * p) < D * q
  · rw [if_pos hcarry, ← hsplit]
    exact Nat.pow_le_pow_right (by decide) hupper
  · rw [if_neg hcarry]
    have hsmall : fexp (j + i) ≤ fexp j + fexp i := by
      apply Nat.le_of_not_gt
      intro hlarge
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hlarge)
      change 2 ^ (fexp j + fexp i + 1) ≤ 2 ^ fexp (j + i) at hpow
      rw [Nat.add_assoc, hsplit] at hpow
      have hprod : P * (2 * p) ≤ Q * q := by
        rw [← Nat.pow_add]
        exact Nat.le_trans hpow (fexp_le (j + i))
      have htest : Q * ((z - 1) * (2 * p)) < Q * (D * q) := by
        calc
          _ = ((z - 1) * Q) * (2 * p) := by ac_rfl
          _ < (D * P) * (2 * p) := Nat.mul_lt_mul_of_pos_right hlo
            (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
          _ = D * (P * (2 * p)) := Nat.mul_assoc ..
          _ ≤ D * (Q * q) := Nat.mul_le_mul_left _ hprod
          _ = _ := by ac_rfl
      exact hcarry (Nat.lt_of_mul_lt_mul_left htest)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
    rwa [Nat.pow_add] at hp

private theorem Bcap_add_le_bucket {D z j : Nat}
    (hlo : (z - 1) * 3 ^ j < D * 2 ^ fexp j) (r : Nat) :
    Bcap (j + r) ≤ 3 ^ r * Bcap j + 2 ^ fexp j * bucketSum D z r := by
  induction r with
  | zero => simp [bucketSum]
  | succ r ih =>
    rw [Nat.add_succ, Bcap_succ, bucketSum, Nat.pow_succ']
    calc
      _ ≤ 3 * (3 ^ r * Bcap j + 2 ^ fexp j * bucketSum D z r) +
          2 ^ fexp j * bucketWeight D z r :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ih) (power_le_bucket_weight hlo)
      _ = _ := by simp only [Nat.mul_add]; ac_rfl

private theorem beatty_block (j : Nat) :
    10000 * Bcap (j + 53) ≤ 3 ^ 53 * (10000 * Bcap j) + (2431 * 53) * 3 ^ (j + 53) := by
  let P := 2 ^ fexp j
  let Q := 3 ^ j
  let z := (512 * P - 1) / Q + 1
  have hQ : 0 < Q := Nat.pow_pos (by decide)
  have hP : 0 < P := Nat.two_pow_pos _
  have hPQ : P ≤ Q := fexp_le j
  have hdiv := Nat.div_add_mod (512 * P - 1) Q
  have hmod := Nat.mod_lt (512 * P - 1) hQ
  have hzlo : (z - 1) * Q < 512 * P := by
    dsimp only [z]
    rw [Nat.add_sub_cancel, Nat.mul_comm]
    omega
  have hzhi : 512 * P ≤ z * Q := by
    dsimp only [z]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((512 * P - 1) / Q)]
    omega
  have hzle : z ≤ 512 := by
    apply Nat.le_of_not_gt
    intro h
    have hle := Nat.mul_le_mul_right Q (show 512 ≤ z - 1 by omega)
    have hpq := Nat.mul_le_mul_left 512 hPQ
    omega
  have hcert := of_decide_eq_true ((List.all_eq_true.mp bucket_certificate) z
    (List.mem_range.mpr (by omega : z < 513)))
  have hcost : 10000 * P * bucketSum 512 z 53 ≤ (2431 * 53) * 3 ^ (j + 53) := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 512)
    calc
      _ = (10000 * bucketSum 512 z 53) * (512 * P) := by ac_rfl
      _ ≤ (10000 * bucketSum 512 z 53) * (z * Q) := Nat.mul_le_mul_left _ hzhi
      _ = Q * (10000 * z * bucketSum 512 z 53) := by ac_rfl
      _ ≤ Q * (512 * (2431 * 53) * 3 ^ 53) := Nat.mul_le_mul_left _ hcert
      _ = _ := by rw [Nat.pow_add]; dsimp only [Q]; ac_rfl
  have hsum := Nat.mul_le_mul_left 10000 (Bcap_add_le_bucket hzlo 53)
  calc
    _ ≤ 10000 * (3 ^ 53 * Bcap j + P * bucketSum 512 z 53) := hsum
    _ = 3 ^ 53 * (10000 * Bcap j) + 10000 * P * bucketSum 512 z 53 := by
      rw [Nat.mul_add]
      congr 1 <;> ac_rfl
    _ ≤ _ := Nat.add_le_add_left hcost _

/-- A normalized charge of `2431 / 10000` per odd step plus
`1500 / 10000` covers the entire Beatty accumulator. -/
theorem beatty_charge (a : Nat) : 10000 * Bcap a ≤ (2431 * a + 1500) * 3 ^ a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : a < 53
    · exact of_decide_eq_true ((List.all_eq_true.mp tail_certificate) a (List.mem_range.mpr h))
    let j := a - 53
    have heq : j + 53 = a := Nat.sub_add_cancel (by omega)
    have hj := ih j (by omega)
    calc
      _ = 10000 * Bcap (j + 53) := by rw [heq]
      _ ≤ 3 ^ 53 * (10000 * Bcap j) + (2431 * 53) * 3 ^ (j + 53) := beatty_block j
      _ ≤ 3 ^ 53 * ((2431 * j + 1500) * 3 ^ j) + (2431 * 53) * 3 ^ (j + 53) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hj) _
      _ = (2431 * a + 1500) * 3 ^ a := by
        rw [← heq, Nat.pow_add, Nat.mul_add]
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl

end Collatz.BeattyPhaseBound
