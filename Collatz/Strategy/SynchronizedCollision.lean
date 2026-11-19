import Collatz.Core.Pigeonhole
import Collatz.Structure.ResidueEndpoint

/-!
# Equal-time collisions in translated intervals

The odd-step count partitions an aligned dyadic block into classes. For
small odd counts the representative endpoints fit in disjoint ternary
intervals. Large odd counts are counted using the existing parity moment.
An interval longer than the resulting capacity must contain two inputs
whose trajectories meet at the same time.
-/

namespace Collatz.SynchronizedCollision

open Collatz.Arith Collatz.Congruence Collatz.Sum

private def high (k cutoff r : Nat) : Bool := decide (cutoff < oddCount r k)

private def code (k cutoff r : Nat) : Nat :=
  if high k cutoff r then 3 ^ (cutoff + 1) + countRange r (high k cutoff)
  else 3 ^ oddCount r k + acceleratedOrbit k r

private theorem count_mono {p : Nat → Bool} {i j : Nat} (h : i ≤ j) :
    countRange i p ≤ countRange j p :=
  sumRange_mono_length _ h

private theorem rank_lt {p : Nat → Bool} {i j : Nat} (hi : p i = true) (hij : i < j) :
    countRange i p < countRange j p := by
  have hs : countRange (i + 1) p = countRange i p + 1 := by simp [countRange_succ, hi]
  have := count_mono (p := p) (show i + 1 ≤ j from hij)
  omega

private theorem light_code_bounds {k cutoff r : Nat} (hr : r < 2 ^ k)
    (h : high k cutoff r = false) :
    3 ^ oddCount r k ≤ code k cutoff r ∧ code k cutoff r < 3 ^ (oddCount r k + 1) := by
  have hrep := ResidueEndpoint.representative_lt_three_pow hr
  simp only [code, h, Bool.false_eq_true, if_false, three_pow_succ]
  omega

private theorem light_code_lt_cutoff {k cutoff r : Nat} (hr : r < 2 ^ k)
    (h : high k cutoff r = false) : code k cutoff r < 3 ^ (cutoff + 1) := by
  have ha : oddCount r k ≤ cutoff := by simpa [high] using h
  exact Nat.lt_of_lt_of_le (light_code_bounds hr h).2 (three_pow_le_three_pow (by omega))

private theorem high_count_le (b : Nat) :
    countRange (2 ^ (13 * b)) (high (13 * b) (8 * b)) ≤ 3 ^ (8 * b) := by
  have h := mul_countRange_le (w := 2 ^ (8 * b))
    (p := high (13 * b) (8 * b)) (n := 2 ^ (13 * b))
    (f := fun r => 2 ^ oddCount r (13 * b)) (by
      intro r _ hr
      have ht : 8 * b < oddCount r (13 * b) := by simpa [high] using hr
      exact two_pow_le_two_pow (Nat.le_of_lt ht))
  change _ ≤ Density.weightSum (13 * b) at h
  rw [Density.weightSum_eq] at h
  have hratio : 3 ^ (13 * b) ≤ 2 ^ (8 * b) * 3 ^ (8 * b) := by
    rw [show 13 * b = 5 * b + 8 * b by omega, Nat.pow_add,
      Nat.pow_mul 3 5 b, Nat.pow_mul 2 8 b]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 3 ^ 5 ≤ 2 ^ 8) b)
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h hratio) (two_pow_pos _)

private theorem code_lt {b r : Nat} (hr : r < 2 ^ (13 * b)) :
    code (13 * b) (8 * b) r < 4 * 3 ^ (8 * b) := by
  cases h : high (13 * b) (8 * b) r with
  | false =>
    have hl := light_code_lt_cutoff hr h
    rw [three_pow_succ] at hl
    omega
  | true =>
    have hl := rank_lt h hr
    have hb := high_count_le b
    simp [code, h, three_pow_succ]
    omega

private theorem landing_eq_of_code_eq {k cutoff m r s : Nat}
    (hr : r < 2 ^ k) (hs : s < 2 ^ k) (h : code k cutoff r = code k cutoff s) :
    acceleratedOrbit k (2 ^ k * m + r) = acceleratedOrbit k (2 ^ k * m + s) := by
  cases h₁ : high k cutoff r with
  | false =>
    cases h₂ : high k cutoff s with
    | false =>
      have hrange := light_code_bounds hr h₁
      have hsrange := light_code_bounds hs h₂
      have hcount : oddCount r k = oddCount s k := by
        rcases Nat.lt_trichotomy (oddCount r k) (oddCount s k) with hlt | heq | hgt
        · have := three_pow_le_three_pow (Nat.succ_le_of_lt hlt)
          omega
        · exact heq
        · have := three_pow_le_three_pow (Nat.succ_le_of_lt hgt)
          omega
      have hland : acceleratedOrbit k r = acceleratedOrbit k s := by
        simpa [code, h₁, h₂, hcount] using h
      rw [accOrbit_pow_two_mul_add, accOrbit_pow_two_mul_add, hcount, hland]
    | true =>
      have hl := light_code_lt_cutoff hr h₁
      have hh : 3 ^ (cutoff + 1) ≤ code k cutoff s := by simp [code, h₂]
      omega
  | true =>
    cases h₂ : high k cutoff s with
    | false =>
      have hl := light_code_lt_cutoff hs h₂
      have hh : 3 ^ (cutoff + 1) ≤ code k cutoff r := by simp [code, h₁]
      omega
    | true =>
      have hsame : countRange r (high k cutoff) = countRange s (high k cutoff) := by
        simpa [code, h₁, h₂] using h
      rcases Nat.lt_trichotomy r s with hlt | heq | hgt
      · exact False.elim (Nat.ne_of_lt (rank_lt h₁ hlt) hsame)
      · rw [heq]
      · exact False.elim (Nat.ne_of_lt (rank_lt h₂ hgt) hsame.symm)

/-- An interval of `blocks` aligned blocks of length `2^(13b)` admits at
most `blocks·4·3^(8b)` distinct synchronized images after `13b` steps. -/
theorem collision_in_aligned_blocks {f : Nat → Nat} {b lo blocks N : Nat}
    (hwin : ∀ i, i ≤ N → lo * 2 ^ (13 * b) ≤ f i ∧ f i < (lo + blocks) * 2 ^ (13 * b))
    (hsize : blocks * (4 * 3 ^ (8 * b)) ≤ N) :
    ∃ i j, i < j ∧ j ≤ N ∧ acceleratedOrbit (13 * b) (f i) = acceleratedOrbit (13 * b) (f j) := by
  let M := 2 ^ (13 * b)
  let B := 4 * 3 ^ (8 * b)
  let rcode := fun i => code (13 * b) (8 * b) (f i % M)
  let label := fun i => B * (f i / M - lo) + rcode i
  have hM : 0 < M := two_pow_pos _
  have hB : 0 < B := Nat.mul_pos (by decide) (three_pow_pos _)
  have hq : ∀ i, i ≤ N → lo ≤ f i / M ∧ f i / M < lo + blocks := by
    intro i hi
    exact ⟨(Nat.le_div_iff_mul_le hM).mpr (hwin i hi).1, (Nat.div_lt_iff_lt_mul hM).mpr (hwin i hi).2⟩
  have hcode (i : Nat) : rcode i < B := code_lt (Nat.mod_lt _ hM)
  have hlabel (i : Nat) (hi : i ≤ N) : label i < blocks * B := by
    have hq' := hq i hi
    calc
      label i < B * (f i / M - lo) + B := Nat.add_lt_add_left (hcode i) _
      _ = (f i / M - lo + 1) * B := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm B (f i / M - lo)]
      _ ≤ blocks * B := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨i, j, hij, hj, heq⟩ := Pigeonhole.exists_repeat hlabel hsize
  have hi := Nat.le_trans (Nat.le_of_lt hij) hj
  have hdiv (i : Nat) : label i / B = f i / M - lo := by
    dsimp [label]
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt (hcode i), Nat.add_zero]
  have hmod (i : Nat) : label i % B = rcode i := by
    dsimp [label]
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hcode i)]
  have hqeq : f i / M = f j / M := by
    have hd := congrArg (fun z => z / B) heq
    rw [hdiv, hdiv] at hd
    have := (hq i hi).1
    have := (hq j hj).1
    omega
  have hceq : rcode i = rcode j := by
    have hm := congrArg (fun z => z % B) heq
    rwa [hmod, hmod] at hm
  refine ⟨i, j, hij, hj, ?_⟩
  have h := landing_eq_of_code_eq (Nat.mod_lt (f i) hM) (Nat.mod_lt (f j) hM)
    (m := f i / M) hceq
  change acceleratedOrbit (13 * b) (M * (f i / M) + f i % M) =
    acceleratedOrbit (13 * b) (M * (f i / M) + f j % M) at h
  rw [Nat.div_add_mod, hqeq, Nat.div_add_mod] at h
  exact h

/-- If an interval of length `2^(13b)` contains more than `8·3^(8b)`
listed states, two of their endpoints after `13b` steps agree. -/
theorem collision_in_interval {f : Nat → Nat} {b lo N : Nat}
    (hwin : ∀ i, i ≤ N → lo ≤ f i ∧ f i < lo + 2 ^ (13 * b))
    (hsize : 8 * 3 ^ (8 * b) ≤ N) :
    ∃ i j, i < j ∧ j ≤ N ∧ acceleratedOrbit (13 * b) (f i) = acceleratedOrbit (13 * b) (f j) := by
  let M := 2 ^ (13 * b)
  let q := lo / M
  have hM : 0 < M := two_pow_pos _
  have hlo : q * M ≤ lo := (Nat.le_div_iff_mul_le hM).mp (Nat.le_refl _)
  have hhi : lo < (q + 1) * M := (Nat.div_lt_iff_lt_mul hM).mp (Nat.lt_succ_self _)
  apply collision_in_aligned_blocks (lo := q) (blocks := 2)
  · intro i hi
    have h := hwin i hi
    change q * M ≤ f i ∧ f i < (q + 2) * M
    refine ⟨Nat.le_trans hlo h.1, ?_⟩
    have ht : (q + 2) * M = (q + 1) * M + M := by
      rw [show q + 2 = q + 1 + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hf : f i < lo + M := h.2
    omega
  · omega

/-- On a nonrepeating trajectory, any distinct visit indices in one such
interval have cardinality at most `8·3^(8b)`. -/
theorem nonrepeating_interval_visits {n b lo N : Nat} {visit : Nat → Nat}
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hvisits : ∀ i j, i < j → j < N → visit i ≠ visit j)
    (hwin : ∀ i, i < N → lo ≤ acceleratedOrbit (visit i) n ∧
      acceleratedOrbit (visit i) n < lo + 2 ^ (13 * b)) : N ≤ 8 * 3 ^ (8 * b) := by
  apply Nat.le_of_not_gt
  intro htoo
  obtain ⟨i, j, hij, hj, hmerge⟩ := collision_in_interval (N := 8 * 3 ^ (8 * b))
    (fun i hi => hwin i (Nat.lt_of_le_of_lt hi htoo)) (Nat.le_refl _)
  rw [acceleratedOrbit_add, acceleratedOrbit_add] at hmerge
  exact hvisits i j hij (Nat.lt_of_le_of_lt hj htoo) (by have := hnr _ _ hmerge; omega)

end Collatz.SynchronizedCollision
