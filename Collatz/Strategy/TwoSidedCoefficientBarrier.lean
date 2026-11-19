import Collatz.Structure.ResidueEndpoint
import Collatz.Strategy.AccumulatorArith
import Collatz.Strategy.ThreeAdicEscape
import Collatz.Strategy.CoefficientEscape
import Collatz.Exploration.DyadicConvergentClasses
import Collatz.Strategy.NeverDrops

/-! A forward window and a backward window with fixed odd-step budget
cannot by themselves force coefficient stopping. The witnesses are
positive integers with arbitrarily large magnitude. -/

namespace Collatz.TwoSidedCoefficientBarrier

open Collatz.Arith Collatz.Density Collatz.Reach

private theorem zero_orbit (k : Nat) : acceleratedOrbit k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [acceleratedOrbit_succ_step, ih]; decide

/-- A terminal value congruent to one modulo `3^H` has no expanding
ancestor prefix with at most `H` odd steps. Proper-prefix constraints
are unnecessary for this obstruction. -/
theorem no_expanding_ancestor_of_mod_one {m k H : Nat}
    (hres : acceleratedOrbit k m % 3 ^ H = 1) (hcount : oddCount m k ≤ H) :
    3 ^ oddCount m k ≤ 2 ^ k := by
  apply Nat.le_of_not_gt
  intro hlarge
  let a := oddCount m k
  let r := m % 2 ^ k
  have ha : 0 < a := by
    by_cases hz : a = 0
    · change 2 ^ k < 3 ^ a at hlarge
      rw [hz, Nat.pow_zero] at hlarge
      exact False.elim (Nat.not_lt_of_ge (one_le_two_pow k) hlarge)
    · omega
  have hmod : acceleratedOrbit k m % 3 ^ a = 1 := by
    rw [← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 hcount), hres]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 3) (three_le_three_pow ha))
  have hland : acceleratedOrbit k r = 1 :=
    (ResidueEndpoint.quotient_remainder m k).2.symm.trans hmod
  obtain ⟨c, hc⟩ := acceleratedOrbit_affine r k
  rw [hland, Nat.mul_one, ← oddCount_mod m k] at hc
  have hr : r = 0 := by
    by_cases hz : r = 0
    · exact hz
    · have hmul := Nat.le_mul_of_pos_right (3 ^ a) (by omega : 0 < r)
      change 2 ^ k = 3 ^ a * r + c at hc
      change 2 ^ k < 3 ^ a at hlarge
      omega
  rw [hr, zero_orbit] at hland
  omega

private theorem prefix_one_odd (m k : Nat) (h : 0 < oddCount m k) :
    ∃ i, 0 < i ∧ i ≤ k ∧ oddCount m i = 1 := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    by_cases hp : 0 < oddCount m k
    · obtain ⟨i, hi, hik, hcount⟩ := ih hp
      exact ⟨i, hi, by omega, hcount⟩
    · rw [oddCount_succ_last] at h
      refine ⟨k + 1, by omega, Nat.le_refl _, ?_⟩
      rw [oddCount_succ_last]
      omega

private theorem one_cycle_count (j : Nat) :
    acceleratedOrbit (2 * j) 1 = 1 ∧ oddCount 1 (2 * j) = j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, AccumulatorArith.oddCount_add,
      ← Nat.add_comm 2 (2 * j), ← acceleratedOrbit_add, ih.1, ih.2]
    exact ⟨by decide, rfl⟩

private theorem one_cycle_length {l H : Nat} (hl : acceleratedOrbit l 1 = 1)
    (hcount : oddCount 1 l = H) : l = 2 * H := by
  have hsplit := Nat.div_add_mod l 2
  rcases mod_two_eq_zero_or_one l with h0 | h1
  · have he : l = 2 * (l / 2) := by omega
    have hc := (one_cycle_count (l / 2)).2
    rw [← he, hcount] at hc
    omega
  · have he : l = 2 * (l / 2) + 1 := by omega
    rw [he, acceleratedOrbit_succ_step, (one_cycle_count (l / 2)).1,
      acceleratedStep_one] at hl
    omega

private theorem twice_three_pow_le_four_pow {H : Nat} (h : 3 ≤ H) :
    2 * 3 ^ H ≤ 4 ^ H := by
  induction H with
  | zero => omega
  | succ H ih =>
    by_cases hH : 3 ≤ H
    · rw [Nat.pow_succ, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_right 3 (ih hH))
        (Nat.mul_le_mul_left (4 ^ H) (by decide))
    · have he : H = 2 := by omega
      subst H
      decide

/-- Above ternary depth two, the congruence to one excludes expansion even
with one more odd step than the depth. The suffix after the first odd step
would have to follow the cycle of one for its entire reduced window. -/
theorem no_expanding_ancestor_of_mod_one_extra {m k H : Nat} (hH : 3 ≤ H)
    (hres : acceleratedOrbit k m % 3 ^ H = 1) (hcount : oddCount m k ≤ H + 1) :
    3 ^ oddCount m k ≤ 2 ^ k := by
  by_cases hc : oddCount m k ≤ H
  · exact no_expanding_ancestor_of_mod_one hres hc
  apply Nat.le_of_not_gt
  intro hg
  have ha : oddCount m k = H + 1 := by omega
  obtain ⟨i, hi, hik, ho⟩ := prefix_one_odd m k (by omega)
  let l := k - i
  let u := acceleratedOrbit i m
  let r := u % 2 ^ l
  have hk : i + l = k := by dsimp [l]; omega
  have hu : oddCount u l = H := by
    have h := AccumulatorArith.oddCount_add m i l
    rw [hk, ha, ho] at h
    change _ = 1 + oddCount u l at h
    omega
  have hlt : 2 ^ l < 2 * 3 ^ H := by
    have hp : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    rw [ha, Nat.pow_succ] at hg
    omega
  have hland : acceleratedOrbit l r = 1 := by
    rw [← (ResidueEndpoint.quotient_remainder u l).2, hu]
    rw [show u = acceleratedOrbit i m from rfl, acceleratedOrbit_add, Nat.add_comm l i, hk]
    exact hres
  have hr : oddCount r l = H := (oddCount_mod u l).symm.trans hu
  obtain ⟨c, hc⟩ := acceleratedOrbit_affine r l
  rw [hland, Nat.mul_one, hr] at hc
  have hrle : r ≤ 1 := by
    apply Nat.le_of_not_gt
    intro hnot
    have hm := Nat.mul_le_mul_left (3 ^ H) (by omega : 2 ≤ r)
    rw [Nat.mul_comm (3 ^ H) 2] at hm
    omega
  have hrpos : r ≠ 0 := by
    intro hz
    rw [hz, zero_orbit] at hland
    omega
  have hrone : r = 1 := by omega
  rw [hrone] at hland hr
  rw [one_cycle_length hland hr, Nat.pow_mul] at hlt
  exact Nat.not_lt_of_ge (twice_three_pow_le_four_pow hH) hlt

private theorem mod_eq_last_of_dvd_succ {n d : Nat} (hd : 0 < d) (h : d ∣ n + 1) :
    n % d = d - 1 := by
  obtain ⟨q, hq⟩ := h
  have hqp : 1 ≤ q := by
    cases q with
    | zero => simp at hq
    | succ _ => omega
  have hsplit : d * (q - 1) + d = d * q := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have he : n = d - 1 + d * (q - 1) := by omega
  rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem joint_residue (K d : Nat) (hd : 1 < d) (hodd : d % 2 = 1) :
    ∃ r, r < 2 ^ K * d ∧ r % d = 1 ∧ 2 ^ K ∣ r + 1 := by
  induction K with
  | zero => exact ⟨1, by simpa, Nat.mod_eq_of_lt hd, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr, hm, q, hq⟩ := ih
    let e := q % 2
    let r' := r + 2 ^ k * d * e
    have he : e ≤ 1 := by dsimp [e]; omega
    have hd' : (q + d * e) % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, hodd, Nat.one_mul]
      dsimp [e]
      rw [Nat.mod_mod]
      omega
    have hq' : q + d * e = 2 * ((q + d * e) / 2) := by
      have ht := Nat.div_add_mod (q + d * e) 2
      omega
    refine ⟨r', ?_, ?_, (q + d * e) / 2, ?_⟩
    · have hstep := Nat.mul_le_mul_left (2 ^ k * d) he
      rw [Nat.mul_one] at hstep
      rw [two_pow_succ, Nat.mul_assoc]
      dsimp [r']
      omega
    · change (r + 2 ^ k * d * e) % d = 1
      rw [show 2 ^ k * d * e = d * (2 ^ k * e) by ac_rfl, Nat.add_mul_mod_self_left, hm]
    · calc
        r' + 1 = (r + 1) + 2 ^ k * (d * e) := by dsimp [r']; ac_rfl
        _ = 2 ^ k * (q + d * e) := by rw [hq, Nat.mul_add]
        _ = 2 ^ k * (2 * ((q + d * e) / 2)) := congrArg (fun z => 2 ^ k * z) hq'
        _ = _ := by rw [← Nat.mul_assoc, ← Nat.pow_succ]

private theorem joint_witness_in_interval (K H lower : Nat) (hH : 0 < H) :
    ∃ n, lower ≤ n ∧ n < lower + 2 ^ K * 3 ^ H ∧ n % 3 ^ H = 1 ∧ 2 ^ K ∣ n + 1 := by
  let d := 3 ^ H
  let W := 2 ^ K * d
  have hd : 1 < d := Nat.lt_of_lt_of_le (by decide : 1 < 3) (three_le_three_pow hH)
  have hw : 0 < W := Nat.mul_pos (two_pow_pos K) (three_pow_pos H)
  obtain ⟨r, hr, hmod, hdiv⟩ := joint_residue K d hd (three_pow_odd H)
  let q := if lower % W ≤ r then lower / W else lower / W + 1
  let n := W * q + r
  have hr' : r < W := hr
  have hlohi : lower ≤ n ∧ n < lower + W := by
    have hbase := Nat.div_add_mod lower W
    have hsmall := Nat.mod_lt lower hw
    dsimp [n, q]
    split
    · omega
    · rw [Nat.mul_add, Nat.mul_one]
      omega
  have hterm : n % 3 ^ H = 1 := by
    change (W * q + r) % d = 1
    have hshift : W * q = d * (2 ^ K * q) := by dsimp [W]; ac_rfl
    rw [hshift, Nat.add_comm, Nat.add_mul_mod_self_left, hmod]
  have hdvd : 2 ^ K ∣ n + 1 := by
    change 2 ^ K ∣ (W * q + r) + 1
    rw [Nat.add_assoc]
    exact Nat.dvd_add ⟨d * q, by dsimp [W]; ac_rfl⟩ hdiv
  exact ⟨n, hlohi.1, hlohi.2, hterm, hdvd⟩

private theorem all_odd_of_pow_two_dvd_succ {n k : Nat} (h : 2 ^ k ∣ n + 1) : oddCount n k = k := by
  rw [oddCount_mod n k, mod_eq_last_of_dvd_succ (two_pow_pos k) h,
    Obstruction.oddCount_two_pow_sub_one]

private theorem forward_expansion_of_all_odd {n K L k : Nat} (hodd : 2 ^ K ∣ n + 1)
    (hroom : K < k → 2 ^ L < 3 ^ K) (hk : 0 < k) (hle : k ≤ L) : 2 ^ k < 3 ^ oddCount n k := by
  by_cases hkK : k ≤ K
  · rw [all_odd_of_pow_two_dvd_succ (Nat.dvd_trans (Nat.pow_dvd_pow 2 hkK) hodd)]
    exact Obstruction.two_pow_lt_three_pow hk
  · have hcount : K ≤ oddCount n k := by
      rw [← show K + (k - K) = k by omega, AccumulatorArith.oddCount_add,
        all_odd_of_pow_two_dvd_succ hodd]
      omega
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hle)
      (Nat.lt_of_lt_of_le (hroom (by omega)) (Nat.pow_le_pow_right (by decide) hcount))

/-- Every interval of length `2^K·3^H` contains a start passing both fixed
tests. Its forward prefixes through `K` expand, and no backward prefix
with at most `H` odd steps expands into it. -/
theorem fixed_window_witness_in_interval (K H lower : Nat) (hH : 0 < H) :
    ∃ n, lower ≤ n ∧ n < lower + 2 ^ K * 3 ^ H ∧
      (∀ k, 0 < k → k ≤ K → 2 ^ k < 3 ^ oddCount n k) ∧
      ∀ m k, oddCount m k ≤ H → acceleratedOrbit k m = n → 3 ^ oddCount m k ≤ 2 ^ k := by
  obtain ⟨n, hlo, hhi, hterm, hdvd⟩ := joint_witness_in_interval K H lower hH
  refine ⟨n, hlo, hhi, fun _ hp hk => forward_expansion_of_all_odd hdvd (by omega) hp hk, ?_⟩
  intro m k hcount hland
  exact no_expanding_ancestor_of_mod_one (by rw [hland, hterm]) hcount

/-- An orbit ending at a multiple of three has used only even steps. -/
theorem oddCount_eq_zero_of_terminal_dvd_three {m k : Nat} (h : 3 ∣ acceleratedOrbit k m) :
    oddCount m k = 0 := by
  induction k generalizing m with
  | zero => exact Congruence.oddCount_zero m
  | succ k ih =>
    rw [acceleratedOrbit_succ] at h
    have hd := (ThreeAdicEscape.orbit_divisible_three_iff k (acceleratedStep m)).mp h
    have hstep : 3 ∣ acceleratedStep m := Nat.dvd_trans (Nat.dvd_mul_right 3 (2 ^ k)) hd
    have hm : m % 2 = 0 := by
      rcases mod_two_eq_zero_or_one m with h0 | h1
      · exact h0
      · have hmod := ThreeAdicEscape.odd_image_mod_three h1
        rw [Nat.dvd_iff_mod_eq_zero] at hstep
        omega
    rw [Congruence.oddCount_succ_of_even hm]
    exact ih h

/-- A `2j`-bit start can survive `3j` forward steps and every backward
depth simultaneously. The examples are multiples of three. -/
theorem unbounded_backward_window_family {j : Nat} (hj : 0 < j) :
    let n := 2 ^ (2 * j) - 1
    (∀ k, 0 < k → k ≤ 3 * j → 2 ^ k < 3 ^ oddCount n k) ∧
      ∀ m k, acceleratedOrbit k m = n → oddCount m k = 0 := by
  let n := 2 ^ (2 * j) - 1
  have hns : n + 1 = 2 ^ (2 * j) := Nat.sub_add_cancel (one_le_two_pow _)
  constructor
  · intro k hk hkj
    have hd : 2 ^ (2 * j) ∣ n + 1 := by rw [hns]; exact Nat.dvd_refl _
    apply forward_expansion_of_all_odd hd _ hk hkj
    intro _
    rw [Nat.pow_mul, Nat.pow_mul]
    exact Nat.pow_lt_pow_left (by decide) (by omega)
  · intro m k he
    have hmod : 2 ^ (2 * j) % 3 = 1 := by
      rw [Nat.pow_mul, Nat.pow_mod (2 ^ 2) j 3]
      change 1 ^ j % 3 = 1
      rw [Nat.one_pow]
    apply oddCount_eq_zero_of_terminal_dvd_three
    rw [he, Nat.dvd_iff_mod_eq_zero]
    omega

/-- At arbitrarily large binary lengths, a nonmultiple of three passes
every forward prefix through its full bit length and every backward test
up to a number of odd steps linear in that length. -/
theorem full_bit_length_unit_witness {b : Nat} (hb : 0 < b) :
    ∃ n, 2 ^ (100 * b) ≤ n ∧ n < 2 ^ (100 * b + 1) ∧ n % 3 = 1 ∧
      (∀ k, 0 < k → k ≤ 100 * b + 1 → 2 ^ k < 3 ^ oddCount n k) ∧
      ∀ m k, oddCount m k ≤ 22 * b + 1 → acceleratedOrbit k m = n → 3 ^ oddCount m k ≤ 2 ^ k := by
  have hroom : 2 ^ (100 * b + 1) < 3 ^ (64 * b + 1) := by
    have hp : (2 ^ 100 : Nat) ^ b ≤ (3 ^ 64 : Nat) ^ b :=
      Nat.pow_le_pow_left (by decide +kernel) b
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_mul, Nat.pow_mul]
    have hpos : 0 < (3 ^ 64 : Nat) ^ b := Nat.pow_pos (by decide)
    omega
  have hwidth : 2 ^ (64 * b + 1) * 3 ^ (22 * b) ≤ 2 ^ (100 * b) := by
    have h2 : 2 ≤ 2 ^ b := two_le_two_pow hb
    calc
      2 ^ (64 * b + 1) * 3 ^ (22 * b) = 2 * ((2 ^ 64 * 3 ^ 22 : Nat) ^ b) := by
        rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_mul, Nat.mul_pow]
        ac_rfl
      _ ≤ 2 ^ b * (2 ^ 64 * 3 ^ 22 : Nat) ^ b := Nat.mul_le_mul_right _ h2
      _ = (2 * (2 ^ 64 * 3 ^ 22) : Nat) ^ b := (Nat.mul_pow ..).symm
      _ ≤ 2 ^ (100 * b) := by
        rw [Nat.pow_mul]
        exact Nat.pow_le_pow_left (by decide +kernel) b
  obtain ⟨n, hlo, hhi, hterm, hdvd⟩ := joint_witness_in_interval (64 * b + 1) (22 * b)
    (2 ^ (100 * b)) (by omega)
  have hnhigh : n < 2 ^ (100 * b + 1) := by rw [Nat.pow_succ]; omega
  have hmod : n % 3 = 1 := by
    have hpow : 3 ∣ 3 ^ (22 * b) := by simpa using Nat.pow_dvd_pow 3 (by omega : 1 ≤ 22 * b)
    rw [← Nat.mod_mod_of_dvd _ hpow, hterm]
  refine ⟨n, hlo, hnhigh, hmod, fun _ hp hk => forward_expansion_of_all_odd hdvd (fun _ => hroom) hp hk, ?_⟩
  intro m k hcount hland
  exact no_expanding_ancestor_of_mod_one_extra (by omega) (by rw [hland, hterm]) hcount

private theorem convergent_unit_expansion (L : Nat) :
    ∃ n, 0 < n ∧ ¬ 3 ∣ n ∧ ReachesOne n ∧
      ∀ k, 0 < k → k ≤ L → 2 ^ k < 3 ^ oddCount n k := by
  let W := 2 ^ (L + 1)
  have hw : 1 < W := two_le_two_pow (Nat.succ_pos _)
  obtain ⟨m, hm, hmod, hreach⟩ :=
    Exploration.DyadicConvergentClasses.every_dyadic_class (L + 1) (W - 1) 0
  change m % W = (W - 1) % W at hmod
  rw [Nat.mod_eq_of_lt (by omega : W - 1 < W)] at hmod
  have hd : W ∣ m + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod, Nat.mod_eq_of_lt hw,
      Nat.sub_add_cancel (by omega : 1 ≤ W), Nat.mod_self]
  have hodd : m % 2 = 1 := by
    have h2 := Nat.dvd_trans (by simpa using Nat.pow_dvd_pow 2 (Nat.succ_le_succ (Nat.zero_le L))) hd
    have he := mod_eq_last_of_dvd_succ (by decide : 0 < 2) h2
    exact he
  let n := acceleratedStep m
  have hn : 0 < n := acceleratedOrbit_positive hm 1
  have hunit : ¬ 3 ∣ n := ThreeAdicEscape.odd_escape_persistent hodd 0
  refine ⟨n, hn, hunit, (Reach.reachesOne_accStep_iff hm).mp hreach, ?_⟩
  intro k hk hkL
  have hdk := Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.succ_le_succ hkL)) hd
  have hc := all_odd_of_pow_two_dvd_succ hdk
  rw [Congruence.oddCount_succ_of_odd hodd] at hc
  change oddCount n k + 1 = k + 1 at hc
  rw [Nat.add_right_cancel hc]
  exact Obstruction.two_pow_lt_three_pow hk

private theorem crossing_of_reaches_one {n : Nat} (hn : 0 < n) (h : ReachesOne n) :
    ∃ k, 3 ^ oddCount n k < 2 ^ k := by
  obtain ⟨i, hi⟩ := (NeverDrops.accReachesOne_iff hn).mp h
  have he : acceleratedOrbit i n = acceleratedOrbit (i + 2) n := by
    rw [Nat.add_comm i 2, ← acceleratedOrbit_add, hi]
    decide
  simpa using CoefficientEscape.factor_crossing_of_repeat hn ⟨i, i + 2, by omega, he⟩ 1

private theorem bounded_convergent_crossing (B : Nat) :
    ∃ L, ∀ n, 0 < n → n ≤ B → ReachesOne n → ∃ k, k ≤ L ∧ 3 ^ oddCount n k < 2 ^ k := by
  induction B with
  | zero => exact ⟨0, fun n hn hb => by omega⟩
  | succ B ih =>
    obtain ⟨L, hL⟩ := ih
    by_cases hc : ReachesOne (B + 1)
    · obtain ⟨k, hk⟩ := crossing_of_reaches_one (Nat.succ_pos B) hc
      refine ⟨L + k, fun n hn hB hreach => ?_⟩
      by_cases hle : n ≤ B
      · obtain ⟨t, ht, hcross⟩ := hL n hn hle hreach
        exact ⟨t, by omega, hcross⟩
      · have he : n = B + 1 := by omega
        exact ⟨k, by omega, he ▸ hk⟩
    · refine ⟨L, fun n hn hB hreach => hL n hn ?_ hreach⟩
      by_cases hle : n ≤ B
      · exact hle
      · have he : n = B + 1 := by omega
        exact False.elim (hc (he ▸ hreach))

/-- Even with unrestricted ancestor depth, no fixed forward horizon can
certify the two-sided unit cover. The witnesses can be arbitrarily large
and reach one. -/
theorem convergent_witness_with_unrestricted_ancestors (K B : Nat) :
    ∃ x, B < x ∧ ¬ 3 ∣ x ∧ ReachesOne x ∧
      (∀ t, 0 < t → t ≤ K → 2 ^ t < 3 ^ oddCount x t) ∧
      ∀ m k, 0 < m → acceleratedOrbit k m = x →
        (¬ 3 ∣ m → 3 ^ oddCount m k ≤ 2 ^ k) ∧ 2 * 3 ^ oddCount m k ≤ 3 * 2 ^ k := by
  obtain ⟨L, hL⟩ := bounded_convergent_crossing B
  obtain ⟨x, hx, ⟨hunit, hreach, hstay⟩, hmin⟩ := Minimum.exists_min_pos
    (P := fun n => (¬ 3 ∣ n) ∧ ReachesOne n ∧
      ∀ t, 0 < t → t ≤ L + K → 2 ^ t < 3 ^ oddCount n t)
    (convergent_unit_expansion (L + K))
  have hxB : B < x := by
    apply Nat.lt_of_not_ge
    intro hle
    obtain ⟨k, hkL, hk⟩ := hL x hx hle hreach
    have hkpos : 0 < k := by
      cases k with
      | zero => simp [Congruence.oddCount_zero] at hk
      | succ k => exact Nat.succ_pos _
    exact Nat.not_lt_of_ge (Nat.le_of_lt (hstay k hkpos (by omega))) hk
  have hback (m k : Nat) (hm : 0 < m) (hmu : ¬ 3 ∣ m) (hland : acceleratedOrbit k m = x) :
      3 ^ oddCount m k ≤ 2 ^ k := by
    apply Nat.le_of_not_gt
    intro he
    obtain ⟨j, _, hj, hjx, hwindow⟩ := CoefficientEscape.smaller_start_of_expanding_ancestor hm hland he
    have hmr : ReachesOne m := Reach.reachesOne_of_accOrbit hm (hland ▸ hreach)
    exact hmin (acceleratedOrbit j m) hj hjx ⟨ThreeAdicEscape.never_enters_three hmu j,
      (Reach.reachesOne_accOrbit_iff hm j).mp hmr, fun t ht htK => hwindow _ hstay t ht (by omega)⟩
  exact ⟨x, hxB, hunit, hreach, fun t ht htK => hstay t ht (by omega), fun m k hm hland =>
    ⟨fun hmu => hback m k hm hmu hland, CoefficientEscape.ancestor_bound_of_unit_ancestor_bound hback hm hland⟩⟩

/-- A concrete witness when the forward depth is the binary length of
the start and the backward odd count can reach its ternary length. -/
theorem length_window_witness_223 :
    (∀ k, 0 < k → k ≤ 8 → 2 ^ k < 3 ^ oddCount 223 k) ∧
      ∀ m k, oddCount m k ≤ 6 → acceleratedOrbit k m = 223 → 3 ^ oddCount m k ≤ 2 ^ k := by
  constructor
  · have h : ∀ k : Fin 9, 0 < k.val → 2 ^ k.val < 3 ^ oddCount 223 k.val := by decide +kernel
    exact fun k hk hk8 => h ⟨k, by omega⟩ hk
  · intro m k ha ht
    apply Nat.le_of_not_gt
    intro he
    have hbound := Nat.pow_le_pow_right (by decide : 0 < 3) ha
    have hk : k < 10 := by
      apply Nat.lt_of_not_ge
      intro hge
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hge
      omega
    obtain ⟨c, hc⟩ := acceleratedOrbit_affine m k
    rw [ht] at hc
    have hm : m < 223 := by
      apply Nat.lt_of_not_ge
      intro hge
      have hp := Nat.mul_le_mul_left (3 ^ oddCount m k) hge
      have hx := Nat.mul_lt_mul_of_pos_right he (by decide : 0 < 223)
      omega
    have h : ∀ (m : Fin 223) (k : Fin 10), acceleratedOrbit k.val m.val = 223 →
        3 ^ oddCount m.val k.val ≤ 2 ^ k.val := by decide +kernel
    exact Nat.not_lt_of_ge (h ⟨m, hm⟩ ⟨k, hk⟩ ht) he

end Collatz.TwoSidedCoefficientBarrier
