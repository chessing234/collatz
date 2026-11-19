import Collatz.Accelerated

/-!
# Threshold covering for the accelerated map

The map is `T(n) = n/2` when `n` is even and `(3n+1)/2` when `n` is odd.
After `j` steps with `a` odd inputs,

    2^j · T^j(n) = 3^a · n + c(n,j),

and `c(n,j)` is a nonnegative integer. Whenever `3^a < 2^j`, the iterate
drops below the start if and only if `n` lies strictly above the threshold
`c(n,j) / (2^j − 3^a)`. A strict drop is impossible when `3^a ≥ 2^j`.
Thus every `n > 1` has a finite stopping time exactly when these threshold
classes cover `{n ∣ n > 1}`. That stopping-time statement is the finite
stopping-time pillar, already known to be equivalent to the Collatz
conjecture.

The patterns that have not contracted by depth `j` are those whose odd
count is at least `lowOdd j`, the least `m` with `2^j ≤ 3^m`. This count
moves by `0` or `1` at each step, so the pointwise minimal unresolved
pattern is the mechanical word of slope `log 3 / log 2`. Every finite
parity word occurs inside some unresolved word: a long enough initial run
of odd steps leaves slack that absorbs an arbitrary continuation.
-/

namespace Collatz.ThresholdCover

open Collatz

/-- The nonnegative affine offset in `2^j · T^j(n) = 3^a · n + offset`. -/
def offset (n j : Nat) : Nat :=
  2 ^ j * acceleratedOrbit j n - 3 ^ oddCount n j * n

theorem parityVector_append (n j : Nat) :
    parityVector n (j + 1) = parityVector n j ++ [acceleratedOrbit j n % 2] := by
  simp [parityVector, List.range_succ, List.map_append]

theorem oddCount_succ_bit (n j : Nat) :
    oddCount n (j + 1) = oddCount n j + if acceleratedOrbit j n % 2 = 1 then 1 else 0 := by
  rw [oddCount, oddCount, parityVector_append, List.count_append]
  by_cases h : acceleratedOrbit j n % 2 = 1
  · simp [h]
  · have h0 : acceleratedOrbit j n % 2 = 0 := by
      have := Nat.mod_two_eq_zero_or_one (acceleratedOrbit j n)
      omega
    simp [h0]

theorem parityVector_cons (n j : Nat) :
    parityVector n (j + 1) = n % 2 :: parityVector (acceleratedStep n) j := by
  refine List.ext_getElem ?_ ?_
  · simp [parityVector]
  · intro i hi _
    cases i with
    | zero => simp [parityVector]
    | succ i =>
      simp [parityVector, acceleratedOrbit_succ]

theorem oddCount_succ_step_even {n : Nat} (h : n % 2 = 0) (j : Nat) :
    oddCount n (j + 1) = oddCount (acceleratedStep n) j := by
  rw [oddCount, parityVector_cons, h, oddCount]
  simp

theorem oddCount_succ_step_odd {n : Nat} (h : n % 2 = 1) (j : Nat) :
    oddCount n (j + 1) = oddCount (acceleratedStep n) j + 1 := by
  rw [oddCount, parityVector_cons, h, oddCount]
  simp

theorem orbit_weighted_ge (n j : Nat) :
    3 ^ oddCount n j * n ≤ 2 ^ j * acceleratedOrbit j n := by
  induction j generalizing n with
  | zero => simp [oddCount, parityVector, acceleratedOrbit]
  | succ j ih =>
    rw [acceleratedOrbit_succ]
    by_cases he : n % 2 = 0
    · rw [oddCount_succ_step_even he, acceleratedStep, if_pos he]
      have ih' := ih (n / 2)
      have hdiv : 2 * (n / 2) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)
      have hmul := Nat.mul_le_mul_left 2 ih'
      have hleft : 2 * (3 ^ oddCount (n / 2) j * (n / 2)) =
          3 ^ oddCount (n / 2) j * n := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_assoc, hdiv]
      have hright : 2 * (2 ^ j * acceleratedOrbit j (n / 2)) =
          2 ^ (j + 1) * acceleratedOrbit j (n / 2) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j), ← Nat.pow_succ]
      rw [← hleft, ← hright]
      exact hmul
    · have ho : n % 2 = 1 := by
        have := Nat.mod_two_eq_zero_or_one n
        omega
      rw [oddCount_succ_step_odd ho, acceleratedStep, if_neg (by omega : ¬ n % 2 = 0)]
      let a := oddCount ((3 * n + 1) / 2) j
      have ih' := ih ((3 * n + 1) / 2)
      have htwo : 2 * ((3 * n + 1) / 2) = 3 * n + 1 :=
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by omega : (3 * n + 1) % 2 = 0))
      have hle : 3 * n ≤ 2 * ((3 * n + 1) / 2) := by omega
      have hscale := Nat.mul_le_mul_left (3 ^ a) hle
      have hih := Nat.mul_le_mul_left 2 ih'
      rw [Nat.pow_succ]
      calc
        3 ^ a * 3 * n = 3 ^ a * (3 * n) := by rw [Nat.mul_assoc]
        _ ≤ 3 ^ a * (2 * ((3 * n + 1) / 2)) := hscale
        _ ≤ 2 * (2 ^ j * acceleratedOrbit j ((3 * n + 1) / 2)) := by
          have hcomm : 3 ^ a * (2 * ((3 * n + 1) / 2)) =
              2 * (3 ^ a * ((3 * n + 1) / 2)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ a) 2, Nat.mul_assoc]
          rw [hcomm]
          exact hih
        _ = 2 ^ (j + 1) * acceleratedOrbit j ((3 * n + 1) / 2) := by
          rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j), ← Nat.pow_succ]

theorem affine_offset (n j : Nat) :
    2 ^ j * acceleratedOrbit j n = 3 ^ oddCount n j * n + offset n j := by
  have h := orbit_weighted_ge n j
  dsimp [offset]
  omega

/-- A contracting pattern drops exactly above its affine threshold. -/
theorem split_threshold (n j : Nat) (h : 3 ^ oddCount n j ≤ 2 ^ j) :
    2 ^ j * n = 3 ^ oddCount n j * n + n * (2 ^ j - 3 ^ oddCount n j) := by
  have hsub : 3 ^ oddCount n j + (2 ^ j - 3 ^ oddCount n j) = 2 ^ j :=
    Nat.add_sub_of_le h
  calc
    2 ^ j * n = n * 2 ^ j := Nat.mul_comm _ _
    _ = n * (3 ^ oddCount n j + (2 ^ j - 3 ^ oddCount n j)) :=
      congrArg (fun t => n * t) hsub.symm
    _ = n * 3 ^ oddCount n j + n * (2 ^ j - 3 ^ oddCount n j) := Nat.mul_add _ _ _
    _ = 3 ^ oddCount n j * n + n * (2 ^ j - 3 ^ oddCount n j) := by rw [Nat.mul_comm n]

theorem drop_iff_offset {n j : Nat} (h : 3 ^ oddCount n j < 2 ^ j) :
    acceleratedOrbit j n < n ↔ offset n j < n * (2 ^ j - 3 ^ oddCount n j) := by
  have haff := affine_offset n j
  have hsplit := split_threshold n j (Nat.le_of_lt h)
  constructor
  · intro hlt
    have hmul := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos j)
    rw [haff, hsplit] at hmul
    exact Nat.lt_of_add_lt_add_left hmul
  · intro hlt
    have hsum : 3 ^ oddCount n j * n + offset n j <
        3 ^ oddCount n j * n + n * (2 ^ j - 3 ^ oddCount n j) :=
      Nat.add_lt_add_left hlt _
    rw [← hsplit, ← haff] at hsum
    exact Nat.lt_of_mul_lt_mul_left hsum

/-- No contracting denominator means the iterate does not fall below the start. -/
theorem no_strict_drop_of_expanding {n j : Nat} (h : 2 ^ j ≤ 3 ^ oddCount n j) :
    n ≤ acceleratedOrbit j n := by
  have haff := affine_offset n j
  have hmul : 2 ^ j * n ≤ 3 ^ oddCount n j * n := Nat.mul_le_mul_right n h
  have : 2 ^ j * n ≤ 2 ^ j * acceleratedOrbit j n := by omega
  exact Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos j)

theorem oddCount_mod (n j : Nat) : oddCount n j = oddCount (n % 2 ^ j) j := by
  simp [oddCount, parityVector_mod_pow_two]

theorem oddCount_class (k m r : Nat) (hr : r < 2 ^ k) :
    oddCount (2 ^ k * m + r) k = oddCount r k := by
  have hmod : (2 ^ k * m + r) % 2 ^ k = r := by
    have hmul : 2 ^ k * m % 2 ^ k = 0 := Nat.mul_mod_right (2 ^ k) m
    rw [Nat.add_mod, hmul, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  rw [oddCount_mod, hmod]

private theorem accStep_class_even {k m r : Nat} (hr : r % 2 = 0) :
    acceleratedStep (2 ^ (k + 1) * m + r) = 2 ^ k * m + acceleratedStep r := by
  have hsplit : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
  have heven : (2 ^ (k + 1) * m + r) % 2 = 0 := by rw [hsplit]; omega
  rw [acceleratedStep, if_pos heven, acceleratedStep, if_pos hr, hsplit]
  omega

private theorem accStep_class_odd {k m r : Nat} (hr : r % 2 = 1) :
    acceleratedStep (2 ^ (k + 1) * m + r) = 2 ^ k * (3 * m) + acceleratedStep r := by
  have hsplit : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
  have hodd : (2 ^ (k + 1) * m + r) % 2 = 1 := by rw [hsplit]; omega
  rw [acceleratedStep, if_neg (by omega), acceleratedStep, if_neg (by omega), hsplit]
  have h3 : 3 * (2 ^ k * m) = 2 ^ k * (3 * m) := by
    rw [Nat.mul_left_comm, Nat.mul_comm 3]
  omega

private theorem orbit_class (k m r : Nat) :
    acceleratedOrbit k (2 ^ k * m + r) = 3 ^ oddCount r k * m + acceleratedOrbit k r := by
  induction k generalizing m r with
  | zero => simp [acceleratedOrbit, oddCount, parityVector]
  | succ k ih =>
    rw [acceleratedOrbit_succ]
    by_cases he : r % 2 = 0
    · rw [accStep_class_even (k := k) he, ih, oddCount_succ_step_even he, acceleratedOrbit_succ]
    · have ho : r % 2 = 1 := by
        have := Nat.mod_two_eq_zero_or_one r
        omega
      rw [accStep_class_odd (k := k) ho, ih, oddCount_succ_step_odd ho, acceleratedOrbit_succ]
      have : 3 ^ (oddCount (acceleratedStep r) k + 1) * m =
          3 ^ oddCount (acceleratedStep r) k * (3 * m) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      omega

theorem offset_class (k m r : Nat) (hr : r < 2 ^ k) :
    offset (2 ^ k * m + r) k = offset r k := by
  have hcount := oddCount_class k m r hr
  have horbit := orbit_class k m r
  unfold offset
  rw [hcount, horbit]
  have hsum : 2 ^ k * (3 ^ oddCount r k * m + acceleratedOrbit k r) =
      3 ^ oddCount r k * (2 ^ k * m) + 2 ^ k * acceleratedOrbit k r := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  have hprod : 3 ^ oddCount r k * (2 ^ k * m + r) =
      3 ^ oddCount r k * (2 ^ k * m) + 3 ^ oddCount r k * r := Nat.mul_add _ _ _
  rw [hsum, hprod, Nat.add_sub_add_left]

/-- Membership in a residue class drops exactly when the start exceeds that
class's threshold. -/
theorem class_drop_iff {k m r : Nat} (hr : r < 2 ^ k)
    (h : 3 ^ oddCount r k < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r ↔
      offset r k < (2 ^ k * m + r) * (2 ^ k - 3 ^ oddCount r k) := by
  have hcount := oddCount_class k m r hr
  have hoff := offset_class k m r hr
  rw [← hcount, ← hoff]
  exact drop_iff_offset (by simpa [hcount] using h)

/-- Finite stopping time is threshold coverage. The `k = 0` pattern is never
contracting, so the witness depth is automatically positive. -/
theorem finiteStopping_iff_threshold (n : Nat) :
    (∃ k, acceleratedOrbit k n < n) ↔
      ∃ k, 3 ^ oddCount n k < 2 ^ k ∧ offset n k < n * (2 ^ k - 3 ^ oddCount n k) := by
  constructor
  · intro ⟨k, hk⟩
    have hnot : ¬ 2 ^ k ≤ 3 ^ oddCount n k := by
      intro hexp
      exact Nat.not_lt_of_ge (no_strict_drop_of_expanding hexp) hk
    have hcontr : 3 ^ oddCount n k < 2 ^ k := by omega
    exact ⟨k, hcontr, (drop_iff_offset hcontr).mp hk⟩
  · intro ⟨k, hcontr, hthr⟩
    exact ⟨k, (drop_iff_offset hcontr).mpr hthr⟩

/-- Every integer above `1` drops below itself if and only if every such
integer lies above the threshold of one of its contracting residue classes. -/
theorem stopping_iff_threshold_cover :
    (∀ n, 1 < n → ∃ k, acceleratedOrbit k n < n) ↔
      ∀ n, 1 < n → ∃ k, 3 ^ oddCount n k < 2 ^ k ∧
        offset n k < n * (2 ^ k - 3 ^ oddCount n k) := by
  constructor
  · intro h n hn
    exact (finiteStopping_iff_threshold n).mp (h n hn)
  · intro h n hn
    exact (finiteStopping_iff_threshold n).mpr (h n hn)

/-! ## The minimal unresolved odd count -/

/-- Least odd count whose ternary power meets `2^j`. This is the lower
mechanical word for the line of slope `log 2 / log 3`. -/
def lowOdd : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let m := lowOdd j
    if 2 ^ (j + 1) ≤ 3 ^ m then m else m + 1

theorem lowOdd_ge (j : Nat) : 2 ^ j ≤ 3 ^ lowOdd j := by
  induction j with
  | zero => simp [lowOdd]
  | succ j ih =>
    dsimp [lowOdd]
    split
    · assumption
    · calc
        2 ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
        _ ≤ 2 ^ j * 3 := Nat.mul_le_mul_left _ (by decide)
        _ ≤ 3 ^ lowOdd j * 3 := Nat.mul_le_mul_right 3 ih
        _ = 3 ^ (lowOdd j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem lowOdd_step (j : Nat) :
    lowOdd (j + 1) = lowOdd j ∨ lowOdd (j + 1) = lowOdd j + 1 := by
  dsimp [lowOdd]
  split <;> simp

theorem lowOdd_min {j m : Nat} (h : 2 ^ j ≤ 3 ^ m) : lowOdd j ≤ m := by
  induction j generalizing m with
  | zero => simp [lowOdd]
  | succ j ih =>
    have hprev : 2 ^ j ≤ 3 ^ m := by
      have : 2 ^ j ≤ 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
      exact Nat.le_trans this h
    have hm := ih hprev
    by_cases hstep : 2 ^ (j + 1) ≤ 3 ^ lowOdd j
    · simpa [lowOdd, hstep] using hm
    · have hlt : lowOdd j < m := by
        cases Nat.lt_or_ge (lowOdd j) m with
        | inl hlt => exact hlt
        | inr hge =>
          have hpow : 3 ^ m ≤ 3 ^ lowOdd j := Nat.pow_le_pow_right (by decide) hge
          exact (hstep (Nat.le_trans h hpow)).elim
      have hdef : lowOdd (j + 1) = lowOdd j + 1 := by simp [lowOdd, hstep]
      omega

theorem lowOdd_le (j : Nat) : lowOdd j ≤ j := by
  induction j with
  | zero => simp [lowOdd]
  | succ j ih =>
    rcases lowOdd_step j with h | h
    · omega
    · omega

theorem lowOdd_mono (j : Nat) : lowOdd j ≤ lowOdd (j + 1) := by
  rcases lowOdd_step j with h | h <;> omega

theorem lowOdd_add (a b : Nat) : lowOdd (a + b) ≤ lowOdd a + b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have heq : a + (b + 1) = a + b + 1 := by omega
    rw [heq]
    have hstep : lowOdd (a + b + 1) ≤ lowOdd (a + b) + 1 := by
      rcases lowOdd_step (a + b) with h | h <;> omega
    exact Nat.le_trans hstep (Nat.add_le_add_right ih 1)

theorem two_pow_three_le_three_pow_two (t : Nat) : 2 ^ (3 * t) ≤ 3 ^ (2 * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      2 ^ (3 * (t + 1)) = 2 ^ (3 * t) * 2 ^ 3 := by
        rw [show 3 * (t + 1) = 3 * t + 3 by omega, Nat.pow_add]
      _ ≤ 3 ^ (2 * t) * 8 := Nat.mul_le_mul_right 8 ih
      _ ≤ 3 ^ (2 * t) * 9 := Nat.mul_le_mul_left _ (by decide)
      _ = 3 ^ (2 * t) * 3 ^ 2 := by simp
      _ = 3 ^ (2 * (t + 1)) := by
        rw [← Nat.pow_add, show 2 * t + 2 = 2 * (t + 1) by omega]

theorem lowOdd_three_mul (t : Nat) : lowOdd (3 * t) ≤ 2 * t :=
  lowOdd_min (two_pow_three_le_three_pow_two t)

theorem coefficient_below_lowOdd {n j : Nat} (h : oddCount n j < lowOdd j) :
    3 ^ oddCount n j < 2 ^ j := by
  apply Nat.lt_of_not_le
  intro hle
  exact Nat.not_lt_of_ge (lowOdd_min hle) h

/-- One step of the minimal unresolved parity word. -/
def sturmianBit (j : Nat) : Nat := lowOdd (j + 1) - lowOdd j

theorem sturmianBit_binary (j : Nat) : sturmianBit j = 0 ∨ sturmianBit j = 1 := by
  rcases lowOdd_step j with h | h
  · left
    simp [sturmianBit, h]
  · right
    simp [sturmianBit, h, Nat.add_sub_cancel_left]

def sturmianWord (K : Nat) : List Nat := (List.range K).map sturmianBit

theorem sturmianWord_bits (K : Nat) : ∀ x ∈ sturmianWord K, x = 0 ∨ x = 1 := by
  intro x hx
  simp [sturmianWord] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact sturmianBit_binary j

theorem sturmianWord_count (j : Nat) : (sturmianWord j).count 1 = lowOdd j := by
  induction j with
  | zero => simp [sturmianWord, lowOdd]
  | succ j ih =>
    rw [sturmianWord, List.range_succ, List.map_append, List.count_append, ← sturmianWord, ih]
    rcases sturmianBit_binary j with h | h
    · have heq : lowOdd (j + 1) = lowOdd j := by
        rcases lowOdd_step j with hs | hs
        · exact hs
        · simp [sturmianBit, hs] at h
      simp [h, heq]
    · have heq : lowOdd (j + 1) = lowOdd j + 1 := by
        rcases lowOdd_step j with hs | hs
        · simp [sturmianBit, hs] at h
        · exact hs
      simp [h, heq]

private theorem map_range_take (f : Nat → Nat) {j K : Nat} (hj : j ≤ K) :
    ((List.range K).map f).take j = (List.range j).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hj]

theorem sturmianWord_take_count {K j : Nat} (hj : j ≤ K) :
    ((sturmianWord K).take j).count 1 = lowOdd j := by
  rw [sturmianWord, map_range_take sturmianBit hj, ← sturmianWord, sturmianWord_count]

/-- The mechanical word is realized by a residue, and its odd counts are the
pointwise minimal counts that have not yet contracted. -/
theorem exists_sturmian_residue (K : Nat) :
    ∃ n, n < 2 ^ K ∧ ∀ j, j ≤ K → oddCount n j = lowOdd j := by
  obtain ⟨n, hn, hvec⟩ := parityVector_surjective_mod_pow_two K (sturmianWord K)
    (by simp [sturmianWord]) (sturmianWord_bits K)
  refine ⟨n, hn, ?_⟩
  intro j hj
  have htake : (parityVector n K).take j = parityVector n j := by
    simp only [parityVector]
    exact map_range_take (fun i => acceleratedOrbit i n % 2) hj
  rw [oddCount, ← htake, hvec, sturmianWord_take_count hj]

private theorem oddCount_le_add (n a b : Nat) : oddCount n a ≤ oddCount n (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hstep : oddCount n (a + b) ≤ oddCount n (a + b + 1) := by
      rw [oddCount_succ_bit]
      omega
    have heq : a + (b + 1) = a + b + 1 := by omega
    rw [heq]
    exact Nat.le_trans ih hstep

/-- `3^{2t} ≥ 2^{3t}` leaves at least `t` steps of slack after an all-odd
prefix of length `3t`. Any parity continuation no longer than that slack
stays above `lowOdd`. -/
theorem unresolved_after_odd_prefix {n t L : Nat} (hL : L ≤ t)
    (hodd : ∀ i, i < 3 * t → acceleratedOrbit i n % 2 = 1) :
    ∀ j, j ≤ 3 * t + L → lowOdd j ≤ oddCount n j := by
  have hprefix : ∀ j, j ≤ 3 * t → oddCount n j = j := by
    intro j hj
    induction j with
    | zero => simp [oddCount, parityVector]
    | succ j ih =>
      have ih' := ih (by omega)
      have hbit : acceleratedOrbit j n % 2 = 1 := hodd j (by omega)
      rw [oddCount_succ_bit, hbit, ih']
      simp
  intro j hj
  by_cases hj' : j ≤ 3 * t
  · rw [hprefix j hj']
    exact lowOdd_le j
  · have hge : 3 * t ≤ j := by omega
    have hcount : 3 * t ≤ oddCount n j := by
      have hk : 3 * t + (j - 3 * t) = j := by omega
      have hbase : oddCount n (3 * t) = 3 * t := hprefix _ (Nat.le_refl _)
      rw [← hbase, ← hk]
      exact oddCount_le_add n (3 * t) (j - 3 * t)
    have hlow : lowOdd j ≤ 2 * t + (j - 3 * t) := by
      have hsum : lowOdd (3 * t + (j - 3 * t)) ≤ 2 * t + (j - 3 * t) :=
        Nat.le_trans (lowOdd_add (3 * t) (j - 3 * t))
          (Nat.add_le_add_right (lowOdd_three_mul t) (j - 3 * t))
      simpa [Nat.add_sub_of_le hge] using hsum
    have hslack : 2 * t + (j - 3 * t) ≤ 3 * t := by omega
    exact Nat.le_trans (Nat.le_trans hlow hslack) hcount
