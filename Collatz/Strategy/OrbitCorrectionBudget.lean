import Collatz.Strategy.SynchronizedCollision
import Collatz.Core.Minimum
import Collatz.Structure.AccCycle

/-! Uniform reciprocal bounds for finite selections with distinct synchronized
images, including selections from a nonrepeating orbit. -/

namespace Collatz.OrbitCorrectionBudget

open Collatz.Arith Collatz.SynchronizedCollision

private def reciprocalSum (f : Nat → Nat) (times : List Nat) : Rat :=
  (times.map fun i => (↑(f i) : Rat)⁻¹).sum

private theorem aligned_list_bound {f : Nat → Nat} {b lo blocks : Nat} {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup)
    (hwin : ∀ i ∈ times, lo * 2 ^ (13 * b) ≤ f i ∧ f i < (lo + blocks) * 2 ^ (13 * b)) :
    times.length ≤ blocks * (4 * 3 ^ (8 * b)) := by
  apply Nat.le_of_not_gt
  intro hlarge
  have hindex (i : Nat) (hi : i < times.length) : times.getD i 0 = times[i] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  obtain ⟨i, j, hij, hj, heq⟩ := collision_in_aligned_blocks
    (f := fun i => f (times.getD i 0)) (N := blocks * (4 * 3 ^ (8 * b))) (b := b) (lo := lo) (blocks := blocks)
    (fun i hi => by
      have ht := Nat.lt_of_le_of_lt hi hlarge
      rw [hindex i ht]
      exact hwin _ (List.getElem_mem ht)) (Nat.le_refl _)
  have hj' := Nat.lt_of_le_of_lt hj hlarge
  have hi' := Nat.lt_trans hij hj'
  rw [hindex i hi', hindex j hj'] at heq
  exact List.pairwise_iff_getElem.mp hnd i j hi' hj' hij
    (hsep _ _ _ (List.getElem_mem hi') (List.getElem_mem hj') heq)

private theorem inv_le_inv {a b : Rat} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := by grind
  apply Rat.le_of_mul_le_mul_right _ ha
  calc
    b⁻¹ * a ≤ b⁻¹ * b := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt (Rat.inv_pos.mpr hb))
    _ = 1 := Rat.inv_mul_cancel b (by grind)
    _ = a⁻¹ * a := (Rat.inv_mul_cancel a (by grind)).symm

private theorem sum_le_count {f : Nat → Rat} {limit : Rat} {l : List Nat}
    (h : ∀ i ∈ l, f i ≤ limit) : (l.map f).sum ≤ (l.length : Rat) * limit := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have hl := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Rat.natCast_add]
    have hsplit : (↑l.length + (↑(1 : Nat) : Rat)) * limit = ↑l.length * limit + limit := by
      grind
    rw [hsplit]
    grind

private theorem sum_split (f : Nat → Nat) (l : List Nat) (p : Nat → Bool) :
    reciprocalSum f l = reciprocalSum f (l.filter p) +
      reciprocalSum f (l.filter fun i => !p i) := by
  induction l with
  | nil => simp [reciprocalSum, Rat.add_zero]
  | cons i l ih =>
    have hstep (l' : List Nat) : reciprocalSum f (i :: l') = (↑(f i) : Rat)⁻¹ + reciprocalSum f l' := rfl
    cases hp : p i <;> simp [hp, hstep, ih] <;> grind

private abbrev ratio : Rat := 6561 / 8192

private theorem ratio_scaled (s : Nat) : ratio ^ s * (8192 : Rat) ^ s = (6561 : Rat) ^ s := by
  induction s with
  | zero => simp [Rat.mul_one]
  | succ s ih =>
    simp only [Rat.pow_succ]
    calc
      _ = (ratio ^ s * (8192 : Rat) ^ s) * (ratio * 8192) := by grind
      _ = _ := by rw [ih, show ratio * 8192 = 6561 by decide +kernel]

private theorem band_budget {f : Nat → Nat} {s j : Nat} {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup)
    (hlo : ∀ i ∈ times, 2 ^ j * 2 ^ (13 * s) ≤ f i)
    (hhi : ∀ i ∈ times, f i < 2 ^ (j + 1) * 2 ^ (13 * s)) :
    reciprocalSum f times ≤ 4 * ratio ^ s := by
  have hcount := aligned_list_bound (lo := 2 ^ j) (blocks := 2 ^ j) (b := s) hsep hnd (by
    intro i hi
    refine ⟨hlo i hi, ?_⟩
    have he : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
    rw [he]
    exact hhi i hi)
  have hcount' : (times.length : Rat) ≤ (2 : Rat) ^ j * (4 * (6561 : Rat) ^ s) := by
    have h := Rat.natCast_le_natCast.mpr hcount
    rw [Nat.pow_mul 3 8, show (3 : Nat) ^ 8 = 6561 by decide] at h
    simpa only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat] using h
  let base := (2 : Rat) ^ j * (8192 : Rat) ^ s
  have hbase : 0 < base := Rat.mul_pos (Rat.pow_pos (by decide)) (Rat.pow_pos (by decide))
  have hweight : ∀ i ∈ times, (↑(f i) : Rat)⁻¹ ≤ base⁻¹ := by
    intro i hi
    apply inv_le_inv hbase
    have h := Rat.natCast_le_natCast.mpr (hlo i hi)
    rw [Nat.pow_mul 2 13, show (2 : Nat) ^ 13 = 8192 by decide] at h
    simpa only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat, base] using h
  have hsum := sum_le_count hweight
  apply Rat.le_of_mul_le_mul_right _ hbase
  calc
    reciprocalSum f times * base ≤ ((times.length : Rat) * base⁻¹) * base :=
      Rat.mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt hbase)
    _ = (times.length : Rat) := by
      rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
    _ ≤ (2 : Rat) ^ j * (4 * (6561 : Rat) ^ s) := hcount'
    _ = (4 * ratio ^ s) * base := by have h := ratio_scaled s; dsimp [base]; grind

private theorem consecutive_bands_budget {f : Nat → Nat} (s j count : Nat) {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup)
    (hlo : ∀ i ∈ times, 2 ^ j * 2 ^ (13 * s) ≤ f i)
    (hhi : ∀ i ∈ times, f i < 2 ^ (j + count) * 2 ^ (13 * s)) :
    reciprocalSum f times ≤ (count : Rat) * (4 * ratio ^ s) := by
  induction count generalizing j times with
  | zero =>
    have hempty : times = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
      have := hlo i hi
      have := hhi i hi
      simp only [Nat.add_zero] at *
      omega
    subst hempty
    simp [reciprocalSum, Rat.zero_mul]
  | succ count ih =>
    let p := fun i => decide (f i < 2 ^ (j + 1) * 2 ^ (13 * s))
    have hfiltered (q : Nat → Bool) (d i j : Nat) (hi : i ∈ times.filter q) (hj : j ∈ times.filter q) :=
      hsep d i j (List.mem_filter.mp hi).1 (List.mem_filter.mp hj).1
    have hb : reciprocalSum f (times.filter p) ≤ 4 * ratio ^ s := by
      apply band_budget (hfiltered p) (List.Nodup.sublist List.filter_sublist hnd)
      · exact fun i hi => hlo i (List.mem_filter.mp hi).1
      · intro i hi
        simpa [p] using (List.mem_filter.mp hi).2
    have ht : reciprocalSum f (times.filter fun i => !p i) ≤ (count : Rat) * (4 * ratio ^ s) := by
      apply ih (j + 1) (hfiltered fun i => !p i) (List.Nodup.sublist List.filter_sublist hnd)
      · intro i hi
        simpa [p] using (List.mem_filter.mp hi).2
      · intro i hi
        simpa only [show j + 1 + count = j + (count + 1) by omega] using hhi i (List.mem_filter.mp hi).1
    change reciprocalSum f times ≤ ((count + 1 : Nat) : Rat) * (4 * ratio ^ s)
    rw [sum_split f times p, Rat.natCast_add, Rat.natCast_ofNat]
    grind

private theorem shell_budget {f : Nat → Nat} {s : Nat} {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup)
    (hlo : ∀ i ∈ times, 2 ^ (13 * s) ≤ f i)
    (hhi : ∀ i ∈ times, f i < 2 ^ (13 * (s + 1))) :
    reciprocalSum f times ≤ 52 * ratio ^ s := by
  have hb := consecutive_bands_budget s 0 13 hsep hnd (by simpa using hlo) (by
    intro i hi
    rw [Nat.zero_add, ← Nat.pow_add, show 13 + 13 * s = 13 * (s + 1) by omega]
    exact hhi i hi)
  calc
    _ ≤ _ := hb
    _ = _ := by grind

private theorem finite_budget {f : Nat → Nat} (s depth : Nat) {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup)
    (hlo : ∀ i ∈ times, 2 ^ (13 * s) ≤ f i)
    (hhi : ∀ i ∈ times, f i < 2 ^ (13 * (s + depth))) :
    reciprocalSum f times ≤ 262 * ratio ^ s := by
  induction depth generalizing s times with
  | zero =>
    have hempty : times = [] := List.eq_nil_iff_forall_not_mem.mpr (fun i hi => by
      have := hlo i hi
      have := hhi i hi
      simp only [Nat.add_zero] at *
      omega)
    subst hempty
    exact Rat.mul_nonneg (by decide) (Rat.pow_nonneg (by decide +kernel : 0 ≤ ratio))
  | succ depth ih =>
    let p := fun i => decide (f i < 2 ^ (13 * (s + 1)))
    let low := times.filter p
    let high := times.filter fun i => !p i
    have hfiltered (q : Nat → Bool) (d i j : Nat) (hi : i ∈ times.filter q) (hj : j ∈ times.filter q) :=
      hsep d i j (List.mem_filter.mp hi).1 (List.mem_filter.mp hj).1
    have hlow : reciprocalSum f low ≤ 52 * ratio ^ s := by
      apply shell_budget (hfiltered p) (List.Nodup.sublist List.filter_sublist hnd)
      · exact fun i hi => hlo i (List.mem_filter.mp hi).1
      · intro i hi
        have h := (List.mem_filter.mp hi).2
        simpa [p] using h
    have hhigh : reciprocalSum f high ≤ 262 * ratio ^ (s + 1) := by
      apply ih (s + 1) (hfiltered fun i => !p i) (List.Nodup.sublist List.filter_sublist hnd)
      · intro i hi
        have h := (List.mem_filter.mp hi).2
        simpa [p] using h
      · intro i hi
        simpa [show s + 1 + depth = s + (depth + 1) by omega] using hhi i (List.mem_filter.mp hi).1
    rw [sum_split f times p]
    change reciprocalSum f low + reciprocalSum f high ≤ _
    calc
      _ ≤ 52 * ratio ^ s + 262 * ratio ^ (s + 1) := by grind
      _ = (52 + 262 * ratio) * ratio ^ s := by
        rw [Rat.pow_succ]
        grind
      _ ≤ _ := Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
        (Rat.pow_nonneg (by decide +kernel : 0 ≤ ratio))

private theorem le_sum_of_mem {a : Nat} {l : List Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with heq | ht
    · omega
    · have := ih ht
      omega

/-- Any finite selection whose synchronized images are distinct, at or above
`8192^s`, has reciprocal sum at most `262(6561/8192)^s`. -/
theorem reciprocal_sum_le_of_separated {f : Nat → Nat} {s : Nat} {times : List Nat}
    (hsep : ∀ d i j, i ∈ times → j ∈ times → acceleratedOrbit d (f i) = acceleratedOrbit d (f j) → i = j)
    (hnd : times.Nodup) (hlo : ∀ i ∈ times, 8192 ^ s ≤ f i) :
    (times.map fun i => (↑(f i) : Rat)⁻¹).sum ≤ 262 * ((6561 : Rat) / 8192) ^ s := by
  let depth := (times.map f).sum
  apply finite_budget s depth hsep hnd (by simpa [Nat.pow_mul] using hlo)
  intro i hi
  have ht : f i ≤ depth := by
    change f i ≤ (times.map f).sum
    exact le_sum_of_mem (List.mem_map.mpr ⟨i, hi, rfl⟩)
  exact Nat.lt_of_le_of_lt ht (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self (n := depth))
    (two_pow_le_two_pow (by omega)))

/-- On a nonrepeating trajectory, any finite selection of distinct visits
at or above `8192^s` has reciprocal sum at most `262(6561/8192)^s`. -/
theorem reciprocal_sum_le {n s : Nat} {times : List Nat}
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hnd : times.Nodup) (hlo : ∀ i ∈ times, 8192 ^ s ≤ acceleratedOrbit i n) :
    (times.map fun i => (↑(acceleratedOrbit i n) : Rat)⁻¹).sum ≤
      262 * ((6561 : Rat) / 8192) ^ s := by
  apply reciprocal_sum_le_of_separated (f := fun i => acceleratedOrbit i n) _ hnd hlo
  intro d i j _ _ h
  rw [acceleratedOrbit_add, acceleratedOrbit_add] at h
  exact Nat.add_left_cancel (hnr _ _ h)

private theorem reciprocalSum_append (f : Nat → Nat) (l r : List Nat) :
    reciprocalSum f (l ++ r) = reciprocalSum f l + reciprocalSum f r := by
  induction l with
  | nil => simp [reciprocalSum, Rat.zero_add]
  | cons i l ih =>
    change (↑(f i) : Rat)⁻¹ + reciprocalSum f (l ++ r) =
      ((↑(f i) : Rat)⁻¹ + reciprocalSum f l) + reciprocalSum f r
    rw [ih, Rat.add_assoc]

private def correctionBudget (n k : Nat) : Rat :=
  (reciprocalSum (fun i => acceleratedOrbit i n) (List.range k) + (n : Rat)⁻¹ -
    (↑(acceleratedOrbit k n) : Rat)⁻¹) / 4

private theorem correctionBudget_succ (n k : Nat) :
    correctionBudget n (k + 1) = correctionBudget n k +
      (2 * (↑(acceleratedOrbit k n) : Rat)⁻¹ - (↑(acceleratedOrbit (k + 1) n) : Rat)⁻¹) / 4 := by
  rw [correctionBudget, List.range_succ, reciprocalSum_append, correctionBudget]
  have hs : reciprocalSum (fun i => acceleratedOrbit i n) [k] = (↑(acceleratedOrbit k n) : Rat)⁻¹ := by
    simp [reciprocalSum, Rat.add_zero]
  rw [hs, Rat.div_def, Rat.div_def, Rat.div_def]
  grind

private theorem compensated_prefix {n : Nat} (hn : 0 < n) (k : Nat) :
    0 ≤ correctionBudget n k ∧
      (1 - correctionBudget n k) * ((2 : Rat) ^ k * (acceleratedOrbit k n : Rat)) ≤
        (3 : Rat) ^ oddCount n k * (n : Rat) := by
  induction k with
  | zero =>
    simp [correctionBudget, reciprocalSum, oddCount, parityVector, Rat.div_def,
      Rat.one_mul, acceleratedOrbit]
    grind
  | succ k ih =>
    let x := acceleratedOrbit k n
    let z : Rat := x
    let y : Rat := acceleratedStep x
    let loss : Rat := (2 * z⁻¹ - y⁻¹) / 4
    let debt := correctionBudget n k
    have hz : 0 < z := Rat.natCast_lt_natCast.mpr (acceleratedOrbit_positive hn k)
    have hy : 0 < y := by
      have h := acceleratedOrbit_positive hn (k + 1)
      rw [acceleratedOrbit_succ_step] at h
      exact Rat.natCast_lt_natCast.mpr h
    have hzi : z⁻¹ * z = 1 := Rat.inv_mul_cancel _ (by grind)
    have hyi : y⁻¹ * y = 1 := Rat.inv_mul_cancel _ (by grind)
    have hdebt : 0 ≤ debt := ih.1
    have hstep := correctionBudget_succ n k
    rw [acceleratedOrbit_succ_step] at hstep
    change correctionBudget n (k + 1) = debt + loss at hstep
    rw [hstep]
    have hcount := Density.oddCount_succ_last n k
    change oddCount n (k + 1) = oddCount n k + x % 2 at hcount
    have htwo : (0 : Rat) ≤ (2 : Rat) ^ k := Rat.pow_nonneg (by decide)
    have hscale : (2 : Rat) ^ (k + 1) * (acceleratedOrbit (k + 1) n : Rat) =
        (2 : Rat) ^ k * (2 * (acceleratedStep x : Rat)) := by
      rw [Rat.pow_succ, Rat.mul_assoc, acceleratedOrbit_succ_step]
    rw [hscale, hcount]
    rcases mod_two_eq_zero_or_one x with he | ho
    · have ht : 2 * acceleratedStep x = x := by rw [acceleratedStep, if_pos he]; omega
      have ht' : (2 : Rat) * y = z := by
        simpa [Rat.natCast_mul] using congrArg (fun v : Nat => (v : Rat)) ht
      have hloss : loss = 0 := by
        have hzloss : (2 * z⁻¹ - y⁻¹) * y = 0 := by
          calc
            _ = z⁻¹ * (2 * y) - y⁻¹ * y := by grind
            _ = _ := by rw [ht', hzi, hyi]; decide +kernel
        have heq : 2 * z⁻¹ - y⁻¹ = 0 := by
          apply Rat.le_antisymm
          · apply Rat.le_of_mul_le_mul_right _ hy
            rw [hzloss, Rat.zero_mul]
            exact Rat.le_refl
          · apply Rat.le_of_mul_le_mul_right _ hy
            rw [hzloss, Rat.zero_mul]
            exact Rat.le_refl
        rw [show loss = (2 * z⁻¹ - y⁻¹) / 4 from rfl, heq, Rat.div_def, Rat.zero_mul]
      change 0 ≤ debt + loss ∧
        (1 - (debt + loss)) * ((2 : Rat) ^ k * (2 * y)) ≤
          (3 : Rat) ^ (oddCount n k + x % 2) * (n : Rat)
      rw [hloss, Rat.add_zero, he, Nat.add_zero, ht']
      exact ih
    · have ht : 2 * acceleratedStep x = 3 * x + 1 := by
        rw [acceleratedStep, if_neg (by omega)]
        omega
      have ht' : (2 : Rat) * y = 3 * z + 1 := by
        simpa [Rat.natCast_mul, Rat.natCast_add] using congrArg (fun v : Nat => (v : Rat)) ht
      have hterm : y⁻¹ * (3 * z + 1) = 2 := by
        rw [← ht']
        calc
          _ = 2 * (y⁻¹ * y) := by grind
          _ = _ := by rw [hyi, Rat.mul_one]
      have hcancel : 1 ≤ loss * (3 * z + 1) := by
        have hi := Rat.le_of_lt (Rat.inv_pos.mpr hz)
        calc
          _ ≤ 1 + z⁻¹ * ((4 : Rat)⁻¹ * 2) := by grind
          _ = loss * (3 * z + 1) := by
            have hc : ((4 : Rat)⁻¹ * 4) = 1 := by decide +kernel
            simp only [loss, Rat.div_def]
            grind
      have hloss : 0 ≤ loss := by
        apply Rat.le_of_mul_le_mul_right _ (show 0 < 3 * z + 1 by grind)
        rw [Rat.zero_mul]
        exact Rat.le_trans (by decide) hcancel
      have hlocal : (1 - (debt + loss)) * (3 * z + 1) ≤ 3 * ((1 - debt) * z) := by
        calc
          _ = 3 * ((1 - debt) * z) + 1 - debt - loss * (3 * z + 1) := by grind
          _ ≤ _ := by grind
      refine ⟨by grind, ?_⟩
      change (1 - (debt + loss)) * ((2 : Rat) ^ k * (2 * y)) ≤
        (3 : Rat) ^ (oddCount n k + x % 2) * (n : Rat)
      rw [ho, ht', Rat.pow_succ]
      calc
        _ = (2 : Rat) ^ k * ((1 - (debt + loss)) * (3 * z + 1)) := by grind
        _ ≤ (2 : Rat) ^ k * (3 * ((1 - debt) * z)) := Rat.mul_le_mul_of_nonneg_left hlocal htwo
        _ = 3 * ((1 - debt) * ((2 : Rat) ^ k * z)) := by grind
        _ ≤ 3 * ((3 : Rat) ^ oddCount n k * (n : Rat)) :=
          Rat.mul_le_mul_of_nonneg_left ih.2 (by decide)
        _ = _ := by grind

/-- The normalized gap between the two powers of a return is bounded by
one quarter of the reciprocal sum along the return. -/
theorem deficit_le_reciprocal_sum_of_return {n L : Nat} (hn : 0 < n)
    (hreturn : acceleratedOrbit L n = n) :
    1 - (3 : Rat) ^ oddCount n L / (2 : Rat) ^ L ≤
      ((List.range L).map fun i => (↑(acceleratedOrbit i n) : Rat)⁻¹).sum / 4 := by
  let A := (3 : Rat) ^ oddCount n L
  let B := (2 : Rat) ^ L
  let debt := correctionBudget n L
  have hx : 0 < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  have hB : 0 < B := Rat.pow_pos (by decide)
  have hb := (compensated_prefix hn L).2
  rw [hreturn] at hb
  have hc : (1 - debt) * B ≤ A := by
    apply Rat.le_of_mul_le_mul_right _ hx
    simpa only [Rat.mul_assoc, A, B, debt] using hb
  have hd : (A / B) * B = A := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
  have hd' : 1 - A / B ≤ debt := by
    apply Rat.le_of_mul_le_mul_right _ hB
    grind
  have hdebt : debt = ((List.range L).map fun i => (↑(acceleratedOrbit i n) : Rat)⁻¹).sum / 4 := by
    simp only [debt, correctionBudget, hreturn, reciprocalSum]
    grind
  rwa [hdebt] at hd'

/-- A uniform lower estimate for the multiplicative coefficient relative
to the actual endpoint of a high nonrepeating prefix. -/
theorem coefficient_floor_bound {n k s : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hfloor : ∀ i, i < k → 8192 ^ s ≤ acceleratedOrbit i n) :
    (1 - (263 / 4 : Rat) * ((6561 : Rat) / 8192) ^ s) *
      ((2 : Rat) ^ k * (acceleratedOrbit k n : Rat)) ≤ (3 : Rat) ^ oddCount n k * (n : Rat) := by
  have h := reciprocal_sum_le (s := s) (times := List.range k) hnr List.nodup_range
    (fun i hi => hfloor i (List.mem_range.mp hi))
  have hb : correctionBudget n k ≤ (263 / 4 : Rat) * ratio ^ s := by
    by_cases hk : k = 0
    · subst k
      have hd : correctionBudget n 0 = 0 := by
        simp [correctionBudget, reciprocalSum, Rat.div_def]
        grind
      rw [hd]
      exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
    have hbase : 0 < (8192 : Rat) ^ s := Rat.pow_pos (by decide)
    have hlo : (8192 : Rat) ^ s ≤ (n : Rat) := by
      simpa only [Rat.natCast_pow, Rat.natCast_ofNat, acceleratedOrbit_zero] using
        Rat.natCast_le_natCast.mpr (hfloor 0 (by omega))
    have hinv : (n : Rat)⁻¹ ≤ ratio ^ s := by
      apply Rat.le_trans (inv_le_inv hbase hlo)
      apply Rat.le_of_mul_le_mul_right _ hbase
      rw [Rat.inv_mul_cancel _ (by grind), ratio_scaled]
      have ht : (1 : Nat) ≤ 6561 ^ s := Nat.pow_pos (by decide)
      simpa only [Rat.natCast_pow, Rat.natCast_ofNat] using Rat.natCast_le_natCast.mpr ht
    have hx := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_lt_natCast.mpr (acceleratedOrbit_positive hn k)))
    have hfull : reciprocalSum (fun i => acceleratedOrbit i n) (List.range k) ≤ 262 * ratio ^ s := h
    unfold correctionBudget
    rw [Rat.div_def, Rat.div_def]
    grind
  exact Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.mul_nonneg (Rat.pow_nonneg (by decide))
      (Rat.natCast_le_natCast.mpr (Nat.zero_le _)))) (compensated_prefix hn k).2

private def stepLoss (x : Nat) : Rat := (x : Rat)⁻¹ * (1 / 3)

private theorem step_loss_control {x : Nat} (hx : 0 < x) :
    0 ≤ stepLoss x ∧ stepLoss x ≤ 1 / 3 ∧
      (1 - stepLoss x) * (2 * (acceleratedStep x : Rat)) ≤ (3 : Rat) ^ (x % 2) * (x : Rat) := by
  have hx' : 0 < (x : Rat) := Rat.natCast_lt_natCast.mpr hx
  have hx1 : 1 ≤ (x : Rat) := Rat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hx)
  have hi₀ := Rat.le_of_lt (Rat.inv_pos.mpr hx')
  have hi₁ := inv_le_inv (by decide : (0 : Rat) < 1) hx1
  rw [show ((1 : Rat)⁻¹) = 1 by decide +kernel] at hi₁
  have hl₀ : 0 ≤ stepLoss x := Rat.mul_nonneg hi₀ (by decide +kernel)
  have hl₁ : stepLoss x ≤ 1 / 3 := by
    simpa only [stepLoss, Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right hi₁
      (by decide +kernel : 0 ≤ (1 / 3 : Rat))
  refine ⟨hl₀, hl₁, ?_⟩
  rcases mod_two_eq_zero_or_one x with he | ho
  · have ht : 2 * acceleratedStep x = x := by rw [acceleratedStep, if_pos he]; omega
    have ht' : 2 * (acceleratedStep x : Rat) = (x : Rat) := by exact_mod_cast ht
    rw [ht', he, Rat.pow_zero, Rat.one_mul]
    simpa only [Rat.one_mul] using Rat.mul_le_mul_of_nonneg_right
      (show 1 - stepLoss x ≤ (1 : Rat) by grind) (Rat.le_of_lt hx')
  · have ht : 2 * acceleratedStep x = 3 * x + 1 := by
      rw [acceleratedStep, if_neg (by omega)]
      omega
    have ht' : 2 * (acceleratedStep x : Rat) = 3 * (x : Rat) + 1 := by exact_mod_cast ht
    have hlx : stepLoss x * (x : Rat) = 1 / 3 := by
      unfold stepLoss
      calc
        _ = ((x : Rat)⁻¹ * (x : Rat)) * (1 / 3) := by grind
        _ = _ := by rw [Rat.inv_mul_cancel _ (by grind), Rat.one_mul]
    rw [ht', ho, Rat.pow_one]
    calc
      _ = 3 * (x : Rat) + 1 - 3 * (stepLoss x * (x : Rat)) - stepLoss x := by grind
      _ ≤ _ := by
        rw [hlx, show 3 * (1 / 3 : Rat) = 1 by decide +kernel]
        grind

private theorem packed_prefix {n : Nat} (hn : 0 < n) (k : Nat) :
    ∃ q : Nat, ∃ u : Rat, 0 ≤ u ∧ u ≤ 1 / 3 ∧
      reciprocalSum (fun i => acceleratedOrbit i n) (List.range k) = (q : Rat) + 3 * u ∧
      ((2 / 3 : Rat) ^ q * (1 - u)) * ((2 : Rat) ^ k * (acceleratedOrbit k n : Rat)) ≤
        (3 : Rat) ^ oddCount n k * (n : Rat) := by
  induction k with
  | zero =>
    refine ⟨0, 0, by decide, by decide +kernel, ?_, ?_⟩
    · change (0 : Rat) = 0 + 3 * 0
      grind
    · rw [Congruence.oddCount_zero]
      change ((2 / 3 : Rat) ^ 0 * (1 - 0)) * ((2 : Rat) ^ 0 * (n : Rat)) ≤
        (3 : Rat) ^ 0 * (n : Rat)
      simp [Rat.pow_zero, Rat.one_mul]
      grind
  | succ k ih =>
    obtain ⟨q, u, hu₀, hu₁, hs, hb⟩ := ih
    let x := acceleratedOrbit k n
    let y := stepLoss x
    let F := (2 / 3 : Rat) ^ q * (1 - u)
    have hx : 0 < x := acceleratedOrbit_positive hn k
    obtain ⟨hy₀, hy₁, hy⟩ := step_loss_control hx
    change 0 ≤ y at hy₀
    change y ≤ 1 / 3 at hy₁
    change (1 - y) * (2 * (acceleratedStep x : Rat)) ≤ (3 : Rat) ^ (x % 2) * (x : Rat) at hy
    have hF : 0 ≤ F := Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by grind)
    have hN : 0 ≤ (2 : Rat) ^ k := Rat.pow_nonneg (by decide)
    have hsum : reciprocalSum (fun i => acceleratedOrbit i n) (List.range (k + 1)) =
        (q : Rat) + 3 * (u + y) := by
      rw [List.range_succ, reciprocalSum_append, hs]
      have he : reciprocalSum (fun i => acceleratedOrbit i n) [k] = (x : Rat)⁻¹ := by
        simp [reciprocalSum, x, Rat.add_zero]
      rw [he]
      dsimp only [y, stepLoss]
      have hthird : 3 * (1 / 3 : Rat) = 1 := by decide +kernel
      grind
    have hadvance (G : Rat) (hG : G ≤ F * (1 - y)) :
        G * ((2 : Rat) ^ (k + 1) * (acceleratedOrbit (k + 1) n : Rat)) ≤
          (3 : Rat) ^ oddCount n (k + 1) * (n : Rat) := by
      have hnon : 0 ≤ (2 : Rat) ^ (k + 1) * (acceleratedOrbit (k + 1) n : Rat) :=
        Rat.mul_nonneg (Rat.pow_nonneg (by decide)) (Rat.natCast_le_natCast.mpr (Nat.zero_le _))
      have hp : 0 ≤ (3 : Rat) ^ (x % 2) := Rat.pow_nonneg (by decide)
      calc
        _ ≤ (F * (1 - y)) * ((2 : Rat) ^ (k + 1) * (acceleratedOrbit (k + 1) n : Rat)) :=
          Rat.mul_le_mul_of_nonneg_right hG hnon
        _ = (F * (2 : Rat) ^ k) * ((1 - y) * (2 * (acceleratedStep x : Rat))) := by
          rw [acceleratedOrbit_succ_step, Rat.pow_succ]
          change _ = (F * (2 : Rat) ^ k) * ((1 - y) * (2 * (acceleratedStep x : Rat)))
          grind
        _ ≤ (F * (2 : Rat) ^ k) * ((3 : Rat) ^ (x % 2) * (x : Rat)) :=
          Rat.mul_le_mul_of_nonneg_left hy (Rat.mul_nonneg hF hN)
        _ = (3 : Rat) ^ (x % 2) * (F * ((2 : Rat) ^ k * (x : Rat))) := by grind
        _ ≤ (3 : Rat) ^ (x % 2) * ((3 : Rat) ^ oddCount n k * (n : Rat)) :=
          Rat.mul_le_mul_of_nonneg_left hb hp
        _ = _ := by
          rw [Density.oddCount_succ_last]
          change (3 : Rat) ^ (x % 2) * ((3 : Rat) ^ oddCount n k * (n : Rat)) =
            (3 : Rat) ^ (oddCount n k + x % 2) * (n : Rat)
          rcases mod_two_eq_zero_or_one x with he | ho
          · rw [he, Nat.add_zero, Rat.pow_zero, Rat.one_mul]
          · rw [ho, Rat.pow_one, Rat.pow_succ]
            grind
    by_cases hsmall : u + y ≤ (1 / 3 : Rat)
    · refine ⟨q, u + y, by grind, hsmall, hsum, hadvance _ ?_⟩
      have huv := Rat.mul_nonneg hu₀ hy₀
      have h : 1 - (u + y) ≤ (1 - u) * (1 - y) := by grind
      calc
        _ ≤ (2 / 3 : Rat) ^ q * ((1 - u) * (1 - y)) :=
          Rat.mul_le_mul_of_nonneg_left h (Rat.pow_nonneg (by decide +kernel))
        _ = _ := by dsimp only [F]; grind
    · let v := u + y - 1 / 3
      have hv₀ : 0 ≤ v := by dsimp only [v]; grind
      have hv₁ : v ≤ 1 / 3 := by dsimp only [v]; grind
      refine ⟨q + 1, v, hv₀, hv₁, ?_, hadvance _ ?_⟩
      · rw [hsum, Rat.natCast_add]
        dsimp only [v]
        have hthird : 3 * (1 / 3 : Rat) = 1 := by decide +kernel
        grind
      · have hprod := Rat.mul_nonneg (show 0 ≤ (1 / 3 : Rat) - u by grind)
          (show 0 ≤ (1 / 3 : Rat) - y by grind)
        have h : (2 / 3 : Rat) * (1 - v) ≤ (1 - u) * (1 - y) := by
          dsimp only [v]
          grind
        rw [Rat.pow_succ]
        calc
          _ = (2 / 3 : Rat) ^ q * ((2 / 3 : Rat) * (1 - v)) := by grind
          _ ≤ (2 / 3 : Rat) ^ q * ((1 - u) * (1 - y)) :=
            Rat.mul_le_mul_of_nonneg_left h (Rat.pow_nonneg (by decide +kernel))
          _ = _ := by dsimp only [F]; grind

/-- The additive correction of any positive nonrepeating orbit is bounded
from the first step by one uniform multiplicative constant. -/
theorem global_coefficient_ceiling {n k : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    2 ^ k * acceleratedOrbit k n ≤ 2 ^ 263 * (3 ^ oddCount n k * n) := by
  obtain ⟨q, u, hu₀, hu₁, hs, hp⟩ := packed_prefix hn k
  have hsum := reciprocal_sum_le (s := 0) (times := List.range k) hnr List.nodup_range (by
    intro i _
    exact acceleratedOrbit_positive hn i)
  change reciprocalSum (fun i => acceleratedOrbit i n) (List.range k) ≤
    262 * ((6561 : Rat) / 8192) ^ 0 at hsum
  rw [hs, Rat.pow_zero, Rat.mul_one] at hsum
  have hq : q ≤ 262 := Rat.natCast_le_natCast.mp (by grind)
  have hpow (r : Nat) : 1 ≤ (2 : Rat) ^ r * (2 / 3 : Rat) ^ r := by
    induction r with
    | zero => rw [Rat.pow_zero, Rat.pow_zero]; decide +kernel
    | succ r ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hc : 1 ≤ 2 * (2 / 3 : Rat) := by decide +kernel
      calc
        _ ≤ ((2 : Rat) ^ r * (2 / 3 : Rat) ^ r) * (2 * (2 / 3 : Rat)) := by
          have h := Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel : 0 ≤ 2 * (2 / 3 : Rat))
          rw [Rat.one_mul] at h
          exact Rat.le_trans hc h
        _ = _ := by grind
  have htwo : (2 : Rat) ^ (q + 1) ≤ (2 : Rat) ^ 263 := by
    have h := two_pow_le_two_pow (by omega : q + 1 ≤ 263)
    exact_mod_cast h
  let F := (2 / 3 : Rat) ^ q * (1 - u)
  have hF : 0 ≤ F := Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by grind)
  have hres : 1 ≤ 2 * (1 - u) := by grind
  have hscale : 1 ≤ (2 : Rat) ^ 263 * F := by
    calc
      _ ≤ ((2 : Rat) ^ q * (2 / 3 : Rat) ^ q) * (2 * (1 - u)) := by
        have h := Rat.mul_le_mul_of_nonneg_right (hpow q) (by grind : 0 ≤ 2 * (1 - u))
        rw [Rat.one_mul] at h
        exact Rat.le_trans hres h
      _ = (2 : Rat) ^ (q + 1) * F := by rw [Rat.pow_succ]; dsimp only [F]; grind
      _ ≤ _ := Rat.mul_le_mul_of_nonneg_right htwo hF
  let X := (2 : Rat) ^ k * (acceleratedOrbit k n : Rat)
  have hX : 0 ≤ X := Rat.mul_nonneg (Rat.pow_nonneg (by decide))
    (Rat.natCast_le_natCast.mpr (Nat.zero_le _))
  have he : X ≤ (2 : Rat) ^ 263 * ((3 : Rat) ^ oddCount n k * (n : Rat)) := by
    calc
      _ ≤ ((2 : Rat) ^ 263 * F) * X := by
        have h := Rat.mul_le_mul_of_nonneg_right hscale hX
        rwa [Rat.one_mul] at h
      _ = (2 : Rat) ^ 263 * (F * X) := Rat.mul_assoc ..
      _ ≤ _ := Rat.mul_le_mul_of_nonneg_left hp (Rat.pow_nonneg (by decide))
  dsimp only [X] at he
  exact_mod_cast he

/-- A prefix of any length that stays above `2^286` on a nonrepeating orbit
must descend below its start if its coefficient falls to one half. -/
theorem descent_of_half_above_floor {n k : Nat} (hn : 0 < n)
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    (hfloor : ∀ i, i < k → 8192 ^ 22 ≤ acceleratedOrbit i n)
    (hhalf : 2 * 3 ^ oddCount n k ≤ 2 ^ k) : acceleratedOrbit k n < n := by
  apply Nat.lt_of_not_ge
  intro hno
  let x : Rat := acceleratedOrbit k n
  let A := (3 : Rat) ^ oddCount n k
  let B := (2 : Rat) ^ k
  have hx : 0 < x := Rat.natCast_lt_natCast.mpr (acceleratedOrbit_positive hn k)
  have hB : 0 < B := Rat.pow_pos (by decide)
  have hA : 0 ≤ A := Rat.pow_nonneg (by decide)
  have hno' : (n : Rat) ≤ x := Rat.natCast_le_natCast.mpr hno
  have hhalf' : 2 * A ≤ B := by
    simpa [Rat.natCast_mul, Rat.natCast_pow, A, B] using Rat.natCast_le_natCast.mpr hhalf
  have hbudget : (1 - (263 / 4 : Rat) * ratio ^ 22) * (B * x) ≤ A * (n : Rat) :=
    coefficient_floor_bound hn hnr hfloor
  have hmargin : (1 / 2 : Rat) < 1 - (263 / 4 : Rat) * ratio ^ 22 := by decide +kernel
  have hlt : (1 / 2 : Rat) * (B * x) < A * (n : Rat) := by
    have h := Rat.mul_lt_mul_of_pos_right hmargin (Rat.mul_pos hB hx)
    grind
  have hge : A * (n : Rat) ≤ (1 / 2 : Rat) * (B * x) := calc
    _ ≤ A * x := Rat.mul_le_mul_of_nonneg_left hno' hA
    _ = (2 * A) * ((1 / 2 : Rat) * x) := by grind
    _ ≤ B * ((1 / 2 : Rat) * x) := Rat.mul_le_mul_of_nonneg_right hhalf'
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hx))
    _ = _ := by grind
  exact (Rat.not_lt.mpr hge) hlt

/-- A nonrepeating natural-number orbit eventually leaves each finite interval. -/
theorem eventually_ge_of_nonrepeating {n : Nat}
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (bound : Nat) :
    ∃ N, ∀ i, N ≤ i → bound ≤ acceleratedOrbit i n := by
  induction bound with
  | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
  | succ bound ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hhit : ∃ j, acceleratedOrbit j n = bound
    · obtain ⟨j, hj⟩ := hhit
      refine ⟨N + j + 1, fun i hi => ?_⟩
      have hge := hN i (by omega)
      have hne : acceleratedOrbit i n ≠ bound := by
        intro heq
        have := hnr i j (heq.trans hj.symm)
        omega
      omega
    · refine ⟨N, fun i hi => ?_⟩
      have hge := hN i hi
      have hne : acceleratedOrbit i n ≠ bound := fun heq => hhit ⟨i, heq⟩
      omega

/-- Every nonrepeating orbit has arbitrarily high tail minima from which
the cumulative coefficient stays strictly above one half forever. -/
theorem arbitrarily_high_tail_without_half {n : Nat}
    (hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (bound : Nat) :
    ∃ j, bound ≤ acceleratedOrbit j n ∧ 8192 ^ 22 ≤ acceleratedOrbit j n ∧
      ∀ k, 2 ^ k < 2 * 3 ^ oddCount (acceleratedOrbit j n) k := by
  obtain ⟨N, hN⟩ := eventually_ge_of_nonrepeating hnr (bound + 8192 ^ 22)
  obtain ⟨x, ⟨j, hj, hx⟩, hmin⟩ := Minimum.exists_min
    (P := fun x => ∃ j, N ≤ j ∧ acceleratedOrbit j n = x)
    ⟨acceleratedOrbit N n, N, Nat.le_refl _, rfl⟩
  have hsize := hN j hj
  have hshift (i : Nat) : acceleratedOrbit i (acceleratedOrbit j n) = acceleratedOrbit (i + j) n :=
    acceleratedOrbit_add i j n
  have hstay (i : Nat) : acceleratedOrbit j n ≤ acceleratedOrbit i (acceleratedOrbit j n) := by
    apply Nat.le_of_not_gt
    intro hi
    exact hmin _ (hx ▸ hi) ⟨i + j, by omega, (hshift i).symm⟩
  refine ⟨j, by omega, by omega, fun k => Nat.lt_of_not_ge ?_⟩
  intro hhalf
  have hnr' : ∀ i l, acceleratedOrbit i (acceleratedOrbit j n) =
      acceleratedOrbit l (acceleratedOrbit j n) → i = l := by
    intro i l heq
    have heq' : acceleratedOrbit (i + j) n = acceleratedOrbit (l + j) n := by
      rw [← hshift, ← hshift, heq]
    exact Nat.add_right_cancel (hnr _ _ heq')
  have hpos : 0 < acceleratedOrbit j n := Nat.lt_of_lt_of_le (by decide) (by omega :
    8192 ^ 22 ≤ acceleratedOrbit j n)
  have hfloor : ∀ i, i < k → 8192 ^ 22 ≤ acceleratedOrbit i (acceleratedOrbit j n) := by
    intro i _
    exact Nat.le_trans (by omega) (hstay i)
  exact Nat.not_lt_of_ge (hstay k) (descent_of_half_above_floor hpos hnr' hfloor hhalf)

/-- Universal half-coefficient crossings above the explicit floor would
exclude all divergent orbits. Periodic orbits require separate exclusion. -/
theorem repeats_of_high_half_crossings
    (hcross : ∀ x, 8192 ^ 22 ≤ x → ∃ k, 2 * 3 ^ oddCount x k ≤ 2 ^ k) (n : Nat) :
    ∃ i j, i < j ∧ acceleratedOrbit i n = acceleratedOrbit j n := by
  apply Classical.byContradiction
  intro hn
  have hnr : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j := by
    intro i j heq
    rcases Nat.lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (hn ⟨i, j, hlt, heq⟩)
    · exact he
    · exact False.elim (hn ⟨j, i, hgt, heq.symm⟩)
  obtain ⟨j, _, hj, hstay⟩ := arbitrarily_high_tail_without_half hnr 0
  obtain ⟨k, hk⟩ := hcross (acceleratedOrbit j n) hj
  exact Nat.not_lt_of_ge hk (hstay k)

/-- Two separate obligations suffice for the standard Collatz statement:
eventual half crossings at large starts and exclusion of other cycles. -/
theorem collatz_of_high_half_crossings_and_cycle_exclusion
    (hcross : ∀ x, 8192 ^ 22 ≤ x → ∃ k, 2 * 3 ^ oddCount x k ≤ 2 ^ k)
    (hcycles : ∀ x L, 0 < x → AccCycle.AccIsCycleOf x L → x ≤ 2) : CollatzConjecture := by
  intro n hn
  obtain ⟨i, j, hij, hrepeat⟩ := repeats_of_high_half_crossings hcross n
  have hpos := acceleratedOrbit_positive hn i
  have hcycle : AccCycle.AccIsCycleOf (acceleratedOrbit i n) (j - i) := by
    refine ⟨by omega, ?_⟩
    rw [acceleratedOrbit_add, show j - i + i = j by omega, ← hrepeat]
  have hsmall := hcycles _ _ hpos hcycle
  apply Reach.reachesOne_of_accOrbit (k := i) hn
  have hcases : acceleratedOrbit i n = 1 ∨ acceleratedOrbit i n = 2 := by omega
  rcases hcases with h | h
  · rw [h]; exact Reach.reachesOne_one
  · rw [h]; exact Reach.reachesOne_two

end Collatz.OrbitCorrectionBudget
