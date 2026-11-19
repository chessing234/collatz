import Collatz.Strategy.SynchronousClasses

/-!
# Dynamics of least synchronous representatives

Halving a least representative keeps it least. The odd step may
compress, but only if the new representative has no odd preimage.
-/

namespace Collatz.SynchronousDynamics

open Collatz.SynchronousClasses Collatz.Reach

private theorem shortcut_odd_preimage {x : Nat} (hx : x % 3 = 2) :
    ∃ z, z % 2 = 1 ∧ acceleratedOrbit 1 z = x := by
  let q := x / 3
  let z := 2 * q + 1
  have ho : z % 2 = 1 := by dsimp [z]; omega
  refine ⟨z, ho, ?_⟩
  change acceleratedStep z = x
  rw [acceleratedStep, if_neg (by omega)]
  dsimp [z, q]
  omega

/-- A least even representative has a least half. -/
theorem least_half {x : Nat} (hx : least (2 * x) = 2 * x) : least x = x := by
  have h := least_le (least_related x).double
  rw [hx] at h
  exact Nat.le_antisymm (least_le_self _) (Nat.le_of_mul_le_mul_left h (by decide))

/-- The halving rule also holds for finite least representatives
when the horizon is decreased by one. -/
theorem leastAt_half {k x : Nat} (hx : leastAt (k + 1) (2 * x) = 2 * x) :
    leastAt k x = x := by
  have hmeet : acceleratedOrbit (k + 1) (2 * x) =
      acceleratedOrbit (k + 1) (2 * leastAt k x) := by
    rw [← acceleratedOrbit_add k 1, ← acceleratedOrbit_add k 1,
      shortcut_double, shortcut_double, leastAt_meets]
  have h := leastAt_le hmeet
  rw [hx] at h
  exact Nat.le_antisymm (leastAt_le rfl) (Nat.le_of_mul_le_mul_left h (by decide))

/-- An even least representative cannot halve into a state with an
odd predecessor, since that predecessor would be a smaller mate. -/
theorem least_half_mod_three {x : Nat} (hx : least (2 * x) = 2 * x) :
    x % 3 ≠ 2 := by
  intro hbad
  obtain ⟨z, hz, hstep⟩ := shortcut_odd_preimage hbad
  have hle := least_le (x := 2 * x) (y := z)
    ⟨1, (shortcut_double x).trans hstep.symm⟩
  rw [hx] at hle
  change acceleratedStep z = x at hstep
  rw [acceleratedStep, if_neg (by omega)] at hstep
  omega

/-- Two consecutive even least representatives require a factor of
three in their common odd part. -/
theorem least_four_dvd_three {x : Nat} (hx : least (4 * x) = 4 * x) :
    x % 3 = 0 := by
  have h4 : least (2 * (2 * x)) = 2 * (2 * x) := by simpa only [← Nat.mul_assoc] using hx
  have h2 := least_half h4
  have hfirst := least_half_mod_three h4
  have hsecond := least_half_mod_three h2
  omega

/-- An odd preimage of a least representative is itself least. -/
theorem least_odd_preimage {x : Nat} (ho : x % 2 = 1)
    (hy : least (acceleratedOrbit 1 x) = acceleratedOrbit 1 x) : least x = x := by
  have hle := least_le_self x
  apply Nat.le_antisymm hle
  apply Nat.le_of_not_gt
  intro hlt
  have hmate := least_le ((least_related x).shift 1)
  rw [hy] at hmate
  change acceleratedStep x ≤ acceleratedStep (least x) at hmate
  rw [acceleratedStep, if_neg (by omega : x % 2 ≠ 0), acceleratedStep] at hmate
  rcases Arith.mod_two_eq_zero_or_one (least x) with he | ho'
  · rw [if_pos he] at hmate
    omega
  · rw [if_neg (by omega : least x % 2 ≠ 0)] at hmate
    omega

/-- When the least representative has an odd preimage, that
preimage is its exact predecessor in the class permutation. -/
theorem previous_eq_odd_preimage {x : Nat} (hx : least x = x) (hmod : x % 3 = 2) :
    previous x % 2 = 1 ∧ acceleratedOrbit 1 (previous x) = x := by
  obtain ⟨z, hz, hstep⟩ := shortcut_odd_preimage hmod
  have hzmin : least z = z := least_odd_preimage hz (by rw [hstep, hx])
  have hrel : SameTime (2 * x) z := ⟨1, (shortcut_double x).trans hstep.symm⟩
  have heq : previous x = z := (least_eq_iff.mpr hrel).trans hzmin
  simpa only [heq] using And.intro hz hstep

/-- An odd least representative can compress its shortcut image
only into a class minimum without an odd predecessor. -/
theorem odd_next_eq_of_mod_three {x : Nat} (hx : least x = x) (ho : x % 2 = 1)
    (hmod : next x % 3 = 2) : next x = acceleratedOrbit 1 x := by
  obtain ⟨z, hz, hstep⟩ := shortcut_odd_preimage hmod
  have hm : SameTime (acceleratedOrbit 1 x) (acceleratedOrbit 1 z) := by
    rw [hstep]
    exact least_related (acceleratedOrbit 1 x)
  have hle := least_le hm.unshift
  rw [hx] at hle
  have hmon : acceleratedOrbit 1 x ≤ acceleratedOrbit 1 z := by
    change acceleratedStep x ≤ acceleratedStep z
    rw [acceleratedStep, acceleratedStep, if_neg (by omega : x % 2 ≠ 0),
      if_neg (by omega : z % 2 ≠ 0)]
    exact Nat.div_le_div_right (by omega)
  rw [hstep] at hmon
  exact Nat.le_antisymm (least_le_self _) hmon

/-- The least representative of the class reached at shortcut time `k`. -/
noncomputable def trajectory (n k : Nat) : Nat :=
  least (acceleratedOrbit k n)

theorem trajectory_step (n k : Nat) : trajectory n (k + 1) = next (trajectory n k) := by
  unfold trajectory next
  rw [Nat.add_comm k 1, ← acceleratedOrbit_add]
  exact least_eq_iff.mpr ((least_related (acceleratedOrbit k n)).shift 1)

theorem trajectory_positive {n : Nat} (hn : 0 < n) (k : Nat) : 0 < trajectory n k :=
  least_positive (acceleratedOrbit_positive hn k)

theorem trajectory_injective {n : Nat}
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∀ i j, trajectory n i = trajectory n j → i = j := by
  intro i j h
  obtain ⟨k, hk⟩ := least_eq_iff.mp h
  rw [acceleratedOrbit_add, acceleratedOrbit_add] at hk
  exact Nat.add_left_cancel (hinj _ _ hk)

theorem trajectory_even_step {n k x : Nat} (hx : trajectory n k = 2 * x) :
    trajectory n (k + 1) = x := by
  rw [trajectory_step, hx, next, shortcut_double]
  have he : least (trajectory n k) = trajectory n k := least_idempotent _
  rw [hx] at he
  exact least_half he

private theorem quotient_order {D x y : Nat} (hD : 0 < D) :
    x < y ↔ x / D < y / D ∨ (x / D = y / D ∧ x % D < y % D) := by
  have hx := Nat.mod_add_div x D
  have hy := Nat.mod_add_div y D
  have hremx := Nat.mod_lt x hD
  have hremy := Nat.mod_lt y hD
  have hlt (a b : Nat) (hab : a / D < b / D) : a < b := by
    have h := Nat.mod_add_div b D
    have hbound : a < (b / D) * D := (Nat.div_lt_iff_lt_mul hD).mp hab
    rw [Nat.mul_comm] at hbound
    omega
  constructor
  · intro h
    rcases Nat.lt_or_ge (x / D) (y / D) with hlt' | hge
    · exact Or.inl hlt'
    · have he := Nat.le_antisymm (Nat.div_le_div_right (Nat.le_of_lt h)) hge
      rw [he] at hx
      exact Or.inr ⟨he, by omega⟩
  · rintro (h | ⟨he, h⟩)
    · exact hlt x y h
    · rw [he] at hx
      omega

private theorem high_part_at_target (k x : Nat) :
    x / 2 ^ k = acceleratedOrbit k x / 3 ^ oddCount x k := by
  let D := 2 ^ k
  let r := x % D
  have hr : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit : D * (x / D) + r = x := by
    simpa only [r, Nat.add_comm] using Nat.mod_add_div x D
  have ht := (orbit_target_iff hr).mp (by rw [hsplit] :
    acceleratedOrbit k (D * (x / D) + r) = acceleratedOrbit k x)
  rw [Density.oddCount_mod x k]
  exact ht.2.symm

private theorem quotient_gap {x a b : Nat} (hab : a < b) :
    3 * (x / 3 ^ b) ≤ x / 3 ^ a := by
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 3))).2
  calc
    _ = (x / 3 ^ b) * 3 ^ (a + 1) := by rw [Nat.pow_succ]; ac_rfl
    _ ≤ (x / 3 ^ b) * 3 ^ b := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hab))
    _ ≤ _ := Nat.div_mul_le_self _ _

/-- When a source occupies a positive dyadic high part, a mate is
smaller exactly when its odd count is larger, or its equal-count
residue is smaller. -/
theorem smaller_mate_iff {k n m : Nat} (hn : 2 ^ k ≤ n)
    (hmeet : acceleratedOrbit k n = acceleratedOrbit k m) :
    m < n ↔ oddCount n k < oddCount m k ∨
      (oddCount n k = oddCount m k ∧ m % 2 ^ k < n % 2 ^ k) := by
  let D := 2 ^ k
  let a := oddCount n k
  let b := oddCount m k
  let x := acceleratedOrbit k n
  have hN : n / D = x / 3 ^ a := high_part_at_target k n
  have hM : m / D = x / 3 ^ b := by
    have ht := high_part_at_target k m
    rw [← hmeet] at ht
    exact ht
  have hp : 0 < n / D := by
    have h := (Nat.le_div_iff_mul_le (show 0 < D from Nat.two_pow_pos k)).2
      (by simpa using hn : 1 * D ≤ n)
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) h
  have horder : m < n ↔ m / D < n / D ∨ (m / D = n / D ∧ m % D < n % D) :=
    quotient_order (Nat.two_pow_pos k)
  change m < n ↔ a < b ∨ (a = b ∧ m % D < n % D)
  rcases Nat.lt_trichotomy a b with hlt | he | hgt
  · have hgap := quotient_gap (x := x) hlt
    rw [← hN, ← hM] at hgap
    have hsmall : m / D < n / D := by omega
    exact ⟨fun _ => Or.inl hlt, fun _ => horder.mpr (Or.inl hsmall)⟩
  · have hq : m / D = n / D := by rw [hM, hN, he]
    constructor
    · intro h
      rcases horder.mp h with hbad | ⟨_, hr⟩
      · rw [hq] at hbad
        exact (Nat.lt_irrefl _ hbad).elim
      · exact Or.inr ⟨he, hr⟩
    · rintro (hbad | ⟨_, hr⟩)
      · rw [he] at hbad
        exact (Nat.lt_irrefl _ hbad).elim
      · exact horder.mpr (Or.inr ⟨hq, hr⟩)
  · have hgap := quotient_gap (x := x) hgt
    rw [← hM, ← hN] at hgap
    have hlarge : n / D < m / D := by omega
    constructor
    · intro h
      rcases horder.mp h with hbad | ⟨hbad, _⟩
      · exact (Nat.not_lt_of_gt hlarge hbad).elim
      · rw [hbad] at hlarge
        exact (Nat.lt_irrefl _ hlarge).elim
    · rintro (hbad | ⟨hbad, _⟩)
      · exact (Nat.not_lt_of_gt hgt hbad).elim
      · rw [hbad] at hgt
        exact (Nat.lt_irrefl _ hgt).elim

/-- An exact finite-horizon descent test using the inverse fiber. -/
theorem leastAt_drops_iff {k n : Nat} (hn : 2 ^ k ≤ n) :
    leastAt k n < n ↔ ∃ m ∈ fiber k (acceleratedOrbit k n),
      oddCount n k < oddCount m k ∨
        (oddCount n k = oddCount m k ∧ m % 2 ^ k < n % 2 ^ k) := by
  constructor
  · intro h
    have hm := leastAt_meets k n
    exact ⟨leastAt k n, mem_fiber.mpr hm, (smaller_mate_iff hn hm.symm).mp h⟩
  · rintro ⟨m, hm, hprofile⟩
    have he := (mem_fiber.mp hm).symm
    exact Nat.lt_of_le_of_lt (leastAt_le he) ((smaller_mate_iff hn he).mpr hprofile)

/-- A larger odd count in the same fiber contracts the original
source by at least a fixed factor once its high part is at least two. -/
theorem larger_count_contracts {k n m : Nat} (hn : 2 * 2 ^ k ≤ n)
    (hmeet : acceleratedOrbit k n = acceleratedOrbit k m)
    (hcount : oddCount n k < oddCount m k) : 3 * m < 2 * n := by
  let D := 2 ^ k
  let u := n / D
  let v := m / D
  have hD : 0 < D := Nat.two_pow_pos k
  have hu : 2 ≤ u := (Nat.le_div_iff_mul_le hD).mpr hn
  have hN := high_part_at_target k n
  have hM := high_part_at_target k m
  rw [← hmeet] at hM
  have hgap := quotient_gap (x := acceleratedOrbit k n) hcount
  rw [← hN, ← hM] at hgap
  change 3 * v ≤ u at hgap
  have hscale : 3 * (v + 1) ≤ 2 * u := by omega
  have hm : m < D * (v + 1) := by
    have hrem := Nat.mod_lt m hD
    have hsplit := Nat.mod_add_div m D
    change m % D + D * v = m at hsplit
    rw [Nat.mul_succ]
    omega
  calc
    _ < 3 * (D * (v + 1)) := Nat.mul_lt_mul_of_pos_left hm (by decide)
    _ = D * (3 * (v + 1)) := Nat.mul_left_comm ..
    _ ≤ D * (2 * u) := Nat.mul_le_mul_left _ hscale
    _ = 2 * (u * D) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

/-- A positive shortcut trajectory cannot become a fixed point in
one equal-time class. -/
theorem next_ne_self {x : Nat} (hx : 0 < x) : next x ≠ x := by
  intro h
  have hrel := least_related (acceleratedOrbit 1 x)
  change SameTime (acceleratedOrbit 1 x) (next x) at hrel
  rw [h] at hrel
  obtain ⟨k, hk⟩ := hrel
  rw [acceleratedOrbit_add, acceleratedOrbit_succ_step] at hk
  have hzero := AccCycle.no_acc_fixed_point hk
  exact Nat.ne_of_gt (acceleratedOrbit_positive hx k) hzero

/-- A larger-count mate for the image of an odd least representative
forces an immediate descent in the class permutation. -/
theorem next_lt_of_larger_count {x k m : Nat} (hx : 0 < x) (ho : x % 2 = 1)
    (hsize : 2 * 2 ^ k ≤ acceleratedOrbit 1 x)
    (hmeet : acceleratedOrbit k (acceleratedOrbit 1 x) = acceleratedOrbit k m)
    (hcount : oddCount (acceleratedOrbit 1 x) k < oddCount m k) : next x < x := by
  have hm := larger_count_contracts hsize hmeet hcount
  have hnext : next x ≤ m := least_le ⟨k, hmeet⟩
  have hstep : 2 * acceleratedOrbit 1 x = 3 * x + 1 := by
    change 2 * acceleratedStep x = 3 * x + 1
    rw [acceleratedStep, if_neg (by omega)]
    omega
  have hle : next x ≤ x := by omega
  exact Nat.lt_of_le_of_ne hle (next_ne_self hx)

private theorem reachesOne_of_related {x y : Nat} (hx : 0 < x) (hy : 0 < y)
    (h : SameTime x y) (hreach : ReachesOne y) : ReachesOne x := by
  obtain ⟨k, hk⟩ := h
  apply reachesOne_of_accOrbit hx (k := k)
  rw [hk]
  exact (reachesOne_accOrbit_iff hy k).mp hreach

/-- It suffices to find a larger-count inverse profile for the image
of every odd least representative above two. -/
theorem collatz_of_larger_count_profiles
    (hboost : ∀ x, 2 < x → least x = x → x % 2 = 1 →
      ∃ k m, 2 * 2 ^ k ≤ acceleratedOrbit 1 x ∧
        acceleratedOrbit k (acceleratedOrbit 1 x) = acceleratedOrbit k m ∧
        oddCount (acceleratedOrbit 1 x) k < oddCount m k) :
    CollatzConjecture := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hsmall : n ≤ 2
    · have hn' : n = 1 ∨ n = 2 := by omega
      rcases hn' with rfl | rfl
      · exact reachesOne_one
      · exact reachesOne_two
    have hlo := least_positive hn
    by_cases hl : least n < n
    · exact reachesOne_of_related hn hlo (least_related n) (ih _ hl hlo)
    have hcanon : least n = n := Nat.le_antisymm (least_le_self _) (Nat.le_of_not_gt hl)
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · have hh : 0 < n / 2 ∧ n / 2 < n := by omega
      exact (reachesOne_even_iff hn he).mpr (ih _ hh.2 hh.1)
    · obtain ⟨k, m, hsize, hmeet, hcount⟩ :=
        hboost n (Nat.lt_of_not_ge hsmall) hcanon ho
      have hdrop := next_lt_of_larger_count hn ho hsize hmeet hcount
      have hpos := acceleratedOrbit_positive hn 1
      have hpos' := least_positive hpos
      have hreach := ih _ hdrop hpos'
      apply reachesOne_of_accOrbit hn (k := 1)
      exact reachesOne_of_related hpos hpos' (least_related _) hreach

end Collatz.SynchronousDynamics
