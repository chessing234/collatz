import Collatz.Strategy.OrbitOccupationBootstrap
import Collatz.Strategy.NeverDrops

/-!
# Least representatives of equal-time Collatz meetings

The shortcut map induces a permutation on equal-time meeting classes.
Choosing each class's least member gives an injective compression map:
it can only lower a shortcut image and it preserves distinct classes.
-/

namespace Collatz.SynchronousClasses

open Collatz.OrbitCapacity Collatz.OrbitOccupationBootstrap Collatz.Reach

/-- Two starts have equal shortcut states after a common number of steps. -/
def SameTime (x y : Nat) : Prop :=
  ∃ k, acceleratedOrbit k x = acceleratedOrbit k y

theorem SameTime.refl (x : Nat) : SameTime x x := ⟨0, rfl⟩

theorem SameTime.symm {x y : Nat} (h : SameTime x y) : SameTime y x := by
  obtain ⟨k, heq⟩ := h
  exact ⟨k, heq.symm⟩

theorem SameTime.trans {x y z : Nat} (hxy : SameTime x y) (hyz : SameTime y z) :
    SameTime x z := by
  obtain ⟨j, hj⟩ := hxy
  obtain ⟨k, hk⟩ := hyz
  refine ⟨k + j, ?_⟩
  calc
    acceleratedOrbit (k + j) x = acceleratedOrbit k (acceleratedOrbit j x) :=
      (acceleratedOrbit_add ..).symm
    _ = acceleratedOrbit (k + j) y := by rw [hj, acceleratedOrbit_add]
    _ = acceleratedOrbit j (acceleratedOrbit k y) := by rw [acceleratedOrbit_add, Nat.add_comm]
    _ = acceleratedOrbit (k + j) z := by rw [hk, acceleratedOrbit_add, Nat.add_comm]

theorem SameTime.shift {x y : Nat} (h : SameTime x y) (j : Nat) :
    SameTime (acceleratedOrbit j x) (acceleratedOrbit j y) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k j,
    ← acceleratedOrbit_add j k x, ← acceleratedOrbit_add j k y, hk]

theorem SameTime.unshift {x y j : Nat}
    (h : SameTime (acceleratedOrbit j x) (acceleratedOrbit j y)) : SameTime x y := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + j, by simpa only [acceleratedOrbit_add] using hk⟩

private theorem exists_least (x : Nat) :
    ∃ y, SameTime x y ∧ ∀ z, z < y → ¬ SameTime x z :=
  Minimum.exists_min ⟨x, SameTime.refl x⟩

/-- The least natural number in an equal-time meeting class. -/
noncomputable def least (x : Nat) : Nat := Classical.choose (exists_least x)

theorem least_related (x : Nat) : SameTime x (least x) :=
  (Classical.choose_spec (exists_least x)).1

theorem least_le {x y : Nat} (h : SameTime x y) : least x ≤ y :=
  Nat.le_of_not_gt (fun hy => (Classical.choose_spec (exists_least x)).2 y hy h)

theorem least_eq_iff {x y : Nat} : least x = least y ↔ SameTime x y := by
  constructor
  · intro h
    have hy := least_related y
    rw [← h] at hy
    exact (least_related x).trans hy.symm
  · intro h
    exact Nat.le_antisymm (least_le (h.trans (least_related y)))
      (least_le (h.symm.trans (least_related x)))

theorem least_idempotent (x : Nat) : least (least x) = least x :=
  least_eq_iff.mpr (least_related x).symm

theorem least_le_self (x : Nat) : least x ≤ x := least_le (SameTime.refl x)

private theorem orbit_zero_state (k : Nat) : acceleratedOrbit k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [acceleratedOrbit_succ, acceleratedStep_zero] using ih

theorem least_positive {x : Nat} (hx : 0 < x) : 0 < least x := by
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨k, hk⟩ := least_related x
  rw [hzero, orbit_zero_state] at hk
  exact (Nat.ne_of_gt (acceleratedOrbit_positive hx k)) hk

private theorem shortcut_double (x : Nat) : acceleratedOrbit 1 (2 * x) = x := by
  have he : (2 * x) % 2 = 0 := by omega
  simp [acceleratedStep, he]

theorem SameTime.double {x y : Nat} (h : SameTime x y) : SameTime (2 * x) (2 * y) := by
  apply SameTime.unshift (j := 1)
  simpa only [shortcut_double] using h

/-- The next representative for the action induced by one shortcut step. -/
noncomputable def next (x : Nat) : Nat := least (acceleratedOrbit 1 x)

/-- The previous representative is obtained from the even predecessor. -/
noncomputable def previous (x : Nat) : Nat := least (2 * x)

theorem next_previous (x : Nat) : next (previous x) = least x := by
  apply least_eq_iff.mpr
  have h := (least_related (2 * x)).shift 1
  rw [shortcut_double] at h
  exact h.symm

theorem previous_next (x : Nat) : previous (next x) = least x := by
  apply least_eq_iff.mpr
  have h := (least_related (acceleratedOrbit 1 x)).double
  have he : SameTime (2 * acceleratedOrbit 1 x) x := ⟨1, shortcut_double _⟩
  exact h.symm.trans he

/-- Distinct least representatives stay distinct after compressing
their shortcut images back to least representatives. -/
theorem compressed_injective {x y : Nat} (hx : least x = x) (hy : least y = y) (k : Nat)
    (h : least (acceleratedOrbit k x) = least (acceleratedOrbit k y)) : x = y := by
  have he := least_eq_iff.mpr (least_eq_iff.mp h).unshift
  simpa only [hx, hy] using he

/-- The number of equal-time classes with a representative below
`X` is bounded by a constant times `X^(19/20)`. -/
theorem least_count_power :
    ∃ C, ∀ {X : Nat}, 0 < X → ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, x < X ∧ least x = x) → xs.length ^ 20 ≤ C * X ^ 19 := by
  obtain ⟨C, hC⟩ := bound_of_compression tilt149
  refine ⟨C ^ 20 * ((2 : Nat) ^ 2980) ^ 19, ?_⟩
  intro X hX xs hnd hx
  apply power_of_aligned hX
  intro j hj
  have hsteps : tilt149.steps * (20 * j) = 2980 * j := by
    rw [← Nat.mul_assoc]
    rfl
  have hsmall (x : Nat) (hxm : x ∈ xs) :
      x < 2 ^ (tilt149.steps * (20 * j)) * 2 ∧ least x = x := by
    obtain ⟨hlt, hleast⟩ := hx x hxm
    rw [hsteps]
    exact ⟨Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt hj)
      (Nat.le_mul_of_pos_right _ (by decide)), hleast⟩
  have hc := hC (fun x => least x = x) (fun k x => least (acceleratedOrbit k x))
    (fun k x _ => ⟨least_idempotent _, least_le_self _⟩)
    (fun k _ _ hx hy => compressed_injective hx hy k) (20 * j) xs hnd hsmall
  refine Nat.le_trans hc (Nat.mul_le_mul_left _ ?_)
  rw [Nat.pow_mul, Nat.pow_mul]
  exact Nat.pow_le_pow_left tilt149_rate j

/-- Equal endpoints and equal odd counts give a class reduction
for every common dyadic lift. -/
theorem least_le_of_residue_collision {x y k : Nat}
    (hval : acceleratedOrbit k x = acceleratedOrbit k y)
    (hcount : oddCount x k = oddCount y k) (t : Nat) :
    least (2 ^ k * t + y) ≤ 2 ^ k * t + x := by
  apply least_le
  refine ⟨k, ?_⟩
  rw [Congruence.accOrbit_pow_two_mul_add, Congruence.accOrbit_pow_two_mul_add, hcount, hval]

/-- For a fixed dyadic residue, the exact preimage of a target is
determined by its ternary remainder and quotient. -/
theorem orbit_target_iff {k r u z : Nat} (hr : r < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * u + r) = z ↔
      z % 3 ^ oddCount r k = acceleratedOrbit k r ∧ z / 3 ^ oddCount r k = u := by
  let A := 3 ^ oddCount r k
  let y := acceleratedOrbit k r
  have hA : 0 < A := Nat.pow_pos (by decide)
  have hy : y < A := by
    simpa using image_lt (k := k) (x := r) (c := 1) (by simpa using hr)
  rw [Congruence.accOrbit_pow_two_mul_add]
  change A * u + y = z ↔ z % A = y ∧ z / A = u
  constructor
  · rintro rfl
    constructor
    · rw [Nat.mul_comm, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hy]
    · rw [Nat.mul_comm, Nat.add_comm (u * A) y, Nat.add_mul_div_right _ _ hA,
        Nat.div_eq_of_lt hy, Nat.zero_add]
  · rintro ⟨hm, hd⟩
    rw [← hm, ← hd]
    exact Nat.div_add_mod _ _

/-- A residue with a larger odd count can coalesce with an entire
mixed dyadic and ternary class of sources of smaller odd count. -/
theorem mixed_residue_meeting {k r s d : Nat} (hr : r < 2 ^ k)
    (hcount : oddCount s k = oddCount r k + d)
    (hmod : acceleratedOrbit k s % 3 ^ oddCount r k = acceleratedOrbit k r) (v : Nat) :
    acceleratedOrbit k
      (2 ^ k * (3 ^ d * v + acceleratedOrbit k s / 3 ^ oddCount r k) + r) =
      acceleratedOrbit k (2 ^ k * v + s) := by
  let A := 3 ^ oddCount r k
  have hA : 0 < A := Nat.pow_pos (by decide)
  rw [Congruence.accOrbit_pow_two_mul_add k v s, hcount, Nat.pow_add]
  apply (orbit_target_iff hr).mpr
  change (A * 3 ^ d * v + acceleratedOrbit k s) % A = acceleratedOrbit k r ∧
    (A * 3 ^ d * v + acceleratedOrbit k s) / A = 3 ^ d * v + acceleratedOrbit k s / A
  rw [Nat.mul_assoc, Nat.mul_comm A, Nat.mul_add_mod_self_right, hmod,
    Nat.add_comm (3 ^ d * v * A), Nat.add_mul_div_right _ _ hA, Nat.add_comm]
  exact ⟨rfl, rfl⟩

/-- If the original lift has high part at least two, the larger-count
alternative in a mixed meeting is less than two thirds of it. -/
theorem mixed_representative_contraction {k r s d v : Nat} (hr : r < 2 ^ k) (hs : s < 2 ^ k)
    (hcount : oddCount s k = oddCount r k + d) (hd : 0 < d)
    (hmod : acceleratedOrbit k s % 3 ^ oddCount r k = acceleratedOrbit k r)
    (hu : 2 ≤ 3 ^ d * v + acceleratedOrbit k s / 3 ^ oddCount r k) :
    3 * least (2 ^ k * (3 ^ d * v + acceleratedOrbit k s / 3 ^ oddCount r k) + r) <
      2 * (2 ^ k * (3 ^ d * v + acceleratedOrbit k s / 3 ^ oddCount r k) + r) := by
  let u := 3 ^ d * v + acceleratedOrbit k s / 3 ^ oddCount r k
  have hleast : least (2 ^ k * u + r) ≤ 2 ^ k * v + s :=
    least_le ⟨k, mixed_residue_meeting hr hcount hmod v⟩
  have hv : 3 * v ≤ u := Nat.le_trans
    (Nat.mul_le_mul_right v (Nat.le_pow hd)) (Nat.le_add_right _ _)
  have huv : 3 * (v + 1) ≤ 2 * u := by
    by_cases hvzero : v = 0
    · subst v; omega
    · omega
  have hlt : 2 ^ k * v + s < 2 ^ k * (v + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_lt_add_left hs _
  calc
    _ ≤ 3 * (2 ^ k * v + s) := Nat.mul_le_mul_left _ hleast
    _ < 3 * (2 ^ k * (v + 1)) := Nat.mul_lt_mul_of_pos_left hlt (by decide)
    _ = 2 ^ k * (3 * (v + 1)) := Nat.mul_left_comm ..
    _ ≤ 2 ^ k * (2 * u) := Nat.mul_le_mul_left _ huv
    _ = 2 * (2 ^ k * u) := Nat.mul_left_comm ..
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/-- Enumerate the preimages of a target at exactly `k` shortcut
steps, checking one ternary remainder per dyadic residue. -/
def fiber (k target : Nat) : List Nat :=
  (List.range (2 ^ k)).filterMap (fun r =>
    let A := 3 ^ oddCount r k
    if target % A = acceleratedOrbit k r then
      some (2 ^ k * (target / A) + r)
    else none)

theorem mem_fiber {k target x : Nat} : x ∈ fiber k target ↔ acceleratedOrbit k x = target := by
  constructor
  · intro hx
    obtain ⟨r, hr, hsome⟩ := List.mem_filterMap.mp hx
    have hr' := List.mem_range.mp hr
    let A := 3 ^ oddCount r k
    change (if target % A = acceleratedOrbit k r then
      some (2 ^ k * (target / A) + r) else none) = some x at hsome
    by_cases hm : target % A = acceleratedOrbit k r
    · rw [if_pos hm] at hsome
      rw [← Option.some.inj hsome]
      exact (orbit_target_iff hr').mpr ⟨hm, rfl⟩
    · simp [hm] at hsome
  · intro hx
    let D := 2 ^ k
    let r := x % D
    let u := x / D
    have hsplit : D * u + r = x := by
      simpa only [r, u, Nat.add_comm] using Nat.mod_add_div x D
    have hr : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
    have he := (orbit_target_iff hr).mp (hsplit ▸ hx)
    apply List.mem_filterMap.mpr
    refine ⟨r, List.mem_range.mpr hr, ?_⟩
    rw [if_pos he.1, he.2, hsplit]

/-- The least source that already meets `n` at the given horizon. -/
def leastAt (k n : Nat) : Nat :=
  (n :: fiber k (acceleratedOrbit k n)).min (by simp)

theorem leastAt_meets (k n : Nat) :
    acceleratedOrbit k (leastAt k n) = acceleratedOrbit k n := by
  have hmem : leastAt k n ∈ n :: fiber k (acceleratedOrbit k n) := List.min_mem (by simp)
  rcases List.mem_cons.mp hmem with heq | hf
  · rw [heq]
  · exact mem_fiber.mp hf

theorem leastAt_le {k n m : Nat} (h : acceleratedOrbit k n = acceleratedOrbit k m) :
    leastAt k n ≤ m :=
  List.min_le_of_mem (List.mem_cons_of_mem _ (mem_fiber.mpr h.symm))

theorem leastAt_antitone {j k n : Nat} (hjk : j ≤ k) : leastAt k n ≤ leastAt j n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  apply leastAt_le
  rw [Nat.add_comm j d, ← acceleratedOrbit_add d j, ← acceleratedOrbit_add d j, leastAt_meets]

theorem leastAt_eventually (n : Nat) : ∃ j, ∀ k, j ≤ k → leastAt k n = least n := by
  obtain ⟨j, hj⟩ := least_related n
  refine ⟨j, ?_⟩
  intro k hk
  exact Nat.le_antisymm (Nat.le_trans (leastAt_antitone hk) (leastAt_le hj))
    (least_le ⟨k, (leastAt_meets k n).symm⟩)

private theorem last_image (k c : Nat) (hc : 0 < c) :
    acceleratedOrbit k (c * 2 ^ k - 1) + 1 = c * 3 ^ k := by
  induction k generalizing c with
  | zero => simpa using Nat.sub_add_cancel (Nat.succ_le_of_lt hc)
  | succ k ih =>
    let a := c * 2 ^ k
    have ha : 0 < a := Nat.mul_pos hc (Nat.two_pow_pos _)
    have ho : (2 * a - 1) % 2 = 1 := by omega
    have hstart : c * 2 ^ (k + 1) - 1 = 2 * a - 1 := by
      rw [Nat.pow_succ 2, ← Nat.mul_assoc, Nat.mul_comm (c * 2 ^ k)]
    have hstep : acceleratedStep (2 * a - 1) = (3 * c) * 2 ^ k - 1 := by
      rw [acceleratedStep, if_neg (by omega : (2 * a - 1) % 2 ≠ 0), Nat.mul_assoc]
      change (3 * (2 * a - 1) + 1) / 2 = 3 * a - 1
      omega
    rw [acceleratedOrbit_succ, hstart, hstep, ih (3 * c) (Nat.mul_pos (by decide) hc),
      Nat.pow_succ 3]
    ac_rfl

private theorem cap_image_unique {k c x : Nat} (hx : x < c * 2 ^ k)
    (heq : acceleratedOrbit k x + 1 = c * 3 ^ k) : x + 1 = c * 2 ^ k := by
  induction k generalizing x c with
  | zero => simpa using heq
  | succ k ih =>
    let a := c * 2 ^ k
    have hx' : x < 2 * a := by
      simpa only [a, Nat.pow_succ 2, ← Nat.mul_assoc, Nat.mul_comm (c * 2 ^ k)] using hx
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hx)
    rw [acceleratedOrbit_succ, Nat.pow_succ 3] at heq
    rcases Arith.mod_two_eq_zero_or_one x with he | ho
    · have hstep : acceleratedStep x < c * 2 ^ k := by
        change acceleratedStep x < a
        rw [acceleratedStep, if_pos he]
        omega
      have ht := image_lt hstep
      have hlt : acceleratedOrbit k (acceleratedStep x) < c * 3 ^ k :=
        Nat.lt_of_lt_of_le ht (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by decide) (AffineExact.oddCount_le_self _ _)))
      have hp := Nat.mul_pos hc (Nat.pow_pos (by decide : 0 < 3) : 0 < 3 ^ k)
      rw [← Nat.mul_assoc] at heq
      omega
    · have hstep : acceleratedStep x < (3 * c) * 2 ^ k := by
        rw [Nat.mul_assoc]
        change acceleratedStep x < 3 * a
        rw [acceleratedStep, if_neg (by omega : x % 2 ≠ 0)]
        omega
      have htarget : acceleratedOrbit k (acceleratedStep x) + 1 = (3 * c) * 3 ^ k := by
        rw [heq]
        ac_rfl
      have hu := ih hstep htarget
      rw [Nat.mul_assoc, acceleratedStep, if_neg (by omega : x % 2 ≠ 0)] at hu
      rw [Nat.pow_succ 2, ← Nat.mul_assoc]
      change (3 * x + 1) / 2 + 1 = 3 * a at hu
      change x + 1 = a * 2
      omega

/-- The last seed in a dyadic period has no smaller equal-time
representative at that horizon. -/
theorem leastAt_last_in_period (k c : Nat) (hc : 0 < c) :
    leastAt k (c * 2 ^ k - 1) = c * 2 ^ k - 1 := by
  let n := c * 2 ^ k - 1
  have hn : n < c * 2 ^ k := by
    dsimp [n]
    have hp := Nat.mul_pos hc (Nat.two_pow_pos k)
    omega
  have hmin : leastAt k n ≤ n := leastAt_le rfl
  have himage : acceleratedOrbit k (leastAt k n) + 1 = c * 3 ^ k := by
    rw [leastAt_meets]
    exact last_image k c hc
  have h := cap_image_unique (Nat.lt_of_le_of_lt hmin hn) himage
  have hN : n + 1 = c * 2 ^ k :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hc (Nat.two_pow_pos k)))
  exact Nat.add_right_cancel (h.trans hN.symm)

private theorem trivial_phases (k : Nat) :
    (acceleratedOrbit k 1 = 1 ∧ acceleratedOrbit k 2 = 2) ∨
      (acceleratedOrbit k 1 = 2 ∧ acceleratedOrbit k 2 = 1) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
    rw [acceleratedOrbit_succ_step, acceleratedOrbit_succ_step]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨by rw [h1, acceleratedStep_one], by rw [h2, acceleratedStep_two]⟩
    · exact Or.inl ⟨by rw [h1, acceleratedStep_two], by rw [h2, acceleratedStep_one]⟩

/-- Collatz is equivalent to every positive equal-time class
having a representative among `1` and `2`. -/
theorem collatz_iff_least_le_two :
    CollatzConjecture ↔ ∀ n, 0 < n → least n ≤ 2 := by
  constructor
  · intro h n hn
    obtain ⟨k, hk⟩ := (NeverDrops.accReachesOne_iff hn).mp (h n hn)
    rcases trivial_phases k with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Nat.le_trans (least_le ⟨k, hk.trans h1.symm⟩) (by decide : 1 ≤ 2)
    · exact least_le ⟨k, hk.trans h2.symm⟩
  · intro h n hn
    have hlo := least_positive hn
    have hhi := h n hn
    have hsmall : least n = 1 ∨ least n = 2 := by omega
    have hreach : ReachesOne (least n) := by
      rcases hsmall with h1 | h2
      · rw [h1]; exact reachesOne_one
      · rw [h2]; exact reachesOne_two
    obtain ⟨k, hk⟩ := least_related n
    apply reachesOne_of_accOrbit hn (k := k)
    rw [hk]
    exact (reachesOne_accOrbit_iff hlo k).mp hreach

/-- It is enough to find a smaller equal-time meeting partner for
every start above the two trivial phases. -/
theorem collatz_iff_synchronous_descent :
    CollatzConjecture ↔ ∀ n, 2 < n → ∃ m, m < n ∧ SameTime n m := by
  rw [collatz_iff_least_le_two]
  constructor
  · intro h n hn
    exact ⟨least n, Nat.lt_of_le_of_lt (h n (by omega)) hn, least_related n⟩
  · intro h n _
    apply Nat.le_of_not_gt
    intro hbig
    obtain ⟨m, hm, hmeet⟩ := h (least n) hbig
    have hle := least_le hmeet
    rw [least_idempotent] at hle
    omega

end Collatz.SynchronousClasses
