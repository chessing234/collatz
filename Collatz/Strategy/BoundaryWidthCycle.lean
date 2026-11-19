import Collatz.Strategy.NarrowCycle

/-! A discrepancy strip of width one period has only one boundary residue
with two possible heights. The blocks cut just before that residue have
order-preserving affine returns. -/

namespace Collatz.BoundaryWidthCycle

open Collatz.Arith Collatz.AccCycle Collatz.AffineExact Collatz.CyclicOrder

private theorem dvd_sub_of_mod_eq {d x y : Nat} (h : x % d = y % d) : d ∣ y - x := by
  have hx := Nat.div_add_mod x d
  have hy := Nat.div_add_mod y d
  refine ⟨y / d - x / d, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  omega

/-- A periodic affine recurrence with one common offset residue preserves
strict order when the possible corrections differ by less than `A * M`. -/
theorem exists_fixed_of_periodic_affine_blocks {f d : Nat → Nat} {A B M C L W : Nat}
    (hL : 0 < L) (hA : M ∣ A) (hcop : M.Coprime B)
    (hspread : W * M < A * M)
    (hperiod : ∀ i, f (i + L) = f i)
    (hstep : ∀ i, B * f (i + 1) = A * f i + (M * d i + C))
    (hoffset : ∀ i j, d i ≤ d j + W) : ∃ i, f (i + 1) = f i := by
  obtain ⟨a, ha⟩ := hA
  have hmod (i : Nat) : (B * f i) % M = C % M := by
    let j := i + (L - 1)
    have hj : j + 1 = i + L := by dsimp [j]; omega
    have he := hstep j
    rw [hj, hperiod i, ha] at he
    rw [he, show M * a * f j + (M * d j + C) = C + M * (a * f j + d j) by
      rw [Nat.mul_add]; ac_rfl, Nat.add_mul_mod_self_left]
  have horder (i j : Nat) (hij : f i < f j) : f (i + 1) < f (j + 1) := by
    have hd := dvd_sub_of_mod_eq ((hmod i).trans (hmod j).symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    have hsep := Nat.le_of_dvd (by omega : 0 < f j - f i) (hcop.dvd_of_dvd_mul_left hd)
    have hscaled := Nat.mul_le_mul_left A hsep
    rw [Nat.mul_sub_left_distrib] at hscaled
    have hoff := Nat.mul_le_mul_left M (hoffset i j)
    rw [Nat.mul_add, Nat.mul_comm M W] at hoff
    apply Nat.lt_of_mul_lt_mul_left (a := B)
    rw [hstep i, hstep j]
    have hcross := Nat.mul_le_mul_left A (Nat.le_of_lt hij)
    omega
  obtain ⟨z, ⟨i, hiz⟩, hmin⟩ := Minimum.exists_min_lt (P := fun z => ∃ i, f i = z)
    ⟨f 0, 0, rfl⟩
  let j := i + (L - 1)
  have hj : f (j + 1) = f i := by
    rw [show j + 1 = i + L by dsimp [j]; omega, hperiod i]
  have hlow (t : Nat) : f i ≤ f t := by rw [hiz]; exact hmin _ ⟨t, rfl⟩
  refine ⟨j, ?_⟩
  by_cases hlt : f i < f j
  · have he := horder i j hlt
    rw [hj] at he
    exact False.elim (Nat.not_lt_of_ge (hlow (i + 1)) he)
  · rw [hj]
    have := hlow j
    omega

/-- Two ordered times have the same discrepancy residue precisely when
their time difference times the odd count is a multiple of the period. -/
theorem phase_dvd_iff {n L i j : Nat} (hij : i ≤ j) :
    ((L : Int) ∣ walk n L j - walk n L i) ↔ L ∣ oddCount n L * (j - i) := by
  let a := oddCount n L
  let W := walk n L j - walk n L i
  have he : W = (L : Int) * ((oddCount n j : Int) - (oddCount n i : Int)) -
      (a : Int) * ((j - i : Nat) : Int) := by
    dsimp [W, a]
    unfold walk
    rw [Int.ofNat_sub hij, Int.mul_sub, Int.mul_sub]
    omega
  have hmul : (L : Int) ∣ (L : Int) * ((oddCount n j : Int) - (oddCount n i : Int)) :=
    ⟨_, rfl⟩
  have hD : ((L : Int) ∣ (a : Int) * ((j - i : Nat) : Int)) ↔ L ∣ a * (j - i) := by
    rw [← Int.natCast_mul]
    exact Int.ofNat_dvd
  change ((L : Int) ∣ W) ↔ L ∣ a * (j - i)
  rw [← hD, he]
  constructor
  · intro hh
    have hs := Int.dvd_sub hmul hh
    have ht (X Y : Int) : X - (X - Y) = Y := by omega
    rwa [ht] at hs
  · exact Int.dvd_sub hmul

private theorem eq_in_strip_of_same_phase {v w m l : Int}
    (hlo : m ≤ v) (hhi : v ≤ m + l) (hinner₁ : m < w) (hinner₂ : w < m + l)
    (hd : l ∣ v - w) : v = w := by
  rcases Int.lt_trichotomy v w with hlt | he | hgt
  · have hn : l ∣ w - v := by
      have hh := Int.dvd_neg.mpr hd
      rwa [show -(v - w) = w - v by omega] at hh
    have hh := Int.le_of_dvd (show 0 < w - v by omega) hn
    omega
  · exact he
  · have hh := Int.le_of_dvd (show 0 < v - w by omega) hd
    omega

private theorem odd_count_one (x : Nat) : oddCount x 1 = x % 2 := by
  change oddCount x (0 + 1) = x % 2
  rw [Density.oddCount_succ_last, Congruence.oddCount_zero, acceleratedOrbit_zero, Nat.zero_add]

private theorem correction_one (x : Nat) : affineC 1 x = x % 2 := by
  rcases mod_two_eq_zero_or_one x with he | ho
  · rw [affineC_even (show acceleratedOrbit 0 x % 2 = 0 from he), affineC_zero, he]
  · rw [affineC_odd (show acceleratedOrbit 0 x % 2 = 1 from ho), affineC_zero, ho]

private theorem two_corrections_close {x y : Nat} (hcount : oddCount x 2 = oddCount y 2) :
    affineC 2 x ≤ affineC 2 y + 1 := by
  change oddCount x (1 + 1) = oddCount y (1 + 1) at hcount
  rw [Density.oddCount_succ_last x 1, Density.oddCount_succ_last y 1, odd_count_one, odd_count_one] at hcount
  change affineC (1 + 1) x ≤ affineC (1 + 1) y + 1
  rcases mod_two_eq_zero_or_one (acceleratedOrbit 1 x) with hx | hx <;>
    rcases mod_two_eq_zero_or_one (acceleratedOrbit 1 y) with hy | hy
  · rw [affineC_even hx, affineC_even hy, correction_one, correction_one]
    omega
  · rw [affineC_even hx, affineC_odd hy, correction_one, correction_one]
    omega
  · rw [affineC_odd hx, affineC_even hy, correction_one, correction_one]
    omega
  · rw [affineC_odd hx, affineC_odd hy, correction_one, correction_one]
    omega

private theorem balanced_of_strict_strip {n L : Nat} (h : AccIsCycleOf n L)
    (hstrip : ∀ i j, walk n L i < walk n L j + L) : NarrowCycle.Balanced n L := by
  intro i j k _
  let a := oddCount n L
  let p := oddCount (acceleratedOrbit i n) k
  let q := oddCount (acceleratedOrbit j n) k
  apply Nat.le_of_not_gt
  intro hd
  change q + 1 < p at hd
  have hprod := Int.mul_le_mul_of_nonneg_left (show 2 ≤ (p : Int) - (q : Int) by omega)
    (show 0 ≤ (L : Int) by omega)
  have hi := walk_shift h.2 i k
  have hj := walk_shift h.2 j k
  have hlo := hstrip j (j + k)
  have hhi := hstrip (i + k) i
  have he₁ : walk (acceleratedOrbit i n) L k = (L : Int) * (p : Int) - (a : Int) * (k : Int) := by
    unfold walk
    rw [RotationLaw.oddCount_rotation_invariant h i]
  have he₂ : walk (acceleratedOrbit j n) L k = (L : Int) * (q : Int) - (a : Int) * (k : Int) := by
    unfold walk
    rw [RotationLaw.oddCount_rotation_invariant h j]
  rw [he₁] at hi
  rw [he₂] at hj
  rw [Int.mul_sub, Int.mul_comm (L : Int) 2] at hprod
  omega

private theorem phase_period_of_boundary {n L i j : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (he : walk n L i = walk n L j + L) :
    ∃ p, 2 ≤ p ∧ p < L ∧ L ∣ oddCount n L * p ∧
      ∀ t, 0 < t → t < p → ¬ L ∣ oddCount n L * t := by
  let a := oddCount n L
  let u := i % L
  let v := j % L
  have hu : u < L := Nat.mod_lt i h.1
  have hv : v < L := Nat.mod_lt j h.1
  have he' : walk n L u = walk n L v + L := by
    rw [← walk_mod h.1 h.2 i, ← walk_mod h.1 h.2 j]
    exact he
  have hL := h.1
  have hne : u ≠ v := by
    intro huv
    rw [huv] at he'
    omega
  have hex : ∃ q, 0 < q ∧ q < L ∧ L ∣ a * q := by
    rcases Nat.lt_or_gt_of_ne hne with huv | hvu
    · refine ⟨v - u, by omega, by omega, (phase_dvd_iff (Nat.le_of_lt huv)).mp ?_⟩
      rw [show walk n L v - walk n L u = -(L : Int) by omega]
      exact Int.dvd_neg.mpr (Int.dvd_refl _)
    · refine ⟨u - v, by omega, by omega, (phase_dvd_iff (Nat.le_of_lt hvu)).mp ?_⟩
      rw [show walk n L u - walk n L v = (L : Int) by omega]
      exact Int.dvd_refl _
  obtain ⟨q, hq, hqL, hqd⟩ := hex
  obtain ⟨p, ⟨hp, hpd⟩, hleast⟩ := Minimum.exists_min_lt
    (P := fun t => 0 < t ∧ L ∣ a * t) ⟨q, hq, hqd⟩
  have hple := hleast q ⟨hq, hqd⟩
  have hp2 : 2 ≤ p := by
    by_cases h1 : p = 1
    · rw [h1, Nat.mul_one] at hpd
      have ha := accCycle_bounds hn h
      change 0 < a ∧ a < L ∧ _ at ha
      have hbad := Nat.le_of_dvd ha.1 hpd
      omega
    · omega
  exact ⟨p, hp2, by omega, hpd, fun t ht htp hd => Nat.not_le_of_gt htp (hleast t ⟨ht, hd⟩)⟩

private theorem interior_at_reference {n L j R p k : Nat} (h : AccIsCycleOf n L)
    (hphase : R + 1 = j + L) (hmin : ∀ t, 0 < t → t < p → ¬ L ∣ oddCount n L * t)
    (hp : 2 ≤ p) (hk : k ≤ p) (hk1 : k ≠ 1)
    (hlo : walk n L j ≤ walk n L (R + k)) (hhi : walk n L (R + k) ≤ walk n L j + L) :
    walk n L j < walk n L (R + k) ∧ walk n L (R + k) < walk n L j + L := by
  have he : walk n L (R + 1) = walk n L j := by rw [hphase, walk_period h.2]
  have hnot : ¬ ((L : Int) ∣ walk n L (R + k) - walk n L (R + 1)) := by
    intro hd
    by_cases hk0 : k = 0
    · have hrev := Int.dvd_neg.mpr hd
      rw [show -(walk n L (R + k) - walk n L (R + 1)) =
          walk n L (R + 1) - walk n L (R + k) by omega] at hrev
      have hnat := (phase_dvd_iff (show R + k ≤ R + 1 by omega)).mp hrev
      rw [show R + 1 - (R + k) = 1 by omega] at hnat
      exact hmin 1 (by omega) (by omega) hnat
    · have hnat := (phase_dvd_iff (show R + 1 ≤ R + k by omega)).mp hd
      rw [show R + k - (R + 1) = k - 1 by omega] at hnat
      exact hmin (k - 1) (by omega) (by omega) hnat
  constructor
  · have hne : walk n L j ≠ walk n L (R + k) := by
      intro heq
      apply hnot
      rw [← heq, he, Int.sub_self]
      exact Int.dvd_zero _
    omega
  · have hne : walk n L (R + k) ≠ walk n L j + L := by
      intro heq
      apply hnot
      rw [heq, he, show walk n L j + L - walk n L j = (L : Int) by omega]
      exact Int.dvd_refl _
    omega

private theorem odd_count_eq_of_walk_agreement {n L i j k : Nat} (h : AccIsCycleOf n L)
    (hstart : walk n L i = walk n L j) (hend : walk n L (i + k) = walk n L (j + k)) :
    oddCount (acceleratedOrbit i n) k = oddCount (acceleratedOrbit j n) k := by
  have hi := walk_shift h.2 i k
  have hj := walk_shift h.2 j k
  rw [hstart, hend] at hi
  have he := hi.trans hj.symm
  unfold walk at he
  rw [RotationLaw.oddCount_rotation_invariant h i, RotationLaw.oddCount_rotation_invariant h j] at he
  have hL := h.1
  exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (L : Int) ≠ 0 by omega) (by omega))

private theorem boundary_strip_impossible {n L i j : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hstrip : ∀ s t, walk n L s ≤ walk n L t + L)
    (he : walk n L i = walk n L j + L) : False := by
  obtain ⟨p, hp2, hpL, hpd, hshort⟩ := phase_period_of_boundary hn h he
  let R := j + (L - 1)
  let pos := fun u => R + p * u
  let base := acceleratedOrbit R n
  let f := fun u => acceleratedOrbit (pos u) n
  have hL := h.1
  have hphase : R + 1 = j + L := by dsimp [R]; omega
  have hlo (t : Nat) : walk n L j ≤ walk n L t := by
    have ht := hstrip i t
    rw [he] at ht
    omega
  have hhi (t : Nat) : walk n L t ≤ walk n L j + L := hstrip t j
  have hwalk (u k : Nat) (hk : k ≤ p) (hk1 : k ≠ 1) :
      walk n L (pos u + k) = walk n L (R + k) := by
    obtain ⟨hlo', hhi'⟩ := interior_at_reference h hphase hshort hp2 hk hk1 (hlo _) (hhi _)
    apply eq_in_strip_of_same_phase (hlo _) (hhi _) hlo' hhi'
    apply (phase_dvd_iff (show R + k ≤ pos u + k by dsimp [pos]; omega)).mpr
    rw [show pos u + k - (R + k) = p * u by dsimp [pos]; omega, ← Nat.mul_assoc]
    exact Nat.dvd_trans hpd (Nat.dvd_mul_right _ _)
  have hstart (u : Nat) : walk n L (pos u) = walk n L R := by
    simpa only [Nat.add_zero] using hwalk u 0 (Nat.zero_le p) (by decide)
  have hcount (u k : Nat) (hk : k ≤ p) (hk1 : k ≠ 1) : oddCount (f u) k = oddCount base k :=
    odd_count_eq_of_walk_agreement h (hstart u) (hwalk u k hk hk1)
  have hpar (u s : Nat) (hs2 : 2 ≤ s) (hs : s < p) :
      acceleratedOrbit (pos u + s) n % 2 = acceleratedOrbit (R + s) n % 2 := by
    have hu := NarrowCycle.walk_step n L (pos u + s)
    have hr := NarrowCycle.walk_step n L (R + s)
    rw [Nat.add_assoc, hwalk u s (by omega) (by omega), hwalk u (s + 1) (by omega) (by omega)] at hu
    rw [Nat.add_assoc] at hr
    exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (L : Int) ≠ 0 by omega) (by omega))
  let k := p - 2
  let v := acceleratedOrbit 2 base
  let q := oddCount v k
  let M := 3 ^ q
  let A := 3 ^ oddCount base p
  let B := 2 ^ p
  let C := 2 ^ 2 * affineC k v
  have htail (u : Nat) : oddCount (acceleratedOrbit 2 (f u)) k = q ∧
      affineC k (acceleratedOrbit 2 (f u)) = affineC k v := by
    apply NarrowCycle.same_parities_same_accumulator k
    intro t ht
    change acceleratedOrbit t (acceleratedOrbit 2 (acceleratedOrbit (pos u) n)) % 2 =
      acceleratedOrbit t (acceleratedOrbit 2 (acceleratedOrbit R n)) % 2
    rw [acceleratedOrbit_add t 2, acceleratedOrbit_add t 2,
      acceleratedOrbit_add (t + 2) (pos u), acceleratedOrbit_add (t + 2) R,
      show t + 2 + pos u = pos u + (2 + t) by ac_rfl,
      show t + 2 + R = R + (2 + t) by ac_rfl]
    exact hpar u (2 + t) (by omega) (by dsimp [k] at ht; omega)
  have hA : M ∣ A := by
    have hs := Discrepancy.oddCount_split (n := base) hp2
    change oddCount base p = oddCount base 2 + q at hs
    exact Nat.pow_dvd_pow 3 (by omega)
  have hb : 0 < oddCount base p := by
    have hw := walk_shift h.2 R p
    have hsame : walk n L (R + p) = walk n L R := by
      simpa only [pos, Nat.mul_one] using hstart 1
    rw [hsame, Int.sub_self] at hw
    unfold walk at hw
    rw [RotationLaw.oddCount_rotation_invariant h R] at hw
    have hpos : 0 < (oddCount n L : Int) * (p : Int) :=
      Int.mul_pos (Int.ofNat_lt.mpr (oddCount_pos_of_accCycle hn h)) (by omega)
    by_cases hz : oddCount base p = 0
    · change (L : Int) * (oddCount base p : Int) - _ = 0 at hw
      rw [hz] at hw
      simp at hw
      omega
    · omega
  have hspread : 1 * M < A * M := by
    have ha := three_le_three_pow hb
    have ha' : 1 < A := by dsimp [A]; omega
    exact Nat.mul_lt_mul_of_pos_right ha' (three_pow_pos q)
  have hcop : M.Coprime B := ((by decide : Nat.Coprime 3 2).pow_left q).pow_right p
  have hperiod (u : Nat) : f (u + L) = f u := by
    change acceleratedOrbit (pos (u + L)) n = acceleratedOrbit (pos u) n
    have ht : pos (u + L) = pos u + L * p := by
      dsimp [pos]
      rw [Nat.mul_add, Nat.mul_comm p L, ← Nat.add_assoc]
    rw [ht, ← acceleratedOrbit_add, accOrbit_mul_period h.2]
  have hnext (u : Nat) : acceleratedOrbit p (f u) = f (u + 1) := by
    change acceleratedOrbit p (acceleratedOrbit (pos u) n) = acceleratedOrbit (pos (u + 1)) n
    rw [acceleratedOrbit_add, show p + pos u = pos (u + 1) by dsimp [pos]; rw [Nat.mul_succ]; omega]
  have hstep (u : Nat) : B * f (u + 1) = A * f u + (M * affineC 2 (f u) + C) := by
    have hC := AccumulatorArith.affineC_add (f u) 2 k
    rw [show 2 + k = p by dsimp [k]; omega, (htail u).1, (htail u).2] at hC
    have hx := affine_exact (f u) p
    rw [hnext u, hcount u p (Nat.le_refl _) (by omega), hC] at hx
    exact hx
  have hoff (u v : Nat) : affineC 2 (f u) ≤ affineC 2 (f v) + 1 :=
    two_corrections_close ((hcount u 2 hp2 (by decide)).trans (hcount v 2 hp2 (by decide)).symm)
  obtain ⟨u, hfix⟩ := exists_fixed_of_periodic_affine_blocks hL hA hcop hspread hperiod hstep hoff
  have heq : acceleratedOrbit (pos u) (acceleratedOrbit p n) = acceleratedOrbit (pos u) n := by
    calc
      _ = acceleratedOrbit p (f u) := by
        change acceleratedOrbit (pos u) (acceleratedOrbit p n) = acceleratedOrbit p (acceleratedOrbit (pos u) n)
        rw [acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm (pos u) p]
      _ = f (u + 1) := hnext u
      _ = _ := hfix
  exact hleast p (by omega) hpL (CycleCollisionBudget.periodic_eq_of_synchronized
    ⟨L, accIsCycleOf_orbit h p⟩ ⟨L, h⟩ heq)

/-- A least positive cycle confined to a discrepancy strip of width at
most one period is trivial, including the boundary of the balanced case. -/
theorem width_at_most_period_forces_trivial {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hwidth : ∀ i j, walk n L i ≤ walk n L j + L) : L = 2 ∧ (n = 1 ∨ n = 2) := by
  by_cases he : ∃ i j, walk n L i = walk n L j + L
  · obtain ⟨i, j, hij⟩ := he
    exact False.elim (boundary_strip_impossible hn h hleast hwidth hij)
  · apply NarrowCycle.balanced_least_cycle_trivial hn h hleast
    apply balanced_of_strict_strip h
    intro i j
    have hle := hwidth i j
    have hne : walk n L i ≠ walk n L j + L := fun hij => he ⟨i, j, hij⟩
    omega

end Collatz.BoundaryWidthCycle
