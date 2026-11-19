import Collatz.Strategy.AlignedOrbitOrder
import Collatz.Strategy.CycleArcSplit

/-! Repeated discrepancy phases synchronize odd counts. The normalized
order of two such rotations cannot stay strict around a cycle. -/

namespace Collatz.PhaseOrderCycle

open Collatz.AccCycle Collatz.CyclicOrder

private theorem exists_proper_phase_offset {a L : Nat} (hL : 0 < L) (hg : 1 < a.gcd L) :
    ∃ p, 0 < p ∧ p < L ∧ L ∣ a * p := by
  let g := a.gcd L
  obtain ⟨p, hp⟩ := Nat.gcd_dvd_right a L
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left a L
  change L = g * p at hp
  change a = g * b at hb
  have hp₀ : 0 < p := by
    by_cases he : p = 0
    · rw [he, Nat.mul_zero] at hp
      omega
    · omega
  have hg' : 2 ≤ g := hg
  have hpL := Nat.mul_le_mul_right p hg'
  rw [← hp, Nat.two_mul] at hpL
  refine ⟨p, hp₀, by omega, b, ?_⟩
  rw [hp, hb]
  ac_rfl

private theorem oddCount_mul_period {n L : Nat} (h : AccIsCycleOf n L) (q : Nat) :
    oddCount n (L * q) = q * oddCount n L := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, AccumulatorArith.oddCount_add, accOrbit_mul_period h.2, ih, Nat.succ_mul]

private theorem higher_density_of_scaled_order {x L p : Nat} (h : AccIsCycleOf x L)
    (hxy : x < acceleratedOrbit p x)
    (hle : ∀ t, 3 ^ oddCount (acceleratedOrbit p x) t * acceleratedOrbit t x ≤
      3 ^ oddCount x t * acceleratedOrbit t (acceleratedOrbit p x)) :
    p * oddCount x L < L * oddCount x p := by
  have hfinal := AlignedOrbitOrder.iterated_offset_order hxy h.1 (fun j _ => hle (p * j))
  rw [Nat.mul_comm p L, accOrbit_mul_period h.2, oddCount_mul_period h] at hfinal
  have hpow := Nat.lt_of_mul_lt_mul_right hfinal
  rw [Nat.mul_comm (oddCount x p) L] at hpow
  exact (Nat.pow_lt_pow_iff_right (by decide : (1 : Nat) < 3)).mp hpow

/-- If a cyclic offset increases the starting value and the two prefix
odd counts always stay within one, its odd density exceeds the cycle mean. -/
theorem increasing_offset_forces_higher_odd_density {x L p : Nat} (h : AccIsCycleOf x L)
    (hxy : x < acceleratedOrbit p x)
    (hnear : ∀ t, oddCount x t ≤ oddCount (acceleratedOrbit p x) t + 1 ∧
      oddCount (acceleratedOrbit p x) t ≤ oddCount x t + 1) :
    p * oddCount x L < L * oddCount x p :=
  higher_density_of_scaled_order h hxy (fun t =>
    AlignedOrbitOrder.scaled_orbit_le (k := t) (Nat.le_of_lt hxy) (fun j _ => hnear j))

private theorem cycle_scaled_order_of_one_side {x y L : Nat}
    (hx : AccIsCycleOf x L) (hy : AccIsCycleOf y L) (ha : oddCount x L = oddCount y L)
    (hxy : x < y)
    (hside : (∀ j, oddCount y j ≤ oddCount x j + 1) ∨
      (∀ j, oddCount x j ≤ oddCount y j + 1)) (t : Nat) :
    3 ^ oddCount y t * acceleratedOrbit t x ≤ 3 ^ oddCount x t * acceleratedOrbit t y := by
  rcases hside with hupper | hlower
  · exact AlignedOrbitOrder.scaled_orbit_le_from (s := 0) (Nat.zero_le _)
      (by simpa using Nat.le_of_lt hxy) (fun j _ _ => hupper j)
  apply Nat.le_of_not_gt
  intro hrev
  let q := t + 1
  have ht : t ≤ L * q := by
    have h := Nat.mul_le_mul_right q hx.1
    rw [Nat.one_mul] at h
    exact Nat.le_trans (by dsimp [q]; omega) h
  have hh := AlignedOrbitOrder.scaled_orbit_le_from ht (Nat.le_of_lt hrev) (fun j _ _ => hlower j)
  rw [accOrbit_mul_period hx.2, accOrbit_mul_period hy.2, oddCount_mul_period hx,
    oddCount_mul_period hy, ha] at hh
  have hbad := Nat.le_of_mul_le_mul_left hh (Nat.pow_pos (by decide))
  omega

private theorem count_side_of_window_spread {x p : Nat}
    (hw : ∀ i j, oddCount (acceleratedOrbit i x) p ≤ oddCount (acceleratedOrbit j x) p + 3) :
    (∀ i, oddCount (acceleratedOrbit p x) i ≤ oddCount x i + 1) ∨
      (∀ i, oddCount x i ≤ oddCount (acceleratedOrbit p x) i + 1) := by
  let y := acceleratedOrbit p x
  let B := fun i => oddCount (acceleratedOrbit i x) p
  have hdelta (i : Nat) : oddCount y i + B 0 = oddCount x i + B i := by
    have h₁ := AccumulatorArith.oddCount_add x p i
    have h₂ := AccumulatorArith.oddCount_add x i p
    rw [Nat.add_comm p i] at h₁
    dsimp only [B, y, acceleratedOrbit_zero]
    omega
  by_cases h₁ : ∀ i, oddCount y i ≤ oddCount x i + 1
  · exact Or.inl h₁
  right
  intro j
  change oddCount x j ≤ oddCount y j + 1
  apply Nat.le_of_not_gt
  intro hj
  apply h₁
  intro i
  have h₃ := hdelta i
  have h₄ := hdelta j
  have h₅ : B i ≤ B j + 3 := hw i j
  omega

/-- A length whose cyclic odd counts span at most three units can increase
a point only when the starting window has above-average odd density. -/
theorem increasing_offset_forces_higher_odd_density_of_window_spread {x L p : Nat}
    (h : AccIsCycleOf x L) (hxy : x < acceleratedOrbit p x)
    (hw : ∀ i j, oddCount (acceleratedOrbit i x) p ≤ oddCount (acceleratedOrbit j x) p + 3) :
    p * oddCount x L < L * oddCount x p := by
  exact higher_density_of_scaled_order h hxy
    (cycle_scaled_order_of_one_side h (accIsCycleOf_orbit h p)
      (AccumulatorCap.oddCount_shift h.2 p).symm hxy (count_side_of_window_spread hw))

private theorem walk_diff_eq_window {x L : Nat} (h : AccIsCycleOf x L) (i p : Nat) :
    walk x L (i + p) - walk x L i =
      (L : Int) * (oddCount (acceleratedOrbit i x) p : Int) - (oddCount x L : Int) * p := by
  rw [← walk_shift h.2 i p]
  unfold walk
  rw [AccumulatorCap.oddCount_shift h.2 i]

private theorem window_spread_of_width_lt_twice {x L p : Nat} (h : AccIsCycleOf x L)
    (hw : ∀ i j, walk x L i < walk x L j + 2 * (L : Int)) :
    ∀ i j, oddCount (acceleratedOrbit i x) p ≤ oddCount (acceleratedOrbit j x) p + 3 := by
  intro i j
  apply Nat.le_of_not_gt
  intro hb
  have hL := h.1
  have hdiff : (4 : Int) ≤ (oddCount (acceleratedOrbit i x) p : Int) -
      (oddCount (acceleratedOrbit j x) p : Int) := by omega
  have hprod := Int.mul_le_mul_of_nonneg_left hdiff (by omega : 0 ≤ (L : Int))
  rw [Int.mul_sub, Int.mul_comm (L : Int) 4] at hprod
  have h₁ := walk_diff_eq_window h i p
  have h₂ := walk_diff_eq_window h j p
  have hu := hw (i + p) i
  have hl := hw j (j + p)
  omega

private theorem walk_pos_of_increasing_offset {x L p : Nat} (h : AccIsCycleOf x L)
    (hw : ∀ i j, walk x L i < walk x L j + 2 * (L : Int)) (hxy : x < acceleratedOrbit p x) :
    0 < walk x L p := by
  have hh := increasing_offset_forces_higher_odd_density_of_window_spread h hxy
    (window_spread_of_width_lt_twice h hw)
  have hh' : (p : Int) * oddCount x L < (L : Int) * oddCount x p := by exact_mod_cast hh
  unfold walk
  rw [Int.mul_comm (oddCount x L : Int)]
  omega

private theorem walk_zero_of_return {x L p : Nat} (h : AccIsCycleOf x L)
    (hp : acceleratedOrbit p x = x) : walk x L p = 0 := by
  by_cases hz : p = 0
  · simp [hz]
  have hcycle : AccIsCycleOf x p := ⟨by omega, hp⟩
  have ha := oddCount_mul_period h p
  have hb := oddCount_mul_period hcycle L
  rw [Nat.mul_comm p L] at hb
  have hc := ha.symm.trans hb
  have hz : (p : Int) * oddCount x L = (L : Int) * oddCount x p := by exact_mod_cast hc
  unfold walk
  rw [Int.mul_comm (oddCount x L : Int), hz, Int.sub_self]

/-- Below twice the period, discrepancy height orders the actual orbit
values, including when the period and odd count are coprime. -/
theorem orbit_lt_iff_walk_lt_of_width_lt_twice {n L : Nat} (h : AccIsCycleOf n L)
    (hw : ∀ i j, walk n L i < walk n L j + 2 * (L : Int)) (i j : Nat) :
    acceleratedOrbit i n < acceleratedOrbit j n ↔ walk n L i < walk n L j := by
  have hoffset (i j : Nat) : ∃ p,
      acceleratedOrbit p (acceleratedOrbit i n) = acceleratedOrbit j n ∧
      walk (acceleratedOrbit i n) L p = walk n L j - walk n L i := by
    let p := j + L * i - i
    have hi := Nat.mul_le_mul_right i h.1
    rw [Nat.one_mul] at hi
    have hp : i + p = j + L * i := by dsimp [p]; omega
    refine ⟨p, ?_, ?_⟩
    · rw [acceleratedOrbit_add, Nat.add_comm p i, hp, ← acceleratedOrbit_add, accOrbit_mul_period h.2]
    · rw [walk_shift h.2, hp, walk_mod h.1 h.2 (j + L * i), Nat.add_mul_mod_self_left, ← walk_mod h.1 h.2]
  have hdir (i j : Nat) (hlt : acceleratedOrbit i n < acceleratedOrbit j n) :
      walk n L i < walk n L j := by
    obtain ⟨p, hp, hwalk⟩ := hoffset i j
    have hh := walk_pos_of_increasing_offset (accIsCycleOf_orbit h i) (p := p)
      (fun s t => by rw [walk_shift h.2, walk_shift h.2]; have := hw (i + s) (i + t); omega)
      (by rwa [hp])
    rw [hwalk] at hh
    omega
  refine ⟨hdir i j, fun hij => ?_⟩
  rcases Nat.lt_trichotomy (acceleratedOrbit i n) (acceleratedOrbit j n) with hlt | he | hgt
  · exact hlt
  · obtain ⟨p, hp, hwalk⟩ := hoffset i j
    have hh := walk_zero_of_return (accIsCycleOf_orbit h i) (hp.trans he.symm)
    rw [hwalk] at hh
    omega
  · have := hdir j i hgt
    omega

private theorem scaled_ne_of_count_lt {x y k : Nat} (h : oddCount x k < oddCount y k) :
    3 ^ oddCount y k * acceleratedOrbit k x ≠ 3 ^ oddCount x k * acceleratedOrbit k y := by
  intro he
  let d := oddCount y k - oddCount x k - 1
  have hc : oddCount y k = oddCount x k + (d + 1) := by dsimp [d]; omega
  rw [hc, Nat.pow_add, Nat.pow_succ, Nat.mul_comm (3 ^ d) 3,
    Nat.mul_assoc, Nat.mul_assoc] at he
  have he' := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) he
  exact AccumulatorArith.three_not_dvd_orbit_of_odd_step (by omega : 0 < oddCount y k) ⟨_, he'.symm⟩

private theorem cycle_scaled_order_strict {x y L : Nat}
    (hx : AccIsCycleOf x L) (hy : AccIsCycleOf y L) (ha : oddCount x L = oddCount y L)
    (hxy : x < y) (hside : (∀ j, oddCount y j ≤ oddCount x j + 1) ∨
      (∀ j, oddCount x j ≤ oddCount y j + 1)) (t : Nat) :
    3 ^ oddCount y t * acceleratedOrbit t x < 3 ^ oddCount x t * acceleratedOrbit t y := by
  apply Nat.lt_of_le_of_ne (cycle_scaled_order_of_one_side hx hy ha hxy hside t)
  intro he
  rcases Nat.lt_trichotomy (oddCount x t) (oddCount y t) with h | h | h
  · exact scaled_ne_of_count_lt h he
  · rw [h] at he
    have he' := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) he
    exact Nat.ne_of_lt hxy (CycleCollisionBudget.periodic_eq_of_synchronized ⟨L, hx⟩ ⟨L, hy⟩ he')
  · exact scaled_ne_of_count_lt h he.symm

private theorem order_from_centered_window {n L p s : Nat} (h : AccIsCycleOf n L)
    (hw : ∀ i j, walk n L i < walk n L j + 2 * (L : Int)) (hs : s < L) :
    let b := oddCount (acceleratedOrbit s n) p
    (walk n L s < walk n L (s + p) →
      3 ^ oddCount n p * n < 3 ^ b * acceleratedOrbit p n) ∧
    (walk n L (s + p) < walk n L s →
      3 ^ b * acceleratedOrbit p n < 3 ^ oddCount n p * n) := by
  let x := acceleratedOrbit s n
  let y := acceleratedOrbit p x
  let b := oddCount x p
  let t := L - s
  have hs' : t + s = L := by dsimp [t]; omega
  have hX : AccIsCycleOf x L := accIsCycleOf_orbit h s
  have hY : AccIsCycleOf y L := accIsCycleOf_orbit hX p
  have ha : oddCount x L = oddCount y L := (AccumulatorCap.oddCount_shift hX.2 p).symm
  have hx (i j : Nat) : walk x L i < walk x L j + 2 * (L : Int) := by
    unfold x
    rw [walk_shift h.2, walk_shift h.2]
    have := hw (s + i) (s + j)
    omega
  have hside := count_side_of_window_spread (window_spread_of_width_lt_twice (p := p) hX hx)
  have hbackX : acceleratedOrbit t x = n := by
    unfold x
    rw [acceleratedOrbit_add, hs', h.2]
  have hbackY : acceleratedOrbit t y = acceleratedOrbit p n := by
    unfold y
    rw [acceleratedOrbit_add, Nat.add_comm t p, ← acceleratedOrbit_add, hbackX]
  have hcnt : b + oddCount y t = oddCount x t + oddCount n p := by
    have h₁ := AccumulatorArith.oddCount_add x p t
    have h₂ := AccumulatorArith.oddCount_add x t p
    rw [Nat.add_comm p t] at h₁
    rw [hbackX] at h₂
    dsimp only [b, y]
    omega
  have hscale₁ : 3 ^ b * (3 ^ oddCount y t * n) = 3 ^ oddCount x t * (3 ^ oddCount n p * n) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, hcnt, Nat.pow_add, Nat.mul_assoc]
  have hscale₂ : 3 ^ b * (3 ^ oddCount x t * acceleratedOrbit p n) =
      3 ^ oddCount x t * (3 ^ b * acceleratedOrbit p n) := Nat.mul_left_comm _ _ _
  have horb : y = acceleratedOrbit (s + p) n := by
    unfold y x
    rw [acceleratedOrbit_add, Nat.add_comm p s]
  have hord := orbit_lt_iff_walk_lt_of_width_lt_twice h hw
  constructor
  · intro hh
    have hxy : x < y := by rw [horb]; exact (hord s (s + p)).mpr hh
    have hc := cycle_scaled_order_strict hX hY ha hxy hside t
    rw [hbackX, hbackY] at hc
    have hlt := Nat.mul_lt_mul_of_pos_left hc (Nat.pow_pos (n := b) (by decide : 0 < 3))
    rw [hscale₁, hscale₂] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  · intro hh
    have hyx : y < x := by rw [horb]; exact (hord (s + p) s).mpr hh
    have hc := cycle_scaled_order_strict hY hX ha.symm hyx (hside.elim Or.inr Or.inl) t
    rw [hbackX, hbackY] at hc
    have hlt := Nat.mul_lt_mul_of_pos_left hc (Nat.pow_pos (n := b) (by decide : 0 < 3))
    rw [hscale₁, hscale₂] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt

/-- When a cyclic window has nonintegral mean, the two neighboring
integer counts bound its endpoint ratio between successive powers of three. -/
theorem endpoint_ratio_between_phase_powers {n L p : Nat} (h : AccIsCycleOf n L)
    (hw : ∀ i j, walk n L i < walk n L j + 2 * (L : Int))
    (hr : p * oddCount n L % L ≠ 0) :
    let b := p * oddCount n L / L
    3 ^ b * acceleratedOrbit p n < 3 ^ oddCount n p * n ∧
      3 ^ oddCount n p * n < 3 ^ (b + 1) * acceleratedOrbit p n := by
  let a := oddCount n L
  let b := p * a / L
  have hL := h.1
  have hsplit : L * b + p * a % L = p * a := Nat.div_add_mod _ _
  have hrem := Nat.mod_lt (p * a) h.1
  change p * a % L ≠ 0 at hr
  have hlo : L * b < p * a := by omega
  have hhi : p * a < L * (b + 1) := Nat.lt_mul_div_succ _ h.1
  obtain ⟨s, hs, hc⟩ := CycleArcSplit.exists_window_count (k := p) (b := b) h
    (by change L * b < p * a + L; omega) (by change p * a < L * b + L; rwa [← Nat.mul_succ])
  obtain ⟨t, ht, hd⟩ := CycleArcSplit.exists_window_count (k := p) (b := b + 1) h
    (by change L * (b + 1) < p * a + L; rw [Nat.mul_succ]; omega)
    (by change p * a < L * (b + 1) + L; omega)
  have h₁ := walk_diff_eq_window h s p
  have h₂ := walk_diff_eq_window h t p
  rw [hc] at h₁
  rw [hd] at h₂
  have hloZ : (L : Int) * (b : Int) < (p : Int) * a := by exact_mod_cast hlo
  have hhiZ : (p : Int) * a < (L : Int) * ((b + 1 : Nat) : Int) := by exact_mod_cast hhi
  have hl := (order_from_centered_window (p := p) h hw hs).2 (by
    rw [Int.mul_comm (oddCount n L : Int)] at h₁
    change (L : Int) * (b : Int) < (p : Int) * oddCount n L at hloZ
    omega)
  have hu := (order_from_centered_window (p := p) h hw ht).1 (by
    rw [Int.mul_comm (oddCount n L : Int)] at h₂
    change (p : Int) * oddCount n L < (L : Int) * ((b + 1 : Nat) : Int) at hhiZ
    omega)
  rw [hc] at hl
  rw [hd] at hu
  exact ⟨hl, hu⟩

private theorem close_prefix_counts_of_width {x L p r : Nat} (h : AccIsCycleOf x L)
    (hlo : -(r : Int) ≤ walk x L p) (hhi : walk x L p ≤ r)
    (hw : ∀ i j, walk x L i + (r : Int) < walk x L j + 2 * (L : Int)) :
    ∀ t, oddCount x t ≤ oddCount (acceleratedOrbit p x) t + 1 ∧
      oddCount (acceleratedOrbit p x) t ≤ oddCount x t + 1 := by
  let y := acceleratedOrbit p x
  have hL : 0 < (L : Int) := by have := h.1; omega
  intro t
  have hshift := walk_shift h.2 p t
  change walk y L t = walk x L (p + t) - walk x L p at hshift
  have hdelta : walk x L (p + t) - walk x L p - walk x L t =
      (L : Int) * ((oddCount y t : Int) - (oddCount x t : Int)) := by
    rw [← hshift]
    unfold walk
    rw [AccumulatorCap.oddCount_shift h.2 p, Int.mul_sub]
    omega
  have hu := hw (p + t) t
  have hl := hw t (p + t)
  change oddCount x t ≤ oddCount y t + 1 ∧ oddCount y t ≤ oddCount x t + 1
  constructor
  · apply Nat.le_of_not_gt
    intro hbad
    have hh := Int.mul_le_mul_of_nonneg_left
      (show (oddCount y t : Int) - (oddCount x t : Int) ≤ -2 by omega) (by omega : 0 ≤ (L : Int))
    rw [Int.mul_neg, Int.mul_comm (L : Int) 2] at hh
    omega
  · apply Nat.le_of_not_gt
    intro hbad
    have hh := Int.mul_le_mul_of_nonneg_left
      (show (2 : Int) ≤ (oddCount y t : Int) - (oddCount x t : Int) by omega) (by omega : 0 ≤ (L : Int))
    rw [Int.mul_comm (L : Int) 2] at hh
    omega

/-- A sufficiently centered offset in a strip narrower than twice the
period can increase the orbit only if its odd count exceeds the mean. -/
theorem increasing_offset_forces_higher_odd_density_of_width {x L p r : Nat} (h : AccIsCycleOf x L)
    (hxy : x < acceleratedOrbit p x)
    (hlo : -(r : Int) ≤ walk x L p) (hhi : walk x L p ≤ r)
    (hw : ∀ i j, walk x L i + (r : Int) < walk x L j + 2 * (L : Int)) :
    p * oddCount x L < L * oddCount x p :=
  increasing_offset_forces_higher_odd_density h hxy (close_prefix_counts_of_width h hlo hhi hw)

private theorem no_increasing_phase_offset {x L p b r : Nat} (h : AccIsCycleOf x L)
    (hphase : L * b = p * oddCount x L) (hb : oddCount x p = b)
    (hxy : x < acceleratedOrbit p x)
    (hra : r ≤ oddCount x L) (hrL : oddCount x L + r ≤ L)
    (hw : ∀ i j, walk x L i < walk x L j + 2 * (L : Int) + r) : False := by
  let y := acceleratedOrbit p x
  let D := fun t => AlignedOrbitOrder.countDifference x y t
  have hL : 0 < (L : Int) := by have := h.1; omega
  have hzero : walk x L p = 0 := by
    unfold walk
    rw [hb, Int.mul_comm (oddCount x L : Int)]
    have he : (L : Int) * (b : Int) = (p : Int) * (oddCount x L : Int) := by exact_mod_cast hphase
    omega
  have hdelta (t : Nat) : walk x L (p + t) - walk x L t = (L : Int) * D t := by
    have hshift := walk_shift h.2 p t
    rw [hzero, Int.sub_zero] at hshift
    rw [← hshift]
    unfold D y AlignedOrbitOrder.countDifference walk
    rw [AccumulatorCap.oddCount_shift h.2 p, Int.mul_sub]
    omega
  have hnear (t : Nat) : -2 ≤ D t ∧ D t ≤ 2 := by
    have hd := hdelta t
    have hu := hw (p + t) t
    have hl := hw t (p + t)
    constructor
    · apply Int.le_of_not_gt
      intro hbad
      have hh := Int.mul_le_mul_of_nonneg_left (show D t ≤ -3 by omega) (by omega : 0 ≤ (L : Int))
      rw [Int.mul_neg, Int.mul_comm (L : Int) 3] at hh
      omega
    · apply Int.le_of_not_gt
      intro hbad
      have hh := Int.mul_le_mul_of_nonneg_left (show (3 : Int) ≤ D t by omega) (by omega : 0 ≤ (L : Int))
      rw [Int.mul_comm (L : Int) 3] at hh
      omega
  have hextreme (t : Nat) (hd : D t = -2 ∨ D t = 2) :
      ∃ u v, walk x L v = walk x L u + 2 * (L : Int) ∧ (L : Int) ∣ walk x L u - walk x L t := by
    have ht := hdelta t
    rcases hd with hd | hd
    · rw [hd, Int.mul_neg, Int.mul_comm (L : Int) 2] at ht
      exact ⟨p + t, t, by omega, -2, by rw [ht, Int.mul_neg, Int.mul_comm (L : Int) 2]⟩
    · rw [hd, Int.mul_comm (L : Int) 2] at ht
      exact ⟨t, p + t, by omega, by simp⟩
  have hsep (t : Nat) (ht : D t = -2 ∨ D t = 2) : -1 ≤ D (t + 1) ∧ D (t + 1) ≤ 1 := by
    have hb' := hnear (t + 1)
    by_cases ht' : D (t + 1) = -2 ∨ D (t + 1) = 2
    · obtain ⟨u, v, huv, hu⟩ := hextreme t ht
      obtain ⟨s, z, hsz, hs⟩ := hextreme (t + 1) ht'
      have h₁ := hw v s
      have h₂ := hw z u
      rw [huv] at h₁
      rw [hsz] at h₂
      have hmod : (L : Int) ∣ walk x L (t + 1) - walk x L t + oddCount x L := by
        refine ⟨(oddCount x (t + 1) : Int) - (oddCount x t : Int), ?_⟩
        unfold walk
        rw [Int.natCast_add, Int.mul_sub, Int.mul_add]
        simp only [Int.natCast_one, Int.mul_one]
        omega
      have hh := Int.dvd_add (Int.dvd_sub hs hu) hmod
      rw [show walk x L s - walk x L (t + 1) - (walk x L u - walk x L t) +
        (walk x L (t + 1) - walk x L t + oddCount x L) =
        walk x L s - walk x L u + oddCount x L by omega] at hh
      have hle := Int.le_of_dvd (by omega) hh
      omega
    · omega
  have hlt := higher_density_of_scaled_order h hxy (fun t =>
    AlignedOrbitOrder.scaled_orbit_le_of_isolated_double (Nat.le_of_lt hxy)
      (fun j _ => hnear j) (fun j _ => hsep j))
  rw [hb, hphase] at hlt
  exact Nat.lt_irrefl _ hlt

private theorem narrow_phase_offset_impossible {n L p b r : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hp : 0 < p) (hpL : p < L) (hb : L * b = p * oddCount n L)
    (hra : r ≤ oddCount n L) (hrL : oddCount n L + r ≤ L)
    (hw : ∀ i j, walk n L i < walk n L j + 2 * (L : Int) + r) : False := by
  obtain ⟨s, _, hs⟩ := CycleArcSplit.exists_window_count (k := p) (b := b) h (by rw [hb]; have := h.1; omega)
    (by rw [hb]; have := h.1; omega)
  let x := acceleratedOrbit s n
  let y := acceleratedOrbit p x
  have hX : AccIsCycleOf x L := accIsCycleOf_orbit h s
  have hY : AccIsCycleOf y L := accIsCycleOf_orbit hX p
  have hxcount : oddCount x L = oddCount n L := AccumulatorCap.oddCount_shift h.2 s
  have hycount : oddCount y L = oddCount x L := AccumulatorCap.oddCount_shift hX.2 p
  have hxphase : L * b = p * oddCount x L := hxcount.symm ▸ hb
  have hxwidth (i j : Nat) : walk x L i < walk x L j + 2 * (L : Int) + r := by
    unfold x
    rw [walk_shift h.2, walk_shift h.2]
    have hh := hw (s + i) (s + j)
    omega
  rcases Nat.lt_trichotomy x y with hxy | he | hyx
  · exact no_increasing_phase_offset hX hxphase hs hxy (by rwa [hxcount]) (by rwa [hxcount]) hxwidth
  · apply hleast p hp hpL
    apply CycleCollisionBudget.periodic_eq_of_synchronized ⟨L, accIsCycleOf_orbit h p⟩ ⟨L, h⟩ (d := s)
    rw [acceleratedOrbit_add, Nat.add_comm s p, ← acceleratedOrbit_add]
    exact he.symm
  · let q := L - p
    have hq : p + q = L := by dsimp [q]; omega
    have hback : acceleratedOrbit q y = x := by
      unfold y
      rw [acceleratedOrbit_add, Nat.add_comm q p, hq, hX.2]
    have hsum := AccumulatorArith.oddCount_add x p q
    rw [hq, hs] at hsum
    change oddCount x L = b + oddCount y q at hsum
    have hyphase : L * oddCount y q = q * oddCount y L := by
      have hfull := congrArg (fun v => L * v) hsum
      have hsplit := congrArg (fun v => v * oddCount x L) hq
      rw [Nat.mul_add, hxphase] at hfull
      rw [Nat.add_mul] at hsplit
      rw [hycount]
      omega
    have hywidth (i j : Nat) : walk y L i < walk y L j + 2 * (L : Int) + r := by
      unfold y
      rw [walk_shift hX.2, walk_shift hX.2]
      have hh := hxwidth (p + i) (p + j)
      omega
    exact no_increasing_phase_offset hY hyphase rfl (by rwa [hback])
      (by rwa [hycount, hxcount]) (by rwa [hycount, hxcount]) hywidth

/-- A least accelerated cycle with a common divisor of its period and
odd count has width at least twice its period plus the smaller step count. -/
theorem repeated_phase_width_lower_bound {n L : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hg : 1 < (oddCount n L).gcd L) :
    ∃ i j, i < L ∧ j < L ∧
      walk n L j + 2 * (L : Int) + (min (oddCount n L) (L - oddCount n L) : Nat) ≤ walk n L i := by
  let r := min (oddCount n L) (L - oddCount n L)
  have hra : r ≤ oddCount n L := Nat.min_le_left _ _
  have hle : oddCount n L ≤ L := by
    simpa [oddCount, parityVector] using (List.count_le_length (a := 1) (l := parityVector n L))
  have hrL : oddCount n L + r ≤ L := by
    have h := Nat.min_le_right (oddCount n L) (L - oddCount n L)
    change r ≤ L - oddCount n L at h
    omega
  apply Classical.byContradiction
  intro hno
  have hw (i j : Nat) : walk n L i < walk n L j + 2 * (L : Int) + r := by
    rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
    apply Int.lt_of_not_ge
    exact fun hl => hno ⟨i % L, j % L, Nat.mod_lt _ h.1, Nat.mod_lt _ h.1, hl⟩
  obtain ⟨p, hp, hpL, b, hb⟩ := exists_proper_phase_offset h.1 hg
  rw [Nat.mul_comm (oddCount n L) p] at hb
  exact narrow_phase_offset_impossible h hleast hp hpL hb.symm hra hrL hw

/-- In particular, repeated phases require discrepancy width at least
twice the least period. -/
theorem repeated_phase_width_ge_twice {n L : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hg : 1 < (oddCount n L).gcd L) :
    ∃ i j, i < L ∧ j < L ∧ walk n L j + 2 * (L : Int) ≤ walk n L i := by
  obtain ⟨i, j, hi, hj, hw⟩ := repeated_phase_width_lower_bound h hleast hg
  exact ⟨i, j, hi, hj, by omega⟩

/-- A least cycle below twice the discrepancy period has coprime
period and odd count. -/
theorem coprime_of_width_lt_twice {n L : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hw : ∀ i j, walk n L i < walk n L j + 2 * (L : Int)) :
    (oddCount n L).Coprime L := by
  change (oddCount n L).gcd L = 1
  have hp := Nat.gcd_pos_of_pos_right (oddCount n L) h.1
  by_cases hg : 1 < (oddCount n L).gcd L
  · obtain ⟨i, j, _, _, hwide⟩ := repeated_phase_width_ge_twice h hleast hg
    exact False.elim (Int.not_lt_of_ge hwide (hw i j))
  · omega

end Collatz.PhaseOrderCycle
