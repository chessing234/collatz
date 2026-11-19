import Collatz.Strategy.OrbitCorrectionBudget
import Collatz.Strategy.PowerSeparation

/-! Distinct periodic points cannot coalesce at a common time, even when
they lie on different cycles. Their reciprocal sums share one bound. -/

namespace Collatz.CycleCollisionBudget

open Collatz.Arith Collatz.AccCycle Collatz.OrbitCorrectionBudget

/-- Iteration is injective on the set of periodic points. -/
theorem periodic_eq_of_synchronized {x y d : Nat} (hx : AccPeriodic x) (hy : AccPeriodic y)
    (heq : acceleratedOrbit d x = acceleratedOrbit d y) : x = y := by
  obtain ⟨L, hL, hx⟩ := hx
  obtain ⟨M, hM, hy⟩ := hy
  let p := L * M * (d + 1)
  have hd : d ≤ p := by
    have hp := Nat.le_mul_of_pos_left (d + 1) (Nat.mul_pos hL hM)
    omega
  have h := congrArg (acceleratedOrbit (p - d)) heq
  rw [acceleratedOrbit_add, acceleratedOrbit_add, Nat.sub_add_cancel hd] at h
  have hpx : acceleratedOrbit p x = x := by
    rw [show p = L * (M * (d + 1)) by simp [p, Nat.mul_assoc]]
    exact accOrbit_mul_period hx _
  have hpy : acceleratedOrbit p y = y := by
    rw [show p = M * (L * (d + 1)) by dsimp [p]; ac_rfl]
    exact accOrbit_mul_period hy _
  exact hpx.symm.trans (h.trans hpy)

/-- The same bound holds across an arbitrary finite list of distinct
periodic points, with no common period required. -/
theorem periodic_reciprocal_sum_le {s : Nat} {values : List Nat}
    (hnd : values.Nodup) (hp : ∀ v ∈ values, AccPeriodic v)
    (hfloor : ∀ v ∈ values, 8192 ^ s ≤ v) :
    (values.map fun v : Nat => (↑v : Rat)⁻¹).sum ≤ 262 * ((6561 : Rat) / 8192) ^ s := by
  exact reciprocal_sum_le_of_separated (f := id)
    (fun _ i j hi hj he => periodic_eq_of_synchronized (hp i hi) (hp j hj) he) hnd hfloor

/-- The points in a period, with the starting point counted once. -/
def periodPoints (n L : Nat) : List Nat := (List.range L).map fun i => acceleratedOrbit i n

/-- A least positive return lists each point of its cycle exactly once. -/
theorem periodPoints_nodup {n L : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n) :
    (periodPoints n L).Nodup := by
  rw [periodPoints, List.Nodup, List.pairwise_map]
  apply List.Pairwise.imp_of_mem (l := List.range L) (R := fun i j => i < j)
  · intro i j _ hj hij heq
    let k := j - i
    have hk : 0 < k := by omega
    have hkl : k < L := by have := List.mem_range.mp hj; omega
    have hjoin : acceleratedOrbit i (acceleratedOrbit k n) = acceleratedOrbit i n := by
      rw [acceleratedOrbit_add, show i + k = j by omega, ← heq]
    exact hmin k hk hkl (periodic_eq_of_synchronized
      ⟨L, accIsCycleOf_orbit h k⟩ ⟨L, h⟩ hjoin)
  · exact List.pairwise_lt_range

/-- The positive normalized power gap of a cycle. -/
def deficit (n L : Nat) : Rat := 1 - (3 : Rat) ^ oddCount n L / (2 : Rat) ^ L

theorem deficit_pos {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) : 0 < deficit n L := by
  have hlt : (3 : Rat) ^ oddCount n L < (2 : Rat) ^ L := by
    simpa only [Rat.natCast_pow, Rat.natCast_ofNat] using Rat.natCast_lt_natCast.mpr (accCycle_bounds hn h).2.2
  have hpos : 0 < (2 : Rat) ^ L := Rat.pow_pos (by decide)
  have he : (3 : Rat) ^ oddCount n L / (2 : Rat) ^ L < 1 := by
    apply Rat.lt_of_mul_lt_mul_right _ (Rat.le_of_lt hpos)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one, Rat.one_mul]
    exact hlt
  unfold deficit
  grind

private theorem sum_deficits_le_reciprocals {cycles : List (Nat × Nat)}
    (hpos : ∀ c ∈ cycles, 0 < c.1) (hp : ∀ c ∈ cycles, AccIsCycleOf c.1 c.2) :
    (cycles.map fun c => deficit c.1 c.2).sum ≤
      ((cycles.flatMap fun c => periodPoints c.1 c.2).map fun v : Nat => (↑v : Rat)⁻¹).sum / 4 := by
  induction cycles with
  | nil => simp [Rat.div_def, Rat.zero_mul]
  | cons c cycles ih =>
    have hh := deficit_le_reciprocal_sum_of_return (hpos c List.mem_cons_self) (hp c List.mem_cons_self).2
    have ht := ih (fun d hd => hpos d (List.mem_cons_of_mem _ hd))
      (fun d hd => hp d (List.mem_cons_of_mem _ hd))
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    simp only [periodPoints, List.map_map, Function.comp_def] at *
    change deficit c.1 c.2 ≤ _ at hh
    rw [Rat.div_def, Rat.add_mul]
    rw [Rat.div_def] at hh ht
    grind

/-- Any finite collection of disjoint cycles above `8192^s`, each listed
over one least period, shares a single bound on the sum of its deficits.
The no-duplicates premise says the concatenated list visits each point
only once. -/
theorem total_deficit_le {s : Nat} {cycles : List (Nat × Nat)}
    (hp : ∀ c ∈ cycles, AccIsCycleOf c.1 c.2)
    (hnd : (cycles.flatMap fun c => periodPoints c.1 c.2).Nodup)
    (hfloor : ∀ v ∈ cycles.flatMap (fun c => periodPoints c.1 c.2), 8192 ^ s ≤ v) :
    (cycles.map fun c => deficit c.1 c.2).sum ≤ (262 / 4 : Rat) * ((6561 : Rat) / 8192) ^ s := by
  have hpos : ∀ c ∈ cycles, 0 < c.1 := by
    intro c hc
    have hm : c.1 ∈ periodPoints c.1 c.2 := List.mem_map.mpr
      ⟨0, List.mem_range.mpr (hp c hc).1, rfl⟩
    exact Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) (hfloor _ (List.mem_flatMap.mpr ⟨c, hc, hm⟩))
  have hrecip := periodic_reciprocal_sum_le hnd (fun v hv => by
    obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨i, _, he⟩ := List.mem_map.mp hv
    rw [← he]
    exact ⟨c.2, accIsCycleOf_orbit (hp c hc) i⟩) hfloor
  apply Rat.le_trans (sum_deficits_le_reciprocals hpos hp)
  rw [Rat.div_def]
  calc
    _ ≤ (262 * ((6561 : Rat) / 8192) ^ s) * (4 : Rat)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hrecip (by decide +kernel)
    _ = _ := by
      rw [show (262 / 4 : Rat) = 262 * (4 : Rat)⁻¹ by decide +kernel]
      grind

/-- The bound on a single cycle is independent of the length of its least period. -/
theorem cycle_deficit_le {n L s : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n)
    (hfloor : ∀ j, j < L → 8192 ^ s ≤ acceleratedOrbit j n) :
    deficit n L ≤ (262 / 4 : Rat) * ((6561 : Rat) / 8192) ^ s := by
  have hb := total_deficit_le (cycles := [(n, L)]) (s := s)
    (fun c hc => by simpa using (show c = (n, L) by simpa using hc) ▸ h)
    (by simpa using periodPoints_nodup h hmin) (by
      intro v hv
      have hv' : v ∈ periodPoints n L := by simpa using hv
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hv'
      exact he ▸ hfloor j (List.mem_range.mp hj))
  simpa [Rat.add_zero] using hb

/-- For a cycle entirely above `2^286`, the least period is the first
exponent whose power of two exceeds the corresponding power of three. -/
theorem period_is_first_power_of_two_above {n L : Nat} (h : AccIsCycleOf n L)
    (hmin : ∀ j, 0 < j → j < L → acceleratedOrbit j n ≠ n)
    (hfloor : ∀ j, j < L → 8192 ^ 22 ≤ acceleratedOrbit j n) :
    3 ^ oddCount n L < 2 ^ L ∧ ∀ r, r < L → 2 ^ r < 3 ^ oddCount n L := by
  have hb := cycle_deficit_le h hmin hfloor
  have hnumeric : (262 / 4 : Rat) * ((6561 : Rat) / 8192) ^ 22 < 1 / 2 := by decide +kernel
  have hsmall : deficit n L < (1 / 2 : Rat) := by grind
  let A := (3 : Rat) ^ oddCount n L
  let B := (2 : Rat) ^ L
  have hB : 0 < B := Rat.pow_pos (by decide)
  have hd : (A / B) * B = A := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
  have hhalf : (1 / 2 : Rat) < A / B := by
    change 1 - A / B < (1 / 2 : Rat) at hsmall
    grind
  have hmul := Rat.mul_lt_mul_of_pos_right hhalf hB
  rw [hd] at hmul
  have hnat : 2 ^ L < 2 * 3 ^ oddCount n L := by
    apply Rat.natCast_lt_natCast.mp
    simp only [Rat.natCast_mul, Rat.natCast_pow, Rat.natCast_ofNat]
    change B < 2 * A
    grind
  have hstart : 0 < n := Nat.lt_of_lt_of_le (two_pow_pos (13 * 22)) (by
    simpa only [Nat.pow_mul, acceleratedOrbit_zero] using hfloor 0 h.1)
  refine ⟨(accCycle_bounds hstart h).2.2, ?_⟩
  intro r hr
  have hle : 2 ^ r * 2 ≤ 2 ^ L := by
    rw [← Nat.pow_succ]
    exact two_pow_le_two_pow (Nat.succ_le_of_lt hr)
  omega

private theorem sum_lower_bound {α : Type} {values : List α} {f : α → Rat} {ε : Rat}
    (h : ∀ v ∈ values, ε ≤ f v) : (values.length : Rat) * ε ≤ (values.map f).sum := by
  induction values with
  | nil => simp [Rat.zero_mul]
  | cons v values ih =>
    have hv := h v List.mem_cons_self
    have ht := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    change ((values.length + 1 : Nat) : Rat) * ε ≤ f v + (values.map f).sum
    rw [Rat.natCast_add, Rat.natCast_ofNat]
    grind

/-- A lower bound on each gap limits how many disjoint cycles can share
the same floor. The bound applies to arbitrary finite selections. -/
theorem cycle_count_mul_deficit_le {s : Nat} {cycles : List (Nat × Nat)} {ε : Rat}
    (hp : ∀ c ∈ cycles, AccIsCycleOf c.1 c.2)
    (hnd : (cycles.flatMap fun c => periodPoints c.1 c.2).Nodup)
    (hfloor : ∀ v ∈ cycles.flatMap (fun c => periodPoints c.1 c.2), 8192 ^ s ≤ v)
    (he : ∀ c ∈ cycles, ε ≤ deficit c.1 c.2) :
    (cycles.length : Rat) * ε ≤ (262 / 4 : Rat) * ((6561 : Rat) / 8192) ^ s :=
  Rat.le_trans (sum_lower_bound he) (total_deficit_le hp hnd hfloor)

/-- The integer power separation estimate supplies a lower bound on the
deficit in terms of a bound on the cycle length. -/
theorem deficit_lower_of_power_separation (hgap : PowerSeparation) {n L K : Nat}
    (hn : 0 < n) (hp : AccIsCycleOf n L) (hK : L ≤ K) :
    ((2 : Rat) * (K : Rat) ^ 14)⁻¹ ≤ deficit n L := by
  let a := oddCount n L
  let d := 2 ^ L - 3 ^ a
  let B := (2 : Rat) ^ L
  let A := (3 : Rat) ^ a
  let C := (2 : Rat) * (K : Rat) ^ 14
  have hnat : 3 ^ a < 2 ^ L := (accCycle_bounds hn hp).2.2
  have hsplit : d + 3 ^ a = 2 ^ L := Nat.sub_add_cancel (Nat.le_of_lt hnat)
  have hsplit' : (d : Rat) + A = B := by
    simpa only [Rat.natCast_add, Rat.natCast_pow, Rat.natCast_ofNat, A, B]
      using congrArg (fun v : Nat => (v : Rat)) hsplit
  have hC : 0 < C := Rat.mul_pos (by decide)
    (Rat.pow_pos (Rat.natCast_lt_natCast.mpr (Nat.lt_of_lt_of_le hp.1 hK)))
  have hB : 0 < B := Rat.pow_pos (by decide)
  have hscale : B ≤ C * (d : Rat) := by
    have ht : 2 ^ L ≤ 2 * K ^ 14 * d := Nat.le_trans (hgap a L hnat)
      (Nat.mul_le_mul_right d (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK 14)))
    simpa only [Rat.natCast_pow, Rat.natCast_mul, Rat.natCast_ofNat, B, C]
      using Rat.natCast_le_natCast.mpr ht
  have hdiv : (A / B) * B = A := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
  have he : deficit n L * B = d := by
    change (1 - A / B) * B = (d : Rat)
    grind
  apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hC hB)
  calc
    C⁻¹ * (C * B) = (C⁻¹ * C) * B := (Rat.mul_assoc ..).symm
    _ = B := by rw [Rat.inv_mul_cancel _ (by grind), Rat.one_mul]
    _ ≤ C * (d : Rat) := hscale
    _ = deficit n L * (C * B) := by rw [← he]; grind

/-- Combining the shared budget with power separation bounds the number
of disjoint cycles of bounded period. The separation estimate is an
explicit hypothesis, kept outside the kernel-checked elementary result. -/
theorem bounded_period_cycle_count (hgap : PowerSeparation) {K s : Nat} {cycles : List (Nat × Nat)}
    (hp : ∀ c ∈ cycles, AccIsCycleOf c.1 c.2 ∧ c.2 ≤ K)
    (hnd : (cycles.flatMap fun c => periodPoints c.1 c.2).Nodup)
    (hfloor : ∀ v ∈ cycles.flatMap (fun c => periodPoints c.1 c.2), 8192 ^ s ≤ v) :
    (cycles.length : Rat) * ((2 : Rat) * (K : Rat) ^ 14)⁻¹ ≤
      (262 / 4 : Rat) * ((6561 : Rat) / 8192) ^ s := by
  apply cycle_count_mul_deficit_le (fun c hc => (hp c hc).1) hnd hfloor
  intro c hc
  have hm : c.1 ∈ periodPoints c.1 c.2 := List.mem_map.mpr
    ⟨0, List.mem_range.mpr (hp c hc).1.1, rfl⟩
  have hn := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) (hfloor _ (List.mem_flatMap.mpr ⟨c, hc, hm⟩))
  exact deficit_lower_of_power_separation hgap hn (hp c hc).1 (hp c hc).2

end Collatz.CycleCollisionBudget
