import Collatz.Strategy.ExcursionAlphabetMass

/-!
# Finite correction products for sparse excursion sources

A geometric saving in dyadic source counts bounds the product of all
reciprocal corrections on a finite set of distinct sources. The proof
uses integer weights at a common dyadic scale, with no logarithms.
-/

namespace Collatz.ExcursionSparseProduct

open Collatz.ExcursionLattice Collatz.ExcursionAlphabetMass Collatz.ExcursionBudget
open Collatz.ExcursionMap

private theorem product_shift_le_power (D : Nat) (weights : List Nat)
    (h : weights.sum ≤ D) :
    (D - weights.sum) * (weights.map (fun w => D + w)).prod ≤
      D ^ (weights.length + 1) := by
  induction weights with
  | nil => simp
  | cons w ws ih =>
    have hsum : w + ws.sum ≤ D := h
    have ht : ws.sum ≤ D := Nat.le_trans (Nat.le_add_left _ _) hsum
    have hpair : (D - (w + ws.sum)) * (D + w) ≤ D * (D - ws.sum) := by
      calc
        _ = D * (D - (w + ws.sum)) + w * (D - (w + ws.sum)) := by
          rw [Nat.mul_add, Nat.mul_comm (D - (w + ws.sum)) D,
            Nat.mul_comm (D - (w + ws.sum)) w]
        _ ≤ D * (D - (w + ws.sum)) + D * w := by
          apply Nat.add_le_add_left
          rw [Nat.mul_comm D w]
          exact Nat.mul_le_mul_left w (Nat.sub_le ..)
        _ = _ := by
          rw [← Nat.mul_add, show D - (w + ws.sum) + w = D - ws.sum by omega]
    change (D - (w + ws.sum)) * ((D + w) * (ws.map (fun w => D + w)).prod) ≤
      D ^ (ws.length + 1 + 1)
    calc
      _ = ((D - (w + ws.sum)) * (D + w)) * (ws.map (fun w => D + w)).prod :=
        (Nat.mul_assoc ..).symm
      _ ≤ (D * (D - ws.sum)) * (ws.map (fun w => D + w)).prod :=
        Nat.mul_le_mul_right _ hpair
      _ = D * ((D - ws.sum) * (ws.map (fun w => D + w)).prod) := Nat.mul_assoc ..
      _ ≤ D * D ^ (ws.length + 1) := Nat.mul_le_mul_left _ (ih ht)
      _ = _ := Nat.pow_succ'.symm

private theorem cross_weight_product (D : Nat) (weight : Nat → Nat) (xs : List Nat)
    (h : ∀ x ∈ xs, D ≤ x * weight x) :
    factors 1 1 xs * D ^ xs.length ≤ xs.prod * (xs.map (fun x => D + weight x)).prod := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hpair : (x + 1) * D ≤ x * (D + weight x) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      exact Nat.add_le_add_left hx _
    change (1 * x + 1) * factors 1 1 xs * D ^ (xs.length + 1) ≤
      x * xs.prod * ((D + weight x) * (xs.map (fun x => D + weight x)).prod)
    rw [Nat.one_mul, Nat.pow_succ]
    calc
      _ = ((x + 1) * D) * (factors 1 1 xs * D ^ xs.length) := by ac_rfl
      _ ≤ (x * (D + weight x)) * (xs.prod * (xs.map (fun x => D + weight x)).prod) :=
        Nat.mul_le_mul hpair ht
      _ = _ := by ac_rfl

/-- If a common integer envelope bounds the reciprocal sum by `1/K`,
the reciprocal product is at most `K/(K-1)`, in cross-multiplied form. -/
theorem reciprocal_le_ratio {D K : Nat} (hD : 0 < D) (hK : 0 < K)
    (weight : Nat → Nat) (xs : List Nat)
    (hpoint : ∀ x ∈ xs, D ≤ x * weight x)
    (hsum : K * (xs.map weight).sum ≤ D) :
    (K - 1) * factors 1 1 xs ≤ K * xs.prod := by
  let ws := xs.map weight
  let S := ws.sum
  let product := (xs.map (fun x => D + weight x)).prod
  change K * S ≤ D at hsum
  have hs : S ≤ D := Nat.le_trans (Nat.le_mul_of_pos_left _ hK) hsum
  have hp : (D - S) * product ≤ D ^ (xs.length + 1) := by
    simpa only [product, S, ws, List.length_map, List.map_map, Function.comp_def]
      using product_shift_le_power D ws hs
  have hscale : (K - 1) * D ≤ K * (D - S) := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_sub_left_distrib]
    omega
  have hproduct : (K - 1) * product ≤ K * D ^ xs.length := by
    apply Nat.le_of_mul_le_mul_left _ hD
    calc
      _ = ((K - 1) * D) * product := by ac_rfl
      _ ≤ (K * (D - S)) * product := Nat.mul_le_mul_right _ hscale
      _ = K * ((D - S) * product) := Nat.mul_assoc ..
      _ ≤ K * D ^ (xs.length + 1) := Nat.mul_le_mul_left _ hp
      _ = D * (K * D ^ xs.length) := by rw [Nat.pow_succ]; ac_rfl
  have hDpow : 0 < D ^ xs.length := Nat.pow_pos hD
  apply Nat.le_of_mul_le_mul_right _ hDpow
  calc
    _ = (K - 1) * (factors 1 1 xs * D ^ xs.length) := Nat.mul_assoc ..
    _ ≤ (K - 1) * (xs.prod * product) := Nat.mul_le_mul_left _
      (cross_weight_product D weight xs hpoint)
    _ = xs.prod * ((K - 1) * product) := by ac_rfl
    _ ≤ xs.prod * (K * D ^ xs.length) := Nat.mul_le_mul_left _ hproduct
    _ = (K * xs.prod) * D ^ xs.length := by ac_rfl

/-- A reciprocal sum bounded by one half gives a product bounded by two. -/
theorem reciprocal_le_two {D : Nat} (hD : 0 < D) (weight : Nat → Nat) (xs : List Nat)
    (hpoint : ∀ x ∈ xs, D ≤ x * weight x)
    (hsum : 2 * (xs.map weight).sum ≤ D) :
    factors 1 1 xs ≤ 2 * xs.prod := by
  simpa using reciprocal_le_ratio hD (by decide : 0 < 2) weight xs hpoint hsum

/-- The upper endpoint of a dyadic band. -/
def cutoff (P j : Nat) : Nat := 2 ^ (P * j) * 2

private def contribution (P H x j : Nat) : Nat :=
  if x < cutoff P (j + 1) then 2 ^ (P * (H - j)) else 0

private def bands (B H : Nat) : List Nat := List.range' B (H + 1 - B)

private def weight (P B H x : Nat) : Nat :=
  ((bands B H).map (contribution P H x)).sum

private theorem le_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hy
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hy) (Nat.le_add_left _ _)

private theorem point_weight {P B H x : Nat} (hBH : B ≤ H)
    (hlo : cutoff P B ≤ x) (hhi : x < cutoff P (H + 1)) :
    cutoff P H ≤ x * weight P B H x := by
  have hex : ∃ j, B ≤ j ∧ x < cutoff P (j + 1) := ⟨H, hBH, hhi⟩
  obtain ⟨j, ⟨hPj, hjx⟩, hmin⟩ := Collatz.Minimum.exists_min hex
  have hjH : j ≤ H := Nat.le_of_not_gt (fun hlt => hmin H hlt ⟨hBH, hhi⟩)
  have hxj : cutoff P j ≤ x := by
    by_cases hjP : j = B
    · simpa only [hjP] using hlo
    · have hlt : B < j := by omega
      apply Nat.le_of_not_gt
      intro hbad
      apply hmin (j - 1) (by omega)
      refine ⟨by omega, ?_⟩
      rw [show j - 1 + 1 = j by omega]
      exact hbad
  have hjmem : j ∈ bands B H := List.mem_range'_1.mpr ⟨hPj, by omega⟩
  have hterm : 2 ^ (P * (H - j)) ≤ weight P B H x := by
    have hm := List.mem_map_of_mem (f := contribution P H x) hjmem
    rw [contribution, if_pos hjx] at hm
    exact le_sum_of_mem hm
  calc
    _ = cutoff P j * 2 ^ (P * (H - j)) := by
      unfold cutoff
      have he : P * j + P * (H - j) = P * H := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hjH]
      rw [← he, Nat.pow_add]
      ac_rfl
    _ ≤ x * weight P B H x := Nat.mul_le_mul hxj hterm

private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ac_rfl

private theorem sum_contribution (P H j : Nat) (xs : List Nat) :
    (xs.map (fun x => contribution P H x j)).sum =
      2 ^ (P * (H - j)) * (xs.filter (fun x => decide (x < cutoff P (j + 1)))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    by_cases hx : x < cutoff P (j + 1)
    · simp [contribution, hx, Nat.mul_add, Nat.add_comm]
    · simp [contribution, hx]

private theorem sum_weight_swap (P H : Nat) (xs js : List Nat) :
    (xs.map (fun x => (js.map (contribution P H x)).sum)).sum =
      (js.map (fun j =>
        2 ^ (P * (H - j)) * (xs.filter (fun x => decide (x < cutoff P (j + 1)))).length)).sum := by
  induction js with
  | nil => induction xs <;> simp_all
  | cons j js ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_add, sum_contribution, ih]

private theorem exponent_sum_le (U J len : Nat) (h : J + len ≤ U) :
    ((List.range' J len).map (fun j => 2 ^ (U - (j + 1)))).sum ≤ 2 ^ (U - J) := by
  induction len generalizing J with
  | zero => simp
  | succ len ih =>
    have h' : J + 1 + len ≤ U := by omega
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    calc
      _ ≤ 2 ^ (U - (J + 1)) + 2 ^ (U - (J + 1)) :=
        Nat.add_le_add_left (ih (J + 1) h') _
      _ = _ := by
        rw [← Nat.two_mul, ← Nat.pow_succ', show (U - (J + 1)).succ = U - J by omega]

private theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem sum_map_scale (xs : List Nat) (A : Nat) (f : Nat → Nat) :
    (xs.map (fun j => A * f j)).sum = A * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp [ih, Nat.mul_add]

private theorem cumulative_weight_le {P B H A : Nat} {xs : List Nat}
    (hP : 0 < P) (hBH : B ≤ H)
    (hcap : ∀ j, (xs.filter (fun x => decide (x < cutoff P j))).length ≤
      A * 2 ^ ((P - 1) * j)) :
    (xs.map (weight P B H)).sum ≤ A * 2 ^ (P * (H + 1) - B) := by
  have hlen : B + (H + 1 - B) ≤ P * (H + 1) := by
    rw [Nat.add_sub_of_le (Nat.le_trans hBH (Nat.le_succ H))]
    exact Nat.le_mul_of_pos_left _ hP
  have hband (j : Nat) (hj : j ∈ bands B H) :
      2 ^ (P * (H - j)) * (xs.filter (fun x => decide (x < cutoff P (j + 1)))).length ≤
        A * 2 ^ (P * (H + 1) - (j + 1)) := by
    have hj' := (List.mem_range'_1.mp hj).2
    have hjH : j ≤ H := by omega
    have he : P * (H - j) + (P - 1) * (j + 1) = P * (H + 1) - (j + 1) := by
      have hs : P * (H - j) + (P - 1) * (j + 1) + (j + 1) = P * (H + 1) := by
        calc
          _ = P * (H - j) + ((P - 1) + 1) * (j + 1) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
          _ = P * (H - j) + P * (j + 1) := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hP)]
          _ = _ := by rw [← Nat.mul_add, show H - j + (j + 1) = H + 1 by omega]
      omega
    calc
      _ ≤ 2 ^ (P * (H - j)) * (A * 2 ^ ((P - 1) * (j + 1))) :=
        Nat.mul_le_mul_left _ (hcap (j + 1))
      _ = A * (2 ^ (P * (H - j)) * 2 ^ ((P - 1) * (j + 1))) := Nat.mul_left_comm ..
      _ = _ := by rw [← Nat.pow_add, he]
  unfold weight
  rw [sum_weight_swap]
  calc
    _ ≤ ((bands B H).map (fun j => A * 2 ^ (P * (H + 1) - (j + 1)))).sum :=
      sum_map_le _ _ _ hband
    _ = A * ((bands B H).map (fun j => 2 ^ (P * (H + 1) - (j + 1)))).sum := sum_map_scale ..
    _ ≤ _ := Nat.mul_le_mul_left _ (exponent_sum_le _ _ _ hlen)

/-- A mass factor up to `2^j` is absorbed by moving the lower cutoff
up another `j` bands. -/
theorem sparse_tail_product_with_mass {P j q H A : Nat} {xs : List Nat}
    (hP : 0 < P) (hA : A ≤ 2 ^ j) (hH : P + j + q ≤ H)
    (hlo : ∀ x ∈ xs, cutoff P (P + j + q) ≤ x)
    (hhi : ∀ x ∈ xs, x < cutoff P (H + 1))
    (hcap : ∀ k, (xs.filter (fun x => decide (x < cutoff P k))).length ≤
      A * 2 ^ ((P - 1) * k)) :
    (2 ^ (q + 1) - 1) * factors 1 1 xs ≤ 2 ^ (q + 1) * xs.prod := by
  let B := P + j + q
  apply reciprocal_le_ratio (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (Nat.two_pow_pos _)
    (weight P B H) xs (fun x hx => point_weight hH (hlo x hx) (hhi x hx))
  have hsum := cumulative_weight_le hP hH hcap
  have he : q + 1 + (j + (P * (H + 1) - B)) = P * H + 1 := by
    have hjq : j + q ≤ P * H := Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ hP)
    dsimp [B]
    rw [Nat.mul_succ]
    omega
  calc
    _ ≤ 2 ^ (q + 1) * (A * 2 ^ (P * (H + 1) - B)) := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ (q + 1) * (2 ^ j * 2 ^ (P * (H + 1) - B)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)
    _ = cutoff P H := by rw [← Nat.pow_add, ← Nat.pow_add, he, Nat.pow_succ, cutoff]

/-- Raising the lower cutoff by `q` bands improves the reciprocal
product bound to `2^(q+1)/(2^(q+1)-1)`. -/
theorem sparse_tail_product_ratio {P q H : Nat} {xs : List Nat}
    (hP : 0 < P) (hPH : P + q ≤ H)
    (hlo : ∀ x ∈ xs, cutoff P (P + q) ≤ x)
    (hhi : ∀ x ∈ xs, x < cutoff P (H + 1))
    (hcap : ∀ j, (xs.filter (fun x => decide (x < cutoff P j))).length ≤ 2 ^ ((P - 1) * j)) :
    (2 ^ (q + 1) - 1) * factors 1 1 xs ≤ 2 ^ (q + 1) * xs.prod := by
  exact sparse_tail_product_with_mass (j := 0) (A := 1) hP (by decide)
    (by simpa using hPH) (by simpa using hlo) hhi (by simpa using hcap)

/-- A distinct dyadic tail with geometric capacity has reciprocal
product at most two, uniformly in its finite upper cutoff. -/
theorem sparse_tail_product {P H : Nat} {xs : List Nat} (hP : 0 < P) (hPH : P ≤ H)
    (hlo : ∀ x ∈ xs, cutoff P P ≤ x) (hhi : ∀ x ∈ xs, x < cutoff P (H + 1))
    (hcap : ∀ j, (xs.filter (fun x => decide (x < cutoff P j))).length ≤ 2 ^ ((P - 1) * j)) :
    factors 1 1 xs ≤ 2 * xs.prod := by
  simpa using sparse_tail_product_ratio (q := 0) hP hPH hlo hhi hcap

private theorem product_filter_partition (xs : List Nat) (f : Nat → Nat) (p : Nat → Bool) :
    (xs.map f).prod =
      ((xs.filter p).map f).prod * ((xs.filter (fun x => !p x)).map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih, Nat.mul_assoc, Nat.mul_left_comm]

private theorem reciprocal_le_pow_length (xs : List Nat) (hpos : ∀ x ∈ xs, 0 < x) :
    factors 1 1 xs ≤ 2 ^ xs.length * xs.prod := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih =>
    have hx := hpos x List.mem_cons_self
    have hpair : x + 1 ≤ 2 * x := by omega
    have htail := ih (fun y hy => hpos y (List.mem_cons_of_mem _ hy))
    change (1 * x + 1) * factors 1 1 xs ≤ 2 ^ (xs.length + 1) * (x * xs.prod)
    rw [Nat.one_mul, Nat.pow_succ]
    calc
      _ ≤ (2 * x) * (2 ^ xs.length * xs.prod) := Nat.mul_le_mul hpair htail
      _ = _ := by ac_rfl

/-- Geometric capacity of distinct values below the dyadic cutoffs. -/
def DyadicCapacity (states : Nat → Nat) (P : Nat) : Prop :=
  ∀ j (xs : List Nat), xs.Nodup →
    (∀ x ∈ xs, x < cutoff P j ∧ ∃ i, states i = x) →
    xs.length ≤ 2 ^ ((P - 1) * j)

/-- A `19/20` occupation estimate at a dyadic cutoff gives a
geometric count at stride twenty, with a fixed mass factor. -/
theorem count_mass_twenty {C j length : Nat} (h : length ^ 20 ≤ C * cutoff 20 j ^ 19) :
    length ≤ (C * 2 ^ 19 + 1) * 2 ^ (19 * j) := by
  let A := C * 2 ^ 19 + 1
  have hA : C * 2 ^ 19 ≤ A ^ 20 :=
    Nat.le_trans (Nat.le_succ _) (Nat.le_pow (by decide : 0 < 20))
  apply (Nat.pow_le_pow_iff_left (by decide : (20 : Nat) ≠ 0)).mp
  calc
    _ ≤ C * cutoff 20 j ^ 19 := h
    _ = (C * 2 ^ 19) * (2 ^ (19 * j)) ^ 20 := by
      rw [cutoff, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        show 20 * j * 19 = 19 * j * 20 by omega]
      ac_rfl
    _ ≤ A ^ 20 * (2 ^ (19 * j)) ^ 20 := Nat.mul_le_mul_right _ hA
    _ = _ := (Nat.mul_pow ..).symm

/-- A finite selection above the specified cutoff has a correction
bound independent of how far its upper endpoint lies. -/
theorem reciprocal_tail_from_count {P j q A : Nat} {xs : List Nat}
    (hP : 0 < P) (hA : A ≤ 2 ^ j)
    (hlo : ∀ x ∈ xs, cutoff P (P + j + q) ≤ x)
    (hcap : ∀ k, (xs.filter (fun x => decide (x < cutoff P k))).length ≤
      A * 2 ^ ((P - 1) * k)) :
    (2 ^ (q + 1) - 1) * factors 1 1 xs ≤ 2 ^ (q + 1) * xs.prod := by
  let H := P + j + q + xs.sum
  have hPH : P + j + q ≤ H := Nat.le_add_right _ _
  have hhi : ∀ x ∈ xs, x < cutoff P (H + 1) := by
    intro x hx
    have hxH : x ≤ H := Nat.le_trans (le_sum_of_mem hx) (Nat.le_add_left _ _)
    have hpow : 2 ^ H ≤ 2 ^ (P * (H + 1)) := Nat.pow_le_pow_right (by decide)
      (Nat.le_trans (Nat.le_succ H) (Nat.le_mul_of_pos_left _ hP))
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hxH Nat.lt_two_pow_self)
      (Nat.le_trans hpow (Nat.le_mul_of_pos_right _ (by decide)))
  exact sparse_tail_product_with_mass hP hA hPH hlo hhi hcap

theorem reciprocal_tail_of_capacity {states : Nat → Nat} {P q : Nat}
    (hP : 0 < P) (hcap : DyadicCapacity states P) {xs : List Nat}
    (hnd : xs.Nodup) (hmember : ∀ x ∈ xs, ∃ i, states i = x)
    (hlo : ∀ x ∈ xs, cutoff P (P + q) ≤ x) :
    (2 ^ (q + 1) - 1) * factors 1 1 xs ≤ 2 ^ (q + 1) * xs.prod := by
  apply reciprocal_tail_from_count (j := 0) (A := 1) hP (by decide) (by simpa using hlo)
  intro j
  simpa only [Nat.one_mul] using hcap j _ (List.filter_sublist.nodup hnd) (fun x hx => by
    obtain ⟨hxmem, hxlt⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hxlt, hmember x hxmem⟩)

/-- Geometric counts with a uniform mass factor bound the entire
reciprocal product of any finite collection of distinct values. -/
theorem reciprocal_product_of_mass {keep : Nat → Prop} {P J A : Nat}
    (hP : 0 < P) (hA : A ≤ 2 ^ J)
    (hpos : ∀ x, keep x → 0 < x)
    (hcapacity : ∀ j (xs : List Nat), xs.Nodup →
      (∀ x ∈ xs, x < cutoff P j ∧ keep x) → xs.length ≤ A * 2 ^ ((P - 1) * j)) :
    ∃ C, ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, keep x) → factors 1 1 xs ≤ C * xs.prod := by
  let M := cutoff P (P + J)
  refine ⟨2 ^ M * 2, ?_⟩
  intro xs hnodup hmember
  let inside := fun x => decide (x < M)
  let low := xs.filter inside
  let high := xs.filter (fun x => !inside x)
  have hlowNodup : low.Nodup := List.filter_sublist.nodup hnodup
  have hhighNodup : high.Nodup := List.filter_sublist.nodup hnodup
  have hlowSubset : low ⊆ List.range M := by
    intro x hx
    exact List.mem_range.mpr (of_decide_eq_true (List.mem_filter.mp hx).2)
  have hlowLen : low.length ≤ M := by
    simpa using hlowNodup.length_le_of_subset hlowSubset
  have hlowPos : ∀ x ∈ low, 0 < x := by
    intro x hx
    exact hpos x (hmember x (List.mem_filter.mp hx).1)
  have hsmall : factors 1 1 low ≤ 2 ^ M * low.prod :=
    Nat.le_trans (reciprocal_le_pow_length low hlowPos)
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hlowLen))
  have hlo : ∀ x ∈ high, cutoff P (P + J + 0) ≤ x := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    simpa [inside, M, Nat.not_lt] using h
  have hlarge : factors 1 1 high ≤ 2 * high.prod := by
    suffices 1 * factors 1 1 high ≤ 2 * high.prod by simpa using this
    apply reciprocal_tail_from_count (q := 0) hP hA hlo
    intro j
    apply hcapacity j _ (List.filter_sublist.nodup hhighNodup)
    intro x hx
    obtain ⟨hxh, hlt⟩ := List.mem_filter.mp hx
    exact ⟨of_decide_eq_true hlt, hmember x (List.mem_filter.mp hxh).1⟩
  have hnum : factors 1 1 xs = factors 1 1 low * factors 1 1 high :=
    product_filter_partition xs (fun x => 1 * x + 1) inside
  have hden : xs.prod = low.prod * high.prod := by
    simpa [low, high] using product_filter_partition xs id inside
  rw [hnum, hden]
  calc
    _ ≤ (2 ^ M * low.prod) * (2 * high.prod) := Nat.mul_le_mul hsmall hlarge
    _ = _ := by ac_rfl

/-- A geometrically sparse sequence has a uniform reciprocal product
bound on every finite subcollection of distinct values. -/
theorem reciprocal_product_of_capacity {states : Nat → Nat} {P : Nat}
    (hP : 0 < P) (hpos : ∀ i, 0 < states i) (hcapacity : DyadicCapacity states P) :
    ∃ C, ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, ∃ i, states i = x) → factors 1 1 xs ≤ C * xs.prod := by
  apply reciprocal_product_of_mass (J := 0) (A := 1) hP (by decide)
  · rintro x ⟨i, rfl⟩
    exact hpos i
  · intro j xs hnd hx
    simpa only [Nat.one_mul] using hcapacity j xs hnd hx

theorem box_reciprocal_product {states : Nat → Nat} {u w : Nat}
    (hL : 0 < u + w) (hf : HasBoxFutures states u w) :
    ∃ C, ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, ∃ i, states i = x) → factors 1 1 xs ≤ C * xs.prod := by
  obtain ⟨P, hP, hcap⟩ := box_geometric_capacity hL hf
  exact reciprocal_product_of_capacity hP (fun i => by have h := (hf i 0).1; omega) hcap

private theorem numerator_le_reciprocal (n : Nat) (rs : List Run) :
    ((visits n rs).map Visit.numerator).prod ≤
      3 ^ ExcursionBudget.oddCount rs * factors 1 1 ((visits n rs).map Visit.source) := by
  induction rs with
  | nil => simp [visits, factors, ExcursionBudget.oddCount]
  | cons r rs ih =>
    let a := 3 ^ r.oddSteps
    let x := Collatz.acceleratedOrbit (time rs) n
    have hhead : a * x + (a - 2 ^ r.oddSteps) ≤ a * (x + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_left (Nat.sub_le ..) _
    change (a * x + (a - 2 ^ r.oddSteps)) * ((visits n rs).map Visit.numerator).prod ≤
      3 ^ (r.oddSteps + ExcursionBudget.oddCount rs) *
        ((1 * x + 1) * factors 1 1 ((visits n rs).map Visit.source))
    rw [Nat.one_mul, Nat.pow_add]
    calc
      _ ≤ (a * (x + 1)) *
          (3 ^ ExcursionBudget.oddCount rs * factors 1 1 ((visits n rs).map Visit.source)) :=
        Nat.mul_le_mul hhead ih
      _ = _ := by dsimp [a]; ac_rfl

/-- An infinite sequence of genuine excursions. -/
structure Sequence where
  values : Nat → Nat
  runs : Nat → Run
  cofactors : Nat → Nat
  step : ∀ i, IsExcursion (values i) (runs i).oddSteps (cofactors i)
    (runs i).halvings (values (i + 1))

def Sequence.profile (s : Sequence) (start : Nat) : Nat → List Run
  | 0 => []
  | k + 1 => s.runs (start + k) :: s.profile start k

theorem Sequence.trace (s : Sequence) (start k : Nat) :
    Trace (s.values start) (s.values (start + k)) (s.profile start k) := by
  induction k with
  | zero => exact Trace.nil
  | succ k ih => exact Trace.step ih (s.step (start + k))

theorem Sequence.visits_eq (s : Sequence) (start k : Nat) :
    ((visits (s.values start) (s.profile start k)).map Visit.source) =
      ((List.range' start k).reverse.map s.values) := by
  induction k with
  | zero => simp [Sequence.profile, visits]
  | succ k ih =>
    simp only [Sequence.profile, visits, List.map_cons, (s.trace start k).landing, ih]
    rw [List.range'_concat, List.reverse_append]
    simp

theorem Sequence.hasBoxFutures {s : Sequence} {u w : Nat}
    (h : ∀ i, s.runs i ∈ box u w) : HasBoxFutures s.values u w := by
  intro start k
  refine ⟨(s.step start).1, s.values (start + k), s.profile start k, s.trace start k, ?_⟩
  induction k with
  | zero => simp [Sequence.profile]
  | succ k ih =>
    refine ⟨by simp [Sequence.profile, ih.1], ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact h _
    · exact ih.2 r ht

/-- An injective excursion sequence with a uniform correction product
is bounded by its multiplicative coefficient up to a fixed factor. -/
theorem coefficient_envelope_of_product {s : Sequence} {C : Nat}
    (hinj : ∀ i j, s.values i = s.values j → i = j)
    (hC : ∀ xs : List Nat, xs.Nodup →
      (∀ x ∈ xs, ∃ i, s.values i = x) → factors 1 1 xs ≤ C * xs.prod) :
    ∀ k, 2 ^ time (s.profile 0 k) * s.values k ≤
      C * s.values 0 * 3 ^ ExcursionBudget.oddCount (s.profile 0 k) := by
  intro k
  let rs := s.profile 0 k
  let xs := (visits (s.values 0) rs).map Visit.source
  have hxs : xs = (List.range' 0 k).reverse.map s.values := s.visits_eq 0 k
  have hnodup : xs.Nodup := by
    rw [hxs]
    apply List.pairwise_map.mpr
    have hindices : (List.range' 0 k).Nodup := List.nodup_range'
    have hr : (List.range' 0 k).reverse.Nodup :=
      List.pairwise_reverse.mpr (hindices.imp (fun h => Ne.symm h))
    exact hr.imp (fun hne heq => hne (hinj _ _ heq))
  have hmember : ∀ x ∈ xs, ∃ i, s.values i = x := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    exact ⟨i, hi⟩
  have hpos : 0 < xs.prod := by
    apply List.prod_pos_iff_forall_pos_nat.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hmember x hx
    have h := (s.step i).1
    omega
  have hrec := hC xs hnodup hmember
  have hnum := numerator_le_reciprocal (s.values 0) rs
  have htrace := trace_product (s.trace 0 k)
  rw [Nat.zero_add] at htrace
  apply Nat.le_of_mul_le_mul_right _ hpos
  change (2 ^ time rs * s.values k) * xs.prod ≤
    (C * s.values 0 * 3 ^ ExcursionBudget.oddCount rs) * xs.prod
  calc
    _ = s.values 0 * ((visits (s.values 0) rs).map Visit.numerator).prod := htrace
    _ ≤ s.values 0 * (3 ^ ExcursionBudget.oddCount rs * factors 1 1 xs) :=
      Nat.mul_le_mul_left _ hnum
    _ ≤ s.values 0 * (3 ^ ExcursionBudget.oddCount rs * (C * xs.prod)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrec)
    _ = _ := by ac_rfl

theorem box_coefficient_envelope {s : Sequence} {u w : Nat}
    (hbox : ∀ i, s.runs i ∈ box u w)
    (hinj : ∀ i j, s.values i = s.values j → i = j) :
    ∃ C, ∀ k, 2 ^ time (s.profile 0 k) * s.values k ≤
      C * s.values 0 * 3 ^ ExcursionBudget.oddCount (s.profile 0 k) := by
  have hL : 0 < u + w := by
    have h := mem_box.mp (hbox 0)
    omega
  obtain ⟨C, hC⟩ := box_reciprocal_product hL (Sequence.hasBoxFutures hbox)
  exact ⟨C, coefficient_envelope_of_product hinj hC⟩

/-- A sequence of distinct naturals eventually exceeds each fixed natural. -/
theorem injective_eventually_above (states : Nat → Nat)
    (hinj : ∀ i j, states i = states j → i = j) (B : Nat) :
    ∃ H, ∀ i, H ≤ i → B < states i := by
  classical
  let locate := fun x => if h : ∃ i, states i = x then Classical.choose h else 0
  let indices := (List.range (B + 1)).map locate
  refine ⟨indices.sum + 1, ?_⟩
  intro i hi
  apply Nat.lt_of_not_ge
  intro hsmall
  have hi' : locate (states i) = i := by
    have hex : ∃ j, states j = states i := ⟨i, rfl⟩
    dsimp [locate]
    rw [dif_pos hex]
    exact hinj _ _ (Classical.choose_spec hex)
  have hmem : i ∈ indices := List.mem_map.mpr
    ⟨states i, List.mem_range.mpr (Nat.lt_succ_of_le hsmall), hi'⟩
  have hle := le_sum_of_mem hmem
  omega

/-- A uniform coefficient envelope forces the multiplier of an
injective excursion sequence to tend to infinity. -/
theorem coefficient_escapes_of_envelope {s : Sequence} {C : Nat}
    (hinj : ∀ i j, s.values i = s.values j → i = j)
    (hC : ∀ k, 2 ^ time (s.profile 0 k) * s.values k ≤
      C * s.values 0 * 3 ^ ExcursionBudget.oddCount (s.profile 0 k)) :
    ∀ R, ∃ H, ∀ k, H ≤ k →
      R * 2 ^ time (s.profile 0 k) < 3 ^ ExcursionBudget.oddCount (s.profile 0 k) := by
  intro R
  obtain ⟨H, hH⟩ := injective_eventually_above s.values hinj (C * s.values 0 * R)
  refine ⟨H, ?_⟩
  intro k hk
  apply Nat.lt_of_not_ge
  intro hsmall
  let B := 2 ^ time (s.profile 0 k)
  have hle : B * s.values k ≤ B * (C * s.values 0 * R) := by
    calc
      _ ≤ C * s.values 0 * 3 ^ ExcursionBudget.oddCount (s.profile 0 k) := hC k
      _ ≤ C * s.values 0 * (R * B) := Nat.mul_le_mul_left _ hsmall
      _ = _ := by ac_rfl
  exact Nat.not_le_of_gt (hH k hk) (Nat.le_of_mul_le_mul_left hle (Nat.two_pow_pos _))

/-- An injective trajectory in a bounded alphabet must have multiplier
`3^V/2^S` tending to infinity. -/
theorem coefficient_escapes_of_box {s : Sequence} {u w : Nat}
    (hbox : ∀ i, s.runs i ∈ box u w)
    (hinj : ∀ i j, s.values i = s.values j → i = j) :
    ∀ R, ∃ H, ∀ k, H ≤ k →
      R * 2 ^ time (s.profile 0 k) < 3 ^ ExcursionBudget.oddCount (s.profile 0 k) := by
  obtain ⟨_, hC⟩ := box_coefficient_envelope hbox hinj
  exact coefficient_escapes_of_envelope hinj hC

end Collatz.ExcursionSparseProduct
