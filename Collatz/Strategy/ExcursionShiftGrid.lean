import Collatz.Strategy.ExcursionSwitchFloor

/-!
# A single factor decision for every rational coordinate shift

A shift `s/d` is stored as the numerator `s` of a common grid `d > 0`.
With `a=3^v` and `b=2^(v+W)`, the sign of
`b*n + 2^v - a*(n+1)` chooses the better affine factor across the
entire grid. The clipped zero-offset case makes the two factors equal.
-/

namespace Collatz.ExcursionShiftGrid

open Collatz.ExcursionMap Collatz.ExcursionSwitchFloor

def offset (d v W s t : Nat) : Nat :=
  3 ^ v * (d - s) + 2 ^ (v + W) * t - d * 2 ^ v

/-- The affine branch, evaluated at the floor, lands at or below the floor. -/
def mapsBelowFloor (n v W : Nat) : Prop :=
  3 ^ v * (n + 1) ≤ 2 ^ (v + W) * n + 2 ^ v

instance (n v W : Nat) : Decidable (mapsBelowFloor n v W) :=
  inferInstanceAs (Decidable (_ ≤ _))

private theorem scaled_affine_le {x y v u W d s t : Nat}
    (h : IsExcursion x v u W y) (hs : s ≤ d) :
    2 ^ (v + W) * (d * y + t) ≤ 3 ^ v * (d * x + s) + offset d v W s t := by
  have hraw := affine_source_succ h
  have hscaled : 2 ^ (v + W) * (d * y) + d * 2 ^ v =
      3 ^ v * (d * x + s) + 3 ^ v * (d - s) := calc
    _ = d * (2 ^ (v + W) * y + 2 ^ v) := by rw [Nat.mul_add]; congr 1; ac_rfl
    _ = 3 ^ v * (d * (x + 1)) := by rw [hraw]; ac_rfl
    _ = _ := by
      rw [← Nat.mul_add, Nat.mul_add d x, Nat.mul_one]
      congr 1
      omega
  rw [Nat.mul_add, offset]
  omega

/-- A general fraction comparison after canceling equal terms. -/
private theorem arrival_le_iff {a b p q e : Nat} (he : e ≤ b * q) :
    (b * p) * (a * q) ≤ (a * p + e) * (b * q - e) ↔
      e = 0 ∨ a * p + e ≤ b * q := by
  have heq : b * q - e + e = b * q := Nat.sub_add_cancel he
  have hleft : (b * p) * (a * q) = a * p * (b * q - e) + a * p * e := calc
    _ = a * p * (b * q) := by ac_rfl
    _ = _ := by rw [← Nat.mul_add, heq]
  rw [hleft, Nat.add_mul]
  constructor
  · intro h
    by_cases hz : e = 0
    · exact Or.inl hz
    · have hh : a * p * e ≤ (b * q - e) * e := by
        rw [Nat.mul_comm (b * q - e) e]
        exact Nat.le_of_add_le_add_left h
      have := Nat.le_of_mul_le_mul_right hh (Nat.pos_of_ne_zero hz)
      exact Or.inr (by omega)
  · rintro (rfl | hb)
    · simp
    · apply Nat.add_le_add_left
      rw [Nat.mul_comm e (b * q - e)]
      exact Nat.mul_le_mul_right e (by omega)

private theorem offset_test {n d v W s t : Nat} (hd : 0 < d) (hs : s ≤ d)
    (he : 0 < offset d v W s t) :
    3 ^ v * (d * n + s) + offset d v W s t ≤ 2 ^ (v + W) * (d * n + t) ↔
      mapsBelowFloor n v W := by
  let a := 3 ^ v
  let b := 2 ^ (v + W)
  let e := offset d v W s t
  have hE : e + d * 2 ^ v = a * (d - s) + b * t := by
    unfold e offset at *
    exact Nat.sub_add_cancel (by omega)
  have hleft : a * (d * n + s) + e + d * 2 ^ v = d * (a * (n + 1)) + b * t := calc
    _ = a * (d * n + s) + (a * (d - s) + b * t) := by rw [Nat.add_assoc, hE]
    _ = a * (d * (n + 1)) + b * t := by
      rw [← Nat.add_assoc, ← Nat.mul_add, Nat.mul_add d n, Nat.mul_one]
      congr 2
      omega
    _ = _ := by rw [Nat.mul_left_comm a d]
  have hright : b * (d * n + t) + d * 2 ^ v = d * (b * n + 2 ^ v) + b * t := by
    rw [Nat.mul_add b (d * n), Nat.mul_add d (b * n), Nat.mul_left_comm b d]
    ac_rfl
  change a * (d * n + s) + e ≤ b * (d * n + t) ↔ a * (n + 1) ≤ b * n + 2 ^ v
  constructor
  · intro h
    have hscaled := Nat.add_le_add_right h (d * 2 ^ v)
    rw [hleft, hright] at hscaled
    exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hscaled) hd
  · intro h
    have hscaled := Nat.add_le_add_right (Nat.mul_le_mul_left d h) (b * t)
    rw [← hleft, ← hright] at hscaled
    exact Nat.le_of_add_le_add_right hscaled

/-- Every grid edge uses the same affine floor test. A zero clipped offset
can use the departure factor since the two factors then coincide. -/
def choose (n d v W : Nat) : Nat → Nat → Nat × Nat :=
  let a := 3 ^ v
  let b := 2 ^ (v + W)
  let c := d * 2 ^ v
  let floor := d * n
  let arrival := decide (mapsBelowFloor n v W)
  fun s t =>
    let e := a * (d - s) + b * t - c
    let p := floor + s
    let q := floor + t
    if arrival then (b * p, b * q - e) else (a * p + e, a * q)

/-- When both factors are available, their order is determined by one
comparison at the floor, independent of the shifts whenever the offset
is positive. -/
theorem arrival_le_departure_iff {n d v W s t : Nat} (hd : 0 < d) (hs : s ≤ d)
    (hvalid : offset d v W s t < 2 ^ (v + W) * (d * n + t)) :
    (2 ^ (v + W) * (d * n + s)) * (3 ^ v * (d * n + t)) ≤
        (3 ^ v * (d * n + s) + offset d v W s t) *
          (2 ^ (v + W) * (d * n + t) - offset d v W s t) ↔
      offset d v W s t = 0 ∨ mapsBelowFloor n v W := by
  rw [arrival_le_iff (Nat.le_of_lt hvalid)]
  by_cases he : offset d v W s t = 0
  · simp [he]
  · simp only [he, false_or]
    exact offset_test hd hs (Nat.pos_of_ne_zero he)

/-- The shared decision gives a valid normalized factor on every grid
edge. The scaled floor coordinates stay positive for positive starts. -/
theorem choose_sound {n d x y v u W s t : Nat} (hn : 0 < n) (hd : 0 < d)
    (h : IsExcursion x v u W y) (hs : s ≤ d) (hx : n ≤ x) (hy : n ≤ y) :
    2 ^ (v + W) * (choose n d v W s t).2 * (d * n + s) * (d * y + t) ≤
      3 ^ v * (choose n d v W s t).1 * (d * n + t) * (d * x + s) := by
  have hlocal := scaled_affine_le h hs (t := t)
  unfold choose
  dsimp only
  split
  · rename_i hdecision
    have hfloor : mapsBelowFloor n v W := of_decide_eq_true hdecision
    have hpos : offset d v W s t < 2 ^ (v + W) * (d * n + t) := by
      by_cases he : offset d v W s t = 0
      · rw [he]
        exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.add_pos_left (Nat.mul_pos hd hn) _)
      · have hb := (offset_test hd hs (Nat.pos_of_ne_zero he)).mpr hfloor
        have hp : 0 < 3 ^ v * (d * n + s) :=
          Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.add_pos_left (Nat.mul_pos hd hn) _)
        omega
    exact arrival_factor_bound hlocal
      (Nat.add_le_add_right (Nat.mul_le_mul_left d hy) t) hpos
  · exact departure_factor_bound hlocal (Nat.add_le_add_right (Nat.mul_le_mul_left d hx) s)

/-- A genuine excursion trace and the products of its grid factors. -/
inductive Trace (n d : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | start {s : Nat} : s ≤ d → Trace n d n s 0 1 1 1 1
  | step {x y s t elapsed A B U D v u W : Nat} :
      Trace n d x s elapsed A B U D →
      IsExcursion x v u W y →
      t ≤ d →
      Trace n d y t (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W))
        (U * (choose n d v W s t).1) (D * (choose n d v W s t).2)

theorem Trace.shift_le {n d x s elapsed A B U D : Nat} (h : Trace n d x s elapsed A B U D) :
    s ≤ d := by
  cases h with
  | start hs => exact hs
  | step _ _ ht => exact ht

theorem Trace.landing {n d x s elapsed A B U D : Nat} (h : Trace n d x s elapsed A B U D) :
    Collatz.acceleratedOrbit elapsed n = x := by
  induction h with
  | start => rfl
  | step _ hstep _ ih => rw [← Collatz.acceleratedOrbit_add, ih, landing_eq hstep]

/-- The positive grid normalizations cancel regardless of how the shifts change. -/
theorem Trace.floor_bound {n d x s elapsed A B U D H : Nat}
    (h : Trace n d x s elapsed A B U D) (hn : 0 < n) (hd : 0 < d)
    (htime : elapsed ≤ H) (hfloor : ∀ k, k ≤ H → n ≤ Collatz.acceleratedOrbit k n) :
    B * D * (d * x + s) ≤ A * U * (d * n + s) := by
  induction h with
  | start => simp
  | @step x y s t elapsed A B U D v u W hprev hstep _ ih =>
    have hbefore : elapsed ≤ H := by omega
    have hx := hfloor elapsed hbefore
    rw [hprev.landing] at hx
    have hy := hfloor (v + W + elapsed) htime
    rw [← Collatz.acceleratedOrbit_add, hprev.landing, landing_eq hstep] at hy
    exact compose_floor_bound (ih hbefore) (choose_sound hn hd hstep hprev.shift_le hx hy)
      (Nat.add_pos_left (Nat.mul_pos hd hn) _)

/-- A strict product crossing rules out a floor at the source by the
elapsed accelerated time. -/
theorem Trace.drop_by {n d x s elapsed A B U D : Nat}
    (h : Trace n d x s elapsed A B U D) (hn : 0 < n) (hd : 0 < d)
    (hcross : A * U < B * D) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n := by
  apply Classical.byContradiction
  intro hnone
  have hfloor (k : Nat) (hk : k ≤ elapsed) : n ≤ Collatz.acceleratedOrbit k n := by
    apply Nat.le_of_not_gt
    intro hdrop
    exact hnone ⟨k, hk, hdrop⟩
  have hx := hfloor elapsed (Nat.le_refl _)
  rw [h.landing] at hx
  have hscaled : B * D * (d * n + s) ≤ A * U * (d * n + s) :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left d hx) s))
      (h.floor_bound hn hd (Nat.le_refl _) hfloor)
  exact (Nat.not_lt_of_ge hscaled)
    (Nat.mul_lt_mul_of_pos_right hcross (Nat.add_pos_left (Nat.mul_pos hd hn) _))

private theorem offset_scaled (d v W s t m : Nat) :
    offset (m * d) v W (m * s) (m * t) = m * offset d v W s t := by
  simp only [offset, Nat.mul_sub_left_distrib, Nat.mul_add]
  congr 1
  · congr 1 <;> ac_rfl
  · ac_rfl

/-- Increasing grid resolution by an integer preserves every old factor
as a rational number. Its numerator and denominator scale together. -/
theorem choose_scaled (n d v W s t m : Nat) :
    choose n (m * d) v W (m * s) (m * t) =
      (m * (choose n d v W s t).1, m * (choose n d v W s t).2) := by
  have hcoord (z : Nat) : (m * d) * n + m * z = m * (d * n + z) := by
    rw [Nat.mul_add, Nat.mul_assoc]
  by_cases h : mapsBelowFloor n v W
  · simp only [choose, decide_eq_true h, if_true]
    change
      (2 ^ (v + W) * ((m * d) * n + m * s),
        2 ^ (v + W) * ((m * d) * n + m * t) - offset (m * d) v W (m * s) (m * t)) =
      (m * (2 ^ (v + W) * (d * n + s)),
        m * (2 ^ (v + W) * (d * n + t) - offset d v W s t))
    rw [hcoord, hcoord, offset_scaled, Nat.mul_sub_left_distrib]
    congr 1
    · ac_rfl
    · congr 1
      ac_rfl
  · simp only [choose, decide_eq_false h, Bool.false_eq_true, if_false]
    change
      (3 ^ v * ((m * d) * n + m * s) + offset (m * d) v W (m * s) (m * t),
        3 ^ v * ((m * d) * n + m * t)) =
      (m * (3 ^ v * (d * n + s) + offset d v W s t), m * (3 ^ v * (d * n + t)))
    rw [hcoord, hcoord, offset_scaled, Nat.mul_add m (3 ^ v * (d * n + s))
      (offset d v W s t)]
    congr 1
    · congr 1
      ac_rfl
    · ac_rfl

/-- Each old schedule embeds in every positive integer refinement of
its grid, with a common positive scaling of the product pair. -/
theorem Trace.refine {n d x s elapsed A B U D : Nat} (h : Trace n d x s elapsed A B U D)
    {m : Nat} (hm : 0 < m) :
    ∃ c, 0 < c ∧ Trace n (m * d) x (m * s) elapsed A B (c * U) (c * D) := by
  induction h with
  | start hs =>
    exact ⟨1, by decide, by simpa using (Trace.start (n := n) (Nat.mul_le_mul_left m hs))⟩
  | @step x y s t elapsed A B U D v u W _ hstep ht ih =>
    obtain ⟨c, hc, htrace⟩ := ih
    refine ⟨c * m, Nat.mul_pos hc hm, ?_⟩
    have hnext := Trace.step htrace hstep (Nat.mul_le_mul_left m ht)
    rw [choose_scaled] at hnext
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnext

/-- Refining a grid cannot lose an existing strict product crossing. -/
theorem Trace.refine_crossing {n d x s elapsed A B U D : Nat}
    (h : Trace n d x s elapsed A B U D) {m : Nat} (hm : 0 < m)
    (hcross : A * U < B * D) :
    ∃ U' D', Trace n (m * d) x (m * s) elapsed A B U' D' ∧ A * U' < B * D' := by
  obtain ⟨c, hc, htrace⟩ := h.refine hm
  refine ⟨c * U, c * D, htrace, ?_⟩
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_lt_mul_of_pos_left hcross hc

private def better (left right : Nat × Nat) : Nat × Nat :=
  if left.1 * right.2 ≤ right.1 * left.2 then left else right

private theorem fold_better_sound {P : Nat × Nat → Prop} {init : Nat × Nat}
    {values : List (Nat × Nat)} (hinit : P init) (hvalues : ∀ z ∈ values, P z) :
    P (values.foldl better init) := by
  induction values generalizing init with
  | nil => exact hinit
  | cons value values ih =>
    apply ih
    · unfold better
      split
      · exact hinit
      · exact hvalues value (List.mem_cons_self)
    · intro z hz
      exact hvalues z (List.mem_cons_of_mem _ hz)

/-- A nonempty finite set of permitted shifts in the common denominator.
The list may change between excursion boundaries. -/
structure Grid (d : Nat) where
  size : Nat
  shift : Fin (size + 1) → Nat
  bounded : ∀ s, shift s ≤ d

def Grid.uniform (d : Nat) : Grid d :=
  ⟨d, Fin.val, fun s => Nat.le_of_lt_succ s.isLt⟩

/-- A materialized vector retains a certified product for each permitted
shift, so later stages reuse the computed products. -/
structure Table (n d x elapsed A B : Nat) (grid : Grid d) where
  entries : Vector (Nat × Nat) (grid.size + 1)
  sound : ∀ s : Fin (grid.size + 1),
    Trace n d x (grid.shift s) elapsed A B (entries.get s).1 (entries.get s).2

def Table.start (n : Nat) {d : Nat} (grid : Grid d) : Table n d n 0 1 1 grid where
  entries := Vector.ofFn fun _ => (1, 1)
  sound := fun s => by
    simpa [Vector.get] using (Trace.start (n := n) (grid.bounded s))

/-- Compare incoming products for every target shift, with the local
factor choice shared across the whole excursion. -/
def Table.advance {n d x y elapsed A B v u W : Nat} {grid : Grid d}
    (table : Table n d x elapsed A B grid) (hstep : IsExcursion x v u W y)
    (target : Grid d := grid) :
    Table n d y (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W)) target := by
  let edge := choose n d v W
  let candidate (t : Fin (target.size + 1)) (s : Fin (grid.size + 1)) : Nat × Nat :=
    let previous := table.entries.get s
    let factor := edge (grid.shift s) (target.shift t)
    (previous.1 * factor.1, previous.2 * factor.2)
  let zero : Fin (grid.size + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let incoming := (List.finRange (grid.size + 1)).tail
  refine ⟨Vector.ofFn (fun t => (incoming.map (candidate t)).foldl better (candidate t zero)), ?_⟩
  intro t
  have hget (f : Fin (target.size + 1) → Nat × Nat) (s : Fin (target.size + 1)) :
      (Vector.ofFn f).get s = f s := by
    change (Vector.ofFn f)[s.val] = f s
    rw [Vector.getElem_ofFn]
  simp only [hget]
  let Valid (z : Nat × Nat) :=
    Trace n d y (target.shift t) (v + W + elapsed) (A * 3 ^ v) (B * 2 ^ (v + W)) z.1 z.2
  have hc (s : Fin (grid.size + 1)) : Valid (candidate t s) :=
    .step (table.sound s) hstep (target.bounded t)
  refine fold_better_sound (P := Valid) (hc zero) ?_
  intro z hz
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hz
  exact hc s

theorem Table.drop_by {n d x elapsed A B : Nat} {grid : Grid d}
    (table : Table n d x elapsed A B grid) (hn : 0 < n) (hd : 0 < d)
    (s : Fin (grid.size + 1))
    (hcross : A * (table.entries.get s).1 < B * (table.entries.get s).2) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n :=
  (table.sound s).drop_by hn hd hcross

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
/-- The eighth-unit table certifies a product below `1.0776` at the first
coefficient crossing of 63. The same table certifies a descent by step 54. -/
theorem sixty_three_eighth_grid :
    ∃ table : Table 63 8 61 54 16677181699666569 18014398509481984 (Grid.uniform 8),
      (table.entries.get ⟨8, by decide⟩).1 * 10000 <
        (table.entries.get ⟨8, by decide⟩).2 * 10776 ∧
      ∃ k, k ≤ 54 ∧ Collatz.acceleratedOrbit k 63 < 63 := by
  let t0 := Table.start 63 (Grid.uniform 8)
  let t1 := t0.advance (show IsExcursion 63 6 1 3 91 by unfold IsExcursion; decide)
  let t2 := t1.advance (show IsExcursion 91 2 23 1 103 by unfold IsExcursion; decide)
  let t3 := t2.advance (show IsExcursion 103 3 13 1 175 by unfold IsExcursion; decide)
  let t4 := t3.advance (show IsExcursion 175 4 11 1 445 by unfold IsExcursion; decide)
  let t5 := t4.advance (show IsExcursion 445 1 223 2 167 by unfold IsExcursion; decide)
  let t6 := t5.advance (show IsExcursion 167 3 21 1 283 by unfold IsExcursion; decide)
  let t7 := t6.advance (show IsExcursion 283 2 71 1 319 by unfold IsExcursion; decide)
  let t8 := t7.advance (show IsExcursion 319 6 5 2 911 by unfold IsExcursion; decide)
  let t9 := t8.advance (show IsExcursion 911 4 57 3 577 by unfold IsExcursion; decide)
  let t10 := t9.advance (show IsExcursion 577 1 289 1 433 by unfold IsExcursion; decide)
  let t11 := t10.advance (show IsExcursion 433 1 217 1 325 by unfold IsExcursion; decide)
  let t12 := t11.advance (show IsExcursion 325 1 163 3 61 by unfold IsExcursion; decide)
  exact ⟨t12, by decide, t12.drop_by (by decide) (by decide) ⟨8, by decide⟩ (by decide)⟩

private def thirdGrid : Grid 3 where
  size := 2
  shift := fun s => match s.val with
    | 0 => 0
    | 1 => 1
    | _ => 3
  bounded := by decide

private def oneTwentySevenTable {d : Nat} (grid : Grid d) :
    Table 127 d 77 15 19683 32768 grid :=
  let t0 := Table.start 127 grid
  let t1 := t0.advance (show IsExcursion 127 7 1 1 1093 by unfold IsExcursion; decide)
  let t2 := t1.advance (show IsExcursion 1093 1 547 3 205 by unfold IsExcursion; decide)
  t2.advance (show IsExcursion 205 1 103 2 77 by unfold IsExcursion; decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- On the first crossing of 127, the three shifts `0, 1/3, 1` give a
strictly tighter ceiling than every endpoint of the sixteenth-unit table. -/
theorem third_grid_beats_sixteenths :
    let sparse := (oneTwentySevenTable thirdGrid).entries.get ⟨0, by decide⟩
    let dense := (oneTwentySevenTable (Grid.uniform 16)).entries
    ∀ s : Fin 17, sparse.1 * (dense.get s).2 < (dense.get s).1 * sparse.2 := by
  decide

end Collatz.ExcursionShiftGrid
