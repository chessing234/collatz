import Collatz.Strategy.ExcursionAnchorSearch
import Collatz.Strategy.ExcursionSwitchFloor

/-!
# Descent from the optimal rational shift product

The finite search depends only on the excursion word and the proposed
orbit floor. If the inverse coefficient exceeds its returned product,
the actual accelerated orbit has a value below that floor.
-/

namespace Collatz.ExcursionAnchor

open Collatz.ExcursionMap

/-- The affine edge in the normalized coordinates at a proposed floor. -/
def Edge.ofRun (floor v W : Nat) : Edge :=
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  ⟨a, b, b * (floor : Rat) + ((2 : Nat) ^ v : Nat) - a * ((floor : Rat) + 1),
    Rat.natCast_pos.mpr (Nat.pow_pos (by decide)), Rat.natCast_pos.mpr (Nat.two_pow_pos _)⟩

private theorem Edge.normalized_bound (e : Edge) {P Q X Y : Rat}
    (hP : 0 < P) (hQ : 0 < Q) (hx : P ≤ X) (hy : Q ≤ Y)
    (h : e.b * Y = e.a * X + (e.b * Q - e.a * P - e.drift)) :
    e.b * (Y / Q) ≤ e.a * e.factor P Q * (X / P) := by
  have hl : e.b * (Y / Q) = (e.b * Y) / Q := by
    simp only [Rat.div_def]
    grind
  have hr : e.a * e.factor P Q * (X / P) = (e.a * e.factor P Q * X) / P := by
    simp only [Rat.div_def]
    grind
  rw [hl, hr, div_le_div_iff_pos hQ hP]
  by_cases hc : e.b * Q ≤ e.a * P + e.drift
  · rw [e.factor_of_clipped hc]
    have hdrop : e.b * Y ≤ e.a * X := by grind
    have hcancel := Rat.div_mul_cancel (a := P) (Rat.ne_of_gt hQ)
    calc
      _ ≤ e.a * X * P := Rat.mul_le_mul_of_nonneg_right hdrop (Rat.le_of_lt hP)
      _ = e.a * X * (P / Q * Q) := by rw [hcancel]
      _ = _ := by grind
  · have hu := Rat.le_of_lt ((Rat.not_le).mp hc)
    rw [e.factor_of_unclipped hP hQ hu]
    let offset := e.b * Q - e.a * P - e.drift
    have he : 0 ≤ offset := by dsimp [offset]; grind
    have hlocal : e.b * Y = e.a * X + offset := h
    split
    · rename_i hd
      let R := e.a * P + e.drift
      have hR : 0 < R := by
        have := Rat.mul_pos e.a_pos hP
        dsimp [R]
        grind
      have heq : R * Y + offset * Y = e.b * Y * Q := by
        dsimp [R, offset]
        grind
      have hscaled : e.b * Y * Q = e.a * X * Q + offset * Q := by
        rw [hlocal, Rat.add_mul]
      have hbudget : R * Y ≤ e.a * X * Q := by
        have hcost := Rat.mul_le_mul_of_nonneg_left hy he
        grind
      have hpos := Rat.mul_pos e.b_pos hP
      have hcancel := Rat.div_mul_cancel (a := e.b * P) (Rat.ne_of_gt hR)
      apply Rat.le_of_mul_le_mul_right _ hR
      calc
        _ = (e.b * P) * (R * Y) := by grind
        _ ≤ (e.b * P) * (e.a * X * Q) :=
          Rat.mul_le_mul_of_nonneg_left hbudget (Rat.le_of_lt hpos)
        _ = (e.b * P / R * R) * (e.a * X * Q) := by rw [hcancel]
        _ = _ := by grind
    · let R := e.b * Q - e.drift
      have hbudget : e.b * Y * P ≤ R * X := by
        have hcost := Rat.mul_le_mul_of_nonneg_left hx he
        have hleft : e.b * Y * P = e.a * X * P + offset * P := by
          rw [hlocal, Rat.add_mul]
        have hright : R * X = e.a * X * P + offset * X := by
          dsimp [R, offset]
          grind
        grind
      have hcancel := Rat.div_mul_cancel (a := R) (Rat.ne_of_gt (Rat.mul_pos e.a_pos hQ))
      calc
        _ ≤ R * X := hbudget
        _ = (R / (e.a * Q) * (e.a * Q)) * X := by rw [hcancel]
        _ = _ := by grind

private def normalized (floor x : Nat) (p : Rat) : Rat :=
  ((x : Rat) + p - (floor : Rat)) / p

private theorem step_normalized_bound {floor x y v u W : Nat} {P Q : Rat}
    (h : IsExcursion x v u W y) (hn : 0 < floor)
    (hP : (floor : Rat) ≤ P) (hQ : (floor : Rat) ≤ Q)
    (hx : floor ≤ x) (hy : floor ≤ y) :
    (Edge.ofRun floor v W).b * normalized floor y Q ≤
      (Edge.ofRun floor v W).a * (Edge.ofRun floor v W).factor P Q * normalized floor x P := by
  let e := Edge.ofRun floor v W
  have hn' : (0 : Rat) < floor := Rat.natCast_pos.mpr hn
  have hP' : 0 < P := by grind
  have hQ' : 0 < Q := by grind
  have hx' : (floor : Rat) ≤ x := Rat.natCast_le_natCast.mpr hx
  have hy' : (floor : Rat) ≤ y := Rat.natCast_le_natCast.mpr hy
  have hraw := congrArg (fun k : Nat => (k : Rat))
    (Collatz.ExcursionSwitchFloor.affine_source_succ h)
  simp only [Rat.natCast_mul, Rat.natCast_add] at hraw
  apply Edge.normalized_bound e hP' hQ' (by grind) (by grind)
  dsimp [e, Edge.ofRun]
  grind

/-- A word of genuine excursions, with its actual endpoint, elapsed
accelerated time, and homogeneous coefficient products. -/
inductive OrbitWord (floor : Nat) : Nat → List Edge → Nat → Nat → Nat → Nat → Prop where
  | nil {x : Nat} : OrbitWord floor x [] x 0 1 1
  | cons {x y v u W endpoint elapsed A B : Nat} {word : List Edge} :
      IsExcursion x v u W y →
      OrbitWord floor y word endpoint elapsed A B →
      OrbitWord floor x (Edge.ofRun floor v W :: word) endpoint (elapsed + (v + W))
        (3 ^ v * A) (2 ^ (v + W) * B)

theorem OrbitWord.landing {floor x endpoint elapsed A B word}
    (h : OrbitWord floor x word endpoint elapsed A B) :
    Collatz.acceleratedOrbit elapsed x = endpoint := by
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
    rw [← Collatz.acceleratedOrbit_add, landing_eq hstep, ih]

private theorem costOn_nonneg (word : List Edge) (coords : List Rat)
    (h : ∀ p ∈ coords, 0 < p) : 0 ≤ costOn word coords := by
  induction word generalizing coords with
  | nil => exact (by decide : (0 : Rat) ≤ 1)
  | cons e rest ih =>
    cases coords with
    | nil => exact (by decide : (0 : Rat) ≤ 1)
    | cons p coords =>
      cases coords with
      | nil => exact (by decide : (0 : Rat) ≤ 1)
      | cons q tail =>
        exact Rat.mul_nonneg (Rat.le_of_lt (e.factor_pos (h p List.mem_cons_self)
          (h q (List.mem_cons_of_mem _ List.mem_cons_self))))
          (ih (q :: tail) (fun p hp => h p (List.mem_cons_of_mem _ hp)))

private theorem OrbitWord.floor_product {floor x endpoint elapsed A B word}
    (h : OrbitWord floor x word endpoint elapsed A B) (hn : 0 < floor)
    (p : Rat) (rest : List Rat) (hlen : rest.length = word.length)
    (hcoords : ∀ q ∈ p :: rest, (floor : Rat) ≤ q)
    (hfloor : ∀ k, k ≤ elapsed → floor ≤ Collatz.acceleratedOrbit k x) :
    (B : Rat) * normalized floor endpoint (rest.getLastD p) ≤
      (A : Rat) * costOn word (p :: rest) * normalized floor x p := by
  induction h generalizing p rest with
  | nil =>
    have hr : rest = [] := List.length_eq_zero_iff.mp hlen
    subst rest
    change 1 * normalized _ _ _ ≤ 1 * 1 * normalized _ _ _
    simp only [Rat.one_mul]
    exact Rat.le_refl
  | @cons x y v u W endpoint elapsed A B word hstep hword ih =>
    cases rest with
    | nil => simp at hlen
    | cons q rest =>
      have hrestLen : rest.length = word.length := by simpa using hlen
      have hx : floor ≤ x := hfloor 0 (Nat.zero_le _)
      have hy := hfloor (v + W) (by omega)
      rw [landing_eq hstep] at hy
      have htail (k : Nat) (hk : k ≤ elapsed) :
          floor ≤ Collatz.acceleratedOrbit k y := by
        have hbound := hfloor (k + (v + W)) (by omega)
        rwa [← Collatz.acceleratedOrbit_add, landing_eq hstep] at hbound
      have hcoords' (r : Rat) (hr : r ∈ q :: rest) : (floor : Rat) ≤ r :=
        hcoords r (List.mem_cons_of_mem _ hr)
      have hprefix := ih q rest hrestLen hcoords' htail
      have hlocal := step_normalized_bound hstep hn (hcoords p List.mem_cons_self)
        (hcoords' q List.mem_cons_self) hx hy
      let e := Edge.ofRun floor v W
      let C := costOn word (q :: rest)
      have hC : 0 ≤ C := costOn_nonneg word (q :: rest) (fun r hr => by
        have hf : (0 : Rat) < floor := Rat.natCast_pos.mpr hn
        have hh := hcoords' r hr
        grind)
      have ha : (0 : Rat) ≤ A := Rat.natCast_nonneg
      simp only [Rat.natCast_mul, List.getLastD_cons, costOn]
      calc
        _ = e.b * ((B : Rat) * normalized floor endpoint (rest.getLastD q)) := by
          unfold e Edge.ofRun
          grind
        _ ≤ e.b * ((A : Rat) * C * normalized floor y q) :=
          Rat.mul_le_mul_of_nonneg_left hprefix (Rat.le_of_lt e.b_pos)
        _ = ((A : Rat) * C) * (e.b * normalized floor y q) := by grind
        _ ≤ ((A : Rat) * C) * (e.a * e.factor p q * normalized floor x p) :=
          Rat.mul_le_mul_of_nonneg_left hlocal (Rat.mul_nonneg ha hC)
        _ = _ := by unfold e Edge.ofRun; grind

private theorem Permitted.word_length {word layers p rest} (h : Permitted word layers p rest) :
    rest.length = word.length := by
  induction h with
  | last _ => rfl
  | more _ _ ih => simp [ih]

private theorem Permitted.coordinate_member {word layers p rest} (h : Permitted word layers p rest) :
    ∀ q ∈ p :: rest, ∃ layer ∈ layers, q ∈ layer := by
  induction h with
  | @last choices p hp =>
    intro q hq
    have he : q = p := by simpa using hq
    subst q
    exact ⟨choices, List.mem_cons_self, hp⟩
  | @more e word choices later p q rest hp _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      exact ⟨choices, List.mem_cons_self, hp⟩
    · obtain ⟨layer, hl, hm⟩ := ih r hr
      exact ⟨layer, List.mem_cons_of_mem _ hl, hm⟩

/-- The exact rational minimum certifies descent if it is strictly below
the inverse homogeneous coefficient of the genuine excursion word. -/
theorem OrbitWord.drop_of_anchorMinimum {n endpoint elapsed A B word result}
    (h : OrbitWord n n word endpoint elapsed A B) (hn : 0 < n)
    (hbest : anchorMinimum n word = some result) (hcross : (A : Rat) * result < (B : Rat)) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n := by
  apply Classical.byContradiction
  intro hnone
  have hfloor (k : Nat) (hk : k ≤ elapsed) : n ≤ Collatz.acceleratedOrbit k n := by
    apply Nat.le_of_not_gt
    intro hdrop
    exact hnone ⟨k, hk, hdrop⟩
  obtain ⟨p, rest, hperm, hcost⟩ := anchorMinimum_attained hbest
  have hcoords (q : Rat) (hq : q ∈ p :: rest) : (n : Rat) ≤ q := by
    obtain ⟨layer, hl, hm⟩ := hperm.coordinate_member q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact (mem_anchorCandidates_iff.mp hm).1.1
  have hproduct := h.floor_product hn p rest hperm.word_length hcoords hfloor
  rw [hcost] at hproduct
  have hnrat : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hp : 0 < p := by
    have hh := hcoords p List.mem_cons_self
    grind
  have hnorm : normalized n n p = 1 := by
    have he : (n : Rat) + p - (n : Rat) = p := by grind
    unfold normalized
    rw [he, Rat.div_def, Rat.mul_inv_cancel p (Rat.ne_of_gt hp)]
  rw [hnorm, Rat.mul_one] at hproduct
  let q := rest.getLastD p
  have hq : 0 < q := by
    have hh := hcoords q List.getLastD_mem_cons
    grind
  have hx := hfloor elapsed (Nat.le_refl _)
  rw [h.landing] at hx
  have hx' : (n : Rat) ≤ endpoint := Rat.natCast_le_natCast.mpr hx
  have hqnorm : 1 ≤ normalized n endpoint q := by
    have hnum : q ≤ (endpoint : Rat) + q - (n : Rat) := by grind
    have hd := Rat.mul_le_mul_of_nonneg_right hnum (Rat.le_of_lt (Rat.inv_pos.mpr hq))
    rw [Rat.mul_inv_cancel q (Rat.ne_of_gt hq)] at hd
    exact hd
  have hB := Rat.mul_le_mul_of_nonneg_left hqnorm (Rat.natCast_nonneg (a := B))
  rw [Rat.mul_one] at hB
  have hcontra := Rat.le_trans hB hproduct
  exact ((Rat.not_lt).mpr hcontra) hcross

/-- The remaining universal condition can be restricted to starts
congruent to three modulo four. -/
theorem collatz_of_anchor_crossings
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 →
      ∃ word endpoint elapsed A B result,
        OrbitWord n n word endpoint elapsed A B ∧
        anchorMinimum n word = some result ∧ (A : Rat) * result < (B : Rat)) :
    CollatzConjecture := by
  apply collatz_of_three_mod_four
  intro n hn hmod
  obtain ⟨word, endpoint, elapsed, A, B, result, hword, hbest, hcross⟩ := h n hn hmod
  obtain ⟨k, _, hdrop⟩ := hword.drop_of_anchorMinimum (by omega) hbest hcross
  exact ⟨k, hdrop⟩

private def word127 : List Edge :=
  [Edge.ofRun 127 7 1, Edge.ofRun 127 1 3, Edge.ofRun 127 1 2]

/-- The anchor search computes the exact rational optimum on the first
excursion coefficient crossing of 127. -/
theorem minimum_127 : anchorMinimum 127 word127 = some (1343488 / 1331883) := by
  decide +kernel

/-- The optimal rational product certifies a descent from 127 within
15 accelerated steps. -/
theorem drop_127 : ∃ k, k ≤ 15 ∧ Collatz.acceleratedOrbit k 127 < 127 := by
  have htrace : OrbitWord 127 127 word127 77 15 19683 32768 :=
    .cons (show IsExcursion 127 7 1 1 1093 by unfold IsExcursion; decide)
      (.cons (show IsExcursion 1093 1 547 3 205 by unfold IsExcursion; decide)
        (.cons (show IsExcursion 205 1 103 2 77 by unfold IsExcursion; decide) .nil))
  exact htrace.drop_of_anchorMinimum (by decide) minimum_127 (by decide +kernel)

end Collatz.ExcursionAnchor
