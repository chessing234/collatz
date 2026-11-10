import Collatz.Strategy.ExcursionLocalAnchors

/-!
# Completeness of the excursion crossing criterion

A genuine prefix that reaches 1 can be extended along the excursion
from 1 back to 1. Each repetition reduces the product after it is scaled
by the homogeneous coefficient. This gives the converse to the
descent certificate and identifies the remaining universal statement.
-/

namespace Collatz.ExcursionAnchor

open Collatz.ExcursionMap

theorem OrbitWord.append {floor x y z t₁ t₂ A₁ A₂ B₁ B₂ left right}
    (hleft : OrbitWord floor x left y t₁ A₁ B₁)
    (hright : OrbitWord floor y right z t₂ A₂ B₂) :
    OrbitWord floor x (left ++ right) z (t₁ + t₂) (A₁ * A₂) (B₁ * B₂) := by
  induction hleft with
  | nil => simpa using hright
  | @cons x y v u W endpoint elapsed A B word hstep _ ih =>
    rw [show elapsed + (v + W) + t₂ = elapsed + t₂ + (v + W) by omega,
      Nat.mul_assoc, Nat.mul_assoc]
    exact .cons hstep (ih hright)

theorem OrbitWord.b_pos {floor x y t A B word} (h : OrbitWord floor x word y t A B) :
    0 < B := by
  induction h with
  | nil => decide
  | cons _ _ ih => exact Nat.mul_pos (Nat.two_pow_pos _) ih

private theorem excursion_prefix (floor k x : Nat) (hx : x % 2 = 1) :
    ∃ word y elapsed A B, OrbitWord floor x word y elapsed A B ∧ k ≤ elapsed ∧ y % 2 = 1 := by
  induction k generalizing x with
  | zero => exact ⟨[], x, 0, 1, 1, .nil, Nat.le_refl _, hx⟩
  | succ k ih =>
    obtain ⟨v, u, W, y, hstep⟩ := exists_excursion hx
    obtain ⟨word, z, elapsed, A, B, hword, htime, hz⟩ := ih y hstep.2.2.1
    have hv := hstep.2.2.2.1
    exact ⟨_, _, _, _, _, .cons hstep hword, by omega, hz⟩

private theorem one_orbit (k : Nat) (x : Nat) (hx : x = 1 ∨ x = 2) :
    acceleratedOrbit k x = 1 ∨ acceleratedOrbit k x = 2 := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    rw [acceleratedOrbit_succ]
    apply ih
    rcases hx with rfl | rfl
    · exact Or.inr acceleratedStep_one
    · exact Or.inl acceleratedStep_two

theorem OrbitWord.to_one {floor x k : Nat} (hx : x % 2 = 1)
    (hone : acceleratedOrbit k x = 1) :
    ∃ word elapsed A B, OrbitWord floor x word 1 elapsed A B := by
  obtain ⟨word, y, elapsed, A, B, h, hk, hy⟩ := excursion_prefix floor k x hx
  have hland := h.landing
  rw [← Nat.sub_add_cancel hk, ← acceleratedOrbit_add, hone] at hland
  rcases one_orbit (elapsed - k) 1 (Or.inl rfl) with h1 | h2
  · rw [h1] at hland
    exact ⟨word, elapsed, A, B, hland ▸ h⟩
  · rw [h2] at hland
    omega

private def loop (n : Nat) : Edge := Edge.ofRun n 1 1

private theorem loop_word (floor j : Nat) :
    OrbitWord floor 1 (List.replicate j (loop floor)) 1 (2 * j) (3 ^ j) (4 ^ j) := by
  induction j with
  | zero => exact .nil
  | succ j ih =>
    have step : IsExcursion 1 1 1 1 1 := by unfold IsExcursion; decide
    rw [List.replicate_succ, show 2 * (j + 1) = 2 * j + (1 + 1) by omega,
      Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_comm (4 ^ j) 4]
    exact .cons step ih

private def flatCost (p : Rat) : List Edge → Rat
  | [] => 1
  | e :: word => e.factor p p * flatCost p word

private def flatWeight (p : Rat) : List Edge → Rat
  | [] => 1
  | e :: word => (e.a / e.b * e.factor p p) * flatWeight p word

private theorem flatCost_schedule (p : Rat) (word : List Edge) :
    costOn word (p :: word.map (fun _ => p)) = flatCost p word := by
  induction word with
  | nil => rfl
  | cons e word ih => simp only [List.map_cons, costOn, flatCost, ih]

private theorem flat_band (p : Rat) (word : List Edge) :
    (Layout.ofSchedule p (word.map (fun e => (e, p)))).band p := by
  have hp : (⟨p, []⟩ : Component).band p := by
    intro q hq
    have he : q = p := by simpa [points] using hq
    rw [he]
    exact ⟨Rat.le_refl, by grind⟩
  induction word with
  | nil => exact hp
  | cons e rest ih => exact ⟨hp, ih⟩

private theorem anchorMinimum_le_flat {n : Nat} (hn : 0 < n) (word : List Edge) :
    ∃ best, anchorMinimum n word = some best ∧ best ≤ flatCost n word := by
  let steps := word.map (fun e => (e, (n : Rat)))
  let layout := Layout.ofSchedule n steps
  have hword : layout.word = word := by
    simp [layout, steps, Layout.ofSchedule_word, List.map_map, Function.comp_def]
  have hcoords : layout.coords = (n : Rat) :: word.map (fun _ => (n : Rat)) := by
    simp [layout, steps, Layout.ofSchedule_coords, List.map_map, Function.comp_def]
  have hband : layout.band n := flat_band n word
  obtain ⟨best, hbest, hle⟩ := layout.anchorMinimum_le (Rat.natCast_pos.mpr hn) hband
  rw [← layout.costOn_eq, hword, hcoords, flatCost_schedule] at hle
  rw [hword] at hbest
  exact ⟨best, hbest, hle⟩

private theorem OrbitWord.flatWeight_spec {n x y t A B word}
    (h : OrbitWord n x word y t A B) :
    (B : Rat) * flatWeight n word = (A : Rat) * flatCost n word := by
  induction h with
  | nil => rfl
  | @cons x y v u W z t A B word _ _ ih =>
    let e := Edge.ofRun n v W
    have ha : ((3 ^ v : Nat) : Rat) = e.a := rfl
    have hb : ((2 ^ (v + W) : Nat) : Rat) = e.b := rfl
    simp only [Rat.natCast_mul, ha, hb, flatCost, flatWeight]
    change e.b * (B : Rat) * ((e.a / e.b * e.factor n n) * flatWeight n word) =
      e.a * (A : Rat) * (e.factor n n * flatCost n word)
    have he := Rat.div_mul_cancel (a := e.a) (Rat.ne_of_gt e.b_pos)
    calc
      _ = (e.a / e.b * e.b) * e.factor n n * ((B : Rat) * flatWeight n word) := by grind
      _ = _ := by rw [he, ih]; grind

private theorem flatWeight_append (p : Rat) (left right : List Edge) :
    flatWeight p (left ++ right) = flatWeight p left * flatWeight p right := by
  induction left with
  | nil => simp [flatWeight, Rat.one_mul]
  | cons e word ih => simp [flatWeight, ih, Rat.mul_assoc]

private def loopWeight (n : Nat) : Rat := (loop n).a / (loop n).b * (loop n).factor n n

private theorem flatWeight_loop (n j : Nat) :
    flatWeight n (List.replicate j (loop n)) = loopWeight n ^ j := by
  induction j with
  | zero => exact (Rat.pow_zero _).symm
  | succ j ih => rw [List.replicate_succ, flatWeight, Rat.pow_succ, ← ih, Rat.mul_comm, loopWeight]

private theorem loopWeight_formula {n : Nat} (hn : 1 < n) :
    loopWeight n = 3 * (n : Rat) / (4 * (n : Rat) - 1) := by
  let e := loop n
  have ha : e.a = 3 := rfl
  have hb : e.b = 4 := rfl
  have hd : e.drift = (n : Rat) - 1 := by
    change 4 * (n : Rat) + 2 - 3 * ((n : Rat) + 1) = _
    grind
  have hn' : (1 : Rat) < n := Rat.natCast_lt_natCast.mpr hn
  have hpos : (0 : Rat) < n := by grind
  have hd' : 0 ≤ e.drift := by rw [hd]; grind
  have hclip : e.a * (n : Rat) + e.drift ≤ e.b * (n : Rat) := by rw [ha, hb, hd]; grind
  have hden : (0 : Rat) < 4 * (n : Rat) - 1 := by grind
  have hden' : 3 * (n : Rat) + ((n : Rat) - 1) = 4 * (n : Rat) - 1 := by grind
  change e.a / e.b * e.factor n n = _
  rw [e.factor_of_unclipped hpos hpos hclip, if_pos hd', ha, hb, hd, hden']
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : (4 : Rat) * (4 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ (by decide +kernel)
  calc
    _ = (3 * (n : Rat)) * (4 * (n : Rat) - 1)⁻¹ * (4 * (4 : Rat)⁻¹) := by grind
    _ = _ := by rw [hcancel, Rat.mul_one]

private theorem loopWeight_pos_lt_one {n : Nat} (hn : 1 < n) :
    0 < loopWeight n ∧ loopWeight n < 1 := by
  rw [loopWeight_formula hn]
  have h : (1 : Rat) < n := Rat.natCast_lt_natCast.mpr hn
  have hd : (0 : Rat) < 4 * (n : Rat) - 1 := by grind
  constructor
  · rw [Rat.div_def]; exact Rat.mul_pos (by grind) (Rat.inv_pos.mpr hd)
  · rw [Rat.div_lt_iff hd, Rat.one_mul]
    grind

private theorem bernoulli {q : Rat} (hq : 1 ≤ q) (j : Nat) :
    1 + (j : Rat) * (q - 1) ≤ q ^ j := by
  induction j with
  | zero =>
    change 1 + 0 * (q - 1) ≤ q ^ 0
    rw [Rat.zero_mul, Rat.add_zero, Rat.pow_zero]
    exact Rat.le_refl
  | succ j ih =>
    have hj : (0 : Rat) ≤ j := Rat.natCast_nonneg
    have hq' : 0 ≤ q - 1 := by grind
    have hq'' : 0 ≤ q := by grind
    have hm := Rat.mul_nonneg hj (Rat.mul_nonneg hq' hq')
    rw [Rat.natCast_add, Rat.pow_succ]
    change 1 + ((j : Rat) + 1) * (q - 1) ≤ _
    calc
      _ ≤ (1 + (j : Rat) * (q - 1)) * q := by grind
      _ ≤ q ^ j * q := Rat.mul_le_mul_of_nonneg_right ih hq''

private theorem exists_nat_gt (r : Rat) : ∃ j : Nat, r < (j : Rat) := by
  let j := r.ceil.toNat
  have h := Rat.le_ceil (x := r)
  have hj : r.ceil ≤ (j : Int) := by omega
  have hj' := Rat.intCast_le_intCast.mpr hj
  have : r ≤ (j : Rat) := Rat.le_trans h hj'
  refine ⟨j + 1, ?_⟩
  rw [Rat.natCast_add]
  change r < (j : Rat) + 1
  grind

private theorem eventually_scaled_lt_one {r : Rat} (hr : 0 < r) (hr' : r < 1) (C : Rat) :
    ∃ j : Nat, C * r ^ j < 1 := by
  let q := r⁻¹
  have hq : 1 < q := by
    have h : (1 : Rat) < 1 / r := (Rat.lt_div_iff hr).mpr (by simpa [Rat.one_mul] using hr')
    simpa [q, Rat.div_def, Rat.one_mul] using h
  have hgap : 0 < q - 1 := by grind
  have hcancel (j : Nat) : q ^ j * r ^ j = 1 := by
    induction j with
    | zero => rw [Rat.pow_zero, Rat.pow_zero, Rat.one_mul]
    | succ j ih =>
      have hqr : q * r = 1 := Rat.inv_mul_cancel r (Rat.ne_of_gt hr)
      rw [Rat.pow_succ, Rat.pow_succ]
      calc
        _ = (q ^ j * r ^ j) * (q * r) := by grind
        _ = _ := by rw [ih, hqr, Rat.one_mul]
  obtain ⟨j, hj⟩ := exists_nat_gt ((C - 1) / (q - 1))
  rw [Rat.div_lt_iff hgap] at hj
  have hC : C < 1 + (j : Rat) * (q - 1) := by grind
  have hbound : C < q ^ j := by have h := bernoulli (Rat.le_of_lt hq) j; grind
  have hpow : 0 < r ^ j := Rat.pow_pos hr
  refine ⟨j, ?_⟩
  rw [← hcancel j]
  exact Rat.mul_lt_mul_of_pos_right hbound hpow

/-- After an odd start reaches 1, enough copies of the (1\to1) excursion
give a strict crossing, even using the constant floor coordinate. -/
theorem OrbitWord.crossing_of_lands_one {n t A B word}
    (h : OrbitWord n n word 1 t A B) (hn : 1 < n) :
    ∃ word' elapsed A' B' best,
      OrbitWord n n word' 1 elapsed A' B' ∧
      localMinimum n word' = some best ∧ (A' : Rat) * best < (B' : Rat) := by
  obtain ⟨hpos, hlt⟩ := loopWeight_pos_lt_one hn
  obtain ⟨j, hj⟩ := eventually_scaled_lt_one hpos hlt (flatWeight n word)
  let word' := word ++ List.replicate j (loop n)
  have trace := h.append (loop_word n j)
  have hword : flatWeight n word' < 1 := by
    change flatWeight n (word ++ List.replicate j (loop n)) < 1
    rw [flatWeight_append, flatWeight_loop]
    exact hj
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_flat (by omega : 0 < n) word'
  rw [← localMinimum_eq_anchorMinimum trace.alphabet] at hbest
  refine ⟨word', _, _, _, best, trace, hbest, ?_⟩
  have hB := Rat.natCast_pos.mpr trace.b_pos
  have hstrict := Rat.mul_lt_mul_of_pos_left hword hB
  rw [trace.flatWeight_spec, Rat.mul_one] at hstrict
  have hbound := Rat.mul_le_mul_of_nonneg_left hle (Rat.natCast_nonneg (a := A * 3 ^ j))
  grind

/-- The universal strict crossing condition is equivalent to the Collatz
conjecture. The reverse implication extends a prefix along the trivial
cycle, while the forward implication uses descent induction. -/
theorem collatz_iff_local_crossings :
    CollatzConjecture ↔ ∀ n : Nat, 1 < n → n % 4 = 3 →
      ∃ word endpoint elapsed A B best,
        OrbitWord n n word endpoint elapsed A B ∧
        localMinimum n word = some best ∧ (A : Rat) * best < (B : Rat) := by
  constructor
  · intro collatz n hn hmod
    have hpos : 0 < n := by omega
    obtain ⟨j, hj⟩ := collatz n hpos
    obtain ⟨k, hk⟩ := Collatz.NeverDrops.accReachesOne_of_orbit j n hpos hj
    obtain ⟨word, elapsed, A, B, trace⟩ := OrbitWord.to_one (floor := n) (by omega) hk
    obtain ⟨word', t, A', B', best, trace', hbest, hcross⟩ := trace.crossing_of_lands_one hn
    exact ⟨word', 1, t, A', B', best, trace', hbest, hcross⟩
  · intro crossings
    apply collatz_of_anchor_crossings
    intro n hn hmod
    obtain ⟨word, endpoint, t, A, B, best, trace, hbest, hcross⟩ := crossings n hn hmod
    rw [localMinimum_eq_anchorMinimum trace.alphabet] at hbest
    exact ⟨word, endpoint, t, A, B, best, trace, hbest, hcross⟩

end Collatz.ExcursionAnchor
