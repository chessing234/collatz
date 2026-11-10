import Collatz.Strategy.ExcursionSignSplit

/-!
# Exact two-edge conflict at a drift sign reversal

The factor is nondecreasing in its source shift and nonincreasing in
its target shift. For a negative-drift edge followed by a nonnegative
one, the two outer shifts can therefore be placed at opposite band
endpoints. With those shifts fixed, the remaining cost is a quotient
of affine functions in the common shift.
-/

namespace Collatz.ExcursionAnchor

theorem Edge.factor_ge_ratio (e : Edge) {p q : Rat} (hp : 0 < p) (hq : 0 < q) :
    p / q ≤ e.factor p q := by
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc]
    exact Rat.le_refl
  · have hu := Rat.le_of_lt ((Rat.not_le).mp hc)
    rw [e.factor_of_unclipped hp hq hu]
    split
    · rename_i hd
      have hden : 0 < e.a * p + e.drift := by
        have h := Rat.mul_pos e.a_pos hp
        grind
      rw [div_le_div_iff_pos hq hden]
      have hs := Rat.mul_le_mul_of_nonneg_left hu (Rat.le_of_lt hp)
      grind
    · rw [div_le_div_iff_pos hq (Rat.mul_pos e.a_pos hq)]
      have h : e.a * p ≤ e.b * q - e.drift := by grind
      have hs := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hq)
      grind

/-- Decreasing the source shift can only improve an individual factor. -/
theorem Edge.factor_mono_source (e : Edge) {p P q : Rat} (hp : 0 < p) (h : p ≤ P)
    (hq : 0 < q) : e.factor p q ≤ e.factor P q := by
  have hP : 0 < P := by grind
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc]
    apply Rat.le_trans _ (e.factor_ge_ratio hP hq)
    rw [div_le_div_iff_pos hq hq]
    exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hq)
  · rw [e.factor_of_unclipped hp hq (Rat.le_of_lt ((Rat.not_le).mp hc))]
    split
    · rename_i hd
      exact e.factor_ge_arrival_at hp h hq hd
    · rename_i hd
      exact e.factor_ge_departure_at hP hq Rat.le_refl ((Rat.not_le).mp hd)

/-- Increasing the target shift can only improve an individual factor. -/
theorem Edge.factor_antitone_target (e : Edge) {p q Q : Rat} (hp : 0 < p)
    (hq : 0 < q) (h : q ≤ Q) : e.factor p Q ≤ e.factor p q := by
  have hQ : 0 < Q := by grind
  by_cases hc : e.b * Q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc]
    apply Rat.le_trans _ (e.factor_ge_ratio hp hq)
    rw [div_le_div_iff_pos hQ hq]
    exact Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hp)
  · rw [e.factor_of_unclipped hp hQ (Rat.le_of_lt ((Rat.not_le).mp hc))]
    split
    · rename_i hd
      exact e.factor_ge_arrival_at hp Rat.le_refl hq hd
    · rename_i hd
      exact e.factor_ge_departure_at hp hq h ((Rat.not_le).mp hd)

private theorem ofRun_unclipped_at_floor {n v W : Nat} {q : Rat} (hq : (n : Rat) ≤ q) :
    (Edge.ofRun n v W).a * (n : Rat) + (Edge.ofRun n v W).drift ≤
      (Edge.ofRun n v W).b * q := by
  let e := Edge.ofRun n v W
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hca : c ≤ e.a := Rat.natCast_le_natCast.mpr (Collatz.Arith.two_pow_le_three_pow v)
  have hd : e.drift = e.b * (n : Rat) + c - e.a * ((n : Rat) + 1) := rfl
  have hscaled := Rat.mul_le_mul_of_nonneg_left hq (Rat.le_of_lt e.b_pos)
  change e.a * (n : Rat) + e.drift ≤ e.b * q
  rw [hd]
  grind

private theorem ofRun_unclipped_at_ceiling {n v W : Nat} {p : Rat} (hp : p ≤ (n : Rat) + 1) :
    (Edge.ofRun n v W).a * p + (Edge.ofRun n v W).drift ≤
      (Edge.ofRun n v W).b * ((n : Rat) + 1) := by
  let e := Edge.ofRun n v W
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hcb : c ≤ e.b := Rat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : e.drift = e.b * (n : Rat) + c - e.a * ((n : Rat) + 1) := rfl
  have hscaled := Rat.mul_le_mul_of_nonneg_left hp (Rat.le_of_lt e.a_pos)
  change e.a * p + e.drift ≤ e.b * ((n : Rat) + 1)
  rw [hd]
  grind

private theorem pair_cost_formula {n v W v' W' : Nat} (hn : 0 < n)
    (hd : (Edge.ofRun n v W).drift < 0) (hd' : 0 ≤ (Edge.ofRun n v' W').drift)
    {q : Rat} (hq : (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    let e := Edge.ofRun n v W
    let f := Edge.ofRun n v' W'
    costOn [e, f] [(n : Rat), q, (n : Rat) + 1] =
      (f.b / e.a) * ((e.b * q - e.drift) / (f.a * q + f.drift)) := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let top := (n : Rat) + 1
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hq' : 0 < q := by have := hq.1; grind
  have htop : 0 < top := by dsimp [top]; grind
  have he := e.factor_of_unclipped hn' hq' (ofRun_unclipped_at_floor (v := v) (W := W) hq.1)
  have hf := f.factor_of_unclipped hq' htop (ofRun_unclipped_at_ceiling (v := v') (W := W') hq.2)
  change e.factor n q * (f.factor q top * 1) = _
  rw [Rat.mul_one, he, hf, if_neg ((Rat.not_le).mpr hd), if_pos hd']
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have hc := Rat.inv_mul_cancel q (Rat.ne_of_gt hq')
  calc
    _ = (f.b * e.a⁻¹) * ((e.b * q - e.drift) * (f.a * q + f.drift)⁻¹) *
        (q⁻¹ * q) := by grind
    _ = _ := by rw [hc, Rat.mul_one]

/-- A pair in the conflicting drift order attains its exact minimum
on one of the two schedules whose outer coordinates are the band
endpoints and whose common coordinate is also an endpoint. -/
theorem anchorMinimum_pair_of_sign {n v W v' W' : Nat} (hn : 0 < n)
    (hd : (Edge.ofRun n v W).drift < 0) (hd' : 0 ≤ (Edge.ofRun n v' W').drift) :
    let word := [Edge.ofRun n v W, Edge.ofRun n v' W']
    let bottom := costOn word [(n : Rat), (n : Rat), (n : Rat) + 1]
    let top := costOn word [(n : Rat), (n : Rat) + 1, (n : Rat) + 1]
    anchorMinimum n word = some (min bottom top) := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let floor : Rat := n
  let ceiling := floor + 1
  let word := [e, f]
  let bottom := costOn word [floor, floor, ceiling]
  let top := costOn word [floor, ceiling, ceiling]
  have hf : 0 < floor := Rat.natCast_pos.mpr hn
  have hfc : floor ≤ ceiling := by dsimp [ceiling]; grind
  have hc : 0 < ceiling := by grind
  have hband₁ (q : Rat) (hq : q ∈ [floor, floor, ceiling]) :
      floor ≤ q ∧ q ≤ ceiling := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact ⟨by grind, by grind⟩
  have hband₂ (q : Rat) (hq : q ∈ [floor, ceiling, ceiling]) :
      floor ≤ q ∧ q ≤ ceiling := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact ⟨by grind, by grind⟩
  obtain ⟨best, hbest, hbottom⟩ := anchorMinimum_le_schedule (word := word) hf rfl hband₁
  obtain ⟨best', hbest', htop⟩ := anchorMinimum_le_schedule (word := word) hf rfl hband₂
  rw [hbest] at hbest'
  obtain rfl := Option.some.inj hbest'
  obtain ⟨p, rest, hlen, hband, hcost⟩ := anchorMinimum_attained_in_band hbest
  have ht : rest.length = 2 := hlen
  have hex : ∃ q r, rest = [q, r] := by
    cases rest with
    | nil => simp at ht
    | cons q rest =>
      cases rest with
      | nil => simp at ht
      | cons r rest =>
        have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using ht)
        exact ⟨q, r, by rw [hr]⟩
  obtain ⟨q, r, rfl⟩ := hex
  have hp := hband p List.mem_cons_self
  have hq := hband q (by simp)
  have hr := hband r (by simp)
  have hq' : 0 < q := by have := hq.1; grind
  have he := e.factor_mono_source hf hp.1 hq'
  have hg := f.factor_antitone_target hq' (by have := hr.1; grind : 0 < r) hr.2
  have he0 : 0 ≤ e.factor p q := Rat.le_of_lt (e.factor_pos (by have := hp.1; grind) hq')
  have hg0 : 0 ≤ f.factor q ceiling := Rat.le_of_lt (f.factor_pos hq' hc)
  have hclamp : costOn word [floor, q, ceiling] ≤ best := by
    rw [← hcost]
    simp only [word, costOn, Rat.mul_one]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right he hg0)
      (Rat.mul_le_mul_of_nonneg_left hg he0)
  have hden (s : Rat) (hs : 0 < s) : 0 < f.a * s + f.drift := by
    have h := Rat.mul_pos f.a_pos hs
    change 0 ≤ f.drift at hd'
    grind
  have hfrac := affine_ratio_end (a := e.b) (b := -e.drift) (c := f.a) (d := f.drift)
    hq.1 hq.2 (hden floor hf) (hden q hq') (hden ceiling hc)
  have hcoeff : 0 ≤ f.b / e.a := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt f.b_pos) (Rat.le_of_lt (Rat.inv_pos.mpr e.a_pos))
  have hbase := pair_cost_formula hn hd hd' (q := floor) ⟨Rat.le_refl, hfc⟩
  have hmid := pair_cost_formula hn hd hd' hq
  have hceil := pair_cost_formula hn hd hd' (q := ceiling) ⟨hfc, Rat.le_refl⟩
  have hchoice : bottom ≤ best ∨ top ≤ best := by
    rcases hfrac with h | h
    · apply Or.inl
      apply Rat.le_trans _ hclamp
      change costOn word [floor, floor, ceiling] ≤ costOn word [floor, q, ceiling]
      rw [hbase, hmid]
      apply Rat.mul_le_mul_of_nonneg_left _ hcoeff
      simpa only [Rat.sub_eq_add_neg] using h
    · apply Or.inr
      apply Rat.le_trans _ hclamp
      change costOn word [floor, ceiling, ceiling] ≤ costOn word [floor, q, ceiling]
      rw [hceil, hmid]
      apply Rat.mul_le_mul_of_nonneg_left _ hcoeff
      simpa only [Rat.sub_eq_add_neg] using h
  have heq : best = min bottom top := by
    change best ≤ bottom at hbottom
    change best ≤ top at htop
    rw [Rat.min_def]
    split
    · grind
    · grind
  change anchorMinimum n word = some (min bottom top)
  rwa [heq] at hbest

/-- One determinant determines which endpoint is optimal. A zero
determinant gives the same product at both endpoints. -/
theorem pair_lower_le_upper_iff {n v W v' W' : Nat} (hn : 0 < n)
    (hd : (Edge.ofRun n v W).drift < 0) (hd' : 0 ≤ (Edge.ofRun n v' W').drift) :
    let e := Edge.ofRun n v W
    let f := Edge.ofRun n v' W'
    let word := [e, f]
    costOn word [(n : Rat), (n : Rat), (n : Rat) + 1] ≤
      costOn word [(n : Rat), (n : Rat) + 1, (n : Rat) + 1] ↔
      0 ≤ e.b * f.drift + f.a * e.drift := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let floor : Rat := n
  let top := floor + 1
  have hn' : 0 < floor := Rat.natCast_pos.mpr hn
  have htop : 0 < top := by dsimp [top]; grind
  have hle : floor ≤ top := by dsimp [top]; grind
  have hden (s : Rat) (hs : 0 < s) : 0 < f.a * s + f.drift := by
    have h := Rat.mul_pos f.a_pos hs
    change 0 ≤ f.drift at hd'
    grind
  have hc : 0 < f.b / e.a := by
    rw [Rat.div_def]
    exact Rat.mul_pos f.b_pos (Rat.inv_pos.mpr e.a_pos)
  change costOn [e, f] [floor, floor, top] ≤ costOn [e, f] [floor, top, top] ↔ _
  rw [pair_cost_formula hn hd hd' (q := floor) ⟨Rat.le_refl, hle⟩,
    pair_cost_formula hn hd hd' (q := top) ⟨hle, Rat.le_refl⟩]
  have hr : (e.b * floor - e.drift) * (f.a * top + f.drift) ≤
      (e.b * top - e.drift) * (f.a * floor + f.drift) ↔
      0 ≤ e.b * f.drift + f.a * e.drift := by
    have he : (e.b * top - e.drift) * (f.a * floor + f.drift) -
        (e.b * floor - e.drift) * (f.a * top + f.drift) =
        e.b * f.drift + f.a * e.drift := by
      dsimp [top]
      grind
    rw [← he, Rat.le_iff_sub_nonneg]
  rw [← hr, ← div_le_div_iff_pos (hden floor hn') (hden top htop)]
  constructor
  · intro h
    exact Rat.le_of_mul_le_mul_left h hc
  · intro h
    exact Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hc)

private def firstPair7 : List Edge := [Edge.ofRun 7 3 1, Edge.ofRun 7 1 2]
private def risingPair27 : List Edge := [Edge.ofRun 27 5 1, unitEdge 27]

/-- Genuine prefixes provide examples in which each endpoint is the
strictly better choice for the shared coordinate. -/
theorem pair_endpoint_examples :
    localMinimum 7 firstPair7 = some (1664 / 1485) ∧
    costOn firstPair7 [7, 7, 8] < costOn firstPair7 [7, 8, 8] ∧
    localMinimum 27 risingPair27 = some (13672 / 13365) ∧
    costOn risingPair27 [27, 28, 28] < costOn risingPair27 [27, 27, 28] := by
  decide +kernel

end Collatz.ExcursionAnchor
