import Collatz.Strategy.ExcursionLocalAnchors
import Init.Data.Nat.Coprime

/-!
# Exact cost and entry residue of a repeated unit excursion

The excursion with one odd step and one halving has affine map
`x ↦ (3x+1)/4`. Its factor has a common minimizer at the lower shift
endpoint, so its minimum over a block is a power of a single rational
number. For a genuine block the input and exit also lie on a rigid
pair of arithmetic progressions.
-/

namespace Collatz.ExcursionAnchor

open Collatz.ExcursionMap

/-- The excursion with one odd step and one extra halving. -/
def unitEdge (n : Nat) : Edge := Edge.ofRun n 1 1

theorem unitEdge_drift (n : Nat) : (unitEdge n).drift = (n : Rat) - 1 := by
  change 4 * (n : Rat) + 2 - 3 * ((n : Rat) + 1) = _
  grind

/-- On a nonnegative-drift edge the arrival expression at the smallest
possible source is a lower bound even when the offset is clipped. -/
theorem Edge.factor_ge_arrival_at (e : Edge) {floor p q : Rat}
    (hn : 0 < floor) (hp : floor ≤ p) (hq : 0 < q) (hd : 0 ≤ e.drift) :
    e.b * floor / (e.a * floor + e.drift) ≤ e.factor p q := by
  have hp' : 0 < p := by grind
  have hf : 0 < e.a * floor + e.drift := by
    have h := Rat.mul_pos e.a_pos hn
    grind
  have hr : 0 < e.a * p + e.drift := by
    have h := Rat.mul_pos e.a_pos hp'
    grind
  have hlower : e.b * floor / (e.a * floor + e.drift) ≤ e.b * p / (e.a * p + e.drift) := by
    rw [div_le_div_iff_pos hf hr]
    have he := Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt e.b_pos) hd)
      ((Rat.le_iff_sub_nonneg _ _).mp hp)
    grind
  apply Rat.le_trans hlower
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc, div_le_div_iff_pos hr hq]
    have hscaled := Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt hp')
    grind
  · rw [e.factor_of_unclipped hp' hq (Rat.le_of_lt ((Rat.not_le).mp hc)), if_pos hd]
    exact Rat.le_refl

/-- The dual lower bound uses the largest possible target on a
nonpositive-drift edge. -/
theorem Edge.factor_ge_departure_at (e : Edge) {ceiling p q : Rat}
    (hp : 0 < p) (hq : 0 < q) (hceiling : q ≤ ceiling) (hd : e.drift < 0) :
    (e.b * ceiling - e.drift) / (e.a * ceiling) ≤ e.factor p q := by
  have hceiling' : 0 < ceiling := by grind
  have ht := Rat.mul_pos e.a_pos hceiling'
  have hq' := Rat.mul_pos e.a_pos hq
  have hlower : (e.b * ceiling - e.drift) / (e.a * ceiling) ≤
      (e.b * q - e.drift) / (e.a * q) := by
    rw [div_le_div_iff_pos ht hq']
    have he := Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt e.a_pos) (by grind : 0 ≤ -e.drift))
      ((Rat.le_iff_sub_nonneg _ _).mp hceiling)
    grind
  apply Rat.le_trans hlower
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc, div_le_div_iff_pos hq' hq]
    have hbase : e.b * q - e.drift ≤ e.a * p := by grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hbase (Rat.le_of_lt hq)
    grind
  · rw [e.factor_of_unclipped hp hq (Rat.le_of_lt ((Rat.not_le).mp hc)),
      if_neg ((Rat.not_le).mpr hd)]
    exact Rat.le_refl

/-- At any positive floor both preferred endpoint bounds are at least
one for a genuine excursion letter. -/
theorem ofRun_factor_ge_one {n v W : Nat} (hn : 0 < n) {p q : Rat}
    (hp : (n : Rat) ≤ p)
    (hq : (n : Rat) ≤ q) (hq' : q ≤ (n : Rat) + 1) :
    1 ≤ (Edge.ofRun n v W).factor p q := by
  let e := Edge.ofRun n v W
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hd : e.drift = e.b * (n : Rat) + c - e.a * ((n : Rat) + 1) := rfl
  have hca : c ≤ e.a := Rat.natCast_le_natCast.mpr (Collatz.Arith.two_pow_le_three_pow v)
  have hcb : c ≤ e.b := Rat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hP : 0 < p := by grind
  have hQ : 0 < q := by grind
  have ht : 0 < (n : Rat) + 1 := by grind
  change 1 ≤ e.factor p q
  by_cases hs : 0 ≤ e.drift
  · apply Rat.le_trans _ (e.factor_ge_arrival_at hn' hp hQ hs)
    let den := e.a * (n : Rat) + e.drift
    have hden : 0 < den := by
      have ha := Rat.mul_pos e.a_pos hn'
      change 0 < e.a * (n : Rat) + e.drift
      grind
    have hcancel := Rat.div_mul_cancel (a := e.b * (n : Rat)) (Rat.ne_of_gt hden)
    apply Rat.le_of_mul_le_mul_right _ hden
    rw [Rat.one_mul, hcancel]
    change e.a * (n : Rat) + e.drift ≤ e.b * (n : Rat)
    rw [hd]
    grind
  · apply Rat.le_trans _ (e.factor_ge_departure_at hP hQ hq' ((Rat.not_le).mp hs))
    have hden := Rat.mul_pos e.a_pos ht
    have hcancel := Rat.div_mul_cancel (a := e.b * ((n : Rat) + 1) - e.drift)
      (Rat.ne_of_gt hden)
    apply Rat.le_of_mul_le_mul_right _ hden
    rw [Rat.one_mul, hcancel, hd]
    grind

/-- The exact minimum of an individual unit factor on the band. -/
def unitFactor (n : Nat) : Rat := 4 * (n : Rat) / (4 * (n : Rat) - 1)

theorem unit_factor_floor {n : Nat} (hn : 0 < n) :
    (unitEdge n).factor n n = unitFactor n := by
  let e := unitEdge n
  have ha : e.a = 3 := rfl
  have hb : e.b = 4 := rfl
  have hd := unitEdge_drift n
  have hpos : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hn' : (1 : Rat) ≤ n := Rat.natCast_le_natCast.mpr hn
  have hd' : 0 ≤ e.drift := by change 0 ≤ (unitEdge n).drift; rw [hd]; grind
  have hunc : e.a * (n : Rat) + e.drift ≤ e.b * (n : Rat) := by
    rw [ha, hb, show e.drift = (n : Rat) - 1 from hd]
    grind
  change e.factor n n = _
  rw [e.factor_of_unclipped hpos hpos hunc, if_pos hd', ha, hb,
    show e.drift = (n : Rat) - 1 from hd, unitFactor]
  congr 1
  grind

theorem unit_factor_le {n : Nat} (hn : 0 < n) {p q : Rat}
    (hp : (n : Rat) ≤ p) (hq : (n : Rat) ≤ q) :
    unitFactor n ≤ (unitEdge n).factor p q := by
  have hpos : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hn' : (1 : Rat) ≤ n := Rat.natCast_le_natCast.mpr hn
  have hd := unitEdge_drift n
  have hd' : 0 ≤ (unitEdge n).drift := by rw [hd]; grind
  have h := (unitEdge n).factor_ge_arrival_at hpos hp (by grind : 0 < q) hd'
  change 4 * (n : Rat) / (3 * (n : Rat) + (unitEdge n).drift) ≤ _ at h
  rw [hd, show 3 * (n : Rat) + ((n : Rat) - 1) = 4 * (n : Rat) - 1 by grind] at h
  exact h

/-- The optimal cost of a unit block is bounded below by the power of
its individual optimum. The constant floor schedule attains this bound. -/
theorem unit_tail_cost {n j : Nat} (hn : 0 < n) {p : Rat} {rest : List Rat}
    (hlen : rest.length = j) (hp : (n : Rat) ≤ p)
    (hband : ∀ q ∈ rest, (n : Rat) ≤ q) :
    unitFactor n ^ j ≤ costOn (List.replicate j (unitEdge n)) (p :: rest) := by
  have hpos : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hunit : 0 < unitFactor n := by
    rw [← unit_factor_floor hn]
    exact (unitEdge n).factor_pos hpos hpos
  induction j generalizing p rest with
  | zero =>
    rw [Rat.pow_zero]
    exact Rat.le_refl
  | succ j ih =>
    cases rest with
    | nil => simp at hlen
    | cons q rest =>
      have hq := hband q List.mem_cons_self
      have hs := ih (by simpa using hlen) hq (fun t ht => hband t (List.mem_cons_of_mem _ ht))
      have he := unit_factor_le hn hp hq
      have hpower := Rat.pow_pos (n := j) hunit
      have hfactor := (unitEdge n).factor_pos (by grind : 0 < p) (by grind : 0 < q)
      rw [Rat.pow_succ, List.replicate_succ, costOn, Rat.mul_comm (unitFactor n ^ j)]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right he (Rat.le_of_lt hpower))
        (Rat.mul_le_mul_of_nonneg_left hs (Rat.le_of_lt hfactor))

theorem unit_tail_cost_at_floor {n : Nat} (hn : 0 < n) (j : Nat) :
    costOn (List.replicate j (unitEdge n)) (List.replicate (j + 1) (n : Rat)) = unitFactor n ^ j := by
  induction j with
  | zero => exact (Rat.pow_zero _).symm
  | succ j ih =>
    rw [List.replicate_succ, List.replicate_succ (n := j + 1), List.replicate_succ (n := j),
      costOn, ← List.replicate_succ (n := j), ih, unit_factor_floor hn, Rat.pow_succ, Rat.mul_comm]

/-- Every factor in the unit block attains its minimum at the same
shift, so the exact finite optimizer computes a power. -/
theorem anchorMinimum_unit {n : Nat} (hn : 0 < n) (j : Nat) :
    anchorMinimum n (List.replicate j (unitEdge n)) = some (unitFactor n ^ j) := by
  let word := List.replicate j (unitEdge n)
  let rest := List.replicate j (n : Rat)
  have hlen : rest.length = word.length := by simp [rest, word]
  have hband (p : Rat) (hp : p ∈ (n : Rat) :: rest) :
      (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
    have he : p = (n : Rat) := by
      rcases List.mem_cons.mp hp with he | hm
      · exact he
      · exact List.eq_of_mem_replicate hm
    rw [he]
    exact ⟨Rat.le_refl, by grind⟩
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_schedule (Rat.natCast_pos.mpr hn) hlen hband
  change best ≤ costOn word (List.replicate (j + 1) (n : Rat)) at hle
  rw [unit_tail_cost_at_floor hn] at hle
  obtain ⟨p, tail, htail, hbands, hcost⟩ := anchorMinimum_attained_in_band hbest
  have htail' : tail.length = j := by simpa [word] using htail
  have hlo := unit_tail_cost hn htail' (hbands p List.mem_cons_self).1
    (fun q hq => (hbands q (List.mem_cons_of_mem _ hq)).1)
  rw [hcost] at hlo
  rwa [Rat.le_antisymm hle hlo] at hbest

private theorem unit_edge_parameters {n v W : Nat}
    (h : (Edge.ofRun n v W).a = 3 ∧ (Edge.ofRun n v W).b = 4) : v = 1 ∧ W = 1 := by
  have ha : ((3 ^ v : Nat) : Rat) = ((3 ^ 1 : Nat) : Rat) := h.1
  have hb : ((2 ^ (v + W) : Nat) : Rat) = ((2 ^ 2 : Nat) : Rat) := h.2
  have hv := (Nat.pow_right_inj (by decide : 1 < 3)).mp (Rat.natCast_inj.mp ha)
  have ht := (Nat.pow_right_inj (by decide : 1 < 2)).mp (Rat.natCast_inj.mp hb)
  exact ⟨hv, by omega⟩

private theorem unit_step_relation {x u y : Nat} (h : IsExcursion x 1 u 1 y) :
    4 * (y - 1) = 3 * (x - 1) := by
  obtain ⟨hx, _, hy, _, _, hsource, htarget⟩ := h
  change x + 1 = 2 * u at hsource
  change 3 * u = 2 * y + 1 at htarget
  omega

theorem OrbitWord.unit_relation {n x y elapsed A B word}
    (h : OrbitWord n x word y elapsed A B)
    (hunit : ∀ e ∈ word, e.a = 3 ∧ e.b = 4) :
    4 ^ word.length * (y - 1) = 3 ^ word.length * (x - 1) := by
  induction h with
  | nil => simp
  | @cons x next v u W y elapsed A B word hstep htail ih =>
    obtain ⟨rfl, rfl⟩ := unit_edge_parameters (hunit _ List.mem_cons_self)
    have hsub := ih (fun e he => hunit e (List.mem_cons_of_mem _ he))
    have hlocal := unit_step_relation hstep
    rw [List.length_cons, Nat.pow_succ, Nat.pow_succ]
    calc
      _ = 4 * (4 ^ word.length * (y - 1)) := by ac_rfl
      _ = 3 ^ word.length * (4 * (next - 1)) := by rw [hsub]; ac_rfl
      _ = _ := by rw [hlocal]; ac_rfl

/-- The exact entry residue for a genuine block of unit excursions.
An odd exit forces one additional factor of two. -/
theorem OrbitWord.unit_entry_dvd {n x y elapsed A B word}
    (h : OrbitWord n x word y elapsed A B)
    (hunit : ∀ e ∈ word, e.a = 3 ∧ e.b = 4) (hy : y % 2 = 1) :
    2 * 4 ^ word.length ∣ x - 1 := by
  have heven : 2 ∣ y - 1 := by omega
  have heq := h.unit_relation hunit
  have hd := Nat.mul_dvd_mul_left (4 ^ word.length) heven
  rw [Nat.mul_comm (4 ^ word.length) 2, heq] at hd
  have hc₁ : Nat.Coprime 2 3 := by decide
  have hc₂ : Nat.Coprime 4 3 := by decide
  have hc : Nat.Coprime (2 * 4 ^ word.length) (3 ^ word.length) :=
    (hc₁.mul_left (hc₂.pow_left _)).pow_right _
  exact hc.dvd_of_dvd_mul_left hd

/-- Conversely, every positive integer in the entry residue follows
the entire unit block and has the indicated exit value. -/
theorem unit_word_of_residue (n j d : Nat) :
    OrbitWord n (1 + 2 * 4 ^ j * d) (List.replicate j (unitEdge n))
      (1 + 2 * 3 ^ j * d) (2 * j) (3 ^ j) (4 ^ j) := by
  induction j generalizing d with
  | zero =>
    change OrbitWord n (1 + 2 * 1 * d) [] (1 + 2 * 1 * d) 0 1 1
    exact .nil
  | succ j ih =>
    let c := 4 ^ j * d
    have hstep : IsExcursion (1 + 8 * c) 1 (1 + 4 * c) 1 (1 + 6 * c) := by
      unfold IsExcursion
      simp only [Nat.pow_one]
      omega
    have hstart : 1 + 2 * 4 ^ (j + 1) * d = 1 + 8 * c := by
      rw [Nat.pow_succ]
      dsimp [c]
      grind
    have hmid : 1 + 2 * 4 ^ j * (3 * d) = 1 + 6 * c := by
      dsimp [c]
      grind
    have hend : 1 + 2 * 3 ^ (j + 1) * d = 1 + 2 * 3 ^ j * (3 * d) := by
      rw [Nat.pow_succ]
      ac_rfl
    have htail := ih (3 * d)
    rw [hmid] at htail
    rw [hstart, hend, List.replicate_succ, Nat.pow_succ, Nat.pow_succ,
      Nat.mul_comm (3 ^ j) 3, Nat.mul_comm (4 ^ j) 4,
      show 2 * (j + 1) = 2 * j + (1 + 1) by omega]
    exact .cons hstep htail

/-- A contracting homogeneous product made from one excursion and a
genuine unit tail requires an exponentially large starting value,
unless the first excursion already landed at one. -/
theorem start_large_of_unit_crossing {n x y v u W elapsed A B word}
    (hfirst : IsExcursion n v u W x) (hx : 1 < x)
    (htail : OrbitWord n x word y elapsed A B)
    (hunit : ∀ e ∈ word, e.a = 3 ∧ e.b = 4) (hy : y % 2 = 1)
    (hcross : 3 ^ v * 3 ^ word.length < 2 ^ (v + W) * 4 ^ word.length) :
    2 * 3 ^ word.length ≤ n := by
  have hd := htail.unit_entry_dvd hunit hy
  have hx' : 2 * 4 ^ word.length ≤ x - 1 := Nat.le_of_dvd (by omega) hd
  let a := 3 ^ v
  let b := 2 ^ (v + W)
  have ha : 0 < a := Nat.pow_pos (by decide)
  have hshift := Collatz.ExcursionSwitchFloor.affine_source_succ hfirst
  change b * x + 2 ^ v = a * (n + 1) at hshift
  have hhead := Nat.mul_le_mul_left b hx'
  have hmargin := Nat.mul_lt_mul_of_pos_left hcross (by decide : 0 < 2)
  have hsum : b * x ≤ a * (n + 1) :=
    hshift ▸ Nat.le_add_right (b * x) (2 ^ v)
  have hless : b * (x - 1) ≤ a * (n + 1) :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hsum
  have hsmall : a * (2 * 3 ^ word.length) < a * (n + 1) := by
    calc
      _ = 2 * (a * 3 ^ word.length) := by ac_rfl
      _ < 2 * (b * 4 ^ word.length) := hmargin
      _ = b * (2 * 4 ^ word.length) := by ac_rfl
      _ ≤ b * (x - 1) := hhead
      _ ≤ _ := hless
  have hbound := (Nat.mul_lt_mul_left ha).mp hsmall
  omega

private def falseTailFromSeven : List Edge :=
  Edge.ofRun 7 3 1 :: List.replicate 2 (unitEdge 7)

/-- The abstract continuation agrees with the first genuine excursion
from 7 and crosses at its third letter. Its last two letters violate
the exact unit-tail entry residue. -/
theorem false_tail_from_seven_crosses :
    IsExcursion 7 3 1 1 13 ∧
      16 ≤ 27 ∧ 64 ≤ 81 ∧ 243 < 256 ∧ ¬ (2 * 4 ^ 2 ∣ 13 - 1) := by
  unfold IsExcursion
  decide +kernel

theorem false_tail_from_seven_exact :
    localMinimum 7 falseTailFromSeven = some (1792 / 1539) := by
  decide +kernel

/-- A strict homogeneous crossing on the abstract continuation is
insufficient, even when the rational shift product is optimized. -/
theorem false_tail_from_seven_fails {best : Rat}
    (hbest : localMinimum 7 falseTailFromSeven = some best) :
    (256 : Rat) < 243 * best := by
  have ha : ExcursionAlphabet 7 falseTailFromSeven := by
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact ⟨3, 1, by decide, by decide, rfl⟩
    · exact ⟨1, 1, by decide, by decide, List.eq_of_mem_replicate ht⟩
  rw [localMinimum_eq_anchorMinimum ha] at hbest
  obtain ⟨p, tail, hlen, hband, hcost⟩ := anchorMinimum_attained_in_band hbest
  cases tail with
  | nil => simp [falseTailFromSeven] at hlen
  | cons q tail =>
    have hP := hband p List.mem_cons_self
    have hQ := hband q (List.mem_cons_of_mem _ List.mem_cons_self)
    have htail : tail.length = 2 := by simpa [falseTailFromSeven] using hlen
    have hunit := unit_tail_cost (by decide : 0 < 7) htail hQ.1
      (fun r hr => (hband r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).1)
    have he := ofRun_factor_ge_one (v := 3) (W := 1) (by decide : 0 < 7) hP.1 hQ.1 hQ.2
    have hpow : 0 < unitFactor 7 ^ 2 := by decide +kernel
    have hle := Rat.mul_le_mul_of_nonneg_right he (Rat.le_of_lt hpow)
    have hle' := Rat.mul_le_mul_of_nonneg_left hunit (by grind :
      0 ≤ (Edge.ofRun 7 3 1).factor p q)
    rw [Rat.one_mul] at hle
    have hcost' : (Edge.ofRun 7 3 1).factor p q *
        costOn (List.replicate 2 (unitEdge 7)) (q :: tail) = best := hcost
    have hbound := Rat.le_trans hle hle'
    rw [hcost'] at hbound
    have hscaled := Rat.mul_le_mul_of_nonneg_left hbound (by decide : (0 : Rat) ≤ 243)
    have hstrict : (256 : Rat) < 243 * unitFactor 7 ^ 2 := by decide +kernel
    grind

end Collatz.ExcursionAnchor
