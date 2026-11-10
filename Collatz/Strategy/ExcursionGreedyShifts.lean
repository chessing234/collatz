import Collatz.Strategy.ExcursionPairMinimum

/-!
# Greedy moves within excursion drift blocks

For a nonnegative-drift edge, the smallest unclipped target improves
the product with the next edge. For a negative-drift edge, the largest
unclipped source improves the product with the preceding edge. These
moves hold with the two outside coordinates fixed.
-/

namespace Collatz.ExcursionAnchor

private theorem quotient_cancel_source {p q : Rat} (hp : 0 < p) :
    (p / q) / p = 1 / q := by
  simp only [Rat.div_def, Rat.one_mul]
  have h := Rat.mul_inv_cancel p (Rat.ne_of_gt hp)
  grind

private theorem arrival_cancel_source (e : Edge) {p : Rat} (hp : 0 < p) :
    (e.b * p / (e.a * p + e.drift)) / p = e.b / (e.a * p + e.drift) := by
  simp only [Rat.div_def]
  have h := Rat.mul_inv_cancel p (Rat.ne_of_gt hp)
  grind

private theorem departure_cancel_target (e : Edge) {q : Rat} (hq : 0 < q) :
    ((e.b * q - e.drift) / (e.a * q)) * q = (e.b * q - e.drift) / e.a := by
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have h := Rat.inv_mul_cancel q (Rat.ne_of_gt hq)
  grind

/-- The factor divided by its source coordinate decreases weakly
with that coordinate. -/
theorem Edge.factor_div_source_antitone (e : Edge) {p P q : Rat}
    (hp : 0 < p) (hq : 0 < q) (h : p ≤ P) :
    e.factor P q / P ≤ e.factor p q / p := by
  have hP : 0 < P := by grind
  by_cases hc : e.b * q ≤ e.a * P + e.drift
  · rw [e.factor_of_clipped hc, quotient_cancel_source hP, ← quotient_cancel_source hp (q := q)]
    rw [div_le_div_iff_pos hp hp]
    exact Rat.mul_le_mul_of_nonneg_right (e.factor_ge_ratio hp hq) (Rat.le_of_lt hp)
  · have hu := Rat.le_of_lt ((Rat.not_le).mp hc)
    have hprod := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt e.a_pos)
    have hu' : e.a * p + e.drift ≤ e.b * q := by grind
    rw [e.factor_of_unclipped hP hq hu, e.factor_of_unclipped hp hq hu']
    by_cases hd : 0 ≤ e.drift
    · rw [if_pos hd, if_pos hd, arrival_cancel_source e hP, arrival_cancel_source e hp]
      have ha : 0 < e.a * p + e.drift := by have hh := Rat.mul_pos e.a_pos hp; grind
      have hA : 0 < e.a * P + e.drift := by grind
      rw [div_le_div_iff_pos hA ha]
      apply Rat.mul_le_mul_of_nonneg_left _ (Rat.le_of_lt e.b_pos)
      grind
    · rw [if_neg hd, if_neg hd, div_le_div_iff_pos hP hp]
      have hn : 0 ≤ e.b * q - e.drift := by have hh := Rat.mul_pos e.b_pos hq; grind
      have hden := Rat.mul_pos e.a_pos hq
      have hcost : 0 ≤ (e.b * q - e.drift) / (e.a * q) := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg hn (Rat.le_of_lt (Rat.inv_pos.mpr hden))
      exact Rat.mul_le_mul_of_nonneg_left h hcost

/-- The factor multiplied by its target coordinate increases weakly
with that coordinate. -/
theorem Edge.factor_mul_target_mono (e : Edge) {p q Q : Rat}
    (hp : 0 < p) (hq : 0 < q) (h : q ≤ Q) :
    e.factor p q * q ≤ e.factor p Q * Q := by
  have hQ : 0 < Q := by grind
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · rw [e.factor_of_clipped hc, Rat.div_mul_cancel (Rat.ne_of_gt hq)]
    have hs := Rat.mul_le_mul_of_nonneg_right (e.factor_ge_ratio hp hQ) (Rat.le_of_lt hQ)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hQ)] at hs
  · have hu := Rat.le_of_lt ((Rat.not_le).mp hc)
    have hprod := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt e.b_pos)
    have hu' : e.a * p + e.drift ≤ e.b * Q := by grind
    by_cases hd : 0 ≤ e.drift
    · have hcost : 0 ≤ e.b * p / (e.a * p + e.drift) := by
        have hp' := Rat.le_of_lt (e.factor_pos hp hq)
        rwa [e.factor_of_unclipped hp hq hu, if_pos hd] at hp'
      rw [e.factor_of_unclipped hp hq hu, e.factor_of_unclipped hp hQ hu', if_pos hd, if_pos hd]
      exact Rat.mul_le_mul_of_nonneg_left h hcost
    · rw [e.factor_of_unclipped hp hq hu, e.factor_of_unclipped hp hQ hu', if_neg hd, if_neg hd,
        departure_cancel_target e hq, departure_cancel_target e hQ,
        div_le_div_iff_pos e.a_pos e.a_pos]
      apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt e.a_pos)
      grind

/-- The best shared shift after a nonnegative-drift edge is its
transport, clipped to the lower endpoint. This move works with any
edge to its right. -/
theorem greedy_after_nonnegative (e f : Edge) {floor p q r : Rat}
    (hn : 0 < floor) (hp : 0 < p) (hq : floor ≤ q) (hr : 0 < r)
    (hd : 0 ≤ e.drift) :
    let next := max floor (e.transport p)
    e.factor p next * f.factor next r ≤ e.factor p q * f.factor q r := by
  let t := e.transport p
  let next := max floor t
  have ht := e.transport_spec p
  change e.factor p next * f.factor next r ≤ e.factor p q * f.factor q r
  have hq' : 0 < q := by grind
  by_cases h : t ≤ floor
  · have hnext : next = floor := by
      change max floor t = floor
      rw [Rat.max_def]
      split <;> grind
    have h₁ := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt e.b_pos)
    have h₂ := Rat.mul_le_mul_of_nonneg_left hq (Rat.le_of_lt e.b_pos)
    have hu : e.a * p + e.drift ≤ e.b * floor := by grind
    have hu' : e.a * p + e.drift ≤ e.b * q := by grind
    rw [hnext, e.factor_of_unclipped hp hn hu, e.factor_of_unclipped hp hq' hu',
      if_pos hd, if_pos hd]
    have hpos := Rat.le_of_lt (e.factor_pos hp hn)
    rw [e.factor_of_unclipped hp hn hu, if_pos hd] at hpos
    exact Rat.mul_le_mul_of_nonneg_left (f.factor_mono_source hn hq hr) hpos
  · have hfloor := Rat.le_of_lt ((Rat.not_le).mp h)
    have hnext : next = t := by
      change max floor t = t
      rw [Rat.max_def, if_pos hfloor]
    have ht' : 0 < t := by grind
    rw [hnext]
    by_cases hqt : q ≤ t
    · have hscaled := Rat.mul_le_mul_of_nonneg_left hqt (Rat.le_of_lt e.b_pos)
      have hc : e.b * q ≤ e.a * p + e.drift := by grind
      rw [e.factor_of_transport, e.factor_of_clipped hc]
      have hf := Rat.mul_le_mul_of_nonneg_left (f.factor_div_source_antitone hq' hr hqt)
        (Rat.le_of_lt hp)
      simp only [Rat.div_def] at hf ⊢
      grind
    · have htq := Rat.le_of_lt ((Rat.not_le).mp hqt)
      have hscaled := Rat.mul_le_mul_of_nonneg_left htq (Rat.le_of_lt e.b_pos)
      have hu : e.a * p + e.drift ≤ e.b * q := by grind
      have hu' : e.a * p + e.drift ≤ e.b * t := by grind
      rw [e.factor_of_unclipped hp ht' hu', e.factor_of_unclipped hp hq' hu, if_pos hd, if_pos hd]
      have hpos := Rat.le_of_lt (e.factor_pos hp ht')
      rw [e.factor_of_unclipped hp ht' hu', if_pos hd] at hpos
      exact Rat.mul_le_mul_of_nonneg_left (f.factor_mono_source ht' htq hr) hpos

/-- The best shared shift before a negative-drift edge is its inverse
transport, clipped to the upper endpoint. This move works with any
edge to its left. -/
theorem greedy_before_negative (e f : Edge) {ceiling p q r : Rat}
    (hp : 0 < p) (hq : 0 < q) (hceil : q ≤ ceiling) (hr : 0 < r)
    (hi : 0 < f.inverse r) (hd : f.drift < 0) :
    let prev := min ceiling (f.inverse r)
    e.factor p prev * f.factor prev r ≤ e.factor p q * f.factor q r := by
  let t := f.inverse r
  let prev := min ceiling t
  have ht := f.inverse_spec r
  change e.factor p prev * f.factor prev r ≤ e.factor p q * f.factor q r
  have hc' : 0 < ceiling := by grind
  have ht' : 0 < t := hi
  by_cases h : ceiling ≤ t
  · have hprev : prev = ceiling := by
      change min ceiling t = ceiling
      rw [Rat.min_def, if_pos h]
    have h₁ := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt f.a_pos)
    have h₂ := Rat.mul_le_mul_of_nonneg_left hceil (Rat.le_of_lt f.a_pos)
    have hu : f.a * ceiling + f.drift ≤ f.b * r := by grind
    have hu' : f.a * q + f.drift ≤ f.b * r := by grind
    rw [hprev, f.factor_of_unclipped hc' hr hu, f.factor_of_unclipped hq hr hu',
      if_neg ((Rat.not_le).mpr hd), if_neg ((Rat.not_le).mpr hd)]
    have hpos := Rat.le_of_lt (f.factor_pos hc' hr)
    rw [f.factor_of_unclipped hc' hr hu, if_neg ((Rat.not_le).mpr hd)] at hpos
    exact Rat.mul_le_mul_of_nonneg_right (e.factor_antitone_target hp hq hceil) hpos
  · have htceil := Rat.le_of_lt ((Rat.not_le).mp h)
    have hprev : prev = t := by
      change min ceiling t = t
      rw [Rat.min_def, if_neg h]
    rw [hprev]
    by_cases hqt : t ≤ q
    · have hscaled := Rat.mul_le_mul_of_nonneg_left hqt (Rat.le_of_lt f.a_pos)
      have hc : f.b * r ≤ f.a * q + f.drift := by grind
      have hc₀ : f.b * r ≤ f.a * t + f.drift := by grind
      rw [f.factor_of_clipped hc₀, f.factor_of_clipped hc]
      have hf := Rat.mul_le_mul_of_nonneg_right (e.factor_mul_target_mono hp ht' hqt)
        (Rat.le_of_lt (Rat.inv_pos.mpr hr))
      simp only [Rat.div_def]
      grind
    · have hqt' := Rat.le_of_lt ((Rat.not_le).mp hqt)
      have hscaled := Rat.mul_le_mul_of_nonneg_left hqt' (Rat.le_of_lt f.a_pos)
      have hu : f.a * t + f.drift ≤ f.b * r := by grind
      have hu' : f.a * q + f.drift ≤ f.b * r := by grind
      rw [f.factor_of_unclipped ht' hr hu, f.factor_of_unclipped hq hr hu',
        if_neg ((Rat.not_le).mpr hd), if_neg ((Rat.not_le).mpr hd)]
      have hpos := Rat.le_of_lt (f.factor_pos ht' hr)
      rw [f.factor_of_unclipped ht' hr hu, if_neg ((Rat.not_le).mpr hd)] at hpos
      exact Rat.mul_le_mul_of_nonneg_right (e.factor_antitone_target hp hq hqt') hpos

private theorem max_eq_floor {n t : Rat} (h : t ≤ n) : max n t = n := by
  rw [Rat.max_def]
  split <;> grind

private theorem min_eq_ceiling {n t : Rat} (h : n ≤ t) : min n t = n := by
  rw [Rat.min_def, if_pos h]

/-- Once the forward rule reaches the floor, every later positive
excursion letter keeps it there. -/
theorem forward_floor_fixed {n v W : Nat} (hv : 0 < v) :
    max (n : Rat) ((Edge.ofRun n v W).transport n) = n :=
  max_eq_floor (Rat.le_of_lt (transport_below hv Rat.le_refl))

/-- Three forward moves force the lower endpoint. A fourth move
therefore has the same value, independent of the initial shift. -/
theorem forward_three_eq_floor {n v₁ W₁ v₂ W₂ v₃ W₃ : Nat}
    (hW₁ : 0 < W₁) (hv₂ : 0 < v₂) (hW₂ : 0 < W₂) (hv₃ : 0 < v₃)
    {p : Rat} (hp : p ≤ (n : Rat) + 1) :
    max (n : Rat) ((Edge.ofRun n v₃ W₃).transport
      (max (n : Rat) ((Edge.ofRun n v₂ W₂).transport
        (max (n : Rat) ((Edge.ofRun n v₁ W₁).transport p))))) = n := by
  let e := Edge.ofRun n v₁ W₁
  let f := Edge.ofRun n v₂ W₂
  let g := Edge.ofRun n v₃ W₃
  change max (n : Rat) (g.transport (max (n : Rat) (f.transport (max (n : Rat) (e.transport p))))) = n
  by_cases h₁ : e.transport p ≤ (n : Rat)
  · rw [max_eq_floor h₁, forward_floor_fixed (W := W₂) hv₂, forward_floor_fixed (W := W₃) hv₃]
  · have h₁' := Rat.le_of_lt ((Rat.not_le).mp h₁)
    rw [Rat.max_def (n := (n : Rat)) (m := e.transport p), if_pos h₁']
    by_cases h₂ : f.transport (e.transport p) ≤ (n : Rat)
    · rw [max_eq_floor h₂, forward_floor_fixed (W := W₃) hv₃]
    · have h₂' := Rat.le_of_lt ((Rat.not_le).mp h₂)
      rw [Rat.max_def (n := (n : Rat)) (m := f.transport (e.transport p)), if_pos h₂']
      apply max_eq_floor
      apply Classical.byContradiction
      intro h₃not
      have h₃ := (Rat.not_le).mp h₃not
      have hsmall := (two_zero_links hW₁ hv₂ hW₂ hp h₂').2.2
      have hlarge := input_ge_third hv₃ (Rat.le_of_lt h₃)
      have hgap : (1 / 8 : Rat) < 1 / 3 := by decide +kernel
      change f.transport (e.transport p) ≤ (n : Rat) + 1 / 8 at hsmall
      change (n : Rat) + 1 / 3 ≤ f.transport (e.transport p) at hlarge
      grind

/-- The backward rule reaches the upper endpoint in two moves when
the first backward edge has negative drift. -/
theorem backward_two_eq_ceiling {n v W v' W' : Nat} (hn : 0 < n)
    (hW : 0 < W) (hv' : 0 < v') (hW' : 0 < W') (hd : (Edge.ofRun n v' W').drift < 0)
    {q : Rat} (hq : (n : Rat) ≤ q) :
    min ((n : Rat) + 1) ((Edge.ofRun n v W).inverse
      (min ((n : Rat) + 1) ((Edge.ofRun n v' W').inverse q))) = (n : Rat) + 1 := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let top := (n : Rat) + 1
  let prev := min top (f.inverse q)
  have hqin : (n : Rat) ≤ f.transport (f.inverse q) := by
    rw [f.transport_eq_of_zero (f.inverse_spec q).symm]
    exact hq
  have hsource : (n : Rat) + 5 / 9 ≤ f.inverse q :=
    input_ge_five_ninths (v_ge_two_of_negative_drift hn hv' hW' hd) hqin
  have hprev : (n : Rat) + 5 / 9 ≤ prev := by
    have h5 : (5 / 9 : Rat) ≤ 1 := by decide +kernel
    change (n : Rat) + 5 / 9 ≤ min top (f.inverse q)
    rw [Rat.min_def]
    split
    · change (n : Rat) + 5 / 9 ≤ (n : Rat) + 1
      grind
    · exact hsource
  have htransport : e.transport top ≤ (n : Rat) + 1 / 2 := output_half hW Rat.le_refl
  have hhalf : (1 / 2 : Rat) ≤ 5 / 9 := by decide +kernel
  have hcomp : e.transport top ≤ prev := by grind
  have hscaled := Rat.mul_le_mul_of_nonneg_left hcomp (Rat.le_of_lt e.b_pos)
  rw [e.transport_spec, ← e.inverse_spec prev] at hscaled
  have htop : top ≤ e.inverse prev := by
    apply Rat.le_of_mul_le_mul_left _ e.a_pos
    grind
  exact min_eq_ceiling htop

private theorem forwardShift_in_band {n v W : Nat} (hW : 0 < W) {p : Rat}
    (hp : p ≤ (n : Rat) + 1) :
    (n : Rat) ≤ max (n : Rat) ((Edge.ofRun n v W).transport p) ∧
      max (n : Rat) ((Edge.ofRun n v W).transport p) ≤ (n : Rat) + 1 := by
  have hhalf := output_half (v := v) hW hp
  have h : (1 / 2 : Rat) ≤ 1 := by decide +kernel
  rw [Rat.max_def]
  split <;> grind

private theorem greedy_target_le_factor (e : Edge) {floor p q : Rat}
    (hn : 0 < floor) (hp : 0 < p) (hq : floor ≤ q) (hd : 0 ≤ e.drift) :
    e.factor p (max floor (e.transport p)) ≤ e.factor p q := by
  let next := max floor (e.transport p)
  have hq' : 0 < q := by grind
  have hnext : floor ≤ next ∧ e.transport p ≤ next := by
    change floor ≤ max floor (e.transport p) ∧ e.transport p ≤ max floor (e.transport p)
    rw [Rat.max_def]
    split <;> grind
  have hnext' : 0 < next := by have := hnext.1; grind
  have h := Rat.mul_le_mul_of_nonneg_left hnext.2 (Rat.le_of_lt e.b_pos)
  rw [e.transport_spec] at h
  change e.factor p next ≤ e.factor p q
  rw [e.factor_of_unclipped hp hnext' h, if_pos hd]
  exact e.factor_ge_arrival_at hp Rat.le_refl hq' hd

/-- Build the schedule for nonnegative drift with the initial
coordinate fixed. -/
def greedyForward (floor : Rat) : List Edge → Rat → List Rat
  | [], p => [p]
  | e :: word, p => p :: greedyForward floor word (max floor (e.transport p))

/-- The forward rule minimizes the full product on a nonnegative
drift word with the initial coordinate prescribed. -/
theorem greedyForward_le {n : Nat} (hn : 0 < n) {word : List Edge}
    (ha : ExcursionAlphabet n word) (hd : ∀ e ∈ word, 0 ≤ e.drift)
    {p : Rat} {rest : List Rat}
    (hlen : rest.length = word.length)
    (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1)
    (hband : ∀ q ∈ rest, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    costOn word (greedyForward n word p) ≤ costOn word (p :: rest) := by
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  induction word generalizing p rest with
  | nil => exact Rat.le_refl
  | cons e word ih =>
    cases rest with
    | nil => simp at hlen
    | cons q rest =>
      have hlen' : rest.length = word.length := by simpa using hlen
      have hq := hband q List.mem_cons_self
      have hpos : 0 < p := by have := hp.1; grind
      have htail (r : Rat) (hr : r ∈ rest) := hband r (List.mem_cons_of_mem _ hr)
      have he := hd e List.mem_cons_self
      obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
      let e := Edge.ofRun n v W
      let next := max (n : Rat) (e.transport p)
      have hnext : (n : Rat) ≤ next ∧ next ≤ (n : Rat) + 1 := forwardShift_in_band hW hp.2
      have hnext' : 0 < next := by have := hnext.1; grind
      have hs := ih (fun f hf => ha f (List.mem_cons_of_mem _ hf))
        (fun f hf => hd f (List.mem_cons_of_mem _ hf)) hlen' hnext htail
      have hhead : ∃ qs, greedyForward n word next = next :: qs := by
        cases word <;> exact ⟨_, rfl⟩
      obtain ⟨qs, hqs⟩ := hhead
      change costOn (e :: word) (p :: greedyForward n word next) ≤ _
      rw [hqs, costOn, ← hqs]
      apply Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hs (Rat.le_of_lt (e.factor_pos hpos hnext')))
      cases word with
      | nil =>
        simp only [costOn, Rat.mul_one]
        exact greedy_target_le_factor e hn' hpos hq.1 he
      | cons f word =>
        cases rest with
        | nil => simp at hlen'
        | cons r rest =>
          have hr := htail r List.mem_cons_self
          have hr' : 0 < r := by have := hr.1; grind
          have hc := costOn_nonneg word (r :: rest)
            (fun x hx => by have := (htail x hx).1; grind)
          simp only [costOn, ← Rat.mul_assoc]
          exact Rat.mul_le_mul_of_nonneg_right (greedy_after_nonnegative e f hn' hpos hq.1 hr' he) hc

private theorem backwardShift_in_band {n v W : Nat} (hv : 0 < v) {q : Rat}
    (hq : (n : Rat) ≤ q) :
    (n : Rat) ≤ min ((n : Rat) + 1) ((Edge.ofRun n v W).inverse q) ∧
      min ((n : Rat) + 1) ((Edge.ofRun n v W).inverse q) ≤ (n : Rat) + 1 := by
  let e := Edge.ofRun n v W
  have ht : (n : Rat) ≤ e.transport (e.inverse q) := by
    rw [e.transport_eq_of_zero (e.inverse_spec q).symm]
    exact hq
  have hthird : (n : Rat) + 1 / 3 ≤ e.inverse q := input_ge_third hv ht
  have h : (0 : Rat) ≤ 1 / 3 := by decide +kernel
  change (n : Rat) ≤ min ((n : Rat) + 1) (e.inverse q) ∧
    min ((n : Rat) + 1) (e.inverse q) ≤ (n : Rat) + 1
  rw [Rat.min_def]
  split <;> grind

private theorem greedy_source_le_factor (e : Edge) {ceiling p q : Rat}
    (hp : 0 < p) (hceil : p ≤ ceiling) (hq : 0 < q) (hi : 0 < e.inverse q)
    (hd : e.drift < 0) :
    e.factor (min ceiling (e.inverse q)) q ≤ e.factor p q := by
  let prev := min ceiling (e.inverse q)
  have hprev : 0 < prev ∧ prev ≤ e.inverse q := by
    change 0 < min ceiling (e.inverse q) ∧ min ceiling (e.inverse q) ≤ e.inverse q
    rw [Rat.min_def]
    split <;> grind
  have h := Rat.mul_le_mul_of_nonneg_left hprev.2 (Rat.le_of_lt e.a_pos)
  have hi' := e.inverse_spec q
  have hunc : e.a * prev + e.drift ≤ e.b * q := by grind
  change e.factor prev q ≤ e.factor p q
  rw [e.factor_of_unclipped hprev.1 hq hunc, if_neg ((Rat.not_le).mpr hd)]
  exact e.factor_ge_departure_at hp hq Rat.le_refl hd

/-- Build the reversed schedule for negative drift, starting at the
specified final coordinate and traversing the reversed word. -/
def greedyBackward (ceiling : Rat) : List Edge → Rat → List Rat
  | [], q => [q]
  | e :: word, q => q :: greedyBackward ceiling word (min ceiling (e.inverse q))

private theorem greedyBackward_length (ceiling : Rat) (rev : List Edge) (q : Rat) :
    (greedyBackward ceiling rev q).length = rev.length + 1 := by
  induction rev generalizing q with
  | nil => rfl
  | cons e rev ih => simp [greedyBackward, ih, Nat.add_assoc]

private theorem reverse_cost_cons (e : Edge) (rev : List Edge) (q p : Rat) (rest : List Rat)
    (hlen : rest.length = rev.length) :
    costOn (e :: rev).reverse (q :: p :: rest).reverse =
      costOn rev.reverse (p :: rest).reverse * e.factor p q := by
  rw [List.reverse_cons, List.reverse_cons, List.reverse_cons, List.append_assoc]
  have h : rest.reverse.length = rev.reverse.length := by simpa using hlen
  change costOn (rev.reverse ++ [e]) (rest.reverse ++ p :: [q]) =
    costOn rev.reverse (rest.reverse ++ [p]) * e.factor p q
  rw [costOn_append_at rev.reverse [e] rest.reverse [q] p h]
  simp [costOn, Rat.mul_one]

/-- The backward rule minimizes the full product on a negative
drift word with the final coordinate prescribed. The input edge and
coordinate lists are both written in reverse order. -/
theorem greedyBackward_le {n : Nat} (hn : 0 < n) {rev : List Edge}
    (ha : ExcursionAlphabet n rev) (hd : ∀ e ∈ rev, e.drift < 0)
    {q : Rat} {rest : List Rat}
    (hlen : rest.length = rev.length)
    (hq : (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1)
    (hband : ∀ p ∈ rest, (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) :
    costOn rev.reverse (greedyBackward ((n : Rat) + 1) rev q).reverse ≤
      costOn rev.reverse (q :: rest).reverse := by
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  let top := (n : Rat) + 1
  induction rev generalizing q rest with
  | nil => exact Rat.le_refl
  | cons e rev ih =>
    cases rest with
    | nil => simp at hlen
    | cons p rest =>
      have hlen' : rest.length = rev.length := by simpa using hlen
      have hp := hband p List.mem_cons_self
      have hpos : 0 < q := by have := hq.1; grind
      have hp' : 0 < p := by have := hp.1; grind
      have htail (r : Rat) (hr : r ∈ rest) := hband r (List.mem_cons_of_mem _ hr)
      have he := hd e List.mem_cons_self
      obtain ⟨v, W, hv, _, rfl⟩ := ha e List.mem_cons_self
      let e := Edge.ofRun n v W
      let prev := min top (e.inverse q)
      have hprev : (n : Rat) ≤ prev ∧ prev ≤ top := backwardShift_in_band (W := W) hv hq.1
      have hprev' : 0 < prev := by have := hprev.1; grind
      have hi : 0 < e.inverse q := by
        have h : prev ≤ e.inverse q := by
          change min top (e.inverse q) ≤ e.inverse q
          rw [Rat.min_def]
          split <;> grind
        grind
      have hs := ih (fun f hf => ha f (List.mem_cons_of_mem _ hf))
        (fun f hf => hd f (List.mem_cons_of_mem _ hf)) hlen' hprev htail
      have hhead : ∃ ps, greedyBackward top rev prev = prev :: ps := by
        cases rev <;> exact ⟨_, rfl⟩
      obtain ⟨ps, hps⟩ := hhead
      have hpslen : ps.length = rev.length := by
        have h := greedyBackward_length top rev prev
        rw [hps, List.length_cons] at h
        omega
      change costOn (e :: rev).reverse (q :: greedyBackward top rev prev).reverse ≤ _
      rw [hps, reverse_cost_cons e rev q prev ps hpslen, ← hps,
        reverse_cost_cons e rev q p rest hlen']
      apply Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hs (Rat.le_of_lt (e.factor_pos hprev' hpos)))
      cases rev with
      | nil =>
        simp only [List.reverse_nil, costOn, Rat.one_mul]
        exact greedy_source_le_factor e hp' hp.2 hpos hi he
      | cons f rev =>
        cases rest with
        | nil => simp at hlen'
        | cons r rest =>
          have hr := htail r List.mem_cons_self
          have hr' : 0 < r := by have := hr.1; grind
          have hl : rest.length = rev.length := by simpa using hlen'
          have hc := costOn_nonneg rev.reverse (r :: rest).reverse
            (fun x hx => by have := (htail x (List.mem_reverse.mp hx)).1; grind)
          rw [reverse_cost_cons f rev prev r rest hl, reverse_cost_cons f rev p r rest hl,
            Rat.mul_assoc, Rat.mul_assoc]
          exact Rat.mul_le_mul_of_nonneg_left (greedy_before_negative f e hr' hp' hp.2 hpos hi he) hc

private theorem greedyForward_length (n : Rat) (word : List Edge) (p : Rat) :
    (greedyForward n word p).length = word.length + 1 := by
  induction word generalizing p with
  | nil => rfl
  | cons e word ih => simp [greedyForward, ih, Nat.add_assoc]

private theorem greedyForward_band {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {p : Rat} (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) :
    ∀ r ∈ greedyForward n word p, (n : Rat) ≤ r ∧ r ≤ (n : Rat) + 1 := by
  induction word generalizing p with
  | nil =>
    intro q hq
    have he : q = p := by simpa [greedyForward] using hq
    rwa [he]
  | cons e word ih =>
    intro q hq
    change q ∈ p :: greedyForward n word (max (n : Rat) (e.transport p)) at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
      exact ih (fun f hf => ha f (List.mem_cons_of_mem _ hf)) (forwardShift_in_band hW hp.2) q hq

private theorem greedyBackward_band {n : Nat} {rev : List Edge} (ha : ExcursionAlphabet n rev)
    {q : Rat} (hq : (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    ∀ p ∈ greedyBackward ((n : Rat) + 1) rev q, (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
  induction rev generalizing q with
  | nil =>
    intro p hp
    have he : p = q := by simpa [greedyBackward] using hp
    rwa [he]
  | cons e rev ih =>
    intro p hp
    change p ∈ q :: greedyBackward ((n : Rat) + 1) rev (min ((n : Rat) + 1) (e.inverse q)) at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq
    · obtain ⟨v, W, hv, _, rfl⟩ := ha e List.mem_cons_self
      exact ih (fun f hf => ha f (List.mem_cons_of_mem _ hf)) (backwardShift_in_band hv hq.1) p hp

/-- Join the backward schedule of the negative block and the forward
schedule of the nonnegative block at the specified common coordinate. -/
def greedyReversal (n : Rat) (leftRev right : List Edge) (mid : Rat) : List Rat :=
  (greedyBackward (n + 1) leftRev mid).tail.reverse ++ greedyForward n right mid

private theorem greedyReversal_length (n : Rat) (leftRev right : List Edge) (mid : Rat) :
    (greedyReversal n leftRev right mid).length = (leftRev.reverse ++ right).length + 1 := by
  have hl := greedyBackward_length (n + 1) leftRev mid
  simp [greedyReversal, List.length_tail, hl, greedyForward_length, Nat.add_assoc]

private theorem greedyReversal_band {n : Nat} {leftRev right : List Edge}
    (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right)
    {mid : Rat} (hm : (n : Rat) ≤ mid ∧ mid ≤ (n : Rat) + 1) :
    ∀ p ∈ greedyReversal n leftRev right mid, (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · apply greedyBackward_band hl hm p
    exact List.mem_of_mem_tail (List.mem_reverse.mp hp)
  · exact greedyForward_band hr hm p hp

/-- For a negative block followed by a nonnegative block, all shifts
apart from their common coordinate can be chosen by the two greedy
rules without worsening the cost. -/
theorem greedyReversal_le {n : Nat} (hn : 0 < n) {leftRev right : List Edge}
    (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right)
    (hdl : ∀ e ∈ leftRev, e.drift < 0) (hdr : ∀ e ∈ right, 0 ≤ e.drift)
    {before after : List Rat} {mid : Rat}
    (hlen : before.length = leftRev.length) (hrlen : after.length = right.length)
    (hband : ∀ p ∈ before ++ mid :: after, (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) :
    costOn (leftRev.reverse ++ right) (greedyReversal n leftRev right mid) ≤
      costOn (leftRev.reverse ++ right) (before ++ mid :: after) := by
  let floor : Rat := n
  let top := floor + 1
  let lcoords := greedyBackward top leftRev mid
  let rcoords := greedyForward floor right mid
  have hn' : 0 < floor := Rat.natCast_pos.mpr hn
  have hm := hband mid (List.mem_append_right _ List.mem_cons_self)
  have hbefore (p : Rat) (hp : p ∈ before.reverse) : floor ≤ p ∧ p ≤ top :=
    hband p (List.mem_append_left _ (List.mem_reverse.mp hp))
  have hafter (p : Rat) (hp : p ∈ after) : floor ≤ p ∧ p ≤ top :=
    hband p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hllen : before.reverse.length = leftRev.length := by simpa using hlen
  have hle := greedyBackward_le hn hl hdl hllen hm hbefore
  have hre := greedyForward_le hn hr hdr hrlen hm hafter
  have hlcoords : lcoords = mid :: lcoords.tail := by cases leftRev <;> rfl
  have hrcoords : rcoords = mid :: rcoords.tail := by cases right <;> rfl
  have hl' : lcoords.tail.reverse.length = leftRev.reverse.length := by
    simp [lcoords, List.length_tail, greedyBackward_length]
  have hlen' : before.length = leftRev.reverse.length := by simpa using hlen
  have hle' : costOn leftRev.reverse (lcoords.tail.reverse ++ [mid]) ≤
      costOn leftRev.reverse (before ++ [mid]) := by
    change costOn leftRev.reverse lcoords.reverse ≤ _ at hle
    have hrev : lcoords.reverse = lcoords.tail.reverse ++ [mid] := by
      simpa only [List.reverse_cons] using congrArg List.reverse hlcoords
    rwa [hrev, List.reverse_cons, List.reverse_reverse] at hle
  have hre' : costOn right (mid :: rcoords.tail) ≤ costOn right (mid :: after) := by
    change costOn right rcoords ≤ _ at hre
    rwa [← hrcoords]
  have hrnonneg : 0 ≤ costOn right (mid :: rcoords.tail) := by
    rw [← hrcoords]
    apply costOn_nonneg
    intro p hp
    have := (greedyForward_band hr hm p hp).1
    grind
  have hlnonneg : 0 ≤ costOn leftRev.reverse (before ++ [mid]) := by
    apply costOn_nonneg
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have := (hband p (List.mem_append_left _ hp)).1
      grind
    · have he : p = mid := by simpa using hp
      rw [he]
      have := hm.1
      grind
  change costOn (leftRev.reverse ++ right) (lcoords.tail.reverse ++ rcoords) ≤ _
  rw [hrcoords]
  rw [costOn_append_at _ _ _ _ _ hl', costOn_append_at _ _ _ _ _ hlen']
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hle' hrnonneg)
    (Rat.mul_le_mul_of_nonneg_left hre' hlnonneg)

private theorem alphabet_reversal {n : Nat} {leftRev right : List Edge}
    (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right) :
    ExcursionAlphabet n (leftRev.reverse ++ right) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hl e (List.mem_reverse.mp he)
  · exact hr e he

private theorem reversal_candidate_iff {n : Nat} {leftRev right : List Edge}
    (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right) (mid : Rat) :
    mid ∈ localLayer n leftRev right ↔
      mid ∈ anchorCandidates n (leftRev.reverse ++ right) leftRev.length := by
  have h := localLayer_mem_iff (alphabet_reversal hl hr) mid
  simpa only [List.reverse_reverse, List.length_reverse] using h

/-- An exact optimum on a word with one conflicting drift boundary
is attained by choosing its common coordinate from the local layer. -/
theorem anchorMinimum_attained_by_greedyReversal {n : Nat} (hn : 0 < n)
    {leftRev right : List Edge} (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right)
    (hdl : ∀ e ∈ leftRev, e.drift < 0) (hdr : ∀ e ∈ right, 0 ≤ e.drift)
    {best : Rat} (hbest : anchorMinimum n (leftRev.reverse ++ right) = some best) :
    ∃ mid ∈ localLayer n leftRev right,
      costOn (leftRev.reverse ++ right) (greedyReversal n leftRev right mid) = best := by
  obtain ⟨p, rest, hperm, hcost⟩ := anchorMinimum_attained hbest
  have hlen := hperm.word_length
  have hband := hperm.anchor_band
  have hlen' : (p :: rest).length = leftRev.length + (right.length + 1) := by
    simp only [List.length_cons, List.length_append, List.length_reverse] at hlen ⊢
    omega
  obtain ⟨before, mid, after, hs, hbefore, hafter⟩ :=
    coordinates_cut (p :: rest) leftRev.length right.length hlen'
  have hmid : (p :: rest)[leftRev.length]? = some mid := by
    rw [hs, List.getElem?_append_right (Nat.le_of_eq hbefore), hbefore, Nat.sub_self]
    rfl
  have hcandidate := (reversal_candidate_iff hl hr mid).mpr (hperm.anchor_coordinate hmid)
  rw [hs] at hband hcost
  have hm := hband mid (List.mem_append_right _ List.mem_cons_self)
  have hle := greedyReversal_le hn hl hr hdl hdr hbefore hafter hband
  rw [hcost] at hle
  obtain ⟨found, hfound, hlo⟩ := anchorMinimum_le_coordinates (Rat.natCast_pos.mpr hn)
    (greedyReversal_length n leftRev right mid) (greedyReversal_band hl hr hm)
  rw [hbest] at hfound
  obtain rfl := Option.some.inj hfound
  exact ⟨mid, hcandidate, Rat.le_antisymm hle hlo⟩

/-- Evaluate the exact product on at most six greedy schedules at the
single conflicting boundary. -/
def reversalMinimum (n : Nat) (leftRev right : List Edge) : Option Rat :=
  ((localLayer n leftRev right).map
    (fun mid => costOn (leftRev.reverse ++ right) (greedyReversal n leftRev right mid))).min?

/-- The one-coordinate search computes the same optimum as the
full rational search on a negative block followed by a
nonnegative block. -/
theorem reversalMinimum_eq_anchorMinimum {n : Nat} (hn : 0 < n)
    {leftRev right : List Edge} (hl : ExcursionAlphabet n leftRev) (hr : ExcursionAlphabet n right)
    (hdl : ∀ e ∈ leftRev, e.drift < 0) (hdr : ∀ e ∈ right, 0 ≤ e.drift) :
    reversalMinimum n leftRev right = anchorMinimum n (leftRev.reverse ++ right) := by
  let word := leftRev.reverse ++ right
  let coords := List.replicate (word.length + 1) (n : Rat)
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hlen : coords.length = word.length + 1 := List.length_replicate
  have hband (p : Rat) (hp : p ∈ coords) : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
    have he : p = (n : Rat) := List.eq_of_mem_replicate hp
    rw [he]
    exact ⟨Rat.le_refl, by grind⟩
  obtain ⟨best, hbest, _⟩ := anchorMinimum_le_coordinates hn' hlen hband
  obtain ⟨mid, hmid, hcost⟩ := anchorMinimum_attained_by_greedyReversal hn hl hr hdl hdr hbest
  unfold reversalMinimum
  rw [hbest]
  apply List.min?_eq_some_iff.mpr
  constructor
  · exact hcost ▸ List.mem_map_of_mem hmid
  · intro price hprice
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hprice
    have hb := (mem_anchorCandidates_iff.mp ((reversal_candidate_iff hl hr q).mp hq)).1
    obtain ⟨r, he, hle⟩ := anchorMinimum_le_coordinates hn'
      (greedyReversal_length n leftRev right q) (greedyReversal_band hl hr hb)
    rw [hbest] at he
    obtain rfl := Option.some.inj he
    exact hle

private theorem greedyForward_from_floor {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word) :
    greedyForward n word n = List.replicate (word.length + 1) (n : Rat) := by
  induction word with
  | nil => rfl
  | cons e word ih =>
    obtain ⟨v, W, hv, _, rfl⟩ := ha e List.mem_cons_self
    rw [greedyForward, forward_floor_fixed hv, ih (fun f hf => ha f (List.mem_cons_of_mem _ hf))]
    rfl

/-- After the first three edges of a forward block, every coordinate
is the lower endpoint. -/
theorem greedyForward_drop_three {n : Nat} {a b c : Edge} {rest : List Edge}
    (ha : ExcursionAlphabet n (a :: b :: c :: rest)) {p : Rat} (hp : p ≤ (n : Rat) + 1) :
    (greedyForward n (a :: b :: c :: rest) p).drop 3 =
      List.replicate (rest.length + 1) (n : Rat) := by
  obtain ⟨v₁, W₁, _, hW₁, rfl⟩ := ha a List.mem_cons_self
  obtain ⟨v₂, W₂, hv₂, hW₂, rfl⟩ := ha b (by simp)
  obtain ⟨v₃, W₃, hv₃, _, rfl⟩ := ha c (by simp)
  change greedyForward n rest
    (max (n : Rat) ((Edge.ofRun n v₃ W₃).transport
      (max (n : Rat) ((Edge.ofRun n v₂ W₂).transport
        (max (n : Rat) ((Edge.ofRun n v₁ W₁).transport p)))))) = _
  rw [forward_three_eq_floor hW₁ hv₂ hW₂ hv₃ hp]
  exact greedyForward_from_floor (fun e he => ha e (by simp [he]))

private theorem backward_ceiling_fixed {n v W : Nat} (hW : 0 < W) :
    min ((n : Rat) + 1) ((Edge.ofRun n v W).inverse ((n : Rat) + 1)) = (n : Rat) + 1 := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  have ht : e.transport top ≤ (n : Rat) + 1 / 2 := output_half hW Rat.le_refl
  have hh : (1 / 2 : Rat) ≤ 1 := by decide +kernel
  have h : e.transport top ≤ top := by change _ ≤ (n : Rat) + 1; grind
  have hs := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt e.b_pos)
  rw [e.transport_spec, ← e.inverse_spec top] at hs
  apply min_eq_ceiling
  apply Rat.le_of_mul_le_mul_left _ e.a_pos
  grind

private theorem greedyBackward_from_ceiling {n : Nat} {rev : List Edge} (ha : ExcursionAlphabet n rev) :
    greedyBackward ((n : Rat) + 1) rev ((n : Rat) + 1) =
      List.replicate (rev.length + 1) ((n : Rat) + 1) := by
  induction rev with
  | nil => rfl
  | cons e rev ih =>
    obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
    rw [greedyBackward, backward_ceiling_fixed hW, ih (fun f hf => ha f (List.mem_cons_of_mem _ hf))]
    rfl

/-- Beyond the last two edges of a negative block, every coordinate
is the upper endpoint when traversing backwards. -/
theorem greedyBackward_drop_two {n : Nat} (hn : 0 < n) {a b : Edge} {rest : List Edge}
    (ha : ExcursionAlphabet n (a :: b :: rest)) (hd : a.drift < 0)
    {q : Rat} (hq : (n : Rat) ≤ q) :
    (greedyBackward ((n : Rat) + 1) (a :: b :: rest) q).drop 2 =
      List.replicate (rest.length + 1) ((n : Rat) + 1) := by
  obtain ⟨v, W, hv, hW, rfl⟩ := ha a List.mem_cons_self
  obtain ⟨v', W', _, hW', rfl⟩ := ha b (by simp)
  change greedyBackward ((n : Rat) + 1) rest
    (min ((n : Rat) + 1) ((Edge.ofRun n v' W').inverse
      (min ((n : Rat) + 1) ((Edge.ofRun n v W).inverse q)))) = _
  rw [backward_two_eq_ceiling hn hW' hv hW hd hq]
  exact greedyBackward_from_ceiling (fun e he => ha e (by simp [he]))

/-- The single reversal in the crossing from 127 gives the exact
product using only the shift shared by the two drift blocks. -/
theorem reversal_minimum_127 :
    reversalMinimum 127 [Edge.ofRun 127 7 1] [Edge.ofRun 127 1 3, Edge.ofRun 127 1 2] =
      some (1343488 / 1331883) := by
  decide +kernel

/-- A genuine negative-to-nonnegative boundary needs at most five
candidate shifts. Its last negative edge cannot be the second
edge of a forward zero-offset chain. -/
theorem reversal_layer_at_most_five {n : Nat} (hn : 0 < n)
    {recent : Edge} {priorRev after : List Edge}
    (ha : ExcursionAlphabet n (recent :: priorRev)) (hd : recent.drift < 0) :
    (localLayer n (recent :: priorRev) after).length ≤ 5 := by
  obtain ⟨v, W, hv, hW, rfl⟩ := ha recent List.mem_cons_self
  exact localLayer_length_of_recent_ge_two (v_ge_two_of_negative_drift hn hv hW hd) hW
    (fun e he => ha e (List.mem_cons_of_mem _ he))

theorem reversal_199_trace :
    OrbitWord 199 199 [Edge.ofRun 199 3 1, unitEdge 199, Edge.ofRun 199 1 2] 95 9 243 512 := by
  exact .cons (show Collatz.ExcursionMap.IsExcursion 199 3 25 1 337 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel)
    (.cons (show Collatz.ExcursionMap.IsExcursion 337 1 169 1 253 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel)
      (.cons (show Collatz.ExcursionMap.IsExcursion 253 1 127 2 95 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel) .nil))

/-- The first conflicting boundary on the genuine crossing from 199
has five distinct candidates. -/
theorem reversal_layer_199 :
    (localLayer 199 [Edge.ofRun 199 3 1] [unitEdge 199, Edge.ofRun 199 1 2]).length = 5 := by
  decide +kernel

private def reversal543Left : List Edge := [Edge.ofRun 543 5 1]
private def reversal543Right : List Edge :=
  [unitEdge 543, Edge.ofRun 543 1 2, Edge.ofRun 543 1 3]

theorem reversal_543_trace :
    OrbitWord 543 543 (reversal543Left.reverse ++ reversal543Right) 109 15 6561 32768 := by
  exact .cons (show Collatz.ExcursionMap.IsExcursion 543 5 17 1 2065 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel)
    (.cons (show Collatz.ExcursionMap.IsExcursion 2065 1 1033 1 1549 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel)
      (.cons (show Collatz.ExcursionMap.IsExcursion 1549 1 775 2 581 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel)
        (.cons (show Collatz.ExcursionMap.IsExcursion 581 1 291 3 109 by unfold Collatz.ExcursionMap.IsExcursion; decide +kernel) .nil)))

/-- A genuine crossing uniquely chooses a shift transported backwards
over two excursions. A search that keeps only one backward link
misses this optimum. -/
theorem reversal_543_two_backward :
    reversalMinimum 543 reversal543Left reversal543Right = some (2719744 / 2714067) ∧
    ∀ q ∈ localLayer 543 reversal543Left reversal543Right,
      q ≠ (543 : Rat) + 7 / 9 →
        (2719744 / 2714067 : Rat) <
          costOn (reversal543Left.reverse ++ reversal543Right)
            (greedyReversal 543 reversal543Left reversal543Right q) := by
  constructor
  · decide +kernel
  · intro q hq hn
    have hlist : localLayer 543 reversal543Left reversal543Right =
        [543, 544, (543 : Rat) + 1 / 2, (543 : Rat) + 1 / 3, (543 : Rat) + 7 / 9] := by
      decide +kernel
    rw [hlist] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | h
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim (hn h)

end Collatz.ExcursionAnchor
