import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

/-!
# Affine endpoint reduction for zero-offset blocks

In normalized coordinates `p=n+s` and `q=n+t`, a switch factor is
`p/q` on a clipped edge. On an unclipped edge it is either independent
of `q` (arrival) or independent of `p` (departure). Along a chain of
zero offsets the factors telescope to the ratio of its two boundary
coordinates. Moving such a block makes its total contribution a
linear-fractional function of a single coordinate.
-/

namespace Collatz.ExcursionAnchor

theorem div_le_div_iff_pos {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have hleft : a / b * (b * d) = a * d := by
    rw [← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hb)]
  have hright : c / d * (b * d) = c * b := by
    rw [Rat.mul_comm b d, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hd)]
  have hpos := Rat.mul_pos hb hd
  constructor
  · intro h
    have hs := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hpos)
    rwa [hleft, hright] at hs
  · intro h
    apply Rat.le_of_mul_le_mul_right _ hpos
    simpa only [hleft, hright] using h

private theorem div_eq_div_iff_pos {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [Rat.le_antisymm_iff (a := a / b), Rat.le_antisymm_iff (a := a * d)]
  rw [div_le_div_iff_pos hb hd, div_le_div_iff_pos hd hb]

/-- A quotient of affine functions with positive denominators is minimized
at an endpoint of an interval. The cross-product determinant fixes its
direction of monotonicity without a calculus argument. -/
theorem affine_ratio_end {a b c d lo x hi : Rat} (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hden_lo : 0 < c * lo + d) (hden_x : 0 < c * x + d) (hden_hi : 0 < c * hi + d) :
    (a * lo + b) / (c * lo + d) ≤ (a * x + b) / (c * x + d) ∨
      (a * hi + b) / (c * hi + d) ≤ (a * x + b) / (c * x + d) := by
  by_cases hs : 0 ≤ a * d - b * c
  · apply Or.inl
    rw [div_le_div_iff_pos hden_lo hden_x, Rat.le_iff_sub_nonneg]
    have heq : (a * x + b) * (c * lo + d) - (a * lo + b) * (c * x + d) =
        (a * d - b * c) * (x - lo) := by grind
    rw [heq]
    exact Rat.mul_nonneg hs ((Rat.le_iff_sub_nonneg lo x).mp hlo)
  · apply Or.inr
    rw [div_le_div_iff_pos hden_hi hden_x, Rat.le_iff_sub_nonneg]
    have heq : (a * x + b) * (c * hi + d) - (a * hi + b) * (c * x + d) =
        (b * c - a * d) * (hi - x) := by grind
    rw [heq]
    have hr : 0 ≤ b * c - a * d := by grind
    exact Rat.mul_nonneg hr ((Rat.le_iff_sub_nonneg x hi).mp hhi)

structure Edge where
  a : Rat
  b : Rat
  drift : Rat
  a_pos : 0 < a
  b_pos : 0 < b

/-- The better of the two normalized factor formulas, expressed by the
clipping regime and the sign of the floor drift. -/
def Edge.factor (e : Edge) (p q : Rat) : Rat :=
  if e.b * q ≤ e.a * p + e.drift then p / q
  else if 0 ≤ e.drift then e.b * p / (e.a * p + e.drift)
  else (e.b * q - e.drift) / (e.a * q)

theorem Edge.factor_of_clipped (e : Edge) {p q : Rat} (h : e.b * q ≤ e.a * p + e.drift) :
    e.factor p q = p / q := by
  simp [Edge.factor, h]

theorem Edge.factor_of_unclipped (e : Edge) {p q : Rat} (_hp : 0 < p) (hq : 0 < q)
    (h : e.a * p + e.drift ≤ e.b * q) :
    e.factor p q =
      if 0 ≤ e.drift then e.b * p / (e.a * p + e.drift)
      else (e.b * q - e.drift) / (e.a * q) := by
  by_cases hc : e.b * q ≤ e.a * p + e.drift
  · have heq := Rat.le_antisymm hc h
    rw [e.factor_of_clipped hc]
    split
    · rw [← heq, div_eq_div_iff_pos hq (Rat.mul_pos e.b_pos hq)]
      grind
    · rw [div_eq_div_iff_pos hq (Rat.mul_pos e.a_pos hq)]
      have hd : e.b * q - e.drift = e.a * p := by grind
      rw [hd]
      grind
  · simp [Edge.factor, hc]

/-- The affine transport for a zero-offset edge. -/
def Edge.transport (e : Edge) (p : Rat) : Rat :=
  (e.a * p + e.drift) / e.b

theorem Edge.transport_spec (e : Edge) (p : Rat) :
    e.b * e.transport p = e.a * p + e.drift := by
  rw [Edge.transport, Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt e.b_pos)]

theorem Edge.transport_affine (e : Edge) (p : Rat) :
    e.transport p = (e.a / e.b) * p + e.drift / e.b := by
  unfold Edge.transport
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind

/-- At a zero-offset edge the normalized factor is exactly the endpoint
ratio, even when arrival and departure are tied. -/
theorem Edge.factor_of_transport (e : Edge) (p : Rat) :
    e.factor p (e.transport p) = p / e.transport p :=
  e.factor_of_clipped (by rw [e.transport_spec]; exact Rat.le_refl)

private def affine (coefficients : Rat × Rat) (x : Rat) : Rat :=
  coefficients.1 * x + coefficients.2

private def Edge.leftCoefficients (e : Edge) (p : Rat) (clipped : Bool) : Rat × Rat :=
  if clipped then (0, p)
  else if 0 ≤ e.drift then (e.b * p / (e.a * p + e.drift), 0)
  else (e.b / e.a, -e.drift / e.a)

private def Edge.rightCoefficients (e : Edge) (q : Rat) (clipped : Bool) : Rat × Rat :=
  if clipped then (0, q)
  else if 0 ≤ e.drift then (e.a / e.b, e.drift / e.b)
  else (e.a * q / (e.b * q - e.drift), 0)

/-- A closed clipping regime. At a zero offset both regimes agree. -/
def Edge.inRegime (e : Edge) (clipped : Bool) (p q : Rat) : Prop :=
  if clipped then e.b * q ≤ e.a * p + e.drift
  else e.a * p + e.drift ≤ e.b * q

private theorem Edge.left_form (e : Edge) {p q : Rat} {clipped : Bool}
    (hp : 0 < p) (hq : 0 < q) (h : e.inRegime clipped p q) :
    e.factor p q * q = affine (e.leftCoefficients p clipped) q := by
  cases clipped with
  | true =>
    rw [e.factor_of_clipped h, Rat.div_mul_cancel (Rat.ne_of_gt hq)]
    simp [Edge.leftCoefficients, affine, Rat.zero_add]
  | false =>
    rw [e.factor_of_unclipped hp hq h]
    simp only [Edge.leftCoefficients, Bool.false_eq_true, if_false]
    split
    · simp [affine, Rat.add_zero]
    · have hq0 := Rat.ne_of_gt hq
      have ha := Rat.ne_of_gt e.a_pos
      simp only [affine, Rat.div_def]
      have hi : (e.a * q)⁻¹ = q⁻¹ * e.a⁻¹ := Rat.inv_mul_rev ..
      rw [hi]
      have hc := Rat.mul_inv_cancel q hq0
      grind

private theorem Edge.right_form (e : Edge) {p q : Rat} {clipped : Bool}
    (hp : 0 < p) (hq : 0 < q) (h : e.inRegime clipped p q) :
    0 < affine (e.rightCoefficients q clipped) p ∧
      e.factor p q / p = 1 / affine (e.rightCoefficients q clipped) p := by
  cases clipped with
  | true =>
    rw [e.factor_of_clipped h]
    simp only [Edge.rightCoefficients, if_true, affine, Rat.zero_mul, Rat.zero_add]
    refine ⟨hq, ?_⟩
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul]
    have hp0 := Rat.ne_of_gt hp
    have hc := Rat.mul_inv_cancel p hp0
    grind
  | false =>
    rw [e.factor_of_unclipped hp hq h]
    simp only [Edge.rightCoefficients, Bool.false_eq_true, if_false, affine]
    split
    · rename_i hg
      let r := e.a * p + e.drift
      have hr : 0 < r := by
        have hprod := Rat.mul_pos e.a_pos hp
        dsimp [r]
        grind
      have hb0 := Rat.ne_of_gt e.b_pos
      have hp0 := Rat.ne_of_gt hp
      have hc := Rat.mul_inv_cancel p hp0
      have heq : e.a / e.b * p + e.drift / e.b = r / e.b := by
        simp only [r, Rat.div_def]
        grind
      rw [heq]
      have hpositive : 0 < r / e.b := by
        rw [Rat.div_def]
        exact Rat.mul_pos hr (Rat.inv_pos.mpr e.b_pos)
      refine ⟨hpositive, ?_⟩
      change e.b * p / r / p = 1 / (r / e.b)
      rw [div_eq_div_iff_pos hp hpositive]
      have hr0 := Rat.ne_of_gt hr
      have hbInv := Rat.mul_inv_cancel e.b hb0
      have hrInv := Rat.mul_inv_cancel r hr0
      simp only [Rat.div_def]
      grind
    · rename_i hg
      let r := e.b * q - e.drift
      have hr : 0 < r := by
        have hprod := Rat.mul_pos e.b_pos hq
        dsimp [r]
        grind
      have hscale := Rat.mul_pos e.a_pos hq
      have hscale0 := Rat.ne_of_gt hscale
      have hr0 := Rat.ne_of_gt hr
      simp only [Rat.add_zero]
      have hpositive : 0 < e.a * q / r * p := by
        rw [Rat.div_def]
        exact Rat.mul_pos (Rat.mul_pos hscale (Rat.inv_pos.mpr hr)) hp
      refine ⟨hpositive, ?_⟩
      change r / (e.a * q) / p = 1 / (e.a * q / r * p)
      rw [div_eq_div_iff_pos hp hpositive]
      have hc := Rat.mul_inv_cancel (e.a * q) hscale0
      have hrc := Rat.mul_inv_cancel r hr0
      simp only [Rat.div_def]
      grind

def endpoint : List Edge → Rat → Rat
  | [], p => p
  | e :: rest, p => endpoint rest (e.transport p)

private def composition : List Edge → Rat × Rat
  | [] => (1, 0)
  | e :: rest =>
    let c := composition rest
    (c.1 * (e.a / e.b), c.1 * (e.drift / e.b) + c.2)

private theorem endpoint_eq (edges : List Edge) (p : Rat) :
    endpoint edges p = affine (composition edges) p := by
  induction edges generalizing p with
  | nil => simp [endpoint, composition, affine, Rat.one_mul, Rat.add_zero]
  | cons e rest ih =>
    rw [endpoint, ih, e.transport_affine]
    simp only [affine, composition]
    grind

def positiveChain : List Edge → Rat → Prop
  | [], p => 0 < p
  | e :: rest, p => 0 < p ∧ positiveChain rest (e.transport p)

theorem positiveChain_start {edges : List Edge} {p : Rat}
    (h : positiveChain edges p) : 0 < p := by
  cases edges with
  | nil => exact h
  | cons _ _ => exact h.1

theorem positiveChain_end {edges : List Edge} {p : Rat}
    (h : positiveChain edges p) : 0 < endpoint edges p := by
  induction edges generalizing p with
  | nil => exact h
  | cons _ _ ih => exact ih h.2

def insideFactor : List Edge → Rat → Rat
  | [], _ => 1
  | e :: rest, p => e.factor p (e.transport p) * insideFactor rest (e.transport p)

theorem insideFactor_ratio {edges : List Edge} {p : Rat}
    (h : positiveChain edges p) : insideFactor edges p = p / endpoint edges p := by
  induction edges generalizing p with
  | nil =>
    have hp : 0 < p := h
    rw [insideFactor, endpoint, Rat.div_def, Rat.mul_inv_cancel p (Rat.ne_of_gt hp)]
  | cons e rest ih =>
    rw [insideFactor, e.factor_of_transport, ih h.2, endpoint]
    have ht := positiveChain_start h.2
    have hc := Rat.mul_inv_cancel (e.transport p) (Rat.ne_of_gt ht)
    simp only [Rat.div_def]
    grind

/-- One edge outside a moving block. Its exterior coordinate stays fixed. -/
structure Boundary where
  edge : Edge
  exterior : Rat
  positive : 0 < exterior
  clipped : Bool

def leftFactor : Option Boundary → Rat → Rat
  | none, _ => 1
  | some b, p => b.edge.factor b.exterior p

def rightFactor : Option Boundary → Rat → Rat
  | none, _ => 1
  | some b, p => b.edge.factor p b.exterior

def leftAllowed : Option Boundary → Rat → Prop
  | none, _ => True
  | some b, p => b.edge.inRegime b.clipped b.exterior p

def rightAllowed : Option Boundary → Rat → Prop
  | none, _ => True
  | some b, p => b.edge.inRegime b.clipped p b.exterior

private def leftForm : Option Boundary → Rat × Rat
  | none => (1, 0)
  | some b => b.edge.leftCoefficients b.exterior b.clipped

private def rightForm : Option Boundary → Rat × Rat
  | none => (1, 0)
  | some b => b.edge.rightCoefficients b.exterior b.clipped

private theorem left_normalized {b : Option Boundary} {p : Rat} (hp : 0 < p)
    (h : leftAllowed b p) : leftFactor b p * p = affine (leftForm b) p := by
  cases b with
  | none => simp [leftFactor, leftForm, affine, Rat.one_mul, Rat.add_zero]
  | some b => exact b.edge.left_form b.positive hp h

private theorem right_normalized {b : Option Boundary} {p : Rat} (hp : 0 < p)
    (h : rightAllowed b p) : 0 < affine (rightForm b) p ∧
      rightFactor b p / p = 1 / affine (rightForm b) p := by
  cases b with
  | none => simpa [rightFactor, rightForm, affine, Rat.one_mul, Rat.add_zero] using hp
  | some b => exact b.edge.right_form hp b.positive h

/-- The internal edges of a moving block are kept at zero offset.
Either exterior edge may be absent at the end of a trace. -/
structure Block where
  before : Option Boundary
  inside : List Edge
  after : Option Boundary

def Block.allowed (block : Block) (p : Rat) : Prop :=
  positiveChain block.inside p ∧ leftAllowed block.before p ∧
    rightAllowed block.after (endpoint block.inside p)

def Block.value (block : Block) (p : Rat) : Rat :=
  leftFactor block.before p * insideFactor block.inside p *
    rightFactor block.after (endpoint block.inside p)

private def Block.denominator (block : Block) : Rat × Rat :=
  let r := rightForm block.after
  let c := composition block.inside
  (r.1 * c.1, r.1 * c.2 + r.2)

private theorem Block.value_ratio (block : Block) {p : Rat} (h : block.allowed p) :
    0 < affine block.denominator p ∧
      block.value p = affine (leftForm block.before) p / affine block.denominator p := by
  obtain ⟨hchain, hleft, hright⟩ := h
  have hleftEq := left_normalized (positiveChain_start hchain) hleft
  have ⟨hrightPos, hrightEq⟩ := right_normalized (positiveChain_end hchain) hright
  have hcompose : affine block.denominator p =
      affine (rightForm block.after) (endpoint block.inside p) := by
    rw [endpoint_eq]
    simp only [Block.denominator, affine]
    grind
  rw [hcompose]
  refine ⟨hrightPos, ?_⟩
  calc
    _ = (leftFactor block.before p * p) *
          (rightFactor block.after (endpoint block.inside p) / endpoint block.inside p) := by
      rw [Block.value, insideFactor_ratio hchain]
      simp only [Rat.div_def]
      grind
    _ = _ := by
      rw [hleftEq, hrightEq, Rat.div_def, Rat.one_mul, ← Rat.div_def]

/-- A free zero-offset block can move to either endpoint without increasing
its contribution. The endpoints must preserve the exterior clipping regimes
and keep all coordinates positive. -/
theorem Block.move_to_endpoint (block : Block) {lo p hi : Rat} (hlo : lo ≤ p) (hhi : p ≤ hi)
    (hvalidLo : block.allowed lo) (hvalid : block.allowed p) (hvalidHi : block.allowed hi) :
    block.value lo ≤ block.value p ∨ block.value hi ≤ block.value p := by
  obtain ⟨hl, hvl⟩ := block.value_ratio hvalidLo
  obtain ⟨hp, hv⟩ := block.value_ratio hvalid
  obtain ⟨hh, hvh⟩ := block.value_ratio hvalidHi
  rw [hvl, hv, hvh]
  exact affine_ratio_end hlo hhi hl hp hh

/-- A closed affine half-space in one rational parameter. -/
structure Constraint where
  slope : Rat
  rhs : Rat

def Constraint.holds (c : Constraint) (p : Rat) : Prop :=
  c.slope * p ≤ c.rhs

def Constraint.tight (c : Constraint) (p : Rat) : Prop :=
  c.slope * p = c.rhs

private theorem rat_div_one (p : Rat) : p / 1 = p := by
  simpa only [Rat.mul_one] using (Rat.div_mul_cancel (a := p) (b := 1) (by decide))

private theorem Constraint.positive_iff (c : Constraint) {p : Rat} (h : 0 < c.slope) :
    c.holds p ↔ p ≤ c.rhs / c.slope := by
  have hh := div_le_div_iff_pos (a := p) (c := c.rhs) (by decide : (0 : Rat) < 1) h
  rw [rat_div_one, Rat.mul_one, Rat.mul_comm p] at hh
  exact hh.symm

private theorem Constraint.negative_iff (c : Constraint) {p : Rat} (h : c.slope < 0) :
    c.holds p ↔ -c.rhs / -c.slope ≤ p := by
  have hp : 0 < -c.slope := by grind
  have hh := div_le_div_iff_pos (a := -c.rhs) (c := p) hp (by decide : (0 : Rat) < 1)
  rw [rat_div_one, Rat.mul_one] at hh
  rw [hh]
  unfold Constraint.holds
  grind

private theorem Constraint.positive_tight (c : Constraint) (h : 0 < c.slope) :
    c.tight (c.rhs / c.slope) := by
  unfold Constraint.tight
  rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt h)]

private theorem Constraint.negative_tight (c : Constraint) (h : c.slope < 0) :
    c.tight (-c.rhs / -c.slope) := by
  have hp : 0 < -c.slope := by grind
  have he : (-c.rhs / -c.slope) * -c.slope = -c.rhs :=
    Rat.div_mul_cancel (Rat.ne_of_gt hp)
  unfold Constraint.tight
  grind

structure Interval where
  lower : Rat
  upper : Rat

def Interval.contains (interval : Interval) (p : Rat) : Prop :=
  interval.lower ≤ p ∧ p ≤ interval.upper

def Interval.restrict (interval : Interval) (c : Constraint) : Interval :=
  if 0 < c.slope then
    ⟨interval.lower, min interval.upper (c.rhs / c.slope)⟩
  else if c.slope < 0 then
    ⟨max interval.lower (-c.rhs / -c.slope), interval.upper⟩
  else interval

def Interval.restrictAll (interval : Interval) (constraints : List Constraint) : Interval :=
  constraints.foldl Interval.restrict interval

/-- The restricted interval still contains the given feasible point, and
both new endpoints come from an original bound or a tight constraint. -/
structure Restriction (old new : Interval) (constraints : List Constraint) (p : Rat) : Prop where
  contains : new.contains p
  valid : ∀ q, new.contains q → old.contains q ∧ ∀ c ∈ constraints, c.holds q
  lower_active : new.lower = old.lower ∨ ∃ c ∈ constraints, c.tight new.lower
  upper_active : new.upper = old.upper ∨ ∃ c ∈ constraints, c.tight new.upper

private theorem restrict_one (interval : Interval) (c : Constraint) {p : Rat}
    (hp : interval.contains p) (hc : c.holds p) :
    Restriction interval (interval.restrict c) [c] p := by
  unfold Interval.restrict
  by_cases hpos : 0 < c.slope
  · rw [if_pos hpos, Rat.min_def]
    have hb := (c.positive_iff hpos).mp hc
    split
    · rename_i hbound
      refine ⟨hp, ?_, Or.inl rfl, Or.inl rfl⟩
      intro q hq
      refine ⟨hq, ?_⟩
      intro z hz
      have hz' : z = c := by simpa using hz
      subst z
      exact (c.positive_iff hpos).mpr (Rat.le_trans hq.2 hbound)
    · rename_i hbound
      refine ⟨⟨hp.1, hb⟩, ?_, Or.inl rfl, Or.inr ⟨c, by simp, c.positive_tight hpos⟩⟩
      intro q hq
      refine ⟨⟨hq.1, Rat.le_trans hq.2 (Rat.le_of_lt ((Rat.not_le).mp hbound))⟩, ?_⟩
      intro z hz
      have hz' : z = c := by simpa using hz
      subst z
      exact (c.positive_iff hpos).mpr hq.2
  · rw [if_neg hpos]
    by_cases hneg : c.slope < 0
    · rw [if_pos hneg, Rat.max_def]
      have hb := (c.negative_iff hneg).mp hc
      split
      · rename_i hbound
        refine ⟨⟨hb, hp.2⟩, ?_, Or.inr ⟨c, by simp, c.negative_tight hneg⟩, Or.inl rfl⟩
        intro q hq
        refine ⟨⟨Rat.le_trans hbound hq.1, hq.2⟩, ?_⟩
        intro z hz
        have hz' : z = c := by simpa using hz
        subst z
        exact (c.negative_iff hneg).mpr hq.1
      · rename_i hbound
        refine ⟨hp, ?_, Or.inl rfl, Or.inl rfl⟩
        intro q hq
        refine ⟨hq, ?_⟩
        intro z hz
        have hz' : z = c := by simpa using hz
        subst z
        exact (c.negative_iff hneg).mpr
          (Rat.le_trans (Rat.le_of_lt ((Rat.not_le).mp hbound)) hq.1)
    · rw [if_neg hneg]
      have hs : c.slope = 0 := by grind
      refine ⟨hp, ?_, Or.inl rfl, Or.inl rfl⟩
      intro q hq
      refine ⟨hq, ?_⟩
      intro z hz
      have hz' : z = c := by simpa using hz
      subst z
      simpa only [Constraint.holds, hs, Rat.zero_mul] using hc

theorem Interval.restrictAll_spec (interval : Interval) (constraints : List Constraint)
    {p : Rat} (hp : interval.contains p) (h : ∀ c ∈ constraints, c.holds p) :
    Restriction interval (interval.restrictAll constraints) constraints p := by
  induction constraints generalizing interval with
  | nil =>
    exact ⟨hp, fun _ hq => ⟨hq, by simp⟩, Or.inl rfl, Or.inl rfl⟩
  | cons c rest ih =>
    have hhead := restrict_one interval c hp (h c List.mem_cons_self)
    have htail := ih (interval.restrict c) hhead.contains
      (fun z hz => h z (List.mem_cons_of_mem _ hz))
    change Restriction interval ((interval.restrict c).restrictAll rest) (c :: rest) p
    refine ⟨htail.contains, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨hq', hrest⟩ := htail.valid q hq
      obtain ⟨hq'', hfirst⟩ := hhead.valid q hq'
      refine ⟨hq'', ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hfirst _ List.mem_cons_self
      · exact hrest z hz
    · rcases htail.lower_active with he | ⟨z, hz, ht⟩
      · rw [he]
        rcases hhead.lower_active with he' | ⟨z, hz, ht⟩
        · exact Or.inl he'
        · exact Or.inr ⟨z, List.mem_cons.mpr (Or.inl (by simpa using hz)), ht⟩
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, ht⟩
    · rcases htail.upper_active with he | ⟨z, hz, ht⟩
      · rw [he]
        rcases hhead.upper_active with he' | ⟨z, hz, ht⟩
        · exact Or.inl he'
        · exact Or.inr ⟨z, List.mem_cons.mpr (Or.inl (by simpa using hz)), ht⟩
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, ht⟩

private def compose (outer inner : Rat × Rat) : Rat × Rat :=
  (outer.1 * inner.1, outer.1 * inner.2 + outer.2)

private theorem affine_compose (outer inner : Rat × Rat) (p : Rat) :
    affine (compose outer inner) p = affine outer (affine inner p) := by
  simp only [affine, compose]
  grind

private def coordinates : List Edge → List (Rat × Rat)
  | [] => [(1, 0)]
  | e :: rest => (1, 0) :: (coordinates rest).map
      (fun form => compose form (e.a / e.b, e.drift / e.b))

private theorem start_coordinate (edges : List Edge) : ((1, 0) : Rat × Rat) ∈ coordinates edges := by
  cases edges <;> simp [coordinates]

/-- Every coordinate of the zero-offset block stays in the shift band. -/
def Block.inBand (block : Block) (n p : Rat) : Prop :=
  ∀ form ∈ coordinates block.inside, n ≤ affine form p ∧ affine form p ≤ n + 1

theorem chain_positive_of_band {edges : List Edge} {n p : Rat} (hn : 0 < n)
    (h : ∀ form ∈ coordinates edges, n ≤ affine form p ∧ affine form p ≤ n + 1) :
    positiveChain edges p := by
  have start_pos (word : List Edge) (x : Rat)
      (hx : ∀ form ∈ coordinates word, n ≤ affine form x ∧ affine form x ≤ n + 1) : 0 < x := by
    have hstart : n ≤ x := by
      simpa [affine, Rat.one_mul, Rat.add_zero] using (hx (1, 0) (start_coordinate word)).1
    grind
  induction edges generalizing p with
  | nil => exact start_pos [] p h
  | cons e rest ih =>
    refine ⟨start_pos (e :: rest) p h, ih ?_⟩
    intro form hform
    let edgeForm : Rat × Rat := (e.a / e.b, e.drift / e.b)
    have hmem : compose form edgeForm ∈ coordinates (e :: rest) :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem hform)
    have hpos := h _ hmem
    rw [affine_compose] at hpos
    have heq : affine edgeForm p = e.transport p := (e.transport_affine p).symm
    rwa [heq] at hpos

private def Constraint.between (left right : Rat × Rat) : Constraint :=
  ⟨left.1 - right.1, right.2 - left.2⟩

private theorem Constraint.holds_between (left right : Rat × Rat) (p : Rat) :
    (Constraint.between left right).holds p ↔ affine left p ≤ affine right p := by
  simp only [Constraint.holds, Constraint.between, affine]
  grind

private theorem Constraint.tight_between (left right : Rat × Rat) (p : Rat) :
    (Constraint.between left right).tight p ↔ affine left p = affine right p := by
  simp only [Constraint.tight, Constraint.between, affine]
  grind

private def bandConstraints (n : Rat) (forms : List (Rat × Rat)) : List Constraint :=
  forms.flatMap fun form =>
    [Constraint.between (0, n) form, Constraint.between form (0, n + 1)]

private theorem band_constraints_iff {n p : Rat} {forms : List (Rat × Rat)} :
    (∀ c ∈ bandConstraints n forms, c.holds p) ↔
      ∀ form ∈ forms, n ≤ affine form p ∧ affine form p ≤ n + 1 := by
  constructor
  · intro h form hform
    have hl := h (Constraint.between (0, n) form)
      (List.mem_flatMap.mpr ⟨form, hform, by simp⟩)
    have hu := h (Constraint.between form (0, n + 1))
      (List.mem_flatMap.mpr ⟨form, hform, by simp⟩)
    rw [Constraint.holds_between] at hl hu
    simpa only [affine, Rat.zero_mul, Rat.zero_add] using And.intro hl hu
  · intro h c hc
    obtain ⟨form, hform, hc⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [Constraint.holds_between]
      simpa only [affine, Rat.zero_mul, Rat.zero_add] using (h form hform).1
    · rw [Constraint.holds_between]
      simpa only [affine, Rat.zero_mul, Rat.zero_add] using (h form hform).2

private theorem band_constraint_tight {n p : Rat} {forms : List (Rat × Rat)} {c : Constraint}
    (hc : c ∈ bandConstraints n forms) (ht : c.tight p) :
    ∃ form ∈ forms, affine form p = n ∨ affine form p = n + 1 := by
  obtain ⟨form, hform, hc⟩ := List.mem_flatMap.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  refine ⟨form, hform, ?_⟩
  rcases hc with rfl | rfl
  · apply Or.inl
    have he := (Constraint.tight_between _ _ _).mp ht
    simpa only [affine, Rat.zero_mul, Rat.zero_add] using he.symm
  · apply Or.inr
    have he := (Constraint.tight_between _ _ _).mp ht
    simpa only [affine, Rat.zero_mul, Rat.zero_add] using he

private def Edge.sourceForm (e : Edge) (form : Rat × Rat) : Rat × Rat :=
  (e.a * form.1, e.a * form.2 + e.drift)

private def Edge.targetForm (e : Edge) (form : Rat × Rat) : Rat × Rat :=
  (e.b * form.1, e.b * form.2)

private theorem Edge.sourceForm_eq (e : Edge) (form : Rat × Rat) (p : Rat) :
    affine (e.sourceForm form) p = e.a * affine form p + e.drift := by
  simp only [Edge.sourceForm, affine]
  grind

private theorem Edge.targetForm_eq (e : Edge) (form : Rat × Rat) (p : Rat) :
    affine (e.targetForm form) p = e.b * affine form p := by
  simp only [Edge.targetForm, affine]
  grind

private def Edge.regimeConstraint (e : Edge) (clipped : Bool) (source target : Rat × Rat) :
    Constraint :=
  if clipped then Constraint.between (e.targetForm target) (e.sourceForm source)
  else Constraint.between (e.sourceForm source) (e.targetForm target)

private theorem Edge.regime_constraint (e : Edge) (clipped : Bool) (source target : Rat × Rat)
    (p : Rat) :
    (e.regimeConstraint clipped source target).holds p ↔
      e.inRegime clipped (affine source p) (affine target p) := by
  cases clipped <;>
    simp [Edge.regimeConstraint, Constraint.holds_between, Edge.inRegime, Edge.sourceForm_eq,
      Edge.targetForm_eq]

private theorem Edge.regime_tight (e : Edge) (clipped : Bool) (source target : Rat × Rat)
    (p : Rat) (h : (e.regimeConstraint clipped source target).tight p) :
    e.b * affine target p = e.a * affine source p + e.drift := by
  cases clipped <;>
    simp [Edge.regimeConstraint, Constraint.tight_between, Edge.sourceForm_eq, Edge.targetForm_eq] at h
  · exact h.symm
  · exact h

private def Block.exteriorConstraints (block : Block) : List Constraint :=
  block.before.toList.map (fun b => b.edge.regimeConstraint b.clipped (0, b.exterior) (1, 0)) ++
    block.after.toList.map
      (fun b => b.edge.regimeConstraint b.clipped (composition block.inside) (0, b.exterior))

private def Block.constraints (block : Block) (n : Rat) : List Constraint :=
  bandConstraints n (coordinates block.inside) ++ block.exteriorConstraints

private theorem Block.constraints_iff (block : Block) (n p : Rat) :
    (∀ c ∈ block.constraints n, c.holds p) ↔
      block.inBand n p ∧ leftAllowed block.before p ∧
        rightAllowed block.after (endpoint block.inside p) := by
  rw [Block.constraints, Block.exteriorConstraints]
  simp only [List.forall_mem_append, band_constraints_iff, Block.inBand]
  apply and_congr_right
  intro _
  apply and_congr
  · cases block.before with
    | none => simp [leftAllowed]
    | some b =>
      simp [leftAllowed, Edge.regime_constraint, affine, Rat.zero_mul, Rat.zero_add,
        Rat.one_mul, Rat.add_zero]
  · cases block.after with
    | none => simp [rightAllowed]
    | some b =>
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, Edge.regime_constraint, rightAllowed]
      rw [endpoint_eq]
      simp [affine, Rat.zero_mul, Rat.zero_add]

/-- A coordinate is on the shift boundary, or an exterior offset is zero
and the block can be joined to its neighbor. -/
def Block.touches (block : Block) (n p : Rat) : Prop :=
  (∃ form ∈ coordinates block.inside, affine form p = n ∨ affine form p = n + 1) ∨
    (∃ b, block.before = some b ∧ b.edge.b * p = b.edge.a * b.exterior + b.edge.drift) ∨
    (∃ b, block.after = some b ∧
      b.edge.b * b.exterior = b.edge.a * endpoint block.inside p + b.edge.drift)

private theorem Block.start_touches (block : Block) {n p : Rat}
    (h : p = n ∨ p = n + 1) : block.touches n p := by
  refine Or.inl ⟨(1, 0), start_coordinate _, ?_⟩
  simpa [affine, Rat.one_mul, Rat.add_zero] using h

private theorem Block.constraint_touches (block : Block) {n p : Rat} {c : Constraint}
    (hc : c ∈ block.constraints n) (ht : c.tight p) : block.touches n p := by
  rcases List.mem_append.mp hc with hband | houter
  · exact Or.inl (band_constraint_tight hband ht)
  · rcases List.mem_append.mp houter with hbefore | hafter
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hbefore
      have hb' : block.before = some b := by simpa using hb
      have he := b.edge.regime_tight b.clipped (0, b.exterior) (1, 0) p ht
      refine Or.inr (Or.inl ⟨b, hb', ?_⟩)
      simpa [affine, Rat.zero_mul, Rat.zero_add, Rat.one_mul, Rat.add_zero] using he
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hafter
      have hb' : block.after = some b := by simpa using hb
      have he := b.edge.regime_tight b.clipped (composition block.inside) (0, b.exterior) p ht
      refine Or.inr (Or.inr ⟨b, hb', ?_⟩)
      rw [endpoint_eq]
      simpa [affine, Rat.zero_mul, Rat.zero_add] using he

/-- Move an entire zero-offset block until a coordinate hits the shift
boundary or an exterior offset becomes zero. All coordinates stay in the
band, both exterior regimes are preserved, and the product cannot increase. -/
theorem Block.anchor_or_join (block : Block) {n p : Rat} (hn : 0 < n)
    (hband : block.inBand n p) (hvalid : block.allowed p) :
    ∃ q, block.inBand n q ∧ block.allowed q ∧ block.value q ≤ block.value p ∧
      block.touches n q := by
  let interval : Interval := ⟨n, n + 1⟩
  let restricted := interval.restrictAll (block.constraints n)
  have hp : interval.contains p := by
    simpa [interval, Interval.contains, affine, Rat.one_mul, Rat.add_zero] using
      hband (1, 0) (start_coordinate block.inside)
  have hh := (block.constraints_iff n p).mpr ⟨hband, hvalid.2.1, hvalid.2.2⟩
  have spec : Restriction interval restricted (block.constraints n) p :=
    interval.restrictAll_spec _ hp hh
  have horder := Rat.le_trans spec.contains.1 spec.contains.2
  have hvalidAt (q : Rat) (hq : restricted.contains q) :
      block.inBand n q ∧ block.allowed q := by
    obtain ⟨hqb, hleft, hright⟩ :=
      (block.constraints_iff n q).mp (spec.valid q hq).2
    exact ⟨hqb, chain_positive_of_band hn hqb, hleft, hright⟩
  have hl := hvalidAt restricted.lower ⟨Rat.le_refl, horder⟩
  have hu := hvalidAt restricted.upper ⟨horder, Rat.le_refl⟩
  rcases block.move_to_endpoint spec.contains.1 spec.contains.2 hl.2 hvalid hu.2 with he | he
  · refine ⟨restricted.lower, hl.1, hl.2, he, ?_⟩
    rcases spec.lower_active with h | ⟨c, hc, ht⟩
    · exact block.start_touches (Or.inl h)
    · exact block.constraint_touches hc ht
  · refine ⟨restricted.upper, hu.1, hu.2, he, ?_⟩
    rcases spec.upper_active with h | ⟨c, hc, ht⟩
    · exact block.start_touches (Or.inr h)
    · exact block.constraint_touches hc ht

/-- Inverse transport along a zero-offset edge. -/
def Edge.inverse (e : Edge) (q : Rat) : Rat :=
  (e.b * q - e.drift) / e.a

theorem Edge.inverse_spec (e : Edge) (q : Rat) :
    e.a * e.inverse q + e.drift = e.b * q := by
  rw [Edge.inverse, Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt e.a_pos)]
  grind

theorem Edge.inverse_transport (e : Edge) (p : Rat) :
    e.inverse (e.transport p) = p := by
  have h := e.inverse_spec (e.transport p)
  rw [e.transport_spec] at h
  apply Rat.le_antisymm
  · apply Rat.le_of_mul_le_mul_left _ e.a_pos
    grind
  · apply Rat.le_of_mul_le_mul_left _ e.a_pos
    grind

/-- Recover the first coordinate of a zero-offset word from its endpoint. -/
def inverseEndpoint : List Edge → Rat → Rat
  | [], p => p
  | e :: rest, p => e.inverse (inverseEndpoint rest p)

theorem inverseEndpoint_endpoint (word : List Edge) (p : Rat) :
    inverseEndpoint word (endpoint word p) = p := by
  induction word generalizing p with
  | nil => rfl
  | cons e rest ih => rw [endpoint, inverseEndpoint, ih, e.inverse_transport]

private def forwardAnchors (n : Rat) : List Edge → List Rat
  | [] => [n, n + 1]
  | e :: rest =>
    endpoint (e :: rest) n :: endpoint (e :: rest) (n + 1) :: forwardAnchors n rest

private def backwardAnchors (n : Rat) : List Edge → List Rat
  | [] => [n, n + 1]
  | e :: rest => n :: (n + 1) :: (backwardAnchors n rest).map e.inverse

private theorem forward_mem {n p : Rat} (word : List Edge) :
    p ∈ forwardAnchors n word ↔
      ∃ pre block q, word = pre ++ block ∧ (q = n ∨ q = n + 1) ∧ p = endpoint block q := by
  induction word with
  | nil =>
    constructor
    · intro h
      refine ⟨[], [], p, rfl, ?_, rfl⟩
      simpa [forwardAnchors] using h
    · rintro ⟨pre, block, q, hword, hq, hp⟩
      have hb : block = [] := (List.append_eq_nil_iff.mp hword.symm).2
      rw [hb, endpoint] at hp
      simpa [forwardAnchors, hp] using hq
  | cons e rest ih =>
    constructor
    · intro h
      simp only [forwardAnchors, List.mem_cons] at h
      rcases h with h | h | h
      · exact ⟨[], e :: rest, n, rfl, Or.inl rfl, h⟩
      · exact ⟨[], e :: rest, n + 1, rfl, Or.inr rfl, h⟩
      · obtain ⟨pre, block, q, hword, hq, hp⟩ := ih.mp h
        exact ⟨e :: pre, block, q, congrArg (List.cons e) hword, hq, hp⟩
    · rintro ⟨pre, block, q, hword, hq, hp⟩
      simp only [forwardAnchors, List.mem_cons]
      cases pre with
      | nil =>
        change e :: rest = block at hword
        subst block
        rcases hq with rfl | rfl
        · exact Or.inl hp
        · exact Or.inr (Or.inl hp)
      | cons first pre =>
        have he := List.cons.inj hword
        exact Or.inr (Or.inr (ih.mpr ⟨pre, block, q, he.2, hq, hp⟩))

private theorem backward_mem {n : Rat} (word : List Edge) (p : Rat) :
    p ∈ backwardAnchors n word ↔
      ∃ block post q, word = block ++ post ∧ (q = n ∨ q = n + 1) ∧
        p = inverseEndpoint block q := by
  induction word generalizing p with
  | nil =>
    constructor
    · intro h
      refine ⟨[], [], p, rfl, ?_, rfl⟩
      simpa [backwardAnchors] using h
    · rintro ⟨block, post, q, hword, hq, hp⟩
      have hb : block = [] := (List.append_eq_nil_iff.mp hword.symm).1
      rw [hb, inverseEndpoint] at hp
      simpa [backwardAnchors, hp] using hq
  | cons e rest ih =>
    constructor
    · intro h
      simp only [backwardAnchors, List.mem_cons] at h
      rcases h with h | h | h
      · exact ⟨[], e :: rest, n, rfl, Or.inl rfl, h⟩
      · exact ⟨[], e :: rest, n + 1, rfl, Or.inr rfl, h⟩
      · obtain ⟨z, hz, hp⟩ := List.mem_map.mp h
        obtain ⟨block, post, q, hword, hq, hz'⟩ := (ih z).mp hz
        exact ⟨e :: block, post, q, congrArg (List.cons e) hword, hq,
          by rw [inverseEndpoint, ← hz', hp]⟩
    · rintro ⟨block, post, q, hword, hq, hp⟩
      simp only [backwardAnchors, List.mem_cons]
      cases block with
      | nil =>
        rw [inverseEndpoint] at hp
        rcases hq with rfl | rfl
        · exact Or.inl hp
        · exact Or.inr (Or.inl hp)
      | cons first block =>
        obtain ⟨he, hrest⟩ := List.cons.inj hword
        subst first
        refine Or.inr (Or.inr (List.mem_map.mpr ⟨inverseEndpoint block q, ?_, ?_⟩))
        · exact (ih _).mpr ⟨block, post, q, hrest, hq, rfl⟩
        · exact hp.symm

/-- A shift at index `i` is linked to a band endpoint by a zero-offset
word on its left or right. The empty word allows either endpoint itself. -/
def AnchoredAt (n : Rat) (word : List Edge) (i : Nat) (p : Rat) : Prop :=
  (∃ pre block q, word.take i = pre ++ block ∧ (q = n ∨ q = n + 1) ∧ p = endpoint block q) ∨
  (∃ block post q, word.drop i = block ++ post ∧ (q = n ∨ q = n + 1) ∧
    p = inverseEndpoint block q)

/-- Enumerate all shifts obtained by transporting a band endpoint from an
earlier or later boundary through a consecutive zero-offset word. -/
def anchorCandidates (n : Rat) (word : List Edge) (i : Nat) : List Rat :=
  (forwardAnchors n (word.take i) ++ backwardAnchors n (word.drop i)).filter
    (fun p => decide (n ≤ p ∧ p ≤ n + 1))

theorem mem_anchorCandidates_iff {n p : Rat} {word : List Edge} {i : Nat} :
    p ∈ anchorCandidates n word i ↔ (n ≤ p ∧ p ≤ n + 1) ∧ AnchoredAt n word i p := by
  rw [anchorCandidates, List.mem_filter, List.mem_append, forward_mem, backward_mem]
  simp [AnchoredAt, and_comm]

private theorem forward_length (n : Rat) (word : List Edge) :
    (forwardAnchors n word).length = 2 * (word.length + 1) := by
  induction word with
  | nil => rfl
  | cons _ _ ih => simp only [forwardAnchors, List.length_cons, ih]; omega

private theorem backward_length (n : Rat) (word : List Edge) :
    (backwardAnchors n word).length = 2 * (word.length + 1) := by
  induction word with
  | nil => rfl
  | cons _ _ ih => simp only [backwardAnchors, List.length_cons, List.length_map, ih]; omega

/-- Every layer has at most two candidate shifts per word boundary,
counting the two copies of its own band endpoints. -/
theorem anchorCandidates_length (n : Rat) (word : List Edge) (i : Nat) :
    (anchorCandidates n word i).length ≤ 2 * (word.length + 2) := by
  unfold anchorCandidates
  apply Nat.le_trans (List.length_filter_le ..)
  rw [List.length_append, forward_length, backward_length]
  have h := congrArg List.length (List.take_append_drop i word)
  rw [List.length_append] at h
  omega

/-- Coordinates of an entire zero-offset block, including both endpoints. -/
def points : List Edge → Rat → List Rat
  | [], p => [p]
  | e :: rest, p => p :: points rest (e.transport p)

private theorem coordinates_points (word : List Edge) (p : Rat) :
    (coordinates word).map (fun f => affine f p) = points word p := by
  induction word generalizing p with
  | nil => simp [coordinates, points, affine, Rat.one_mul, Rat.add_zero]
  | cons e rest ih =>
    simp only [coordinates, points, List.map_cons, affine, Rat.one_mul, Rat.add_zero]
    congr 1
    rw [← ih, List.map_map]
    apply List.map_congr_left
    intro f _
    change affine (compose f (e.a / e.b, e.drift / e.b)) p = affine f (e.transport p)
    rw [affine_compose, e.transport_affine]
    rfl

theorem Block.inBand_iff_points (block : Block) (n p : Rat) :
    block.inBand n p ↔ ∀ x ∈ points block.inside p, n ≤ x ∧ x ≤ n + 1 := by
  unfold Block.inBand
  rw [← coordinates_points]
  simp only [List.forall_mem_map]

theorem Block.allowed_of_band (block : Block) {n p : Rat} (hn : 0 < n)
    (hband : block.inBand n p) (hleft : leftAllowed block.before p)
    (hright : rightAllowed block.after (endpoint block.inside p)) : block.allowed p :=
  ⟨chain_positive_of_band hn hband, hleft, hright⟩

theorem Block.touches_iff_points (block : Block) (n p : Rat) :
    block.touches n p ↔
      (∃ x ∈ points block.inside p, x = n ∨ x = n + 1) ∨
      (∃ b, block.before = some b ∧ b.edge.b * p = b.edge.a * b.exterior + b.edge.drift) ∨
      (∃ b, block.after = some b ∧
        b.edge.b * b.exterior = b.edge.a * endpoint block.inside p + b.edge.drift) := by
  unfold Block.touches
  rw [← coordinates_points]
  apply or_congr _ Iff.rfl
  constructor
  · rintro ⟨form, hform, he⟩
    exact ⟨affine form p, List.mem_map_of_mem hform, he⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨form, hf, rfl⟩ := List.mem_map.mp hx
    exact ⟨form, hf, he⟩

theorem endpoint_append (left right : List Edge) (p : Rat) :
    endpoint (left ++ right) p = endpoint right (endpoint left p) := by
  induction left generalizing p with
  | nil => rfl
  | cons e rest ih => exact ih (e.transport p)

theorem points_join (left right : List Edge) (e : Edge) (p : Rat) :
    points (left ++ e :: right) p = points left p ++ points right (e.transport (endpoint left p)) := by
  induction left generalizing p with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.cons_append, points, endpoint, List.cons.injEq, true_and]
    exact ih (a.transport p)

theorem insideFactor_join (left right : List Edge) (e : Edge) (p : Rat) :
    insideFactor (left ++ e :: right) p =
      insideFactor left p * e.factor (endpoint left p) (e.transport (endpoint left p)) *
        insideFactor right (e.transport (endpoint left p)) := by
  induction left generalizing p with
  | nil => simp [insideFactor, endpoint, Rat.one_mul]
  | cons a rest ih =>
    simp only [List.cons_append, insideFactor, endpoint]
    rw [ih]
    grind

theorem Edge.transport_eq_of_zero (e : Edge) {p q : Rat}
    (h : e.b * q = e.a * p + e.drift) : e.transport p = q := by
  have h' : e.b * e.transport p = e.b * q := (e.transport_spec p).trans h.symm
  exact Rat.le_antisymm
    (Rat.le_of_mul_le_mul_left (by rw [h']; exact Rat.le_refl) e.b_pos)
    (Rat.le_of_mul_le_mul_left (by rw [h']; exact Rat.le_refl) e.b_pos)

theorem Edge.factor_pos (e : Edge) {p q : Rat} (hp : 0 < p) (hq : 0 < q) :
    0 < e.factor p q := by
  unfold Edge.factor
  split
  · rw [Rat.div_def]
    exact Rat.mul_pos hp (Rat.inv_pos.mpr hq)
  · split
    · rename_i hd
      rw [Rat.div_def]
      apply Rat.mul_pos (Rat.mul_pos e.b_pos hp)
      apply Rat.inv_pos.mpr
      have hprod := Rat.mul_pos e.a_pos hp
      grind
    · rename_i hd
      rw [Rat.div_def]
      apply Rat.mul_pos _ (Rat.inv_pos.mpr (Rat.mul_pos e.a_pos hq))
      have hprod := Rat.mul_pos e.b_pos hq
      grind

end Collatz.ExcursionAnchor
