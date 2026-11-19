import Collatz.Strategy.ExcursionGreedyShifts

/-!
# Exact clipping thresholds at a conflicting boundary

With the outer shifts fixed, a negative-drift edge followed by a
nonnegative-drift edge has two clipping thresholds. Outside the
thresholds a weighted monotonicity moves the shared shift towards
one of them. Between them both factors are unclipped and the product
is linear-fractional. Thus one of the two thresholds minimizes it.
-/

namespace Collatz.ExcursionAnchor

private theorem min_le_left_rat (x y : Rat) : min x y ≤ x := by
  rw [Rat.min_def]
  split <;> grind

private theorem min_le_right_rat (x y : Rat) : min x y ≤ y := by
  rw [Rat.min_def]
  split <;> grind

private theorem conflict_inside (e f : Edge) {p q r : Rat}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hd : e.drift < 0) (hd' : 0 ≤ f.drift)
    (he : e.a * p + e.drift ≤ e.b * r) (hf : f.a * r + f.drift ≤ f.b * q) :
    e.factor p r * f.factor r q =
      (f.b / e.a) * ((e.b * r - e.drift) / (f.a * r + f.drift)) := by
  rw [e.factor_of_unclipped hp hr he, f.factor_of_unclipped hr hq hf,
    if_neg ((Rat.not_le).mpr hd), if_pos hd']
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have hc := Rat.inv_mul_cancel r (Rat.ne_of_gt hr)
  calc
    _ = (f.b * e.a⁻¹) * ((e.b * r - e.drift) * (f.a * r + f.drift)⁻¹) * (r⁻¹ * r) := by grind
    _ = _ := by rw [hc, Rat.mul_one]

/-- Either clipping threshold is a sufficient candidate when the
outer coordinates are fixed. Their smaller product is the exact
minimum over positive common coordinates, provided the thresholds
themselves are positive. -/
theorem conflict_threshold_min (e f : Edge) {p q r : Rat}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hd : e.drift < 0) (hd' : 0 ≤ f.drift)
    (hL : 0 < e.transport p) (hU : 0 < f.inverse q) :
    let left := e.transport p
    let right := f.inverse q
    min (e.factor p left * f.factor left q) (e.factor p right * f.factor right q) ≤
      e.factor p r * f.factor r q := by
  let left := e.transport p
  let right := f.inverse q
  have hleft := e.transport_spec p
  have hright := f.inverse_spec q
  have hL' : 0 < left := hL
  have hU' : 0 < right := hU
  change min (e.factor p left * f.factor left q) (e.factor p right * f.factor right q) ≤
    e.factor p r * f.factor r q
  by_cases hl : r ≤ left
  · have hscale := Rat.mul_le_mul_of_nonneg_left hl (Rat.le_of_lt e.b_pos)
    have hc : e.b * r ≤ e.a * p + e.drift := by grind
    apply Rat.le_trans (min_le_left_rat _ _)
    rw [e.factor_of_transport, e.factor_of_clipped hc]
    have hs := Rat.mul_le_mul_of_nonneg_left (f.factor_div_source_antitone hr hq hl)
      (Rat.le_of_lt hp)
    simp only [Rat.div_def] at hs ⊢
    grind
  · by_cases hu : right ≤ r
    · have hscale := Rat.mul_le_mul_of_nonneg_left hu (Rat.le_of_lt f.a_pos)
      have hc : f.b * q ≤ f.a * r + f.drift := by grind
      have hc' : f.b * q ≤ f.a * right + f.drift := by grind
      apply Rat.le_trans (min_le_right_rat _ _)
      rw [f.factor_of_clipped hc', f.factor_of_clipped hc]
      have hs := Rat.mul_le_mul_of_nonneg_right (e.factor_mul_target_mono hp hU' hu)
        (Rat.le_of_lt (Rat.inv_pos.mpr hq))
      simp only [Rat.div_def]
      grind
    · have hlo := Rat.le_of_lt ((Rat.not_le).mp hl)
      have hhi := Rat.le_of_lt ((Rat.not_le).mp hu)
      have horder := Rat.le_trans hlo hhi
      have he (x : Rat) (hx : left ≤ x) : e.a * p + e.drift ≤ e.b * x := by
        have hs := Rat.mul_le_mul_of_nonneg_left hx (Rat.le_of_lt e.b_pos)
        grind
      have hf (x : Rat) (hx : x ≤ right) : f.a * x + f.drift ≤ f.b * q := by
        have hs := Rat.mul_le_mul_of_nonneg_left hx (Rat.le_of_lt f.a_pos)
        grind
      have hden (x : Rat) (hx : 0 < x) : 0 < f.a * x + f.drift := by
        have hs := Rat.mul_pos f.a_pos hx
        grind
      have hs : 0 ≤ f.b / e.a := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.le_of_lt f.b_pos) (Rat.le_of_lt (Rat.inv_pos.mpr e.a_pos))
      have hratio := affine_ratio_end (a := e.b) (b := -e.drift) (c := f.a) (d := f.drift)
        hlo hhi (hden left hL') (hden r hr) (hden right hU')
      rcases hratio with h | h
      · apply Rat.le_trans (min_le_left_rat _ _)
        rw [conflict_inside e f hp hq hL' hd hd' (he left Rat.le_refl) (hf left horder),
          conflict_inside e f hp hq hr hd hd' (he r hlo) (hf r hhi)]
        exact Rat.mul_le_mul_of_nonneg_left (by simpa only [Rat.sub_eq_add_neg] using h) hs
      · apply Rat.le_trans (min_le_right_rat _ _)
        rw [conflict_inside e f hp hq hU' hd hd' (he right horder) (hf right Rat.le_refl),
          conflict_inside e f hp hq hr hd hd' (he r hlo) (hf r hhi)]
        exact Rat.mul_le_mul_of_nonneg_left (by simpa only [Rat.sub_eq_add_neg] using h) hs

private theorem threshold_transport_in_band {n v W : Nat} (hW : 0 < W) :
    (n : Rat) ≤ (Edge.ofRun n v W).transport ((n : Rat) + 1) ∧
      (Edge.ofRun n v W).transport ((n : Rat) + 1) ≤ (n : Rat) + 1 := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hc : 0 ≤ c := Rat.natCast_nonneg
  have hd : e.drift = e.b * (n : Rat) + c - e.a * top := rfl
  have ht := e.transport_spec top
  have hhalf : e.transport top ≤ (n : Rat) + 1 / 2 := output_half hW Rat.le_refl
  have hgap : (1 / 2 : Rat) ≤ 1 := by decide +kernel
  constructor
  · apply Rat.le_of_mul_le_mul_left _ e.b_pos
    change e.b * (n : Rat) ≤ e.b * e.transport top
    rw [ht, hd]
    grind
  · change e.transport top ≤ (n : Rat) + 1
    grind

private theorem threshold_inverse_in_band {n v W : Nat} (hv : 0 < v) :
    (n : Rat) ≤ (Edge.ofRun n v W).inverse n ∧
      (Edge.ofRun n v W).inverse n ≤ (n : Rat) + 1 := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hc : 0 ≤ c := Rat.natCast_nonneg
  have hd : e.drift = e.b * (n : Rat) + c - e.a * top := rfl
  have hi := e.inverse_spec n
  have htransport : e.transport (e.inverse n) = (n : Rat) :=
    e.transport_eq_of_zero hi.symm
  have hthird := input_ge_third hv (by rw [htransport]; exact Rat.le_refl)
  have hgap : (0 : Rat) ≤ 1 / 3 := by decide +kernel
  constructor
  · change (n : Rat) ≤ e.inverse n
    grind
  · apply Rat.le_of_mul_le_mul_left _ e.a_pos
    change e.a * e.inverse n ≤ e.a * top
    rw [hd] at hi
    grind

/-- Cost of a conflict with the outer shifts placed at the ends most
expensive for the product. -/
def worstPair (floor : Rat) (e f : Edge) (mid : Rat) : Rat :=
  e.factor (floor + 1) mid * f.factor mid floor

/-- Evaluate the two clipping thresholds for the worst exterior. -/
def thresholdBudget (floor : Rat) (e f : Edge) : Rat :=
  min (worstPair floor e f (e.transport (floor + 1))) (worstPair floor e f (f.inverse floor))

/-- A shared shift realizing the threshold budget. -/
def thresholdShift (floor : Rat) (e f : Edge) : Rat :=
  let left := e.transport (floor + 1)
  let right := f.inverse floor
  if worstPair floor e f left ≤ worstPair floor e f right then left else right

theorem thresholdShift_spec (floor : Rat) (e f : Edge) :
    worstPair floor e f (thresholdShift floor e f) = thresholdBudget floor e f := by
  unfold thresholdShift thresholdBudget
  rw [Rat.min_def]
  split <;> simp [*]

theorem thresholdShift_in_band {n v W v' W' : Nat} (hW : 0 < W) (hv' : 0 < v') :
    let mid := thresholdShift n (Edge.ofRun n v W) (Edge.ofRun n v' W')
    (n : Rat) ≤ mid ∧ mid ≤ (n : Rat) + 1 := by
  dsimp only [thresholdShift]
  split
  · exact threshold_transport_in_band hW
  · exact threshold_inverse_in_band hv'

/-- The same shared shift bounds the pair for any feasible exterior. -/
theorem thresholdBudget_bounds_pair {n v W v' W' : Nat} (hn : 0 < n)
    (hW : 0 < W) (hv' : 0 < v') {p q : Rat}
    (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) (hq : (n : Rat) ≤ q) :
    let e := Edge.ofRun n v W
    let f := Edge.ofRun n v' W'
    let mid := thresholdShift n e f
    e.factor p mid * f.factor mid q ≤ thresholdBudget n e f := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let top := (n : Rat) + 1
  let mid := thresholdShift n e f
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hm : (n : Rat) ≤ mid ∧ mid ≤ top := thresholdShift_in_band hW hv'
  have hp' : 0 < p := by have := hp.1; grind
  have hq' : 0 < q := by grind
  have hm' : 0 < mid := by have := hm.1; grind
  have htop : 0 < top := by dsimp [top]; grind
  have he := e.factor_mono_source hp' hp.2 hm'
  have hf := f.factor_antitone_target hm' hn' hq
  have he0 := Rat.le_of_lt (e.factor_pos htop hm')
  have hf0 := Rat.le_of_lt (f.factor_pos hm' hq')
  change e.factor p mid * f.factor mid q ≤ thresholdBudget n e f
  rw [← thresholdShift_spec n e f]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right he hf0)
    (Rat.mul_le_mul_of_nonneg_left hf he0)

end Collatz.ExcursionAnchor
