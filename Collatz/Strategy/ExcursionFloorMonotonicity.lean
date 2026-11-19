import Collatz.Strategy.ExcursionReversalBudget

/-!
# Excursion shift bounds improve as the floor increases

Keep the excursion letters and the relative shifts fixed while
raising the proposed floor. The clipping condition is independent
of the floor. In each unclipped formula the determinant has the
same strict sign, and a drift switch can only select the smaller
formula. This makes the bound monotone along every realization
class of an excursion word.
-/

namespace Collatz.ExcursionAnchor

/-- An affine excursion edge at a rational floor, with its constant
written in the unshifted coordinate. -/
def Edge.atFloor (a b c floor : Rat) (ha : 0 < a) (hb : 0 < b) : Edge :=
  ⟨a, b, b * floor + c - a * (floor + 1), ha, hb⟩

private theorem div_lt_div_iff_pos {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ a * d < c * b := by
  calc
    _ ↔ ¬ c / d ≤ a / b := (Rat.not_le).symm
    _ ↔ ¬ c * b ≤ a * d := not_congr (div_le_div_iff_pos hd hb)
    _ ↔ _ := Rat.not_le

private theorem affine_ratio_strict_decreasing {a b c d x y : Rat}
    (hxy : x < y) (hs : 0 < b * c - a * d)
    (hx : 0 < c * x + d) (hy : 0 < c * y + d) :
    (a * y + b) / (c * y + d) < (a * x + b) / (c * x + d) := by
  rw [div_lt_div_iff_pos hy hx, Rat.lt_iff_sub_pos]
  have he : (a * x + b) * (c * y + d) - (a * y + b) * (c * x + d) =
      (b * c - a * d) * (y - x) := by grind
  rw [he]
  exact Rat.mul_pos hs (by grind)

private theorem convex_offset_pos {a b c s : Rat} (hca : c < a) (hcb : c < b)
    (hs : 0 ≤ s) (hs' : s ≤ 1) : 0 < a - c + (b - a) * s := by
  have he : a - c + (b - a) * s = (a - c) * (1 - s) + (b - c) * s := by grind
  rw [he]
  have h₀ := Rat.mul_nonneg (by grind : 0 ≤ a - c) (by grind : 0 ≤ 1 - s)
  by_cases h : s = 0
  · rw [h, Rat.mul_zero, Rat.add_zero]
    grind
  · have h₁ := Rat.mul_pos (by grind : 0 < b - c) (by grind : 0 < s)
    grind

private theorem Edge.arrival_le_departure (e : Edge) {p q : Rat}
    (hp : 0 < p) (hq : 0 < q) (hd : 0 ≤ e.drift)
    (h : e.a * p + e.drift ≤ e.b * q) :
    e.b * p / (e.a * p + e.drift) ≤ (e.b * q - e.drift) / (e.a * q) := by
  have hR : 0 < e.a * p + e.drift := by
    have ha := Rat.mul_pos e.a_pos hp
    grind
  rw [div_le_div_iff_pos hR (Rat.mul_pos e.a_pos hq), Rat.le_iff_sub_nonneg]
  have he : (e.b * q - e.drift) * (e.a * p + e.drift) - (e.b * p) * (e.a * q) =
      e.drift * (e.b * q - (e.a * p + e.drift)) := by grind
  rw [he]
  exact Rat.mul_nonneg hd ((Rat.le_iff_sub_nonneg _ _).mp h)

/-- Increasing the floor strictly decreases every genuine excursion
factor at a fixed pair of relative shifts. This includes a possible
change of preferred formula as the drift changes sign. -/
theorem Edge.atFloor_factor_strict {a b c n m s t : Rat}
    (ha : 0 < a) (hb : 0 < b) (hca : c < a) (hcb : c < b)
    (hn : 0 < n) (hnm : n < m) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (Edge.atFloor a b c m ha hb).factor (m + s) (m + t) <
      (Edge.atFloor a b c n ha hb).factor (n + s) (n + t) := by
  let e := Edge.atFloor a b c n ha hb
  let f := Edge.atFloor a b c m ha hb
  have hnS : 0 < n + s := by grind
  have hmS : 0 < m + s := by grind
  have hnT : 0 < n + t := by grind
  have hmT : 0 < m + t := by grind
  have hslope := convex_offset_pos hca hcb hs hs'
  have htlope := convex_offset_pos hca hcb ht ht'
  change f.factor (m + s) (m + t) < e.factor (n + s) (n + t)
  by_cases hc : b * t ≤ a * s + c - a
  · have hen : e.b * (n + t) ≤ e.a * (n + s) + e.drift := by
      change b * (n + t) ≤ a * (n + s) + (b * n + c - a * (n + 1))
      grind
    have hem : f.b * (m + t) ≤ f.a * (m + s) + f.drift := by
      change b * (m + t) ≤ a * (m + s) + (b * m + c - a * (m + 1))
      grind
    rw [f.factor_of_clipped hem, e.factor_of_clipped hen]
    have hst : t < s := by
      apply Classical.byContradiction
      intro h
      have hsle := (Rat.not_lt).mp h
      have hscaled := Rat.mul_le_mul_of_nonneg_left hsle (Rat.le_of_lt hb)
      grind
    have hdet : 0 < s * 1 - 1 * t := by grind
    simpa only [Rat.one_mul] using
      affine_ratio_strict_decreasing hnm hdet (by simpa only [Rat.one_mul] using hnT)
        (by simpa only [Rat.one_mul] using hmT)
  · have hu := Rat.le_of_lt ((Rat.not_le).mp hc)
    have hen : e.a * (n + s) + e.drift ≤ e.b * (n + t) := by
      change a * (n + s) + (b * n + c - a * (n + 1)) ≤ b * (n + t)
      grind
    have hem : f.a * (m + s) + f.drift ≤ f.b * (m + t) := by
      change a * (m + s) + (b * m + c - a * (m + 1)) ≤ b * (m + t)
      grind
    have hdep :
        (f.b * (m + t) - f.drift) / (f.a * (m + t)) <
          (e.b * (n + t) - e.drift) / (e.a * (n + t)) := by
      have hdet : 0 < (a + b * t - c) * a - a * (a * t) := by
        have h := Rat.mul_pos ha htlope
        grind
      have hnD : 0 < a * n + a * t := by rw [← Rat.mul_add]; exact Rat.mul_pos ha hnT
      have hmD : 0 < a * m + a * t := by rw [← Rat.mul_add]; exact Rat.mul_pos ha hmT
      have h := affine_ratio_strict_decreasing hnm hdet hnD hmD
      have hnum (x : Rat) : b * (x + t) - (b * x + c - a * (x + 1)) =
          a * x + (a + b * t - c) := by grind
      change (b * (m + t) - (b * m + c - a * (m + 1))) / (a * (m + t)) <
        (b * (n + t) - (b * n + c - a * (n + 1))) / (a * (n + t))
      rwa [hnum, hnum, Rat.mul_add a m t, Rat.mul_add a n t]
    by_cases hd : 0 ≤ e.drift
    · have hnd : 0 ≤ (b - a) * n - (a - c) := by
        change 0 ≤ b * n + c - a * (n + 1) at hd
        grind
      have hba : 0 < b - a := by
        apply Classical.byContradiction
        intro h
        have hle := (Rat.not_lt).mp h
        have hs := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hn)
        grind
      have hscale := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hnm) (Rat.le_of_lt hba)
      have hd' : 0 ≤ f.drift := by
        change 0 ≤ b * m + c - a * (m + 1)
        grind
      have hnA : 0 < e.a * (n + s) + e.drift := by
        have hn' := Rat.mul_pos e.a_pos hnS
        grind
      have hmA : 0 < f.a * (m + s) + f.drift := by
        have hm' := Rat.mul_pos f.a_pos hmS
        grind
      rw [f.factor_of_unclipped hmS hmT hem, e.factor_of_unclipped hnS hnT hen, if_pos hd', if_pos hd]
      have hdet : 0 < (b * s) * b - b * (c + a * s - a) := by
        have h := Rat.mul_pos hb hslope
        grind
      have hden (x : Rat) : a * (x + s) + (b * x + c - a * (x + 1)) =
          b * x + (c + a * s - a) := by grind
      change 0 < a * (n + s) + (b * n + c - a * (n + 1)) at hnA
      change 0 < a * (m + s) + (b * m + c - a * (m + 1)) at hmA
      rw [hden] at hnA hmA
      have h := affine_ratio_strict_decreasing hnm hdet hnA hmA
      change b * (m + s) / (a * (m + s) + (b * m + c - a * (m + 1))) <
        b * (n + s) / (a * (n + s) + (b * n + c - a * (n + 1)))
      rwa [hden, hden, Rat.mul_add b m s, Rat.mul_add b n s]
    · rw [e.factor_of_unclipped hnS hnT hen, if_neg hd, f.factor_of_unclipped hmS hmT hem]
      by_cases hd' : 0 ≤ f.drift
      · rw [if_pos hd']
        have h := f.arrival_le_departure hmS hmT hd' hem
        grind
      · rw [if_neg hd']
        exact hdep

theorem Edge.ofRun_factor_strict_floor {n m v W : Nat} (hn : 0 < n) (hnm : n < m)
    (hv : 0 < v) (hW : 0 < W) {p q : Rat}
    (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) (hq : (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    (Edge.ofRun m v W).factor (p + ((m : Rat) - (n : Rat))) (q + ((m : Rat) - (n : Rat))) <
      (Edge.ofRun n v W).factor p q := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have ha := (Edge.ofRun n v W).a_pos
  have hb := (Edge.ofRun n v W).b_pos
  have hca : c < a := three_pow_gt_two hv
  have hcb : c < b :=
    Rat.natCast_lt_natCast.mpr (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hnm' : (n : Rat) < m := Rat.natCast_lt_natCast.mpr hnm
  let s := p - (n : Rat)
  let t := q - (n : Rat)
  have hs : 0 ≤ s := by dsimp [s]; grind [hp.1]
  have hs' : s ≤ 1 := by dsimp [s]; grind [hp.2]
  have ht : 0 ≤ t := by dsimp [t]; grind [hq.1]
  have ht' : t ≤ 1 := by dsimp [t]; grind [hq.2]
  have h := Edge.atFloor_factor_strict ha hb hca hcb hn' hnm' hs hs' ht ht'
  have hnS : (n : Rat) + s = p := by dsimp [s]; grind
  have hnT : (n : Rat) + t = q := by dsimp [t]; grind
  have hmS : (m : Rat) + s = p + ((m : Rat) - (n : Rat)) := by dsimp [s]; grind
  have hmT : (m : Rat) + t = q + ((m : Rat) - (n : Rat)) := by dsimp [t]; grind
  rw [hnS, hnT, hmS, hmT] at h
  exact h

/-- Interpret the same run parameters at any proposed floor. -/
def wordAt (floor : Nat) (runs : List (Nat × Nat)) : List Edge :=
  runs.map fun (v, W) => Edge.ofRun floor v W

private theorem wordAt_alphabet (floor : Nat) {runs : List (Nat × Nat)}
    (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2) : ExcursionAlphabet floor (wordAt floor runs) := by
  intro e he
  obtain ⟨⟨v, W⟩, hm, rfl⟩ := List.mem_map.mp he
  exact ⟨v, W, (ha _ hm).1, (ha _ hm).2, rfl⟩

private theorem costOn_pos (word : List Edge) (coords : List Rat)
    (h : ∀ p ∈ coords, 0 < p) : 0 < costOn word coords := by
  induction word generalizing coords with
  | nil => exact (by decide : (0 : Rat) < 1)
  | cons e rest ih =>
    cases coords with
    | nil => exact (by decide : (0 : Rat) < 1)
    | cons p coords =>
      cases coords with
      | nil => exact (by decide : (0 : Rat) < 1)
      | cons q tail =>
        exact Rat.mul_pos (e.factor_pos (h p List.mem_cons_self)
          (h q (List.mem_cons_of_mem _ List.mem_cons_self)))
          (ih (q :: tail) (fun p hp => h p (List.mem_cons_of_mem _ hp)))

private theorem costOn_floor_compare {n m : Nat} (hn : 0 < n) (hnm : n < m)
    {runs : List (Nat × Nat)} (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2)
    {p : Rat} {rest : List Rat} (hlen : rest.length = runs.length)
    (hband : ∀ q ∈ p :: rest, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    let shifted := (p :: rest).map (fun q => q + ((m : Rat) - (n : Rat)))
    costOn (wordAt m runs) shifted ≤ costOn (wordAt n runs) (p :: rest) ∧
      (runs ≠ [] → costOn (wordAt m runs) shifted < costOn (wordAt n runs) (p :: rest)) := by
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hnm' : (n : Rat) < m := Rat.natCast_lt_natCast.mpr hnm
  let shift := fun q : Rat => q + ((m : Rat) - (n : Rat))
  induction runs generalizing p rest with
  | nil => exact ⟨Rat.le_refl, fun h => False.elim (h rfl)⟩
  | cons run runs ih =>
    rcases run with ⟨v, W⟩
    cases rest with
    | nil => simp at hlen
    | cons q rest =>
      have hp := hband p List.mem_cons_self
      have htail (r : Rat) (hr : r ∈ q :: rest) := hband r (List.mem_cons_of_mem _ hr)
      have hq := htail q List.mem_cons_self
      have hrun := ha (v, W) List.mem_cons_self
      have hlocal := Edge.ofRun_factor_strict_floor hn hnm hrun.1 hrun.2 hp hq
      have hs := (ih (fun r hr => ha r (List.mem_cons_of_mem _ hr)) (by simpa using hlen) htail).1
      have hspos : 0 < costOn (wordAt m runs) ((q :: rest).map shift) := by
        apply costOn_pos
        intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        have h := (htail z hz).1
        dsimp [shift]
        grind
      have hp' : 0 < p := by have := hp.1; grind
      have hq' : 0 < q := by have := hq.1; grind
      have hl := Rat.mul_lt_mul_of_pos_right hlocal hspos
      have hr := Rat.mul_le_mul_of_nonneg_left hs
        (Rat.le_of_lt ((Edge.ofRun n v W).factor_pos hp' hq'))
      have hlt : costOn (wordAt m ((v, W) :: runs)) ((p :: q :: rest).map shift) <
          costOn (wordAt n ((v, W) :: runs)) (p :: q :: rest) := by
        change (Edge.ofRun m v W).factor (shift p) (shift q) *
            costOn (wordAt m runs) ((q :: rest).map shift) <
          (Edge.ofRun n v W).factor p q * costOn (wordAt n runs) (q :: rest)
        change _ * costOn (wordAt m runs) ((q :: rest).map shift) ≤ _ at hr
        grind
      exact ⟨Rat.le_of_lt hlt, fun _ => hlt⟩

/-- The optimal rational product for a fixed nonempty excursion word
strictly decreases as the proposed floor increases. -/
theorem anchorMinimum_strict_floor {n m : Nat} (hn : 0 < n) (hnm : n < m)
    {runs : List (Nat × Nat)} (hne : runs ≠ []) (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2)
    {old : Rat} (hold : anchorMinimum n (wordAt n runs) = some old) :
    ∃ best, anchorMinimum m (wordAt m runs) = some best ∧ best < old := by
  obtain ⟨p, rest, hlen, hband, hcost⟩ := anchorMinimum_attained_in_band hold
  let shift := fun q : Rat => q + ((m : Rat) - (n : Rat))
  let coords := (p :: rest).map shift
  have hsize : rest.length = runs.length := by simpa [wordAt] using hlen
  have hcmp := (costOn_floor_compare hn hnm ha hsize hband).2 hne
  rw [hcost] at hcmp
  have hlen' : coords.length = (wordAt m runs).length + 1 := by
    simp [coords, wordAt, hsize]
  have hband' (r : Rat) (hr : r ∈ coords) : (m : Rat) ≤ r ∧ r ≤ (m : Rat) + 1 := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    have h := hband q hq
    dsimp [shift]
    grind
  have hm : (0 : Rat) < m := Rat.natCast_pos.mpr (by omega)
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_coordinates hm hlen' hband'
  change costOn (wordAt m runs) coords < old at hcmp
  exact ⟨best, hbest, by grind⟩

theorem localMinimum_strict_floor {n m : Nat} (hn : 0 < n) (hnm : n < m)
    {runs : List (Nat × Nat)} (hne : runs ≠ []) (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2)
    {old : Rat} (hold : localMinimum n (wordAt n runs) = some old) :
    ∃ best, localMinimum m (wordAt m runs) = some best ∧ best < old := by
  rw [localMinimum_eq_anchorMinimum (wordAt_alphabet n ha)] at hold
  rw [localMinimum_eq_anchorMinimum (wordAt_alphabet m ha)]
  exact anchorMinimum_strict_floor hn hnm hne ha hold

private theorem OrbitWord.a_pos {n x word endpoint elapsed A B}
    (h : OrbitWord n x word endpoint elapsed A B) : 0 < A := by
  induction h with
  | nil => decide
  | cons _ _ ih => exact Nat.mul_pos (Nat.pow_pos (by decide)) ih

/-- Even equality at a smaller floor gives a strict descent
certificate for every larger genuine realization of the same word. -/
theorem OrbitWord.drop_of_smaller_floor_touch {n m endpoint elapsed A B : Nat}
    {runs : List (Nat × Nat)} (h : OrbitWord m m (wordAt m runs) endpoint elapsed A B)
    (hn : 0 < n) (hnm : n < m) (hne : runs ≠ [])
    (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2)
    {old : Rat} (hold : localMinimum n (wordAt n runs) = some old)
    (htouch : (A : Rat) * old ≤ (B : Rat)) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k m < m := by
  obtain ⟨best, hbest, hlt⟩ := localMinimum_strict_floor hn hnm hne ha hold
  have hA := h.a_pos
  have hcross := Rat.mul_lt_mul_of_pos_left hlt (Rat.natCast_pos.mpr hA)
  exact h.drop_of_localMinimum (by omega) hbest (by grind)


private theorem costOn_le_band_power {n : Nat} (hn : 0 < n) {runs : List (Nat × Nat)}
    {p : Rat} {rest : List Rat} (hlen : rest.length = runs.length)
    (hband : ∀ q ∈ p :: rest, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    costOn (wordAt n runs) (p :: rest) ≤ (((n : Rat) + 1) / n) ^ runs.length := by
  let R := ((n : Rat) + 1) / n
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hR : 0 ≤ R := by
    change 0 ≤ ((n : Rat) + 1) / n
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hn'))
  induction runs generalizing p rest with
  | nil =>
    change 1 ≤ R ^ 0
    rw [Rat.pow_zero]
    exact Rat.le_refl
  | cons run runs ih =>
    rcases run with ⟨v, W⟩
    cases rest with
    | nil => simp at hlen
    | cons q rest =>
      have hp := hband p List.mem_cons_self
      have htail (r : Rat) (hr : r ∈ q :: rest) := hband r (List.mem_cons_of_mem _ hr)
      have hq := htail q List.mem_cons_self
      have he := ofRun_factor_le_band_ratio (v := v) (W := W) hn hp.1 hp.2 hq.1
      have hc := costOn_nonneg (wordAt n runs) (q :: rest)
        (fun r hr => by have hh := (htail r hr).1; grind)
      have hnext := ih (by simpa using hlen) htail
      change (Edge.ofRun n v W).factor p q * costOn (wordAt n runs) (q :: rest) ≤
        R ^ (runs.length + 1)
      calc
        _ ≤ R * costOn (wordAt n runs) (q :: rest) := Rat.mul_le_mul_of_nonneg_right he hc
        _ ≤ R * R ^ runs.length := Rat.mul_le_mul_of_nonneg_left hnext hR
        _ = _ := by rw [Rat.pow_succ, Rat.mul_comm]

private theorem band_power_le {n : Rat} (hn : 0 < n) (j : Nat) (hj : (j : Rat) < n) :
    ((n + 1) / n) ^ j ≤ n / (n - (j : Rat)) := by
  induction j with
  | zero =>
    change ((n + 1) / n) ^ 0 ≤ n / (n - 0)
    have he : n - 0 = n := by grind
    rw [Rat.pow_zero, he, Rat.div_def, Rat.mul_inv_cancel n (Rat.ne_of_gt hn)]
    exact Rat.le_refl
  | succ j ih =>
    have hj' : (j : Rat) + 1 < n := by
      rw [Rat.natCast_add] at hj
      exact hj
    have hbase : (j : Rat) < n := by grind
    have hden : 0 < n - (j : Rat) := by grind
    have hden' : 0 < n - ((j + 1 : Nat) : Rat) := by grind
    have hnonneg : 0 ≤ (n + 1) / n := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
    have heq : (n / (n - (j : Rat))) * ((n + 1) / n) = (n + 1) / (n - (j : Rat)) := by
      simp only [Rat.div_def]
      have hcancel := Rat.mul_inv_cancel n (Rat.ne_of_gt hn)
      grind
    rw [Rat.pow_succ]
    calc
      _ ≤ (n / (n - (j : Rat))) * ((n + 1) / n) :=
        Rat.mul_le_mul_of_nonneg_right (ih hbase) hnonneg
      _ = _ := heq
      _ ≤ _ := by
        rw [div_le_div_iff_pos hden hden', Rat.natCast_add]
        have h : (0 : Rat) ≤ j := Rat.natCast_nonneg
        change (n + 1) * (n - ((j : Rat) + 1)) ≤ n * (n - (j : Rat))
        grind

/-- Every finite coefficient-crossing word has a certified size
cutoff. The integer margin uses only the word length and coefficients. -/
theorem localMinimum_crosses_above_gap_size {n A B : Nat} {runs : List (Nat × Nat)}
    (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2)
    (hmargin : B * runs.length < (B - A) * n) :
    ∃ best, localMinimum n (wordAt n runs) = some best ∧ (A : Rat) * best < (B : Rat) := by
  have hlength : runs.length < n := Nat.lt_of_mul_lt_mul_left
    (Nat.lt_of_lt_of_le hmargin (Nat.mul_le_mul_right n (Nat.sub_le B A)))
  have hAB : A ≤ B := by
    apply Nat.le_of_not_gt
    intro h
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h), Nat.zero_mul] at hmargin
    omega
  have hn : 0 < n := by omega
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  let rest := List.replicate runs.length (n : Rat)
  have hlen : rest.length = (wordAt n runs).length := by simp [rest, wordAt]
  have hband (p : Rat) (hp : p ∈ (n : Rat) :: rest) :
      (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
    have he : p = (n : Rat) := by
      rcases List.mem_cons.mp hp with he | he
      · exact he
      · exact List.eq_of_mem_replicate he
    rw [he]
    exact ⟨Rat.le_refl, by grind⟩
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_schedule hn' hlen hband
  have hcost := costOn_le_band_power (runs := runs) hn (by simp [rest]) hband
  have hj := Rat.natCast_lt_natCast.mpr hlength
  have hpow := band_power_le hn' runs.length hj
  have hbound := Rat.le_trans hle (Rat.le_trans hcost hpow)
  have hrat := Rat.natCast_lt_natCast.mpr hmargin
  have hcast := congrArg (fun x : Nat => (x : Rat)) (Nat.sub_add_cancel hAB)
  rw [Rat.natCast_add] at hcast
  have hsub : ((B - A : Nat) : Rat) = (B : Rat) - (A : Rat) := by grind
  rw [Rat.natCast_mul, Rat.natCast_mul, hsub] at hrat
  have hden : (0 : Rat) < (n : Rat) - (runs.length : Rat) := by grind
  have hcancel := Rat.div_mul_cancel (a := (n : Rat)) (Rat.ne_of_gt hden)
  have hstrict : (A : Rat) * ((n : Rat) / ((n : Rat) - (runs.length : Rat))) < (B : Rat) := by
    apply (Rat.mul_lt_mul_right hden).mp
    calc
      _ = (A : Rat) * (n : Rat) := by rw [Rat.mul_assoc, hcancel]
      _ < _ := by grind
  have hscaled := Rat.mul_le_mul_of_nonneg_left hbound (Rat.natCast_nonneg (a := A))
  rw [← localMinimum_eq_anchorMinimum (wordAt_alphabet n ha)] at hbest
  exact ⟨best, hbest, by grind⟩

private theorem least_nat_of_exists {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ t, P t ∧ ∀ n, n < t → ¬ P n := by
  have hleast : ∀ k, P k → ∃ t, P t ∧ ∀ n, n < t → ¬ P n := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      by_cases he : ∃ j, j < k ∧ P j
      · obtain ⟨j, hj, hp⟩ := he
        exact ih j hj hp
      · refine ⟨k, hk, ?_⟩
        intro j hj hp
        exact he ⟨j, hj, hp⟩
  obtain ⟨k, hk⟩ := h
  exact hleast k hk

/-- The positive floors certifying a fixed nonempty coefficient-
crossing word form an upper interval with an explicit finite bound
on its first element. -/
theorem exists_word_floor_threshold {A B : Nat} (hAB : A < B)
    {runs : List (Nat × Nat)} (hne : runs ≠ [])
    (ha : ∀ run ∈ runs, 0 < run.1 ∧ 0 < run.2) :
    ∃ threshold : Nat, 0 < threshold ∧ threshold ≤ B * runs.length + 1 ∧
      ∀ n : Nat, 0 < n →
        ((∃ best, localMinimum n (wordAt n runs) = some best ∧ (A : Rat) * best < (B : Rat)) ↔
          threshold ≤ n) := by
  let P := fun n : Nat => 0 < n ∧
    ∃ best, localMinimum n (wordAt n runs) = some best ∧ (A : Rat) * best < (B : Rat)
  let cutoff := B * runs.length + 1
  have hgap : 1 ≤ B - A := by omega
  have hscale := Nat.mul_le_mul_right cutoff hgap
  simp only [Nat.one_mul] at hscale
  have hmargin : B * runs.length < (B - A) * cutoff :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hscale
  have hc : P cutoff := ⟨by omega, localMinimum_crosses_above_gap_size ha hmargin⟩
  obtain ⟨threshold, ht, hmin⟩ := least_nat_of_exists ⟨cutoff, hc⟩
  have hcut : threshold ≤ cutoff := by
    apply Nat.le_of_not_gt
    intro h
    exact hmin cutoff h hc
  refine ⟨threshold, ht.1, hcut, ?_⟩
  intro n hn
  constructor
  · intro h
    apply Nat.le_of_not_gt
    intro hlt
    exact hmin n hlt ⟨hn, h⟩
  · intro h
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact ht.2
    · obtain ⟨old, hold, hcross⟩ := ht.2
      obtain ⟨best, hbest, hbetter⟩ := localMinimum_strict_floor ht.1 hlt hne ha hold
      have hle := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hbetter) (Rat.natCast_nonneg (a := A))
      exact ⟨best, hbest, by grind⟩

/-- This pair of floors exercises the change of preferred formula. -/
theorem ofRun_floor_switch_example :
    (Edge.ofRun 1 4 3).drift < 0 ∧ 0 ≤ (Edge.ofRun 2 4 3).drift ∧
      (Edge.ofRun 2 4 3).factor (2 + 3 / 4) (2 + 2 / 3) <
        (Edge.ofRun 1 4 3).factor (1 + 3 / 4) (1 + 2 / 3) := by
  decide +kernel

/-- The product touches the coefficient at floor 1, but certifies
the genuine one-excursion descent from 9. -/
theorem drop_9_from_touch_at_one :
    ∃ k, k ≤ 2 ∧ Collatz.acceleratedOrbit k 9 < 9 := by
  have trace : OrbitWord 9 9 (wordAt 9 [(1, 1)]) 7 2 3 4 :=
    .cons (show Collatz.ExcursionMap.IsExcursion 9 1 5 1 7 by
      unfold Collatz.ExcursionMap.IsExcursion
      decide) .nil
  have ha : ∀ run ∈ ([(1, 1)] : List (Nat × Nat)), 0 < run.1 ∧ 0 < run.2 := by
    intro run h
    have he : run = (1, 1) := by simpa using h
    rw [he]
    decide
  have hopt : localMinimum 1 (wordAt 1 [(1, 1)]) = some (4 / 3) := by decide +kernel
  exact trace.drop_of_smaller_floor_touch (by decide) (by decide) (by simp) ha hopt (by decide +kernel)

/-- The first coefficient-crossing word from 63 has exact
certificate threshold 61, considered as an abstract word. -/
theorem floor_threshold_63 (n : Nat) (hn : 0 < n) :
    (∃ best, localMinimum n (wordAt n runParameters63) = some best ∧
      (16677181699666569 : Rat) * best < (18014398509481984 : Rat)) ↔ 61 ≤ n := by
  let A : Nat := 16677181699666569
  let B : Nat := 18014398509481984
  have ha : ∀ run ∈ runParameters63, 0 < run.1 ∧ 0 < run.2 := by
    rintro ⟨v, W⟩ hr
    simp only [runParameters63, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
    omega
  obtain ⟨t, _, _, ht⟩ := exists_word_floor_threshold (A := A) (B := B)
    (by decide) (by decide : runParameters63 ≠ []) ha
  have h61 : ∃ best, localMinimum 61 (wordAt 61 runParameters63) = some best ∧
      (A : Rat) * best < (B : Rat) := by
    refine ⟨940558659001986165720875008 / 870752088223798699522806345, ?_, ?_⟩ <;> decide +kernel
  have h60 : ¬ ∃ best, localMinimum 60 (wordAt 60 runParameters63) = some best ∧
      (A : Rat) * best < (B : Rat) := by
    rintro ⟨best, hbest, hlt⟩
    have hcalc : localMinimum 60 (wordAt 60 runParameters63) =
        some (209751981010694717636608000 / 193938400498936914607618323) := by decide +kernel
    rw [hcalc] at hbest
    obtain rfl := Option.some.inj hbest
    exact (by decide +kernel : ¬ (A : Rat) *
      (209751981010694717636608000 / 193938400498936914607618323) < (B : Rat)) hlt
  have hhi := (ht 61 (by decide)).mp h61
  have hlo : ¬ t ≤ 60 := fun h => h60 ((ht 60 (by decide)).mpr h)
  have he : t = 61 := by omega
  simpa only [he, A, B, Rat.natCast_ofNat] using ht n hn

end Collatz.ExcursionAnchor
