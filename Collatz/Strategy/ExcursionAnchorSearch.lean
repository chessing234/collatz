import Collatz.Strategy.ExcursionAnchorLayout

/-!
# Exact finite optimization over excursion anchors

Work backwards through the candidate layers. At each coordinate retain
the minimum product attainable over the remaining word. The finite
anchor theorem makes this also a minimum over all rational shifts in
the band.
-/

namespace Collatz.ExcursionAnchor

/-- A schedule with its coordinates taken from the supplied layers. -/
inductive Permitted : List Edge → List (List Rat) → Rat → List Rat → Prop where
  | last {choices : List Rat} {p : Rat} :
      p ∈ choices → Permitted [] [choices] p []
  | more {e : Edge} {word : List Edge} {choices : List Rat} {later : List (List Rat)}
      {p q : Rat} {rest : List Rat} :
      p ∈ choices → Permitted word later q rest →
      Permitted (e :: word) (choices :: later) p (q :: rest)

private theorem Permitted.first_pos {word layers p rest} (h : Permitted word layers p rest)
    (positive : ∀ layer ∈ layers, ∀ q ∈ layer, 0 < q) : 0 < p := by
  cases h with
  | last hp => exact positive _ List.mem_cons_self _ hp
  | more hp _ => exact positive _ List.mem_cons_self _ hp

/-- One suffix-product entry per permitted starting coordinate. -/
def productTable : List Edge → List (List Rat) → List (Rat × Rat)
  | [], [choices] => choices.map (fun p => (p, 1))
  | e :: rest, choices :: later =>
    let suffix := productTable rest later
    choices.filterMap fun p =>
      ((suffix.map (fun z => e.factor p z.1 * z.2)).min?).map (fun c => (p, c))
  | _, _ => []

/-- Every computed minimum has a schedule that attains it. -/
theorem productTable_attained {word layers p result} (h : (p, result) ∈ productTable word layers) :
    ∃ rest, Permitted word layers p rest ∧ costOn word (p :: rest) = result := by
  induction word generalizing layers p result with
  | nil =>
    cases layers with
    | nil => simp [productTable] at h
    | cons choices later =>
      cases later with
      | nil =>
        have hh : (p, result) ∈ choices.map (fun q => (q, (1 : Rat))) := h
        obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
        cases heq
        exact ⟨[], .last hq, rfl⟩
      | cons _ _ => simp [productTable] at h
  | cons e word ih =>
    cases layers with
    | nil => simp [productTable] at h
    | cons choices later =>
      simp only [productTable, List.mem_filterMap] at h
      obtain ⟨q, hq, hpair⟩ := h
      let values := (productTable word later).map (fun z => e.factor q z.1 * z.2)
      change values.min?.map (fun c => (q, c)) = some (p, result) at hpair
      cases hm : values.min? with
      | none => simp [hm] at hpair
      | some r =>
        have heq : (q, r) = (p, result) := by simpa [hm] using hpair
        cases heq
        obtain ⟨⟨target, price⟩, hentry, hprice⟩ := List.mem_map.mp (List.min?_mem hm)
        obtain ⟨rest, hrest, hcost⟩ := ih hentry
        refine ⟨target :: rest, .more hq hrest, ?_⟩
        rw [costOn, hcost]
        exact hprice

/-- The table computes a product no greater than any permitted schedule.
Only positivity of the coordinates is needed for the backward comparison. -/
theorem Permitted.cover {word layers p rest} (h : Permitted word layers p rest)
    (positive : ∀ layer ∈ layers, ∀ q ∈ layer, 0 < q) :
    ∃ r, (p, r) ∈ productTable word layers ∧ r ≤ costOn word (p :: rest) := by
  induction h with
  | @last choices p hp =>
    refine ⟨1, ?_, Rat.le_refl⟩
    exact List.mem_map_of_mem hp
  | @more e word choices later p q rest hp hrest ih =>
    have hpositive : ∀ layer ∈ later, ∀ z ∈ layer, 0 < z :=
      fun layer hl => positive layer (List.mem_cons_of_mem _ hl)
    obtain ⟨r, hr, hle⟩ := ih hpositive
    let values := (productTable word later).map (fun z => e.factor p z.1 * z.2)
    have hmember : e.factor p q * r ∈ values := List.mem_map_of_mem hr
    cases hm : values.min? with
    | none =>
      rw [List.min?_eq_none_iff.mp hm] at hmember
      exact False.elim (List.not_mem_nil hmember)
    | some best =>
      refine ⟨best, ?_, ?_⟩
      · apply List.mem_filterMap.mpr
        refine ⟨p, hp, ?_⟩
        change values.min?.map (fun c => (p, c)) = _
        rw [hm]
        rfl
      · have hmin := (List.min?_eq_some_iff.mp hm).2 _ hmember
        have hp' := positive choices List.mem_cons_self p hp
        have hq' := hrest.first_pos hpositive
        exact Rat.le_trans hmin
          (Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt (e.factor_pos hp' hq')))

/-- All boundary layers of the finite anchor search. -/
def anchorLayers (n : Rat) (word : List Edge) : List (List Rat) :=
  (List.range (word.length + 1)).map (anchorCandidates n word)

def anchorMinimum (n : Rat) (word : List Edge) : Option Rat :=
  ((productTable word (anchorLayers n word)).map Prod.snd).min?

private theorem permitted_of_coordinates {word : List Edge} {layers : List (List Rat)}
    {coordinates : List Rat} (hlength : layers.length = word.length + 1)
    (hcoords : coordinates.length = word.length + 1)
    (hmem : ∀ (i : Nat) (p : Rat), coordinates[i]? = some p → ∃ layer : List Rat, layers[i]? = some layer ∧ p ∈ layer) :
    ∃ p rest, coordinates = p :: rest ∧ Permitted word layers p rest := by
  induction word generalizing layers coordinates with
  | nil =>
    cases layers with
    | nil => simp at hlength
    | cons choices later =>
      cases coordinates with
      | nil => simp at hcoords
      | cons p rest =>
        have hl : later = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlength
        have hc : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hcoords
        subst later
        subst rest
        obtain ⟨layer, he, hp⟩ := hmem 0 p rfl
        have heq : choices = layer := Option.some.inj he
        subst layer
        exact ⟨p, [], rfl, .last hp⟩
  | cons e word ih =>
    cases layers with
    | nil => simp at hlength
    | cons choices later =>
      cases coordinates with
      | nil => simp at hcoords
      | cons p coords =>
        obtain ⟨layer, he, hp⟩ := hmem 0 p rfl
        have heq : choices = layer := Option.some.inj he
        subst layer
        have hl : later.length = word.length + 1 := by simpa using hlength
        have hc : coords.length = word.length + 1 := by simpa using hcoords
        have hm : ∀ (i : Nat) (q : Rat), coords[i]? = some q → ∃ layer : List Rat, later[i]? = some layer ∧ q ∈ layer := by
          intro i q hq
          exact hmem (i + 1) q hq
        obtain ⟨q, rest, rfl, hs⟩ := ih hl hc hm
        exact ⟨p, q :: rest, rfl, .more hp hs⟩

private theorem anchorLayers_positive {n : Rat} (word : List Edge) (hn : 0 < n) :
    ∀ layer ∈ anchorLayers n word, ∀ p ∈ layer, 0 < p := by
  intro layer hl p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  have h := (mem_anchorCandidates_iff.mp hp).1.1
  grind

/-- The finite rational search returns a product no larger than the
product of any rational layout in the shift band. -/
theorem Layout.anchorMinimum_le (layout : Layout) {n : Rat} (hn : 0 < n)
    (hband : layout.band n) :
    ∃ best, anchorMinimum n layout.word = some best ∧ best ≤ layout.value := by
  obtain ⟨better, hword, hvalue, hmembers⟩ := layout.finite_anchors hn hband
  have hlength : (anchorLayers n layout.word).length = layout.word.length + 1 := by
    simp [anchorLayers]
  have hcoords : better.coords.length = layout.word.length + 1 := by
    rw [better.coords_length, hword]
  have hmem : ∀ (i : Nat) (p : Rat), better.coords[i]? = some p →
      ∃ layer : List Rat, (anchorLayers n layout.word)[i]? = some layer ∧ p ∈ layer := by
    intro i p hp
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hp
    have hi' : i < layout.word.length + 1 := by omega
    refine ⟨anchorCandidates n layout.word i, ?_, ?_⟩
    · rw [anchorLayers, List.getElem?_map, List.getElem?_range hi']
      rfl
    · rw [← he]
      exact hmembers i hi
  obtain ⟨p, rest, hp, hperm⟩ := permitted_of_coordinates hlength hcoords hmem
  obtain ⟨r, hr, hle⟩ := hperm.cover (anchorLayers_positive _ hn)
  have hcost : costOn layout.word (p :: rest) = better.value := by
    rw [← hp, ← hword, better.costOn_eq]
  have hentry : r ∈ (productTable layout.word (anchorLayers n layout.word)).map Prod.snd :=
    List.mem_map_of_mem hr
  unfold anchorMinimum
  cases hm : ((productTable layout.word (anchorLayers n layout.word)).map Prod.snd).min? with
  | none =>
    rw [List.min?_eq_none_iff.mp hm] at hentry
    exact False.elim (List.not_mem_nil hentry)
  | some best =>
    refine ⟨best, rfl, ?_⟩
    rw [hcost] at hle
    exact Rat.le_trans ((List.min?_eq_some_iff.mp hm).2 r hentry) (Rat.le_trans hle hvalue)

/-- The returned product is attained by a rational schedule on the finite
anchor layers. Together with `Layout.anchorMinimum_le`, this is exact
optimization over the rational shift band. -/
theorem anchorMinimum_attained {n : Rat} {word : List Edge} {r : Rat}
    (h : anchorMinimum n word = some r) :
    ∃ p rest, Permitted word (anchorLayers n word) p rest ∧ costOn word (p :: rest) = r := by
  have hm : r ∈ (productTable word (anchorLayers n word)).map Prod.snd :=
    List.min?_mem h
  obtain ⟨⟨p, result⟩, hentry, hr⟩ := List.mem_map.mp hm
  obtain ⟨rest, hperm, hcost⟩ := productTable_attained hentry
  exact ⟨p, rest, hperm, hcost.trans hr⟩

end Collatz.ExcursionAnchor
