import Collatz.Strategy.ExcursionRealization

/-!
# Source bounds uniform over the balanced coefficient phase

Feasibility of a coefficient corridor is a pairwise comparison of
prefix ratios. Pruning by this comparison enumerates all allowed
words for every initial phase at once. Their canonical sources
then give a uniform lower bound on any genuine realization.
-/

namespace Collatz.ExcursionPhaseWords

open ExcursionBudget ExcursionRays

private def coefficientPairs : List Run → List (Nat × Nat)
  | [] => [(1, 1)]
  | r :: rs => (3 ^ ExcursionBudget.oddCount (r :: rs), 2 ^ time (r :: rs)) :: coefficientPairs rs

private def phaseBound (p q : Nat) (pair : Nat × Nat) : Prop :=
  2 * q * pair.1 < 3 * p * pair.2 ∧ p * pair.2 ≤ q * pair.1

private instance (p q : Nat) (pair : Nat × Nat) : Decidable (phaseBound p q pair) :=
  inferInstanceAs (Decidable (2 * q * pair.1 < 3 * p * pair.2 ∧ p * pair.2 ≤ q * pair.1))

/-- Every prefix inverse coefficient, multiplied by the initial
phase `p/q`, stays in `(2/3,1]`. -/
def Corridor (p q : Nat) : List Run → Prop
  | [] => phaseBound p q (1, 1)
  | r :: rs => phaseBound p q (3 ^ ExcursionBudget.oddCount (r :: rs), 2 ^ time (r :: rs)) ∧
      Corridor p q rs

instance instDecidableCorridor (p q : Nat) : (rs : List Run) → Decidable (Corridor p q rs)
  | [] => inferInstanceAs (Decidable (phaseBound p q (1, 1)))
  | r :: rs =>
    haveI : Decidable (Corridor p q rs) := instDecidableCorridor p q rs
    inferInstanceAs (Decidable (phaseBound p q
      (3 ^ ExcursionBudget.oddCount (r :: rs), 2 ^ time (r :: rs)) ∧ Corridor p q rs))

private theorem pair_bound_of_corridor {p q : Nat} {rs : List Run} (hc : Corridor p q rs)
    {pair : Nat × Nat} (hp : pair ∈ coefficientPairs rs) : phaseBound p q pair := by
  induction rs with
  | nil => have he := List.mem_singleton.mp hp; subst pair; exact hc
  | cons r rs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hc.1
    · exact ih hc.2 hp

private theorem pair_denominator_pos {rs : List Run} {pair : Nat × Nat}
    (hp : pair ∈ coefficientPairs rs) : 0 < pair.2 := by
  induction rs with
  | nil => have he := List.mem_singleton.mp hp; subst pair; decide
  | cons r rs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.two_pow_pos _
    · exact ih hp

private def phasePossible (rs : List Run) : Bool :=
  (coefficientPairs rs).all fun left => (coefficientPairs rs).all fun right =>
    decide (2 * left.1 * right.2 < 3 * right.1 * left.2)

private theorem phase_possible_of_corridor {p q : Nat} {rs : List Run}
    (hc : Corridor p q rs) : phasePossible rs = true := by
  apply List.all_eq_true.mpr
  intro left hl
  apply List.all_eq_true.mpr
  intro right hr
  simp only [decide_eq_true_eq]
  have hleft := (pair_bound_of_corridor hc hl).1
  have hright := (pair_bound_of_corridor hc hr).2
  apply Nat.lt_of_mul_lt_mul_left (a := q)
  calc
    _ = (2 * q * left.1) * right.2 := by ac_rfl
    _ < (3 * p * left.2) * right.2 := Nat.mul_lt_mul_of_pos_right hleft (pair_denominator_pos hr)
    _ = (3 * left.2) * (p * right.2) := by ac_rfl
    _ ≤ (3 * left.2) * (q * right.1) := Nat.mul_le_mul_left _ hright
    _ = _ := by ac_rfl

/-- All phase-feasible words of the given length, in reverse chronology. -/
def phaseWords : Nat → List (List Run)
  | 0 => [[]]
  | k + 1 => ((phaseWords k).flatMap fun rs => [⟨1, 1⟩ :: rs, ⟨2, 1⟩ :: rs]).filter phasePossible

theorem mem_phaseWords_of_corridor {p q : Nat} {rs : List Run}
    (hc : Corridor p q rs) (hshape : ∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) :
    rs ∈ phaseWords rs.length := by
  induction rs with
  | nil => simp [phaseWords]
  | cons r rs ih =>
    have hm := ih hc.2 (fun s hs => hshape s (List.mem_cons_of_mem _ hs))
    change r :: rs ∈ ((phaseWords rs.length).flatMap
      fun xs => [⟨1, 1⟩ :: xs, ⟨2, 1⟩ :: xs]).filter phasePossible
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨rs, hm, ?_⟩, phase_possible_of_corridor hc⟩
    rcases hshape r (List.mem_cons_self ..) with rfl | rfl <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem phase_source_certificate :
    (phaseWords 30).all (fun rs => decide (204661442731210757479531 ≤ canonicalSource rs)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem phase_word_count : (phaseWords 30).length = 31 := by decide +kernel

/-- Every thirty-excursion balanced corridor, for every positive
initial phase, needs a source above two hundred sextillion. -/
theorem source_large_of_thirty_phase_corridor {n e p q : Nat} {rs : List Run}
    (ht : Trace n e rs) (hc : Corridor p q rs)
    (hshape : ∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) (hlen : rs.length = 30) :
    204661442731210757479531 ≤ n := by
  have hm := mem_phaseWords_of_corridor hc hshape
  rw [hlen] at hm
  have hsource := of_decide_eq_true ((List.all_eq_true.mp phase_source_certificate) rs hm)
  cases rs with
  | nil => simp at hlen
  | cons r rs =>
    have hvalid : PositiveProfile (r :: rs) := by
      intro s hs
      rcases hshape s hs with rfl | rfl <;> decide
    have hres := (realizes_iff_canonical_source hvalid).mp ⟨e, ht⟩
    have hle : canonicalSource (r :: rs) ≤ n := hres ▸ Nat.mod_le n _
    exact Nat.le_trans hsource hle

private theorem corridor_of_append {p q : Nat} {later earlier : List Run}
    (hc : Corridor p q (later ++ earlier)) : Corridor p q earlier := by
  induction later with
  | nil => exact hc
  | cons r rs ih => exact ih hc.2

private theorem corridor_initial {p q : Nat} {rs : List Run} (hc : Corridor p q rs) :
    2 * q < 3 * p ∧ p ≤ q := by
  have h := corridor_of_append (later := rs) (earlier := []) (by simpa only [List.append_nil] using hc)
  simpa only [Corridor, phaseBound, Nat.mul_one] using h

/-- Any longer corridor contains an initial thirty-run corridor,
so the same source bound applies. -/
theorem source_large_of_phase_corridor {n e p q : Nat} {rs : List Run}
    (ht : Trace n e rs) (hc : Corridor p q rs)
    (hshape : ∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) (hlen : 30 ≤ rs.length) :
    204661442731210757479531 ≤ n := by
  let k := rs.length - 30
  have hsplit : rs.take k ++ rs.drop k = rs := List.take_append_drop k rs
  obtain ⟨x, hpre, _⟩ := split_trace (hsplit.symm ▸ ht)
  have hcorr := corridor_of_append (hsplit.symm ▸ hc)
  have hlen' : (rs.drop k).length = 30 := by rw [List.length_drop]; dsimp only [k]; omega
  exact source_large_of_thirty_phase_corridor hpre hcorr
    (fun r hr => hshape r (List.mem_of_mem_drop hr)) hlen'

/-- A bounded heavy prefix cannot feed a long balanced corridor
near the top of its global coefficient range. -/
theorem source_sum_large_of_phase_corridor_after_prefix {n x e : Nat} {earlier rs : List Run}
    (hpre : Trace n x earlier) (hproper : ProperPrefixBound 1 1 earlier)
    (ht : Trace x e rs) (hc : Corridor (2 ^ time earlier) (3 ^ ExcursionBudget.oddCount earlier) rs)
    (hshape : ∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) (hlen : 30 ≤ rs.length) :
    2 * 204661442731210757479531 < 3 * (n + earlier.length) := by
  let A := 3 ^ ExcursionBudget.oddCount earlier
  let B := 2 ^ time earlier
  have hsource := source_large_of_phase_corridor ht hc hshape hlen
  have hlow : 2 * A < 3 * B := (corridor_initial hc).1
  have hC := offset_le_length_mul_coefficient hproper
  have hsize : B * x ≤ A * (n + earlier.length) := by
    rw [← hpre.affine, Nat.mul_add]
    exact Nat.add_le_add_left hC _
  apply Nat.lt_of_mul_lt_mul_left (a := A)
  calc
    _ = (2 * A) * 204661442731210757479531 := by ac_rfl
    _ < (3 * B) * 204661442731210757479531 :=
      Nat.mul_lt_mul_of_pos_right hlow (by decide)
    _ ≤ (3 * B) * x := Nat.mul_le_mul_left _ hsource
    _ = 3 * (B * x) := Nat.mul_assoc ..
    _ ≤ 3 * (A * (n + earlier.length)) := Nat.mul_le_mul_left _ hsize
    _ = _ := by ac_rfl

/-- A convenient bounded-source form for prefixes in the exponent window. -/
theorem corridor_length_lt_thirty_after_bounded_prefix {n x e : Nat} {earlier rs : List Run}
    (hpre : Trace n x earlier) (hproper : ProperPrefixBound 1 1 earlier)
    (hn : n < 2 ^ 75) (hshort : earlier.length < 325000000000)
    (ht : Trace x e rs) (hc : Corridor (2 ^ time earlier) (3 ^ ExcursionBudget.oddCount earlier) rs)
    (hshape : ∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) : rs.length < 30 := by
  apply Nat.lt_of_not_ge
  intro hlong
  have hsum := source_sum_large_of_phase_corridor_after_prefix hpre hproper ht hc hshape hlong
  omega

private def witnessSteps : List Nat :=
  [2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1]

private def witnessProfile : List Run := witnessSteps.reverse.map (fun v => ⟨v, 1⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem witness_spec :
    Corridor 1853020188851841 2251799813685248 witnessProfile ∧
      witnessProfile.length = 30 ∧
      canonicalSource witnessProfile = 204661442731210757479531 ∧
      canonicalLanding witnessProfile = 182301555038774009708197 := by decide +kernel

/-- A genuine orbit attains the uniform source bound. -/
theorem phase_source_bound_attained :
    ∃ rs : List Run, rs.length = 30 ∧ Corridor 1853020188851841 2251799813685248 rs ∧
      (∀ r ∈ rs, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) ∧
      Trace 204661442731210757479531 182301555038774009708197 rs := by
  obtain ⟨hc, hl, hn, he⟩ := witness_spec
  have hs : ∀ r ∈ witnessProfile, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩ := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    have hv12 : ∀ v ∈ witnessSteps, v = 1 ∨ v = 2 := by decide +kernel
    rcases hv12 v (List.mem_reverse.mp hv) with rfl | rfl <;> simp
  have hv : PositiveProfile witnessProfile := by
    intro r hr
    rcases hs r hr with rfl | rfl <;> decide
  have ht := canonical_trace_of_positive_profile hv
  rw [hn, he] at ht
  exact ⟨witnessProfile, hl, hc, hs, ht⟩

end Collatz.ExcursionPhaseWords
