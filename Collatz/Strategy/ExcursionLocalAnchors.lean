import Collatz.Strategy.ExcursionAnchorCertificate

/-!
# Zero-offset excursion blocks have length at most two

In shifts relative to the floor, a zero edge satisfies
`2^(v+W) t = 3^v (s-1) + 2^v`. Valid input shifts are at least
`1/3` and valid outputs are at most `1/2`. Two consecutive links
force the first to have one extra halving and the second to have
odd-run length one. Their final shift is at most `1/8`.
-/

namespace Collatz.ExcursionAnchor

/-- The edges come from positive odd runs followed by positive halving runs. -/
def ExcursionAlphabet (floor : Nat) (word : List Edge) : Prop :=
  ∀ e ∈ word, ∃ v W : Nat, 0 < v ∧ 0 < W ∧ e = Edge.ofRun floor v W

theorem OrbitWord.alphabet {floor x endpoint elapsed A B word}
    (h : OrbitWord floor x word endpoint elapsed A B) : ExcursionAlphabet floor word := by
  induction h with
  | nil => simp [ExcursionAlphabet]
  | @cons x y v u W endpoint elapsed A B word hstep _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨v, W, hstep.2.2.2.1, hstep.2.2.2.2.1, rfl⟩
    · exact ih e he

private theorem zero_identity (n v W : Nat) (p : Rat) :
    (((2 : Nat) ^ (v + W) : Nat) : Rat) *
        ((Edge.ofRun n v W).transport p - (n : Rat)) =
      (((3 : Nat) ^ v : Nat) : Rat) * (p - ((n : Rat) + 1)) + ((2 : Nat) ^ v : Nat) := by
  have h := (Edge.ofRun n v W).transport_spec p
  change (((2 : Nat) ^ (v + W) : Nat) : Rat) * (Edge.ofRun n v W).transport p =
    (((3 : Nat) ^ v : Nat) : Rat) * p +
      ((((2 : Nat) ^ (v + W) : Nat) : Rat) * (n : Rat) + ((2 : Nat) ^ v : Nat) -
        (((3 : Nat) ^ v : Nat) : Rat) * ((n : Rat) + 1)) at h
  grind

private theorem inverse_identity (n v W : Nat) (q : Rat) :
    (((3 : Nat) ^ v : Nat) : Rat) *
        ((Edge.ofRun n v W).inverse q - ((n : Rat) + 1)) =
      (((2 : Nat) ^ (v + W) : Nat) : Rat) * (q - (n : Rat)) - ((2 : Nat) ^ v : Nat) := by
  have h := (Edge.ofRun n v W).inverse_spec q
  change (((3 : Nat) ^ v : Nat) : Rat) * (Edge.ofRun n v W).inverse q +
    ((((2 : Nat) ^ (v + W) : Nat) : Rat) * (n : Rat) + ((2 : Nat) ^ v : Nat) -
      (((3 : Nat) ^ v : Nat) : Rat) * ((n : Rat) + 1)) =
        (((2 : Nat) ^ (v + W) : Nat) : Rat) * q at h
  grind

private theorem three_pow_gt_two {v : Nat} (hv : 0 < v) :
    (((2 : Nat) ^ v : Nat) : Rat) < ((3 : Nat) ^ v : Nat) :=
  Rat.natCast_lt_natCast.mpr (Nat.pow_lt_pow_left (by decide) (by omega))

private theorem numerator_le {v : Nat} (k : Nat) (hk : k ≤ v) :
    3 ^ k * (2 : Nat) ^ v ≤ 2 ^ k * 3 ^ v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.pow_add 2 k m, Nat.pow_add 3 k m]
  calc
    _ = (3 ^ k * 2 ^ k) * 2 ^ m := by ac_rfl
    _ ≤ (3 ^ k * 2 ^ k) * 3 ^ m :=
      Nat.mul_le_mul_left _ (Collatz.Arith.two_pow_le_three_pow m)
    _ = _ := by ac_rfl

theorem input_ge_third {n v W : Nat} (hv : 0 < v) {p : Rat}
    (hq : (n : Rat) ≤ (Edge.ofRun n v W).transport p) :
    (n : Rat) + 1 / 3 ≤ p := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  let q := (Edge.ofRun n v W).transport p
  have ha : 0 < a := (Edge.ofRun n v W).a_pos
  have hb : 0 < b := (Edge.ofRun n v W).b_pos
  have hratio : 3 * c ≤ 2 * a := by
    have h := Rat.natCast_le_natCast.mpr (numerator_le 1 (by omega : 1 ≤ v))
    simpa [a, c, Nat.pow_one, Rat.natCast_mul] using h
  have hraw : b * (q - (n : Rat)) = a * (p - ((n : Rat) + 1)) + c :=
    zero_identity n v W p
  have hq0 : 0 ≤ q - (n : Rat) := (Rat.le_iff_sub_nonneg _ _).mp hq
  have hprod := Rat.mul_nonneg (Rat.le_of_lt hb) hq0
  apply Rat.le_of_mul_le_mul_left _ ha
  grind

theorem input_ge_five_ninths {n v W : Nat} (hv : 2 ≤ v) {p : Rat}
    (hq : (n : Rat) ≤ (Edge.ofRun n v W).transport p) :
    (n : Rat) + 5 / 9 ≤ p := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  let q := (Edge.ofRun n v W).transport p
  have ha : 0 < a := (Edge.ofRun n v W).a_pos
  have hb : 0 < b := (Edge.ofRun n v W).b_pos
  have hratio : 9 * c ≤ 4 * a := by
    have h := Rat.natCast_le_natCast.mpr (numerator_le 2 hv)
    simpa [a, c, show (3 : Nat) ^ 2 = 9 by decide, show (2 : Nat) ^ 2 = 4 by decide,
      Rat.natCast_mul] using h
  have hraw : b * (q - (n : Rat)) = a * (p - ((n : Rat) + 1)) + c :=
    zero_identity n v W p
  have hq0 : 0 ≤ q - (n : Rat) := (Rat.le_iff_sub_nonneg _ _).mp hq
  have hprod := Rat.mul_nonneg (Rat.le_of_lt hb) hq0
  apply Rat.le_of_mul_le_mul_left _ ha
  grind

private theorem output_le {n v W k : Nat} {p : Rat}
    (hk : k ≤ W) (hp : p ≤ (n : Rat) + 1) :
    (Edge.ofRun n v W).transport p ≤ (n : Rat) + 1 / (((2 : Nat) ^ k : Nat) : Rat) := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  let q := (Edge.ofRun n v W).transport p
  let power : Rat := ((2 : Nat) ^ k : Nat)
  have ha : 0 < a := (Edge.ofRun n v W).a_pos
  have hb : 0 < b := (Edge.ofRun n v W).b_pos
  have hpower : 0 < power := Rat.natCast_pos.mpr (Nat.two_pow_pos _)
  have hmul : c * power ≤ b := by
    have h := Nat.mul_le_mul_left ((2 : Nat) ^ v)
      (Nat.pow_le_pow_right (n := 2) (by decide) hk)
    have h' := Rat.natCast_le_natCast.mpr h
    change c * power ≤ (((2 : Nat) ^ (v + W) : Nat) : Rat)
    rw [Nat.pow_add 2 v W, Rat.natCast_mul]
    simpa [c, power, Rat.natCast_mul] using h'
  have hraw : b * (q - (n : Rat)) = a * (p - ((n : Rat) + 1)) + c :=
    zero_identity n v W p
  have hpart := Rat.mul_le_mul_of_nonneg_left (a := p - ((n : Rat) + 1))
    (b := 0) (c := a) (by grind) (Rat.le_of_lt ha)
  have hcone : c / 1 = c := by
    simpa only [Rat.mul_one] using (Rat.div_mul_cancel (a := c) (b := 1) (by decide))
  have hdiv : c / 1 ≤ b / power :=
    (div_le_div_iff_pos (by decide : (0 : Rat) < 1) hpower).mpr (by simpa [Rat.mul_one] using hmul)
  rw [hcone] at hdiv
  apply Rat.le_of_mul_le_mul_left _ hb
  change b * q ≤ b * ((n : Rat) + 1 / power)
  have hright : b * ((n : Rat) + 1 / power) = b * (n : Rat) + b / power := by
    rw [Rat.mul_add]
    simp [Rat.div_def, Rat.one_mul]
  rw [hright]
  grind

theorem output_half {n v W : Nat} {p : Rat} (hW : 0 < W)
    (hp : p ≤ (n : Rat) + 1) :
    (Edge.ofRun n v W).transport p ≤ (n : Rat) + 1 / 2 := by
  simpa using output_le (k := 1) hW hp

private theorem output_quarter {n v W : Nat} {p : Rat} (hW : 2 ≤ W)
    (hp : p ≤ (n : Rat) + 1) :
    (Edge.ofRun n v W).transport p ≤ (n : Rat) + 1 / 4 := by
  simpa using output_le (k := 2) hW hp

private theorem short_output_eighth {n W : Nat} {p : Rat} (hW : 0 < W)
    (hp : p ≤ (n : Rat) + 1 / 2) :
    (Edge.ofRun n 1 W).transport p ≤ (n : Rat) + 1 / 8 := by
  let b : Rat := ((2 : Nat) ^ (1 + W) : Nat)
  let q := (Edge.ofRun n 1 W).transport p
  have hb : 0 < b := (Edge.ofRun n 1 W).b_pos
  have hbig : 4 ≤ b := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 1 + W)
    exact Rat.natCast_le_natCast.mpr h
  have hraw : b * (q - (n : Rat)) = 3 * (p - ((n : Rat) + 1)) + 2 :=
    zero_identity n 1 W p
  apply Rat.le_of_mul_le_mul_left _ hb
  change b * q ≤ b * ((n : Rat) + 1 / 8)
  grind

/-- Two consecutive zero links force the first extra-halving count and
the second odd-run length to be one. The end of the pair is at most
one eighth above the floor. -/
theorem two_zero_links {n v W v' W' : Nat} (hW : 0 < W)
    (hv' : 0 < v') (hW' : 0 < W') {p : Rat} (hp : p ≤ (n : Rat) + 1)
    (hq : (n : Rat) ≤ (Edge.ofRun n v' W').transport ((Edge.ofRun n v W).transport p)) :
    W = 1 ∧ v' = 1 ∧
      (Edge.ofRun n v' W').transport ((Edge.ofRun n v W).transport p) ≤ (n : Rat) + 1 / 8 := by
  let mid := (Edge.ofRun n v W).transport p
  have hthird : (n : Rat) + 1 / 3 ≤ mid := input_ge_third hv' hq
  have hhalf : mid ≤ (n : Rat) + 1 / 2 := output_half hW hp
  have hWone : W = 1 := by
    by_cases he : W = 1
    · exact he
    · have hqtr : mid ≤ (n : Rat) + 1 / 4 := output_quarter (by omega) hp
      grind
  have hvone : v' = 1 := by
    by_cases he : v' = 1
    · exact he
    · have hfive : (n : Rat) + 5 / 9 ≤ mid := input_ge_five_ninths (by omega) hq
      grind
  refine ⟨hWone, hvone, ?_⟩
  rw [hvone]
  exact short_output_eighth hW' hhalf

theorem transport_below {n v W : Nat} (hv : 0 < v) {p : Rat} (hp : p ≤ (n : Rat)) :
    (Edge.ofRun n v W).transport p < (n : Rat) := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  let q := (Edge.ofRun n v W).transport p
  have ha : 0 < a := (Edge.ofRun n v W).a_pos
  have hb : 0 < b := (Edge.ofRun n v W).b_pos
  have hac : c < a := three_pow_gt_two hv
  have hraw : b * (q - (n : Rat)) = a * (p - ((n : Rat) + 1)) + c :=
    zero_identity n v W p
  have hm := Rat.mul_le_mul_of_nonneg_left (a := p - ((n : Rat) + 1))
    (b := -1) (c := a) (by grind) (Rat.le_of_lt ha)
  apply (Rat.mul_lt_mul_left hb).mp
  change b * q < b * (n : Rat)
  grind

private theorem inverse_above {n v W : Nat} (hW : 0 < W) {q : Rat}
    (hq : (n : Rat) + 1 ≤ q) : (n : Rat) + 1 < (Edge.ofRun n v W).inverse q := by
  let a : Rat := ((3 : Nat) ^ v : Nat)
  let b : Rat := ((2 : Nat) ^ (v + W) : Nat)
  let c : Rat := ((2 : Nat) ^ v : Nat)
  let p := (Edge.ofRun n v W).inverse q
  have ha : 0 < a := (Edge.ofRun n v W).a_pos
  have hb : 0 < b := (Edge.ofRun n v W).b_pos
  have hc : 0 < c := Rat.natCast_pos.mpr (Nat.two_pow_pos _)
  have hbc : c * 2 ≤ b := by
    have h := Nat.mul_le_mul_left ((2 : Nat) ^ v) (Collatz.Arith.two_le_two_pow hW)
    have h' := Rat.natCast_le_natCast.mpr h
    change c * 2 ≤ (((2 : Nat) ^ (v + W) : Nat) : Rat)
    rw [Nat.pow_add 2 v W, Rat.natCast_mul]
    simpa [c, Rat.natCast_mul] using h'
  have hraw : a * (p - ((n : Rat) + 1)) = b * (q - (n : Rat)) - c :=
    inverse_identity n v W q
  have hm := Rat.mul_le_mul_of_nonneg_left (a := 1) (b := q - (n : Rat))
    (c := b) (by grind) (Rat.le_of_lt hb)
  apply (Rat.mul_lt_mul_left ha).mp
  change a * ((n : Rat) + 1) < a * p
  grind

private theorem alphabet_tail {n : Nat} {e : Edge} {rest : List Edge}
    (h : ExcursionAlphabet n (e :: rest)) : ExcursionAlphabet n rest :=
  fun a ha => h a (List.mem_cons_of_mem _ ha)

private theorem endpoint_stays_below {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {p : Rat} (hp : p < (n : Rat)) : endpoint word p < (n : Rat) := by
  induction word generalizing p with
  | nil => exact hp
  | cons e rest ih =>
    obtain ⟨v, W, hv, _, rfl⟩ := ha e List.mem_cons_self
    exact ih (alphabet_tail ha) (transport_below hv (Rat.le_of_lt hp))

private theorem inverse_stays_above {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {p : Rat} (hp : (n : Rat) + 1 ≤ p) : (n : Rat) + 1 ≤ inverseEndpoint word p := by
  induction word with
  | nil => exact hp
  | cons e rest ih =>
    obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
    exact Rat.le_of_lt (inverse_above hW (ih (alphabet_tail ha)))

private theorem endpoint_inverseEndpoint (word : List Edge) (p : Rat) :
    endpoint word (inverseEndpoint word p) = p := by
  induction word with
  | nil => rfl
  | cons e rest ih =>
    rw [endpoint, inverseEndpoint, e.transport_eq_of_zero (e.inverse_spec _).symm, ih]

private theorem band_from_endpoints {n : Nat} {word : List Edge}
    (ha : ExcursionAlphabet n word) {p : Rat}
    (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) (hend : (n : Rat) ≤ endpoint word p) :
    ∀ q ∈ points word p, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1 := by
  induction word generalizing p with
  | nil =>
    intro q hq
    have he : q = p := by simpa [points] using hq
    simpa [he] using hp
  | cons e rest ih =>
    obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
    let q := (Edge.ofRun n v W).transport p
    have ha' := alphabet_tail ha
    have hlow : (n : Rat) ≤ q := by
      apply Classical.byContradiction
      intro hnot
      have hlt := endpoint_stays_below ha' ((Rat.not_le).mp hnot)
      exact ((Rat.not_le).mpr hlt) hend
    have hhigh : q ≤ (n : Rat) + 1 := by
      have hhalf : q ≤ (n : Rat) + 1 / 2 := output_half hW hp.2
      grind
    intro z hz
    change z ∈ p :: points rest q at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hp
    · exact ih ha' ⟨hlow, hhigh⟩ hend z hz

/-- Every zero-offset excursion block contained in the shift band has at
most two edges. -/
theorem zero_word_length {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {p : Rat} (hband : ∀ q ∈ points word p, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) :
    word.length ≤ 2 := by
  match word with
  | [] => decide
  | [_] => simp
  | [_, _] => simp
  | first :: second :: third :: rest =>
    exfalso
    obtain ⟨v, W, _, hW, rfl⟩ := ha first (by simp)
    obtain ⟨v', W', hv', hW', rfl⟩ := ha second (by simp)
    obtain ⟨v'', W'', hv'', _, rfl⟩ := ha third (by simp)
    let q := (Edge.ofRun n v W).transport p
    let r := (Edge.ofRun n v' W').transport q
    let s := (Edge.ofRun n v'' W'').transport r
    have hp : p ≤ (n : Rat) + 1 := (hband p (by simp [points])).2
    have hr : (n : Rat) ≤ r := (hband r (by simp [points, r, q])).1
    have hsMem : s ∈ points rest s := by cases rest <;> simp [points]
    have hs : (n : Rat) ≤ s := (hband s (by
      change s ∈ p :: q :: r :: points rest s
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsMem)))).1
    have hshort : r ≤ (n : Rat) + 1 / 8 := (two_zero_links hW hv' hW' hp hr).2.2
    have hlong : (n : Rat) + 1 / 3 ≤ r := input_ge_third hv'' hs
    grind

/-- A forward transport from a band endpoint can reach a candidate only
through an empty word or from the upper endpoint, in at most two links. -/
theorem forward_anchor_short {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {p : Rat} (hanchor : p = (n : Rat) ∨ p = (n : Rat) + 1)
    (hend : (n : Rat) ≤ endpoint word p) :
    word.length ≤ 2 ∧ (word = [] ∨ p = (n : Rat) + 1) := by
  have hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by rcases hanchor with rfl | rfl <;> grind
  refine ⟨zero_word_length ha (band_from_endpoints ha hp hend), ?_⟩
  rcases hanchor with rfl | h
  · cases word with
    | nil => exact Or.inl rfl
    | cons e rest =>
      obtain ⟨v, W, hv, _, rfl⟩ := ha e List.mem_cons_self
      have hlt := endpoint_stays_below (alphabet_tail ha)
        (transport_below (n := n) (W := W) hv Rat.le_refl)
      exact False.elim (((Rat.not_le).mpr hlt) hend)
  · exact Or.inr h

/-- A backward transport from a band endpoint can reach a candidate only
through an empty word or from the lower endpoint, in at most two links. -/
theorem backward_anchor_short {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word)
    {q : Rat} (hanchor : q = (n : Rat) ∨ q = (n : Rat) + 1)
    (hp : (n : Rat) ≤ inverseEndpoint word q ∧ inverseEndpoint word q ≤ (n : Rat) + 1) :
    word.length ≤ 2 ∧ (word = [] ∨ q = (n : Rat)) := by
  have hq : (n : Rat) ≤ q := by rcases hanchor with rfl | rfl <;> grind
  have hend : (n : Rat) ≤ endpoint word (inverseEndpoint word q) := by
    rw [endpoint_inverseEndpoint]
    exact hq
  refine ⟨zero_word_length ha (band_from_endpoints ha hp hend), ?_⟩
  rcases hanchor with h | rfl
  · exact Or.inr h
  · cases word with
    | nil => exact Or.inl rfl
    | cons e rest =>
      obtain ⟨v, W, _, hW, rfl⟩ := ha e List.mem_cons_self
      have hlt := inverse_above (v := v) hW (inverse_stays_above (alphabet_tail ha) Rat.le_refl)
      exact False.elim (((Rat.not_lt).mpr hp.2) hlt)

private def forwardLocal (n : Rat) : List Edge → List Rat
  | [] => []
  | [recent] => [recent.transport (n + 1)]
  | recent :: older :: _ =>
    [recent.transport (n + 1), recent.transport (older.transport (n + 1))]

private def backwardLocal (n : Rat) : List Edge → List Rat
  | [] => []
  | [next] => [next.inverse n]
  | next :: later :: _ => [next.inverse n, next.inverse (later.inverse n)]

private theorem forwardLocal_iff (n : Rat) (rev : List Edge) (p : Rat) :
    p ∈ forwardLocal n rev ↔
      ∃ pre block, rev.reverse = pre ++ block ∧ block ≠ [] ∧ block.length ≤ 2 ∧
        p = endpoint block (n + 1) := by
  constructor
  · intro h
    cases rev with
    | nil => simp [forwardLocal] at h
    | cons recent tail =>
      cases tail with
      | nil =>
        have hp : p = recent.transport (n + 1) := by simpa [forwardLocal] using h
        exact ⟨[], [recent], rfl, by simp, by simp, hp⟩
      | cons older rest =>
        have hp : p = recent.transport (n + 1) ∨
            p = recent.transport (older.transport (n + 1)) := by
          simpa [forwardLocal] using h
        rcases hp with hp | hp
        · exact ⟨(older :: rest).reverse, [recent], by simp [List.reverse_cons], by simp, by simp, hp⟩
        · exact ⟨rest.reverse, [older, recent], by simp [List.reverse_cons, List.append_assoc],
            by simp, by simp, hp⟩
  · rintro ⟨pre, block, he, hne, hlen, hp⟩
    have hrev := congrArg List.reverse he
    simp only [List.reverse_reverse, List.reverse_append] at hrev
    rw [hrev]
    cases block with
    | nil => exact False.elim (hne rfl)
    | cons older tail =>
      cases tail with
      | nil =>
        cases pre.reverse <;> simp [forwardLocal, endpoint] at hp ⊢ <;> simp [hp]
      | cons recent rest =>
        have hr : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        subst rest
        simp [forwardLocal, endpoint] at hp ⊢
        exact Or.inr hp

private theorem backwardLocal_iff (n : Rat) (after : List Edge) (p : Rat) :
    p ∈ backwardLocal n after ↔
      ∃ block post, after = block ++ post ∧ block ≠ [] ∧ block.length ≤ 2 ∧
        p = inverseEndpoint block n := by
  constructor
  · intro h
    cases after with
    | nil => simp [backwardLocal] at h
    | cons next tail =>
      cases tail with
      | nil =>
        have hp : p = next.inverse n := by simpa [backwardLocal] using h
        exact ⟨[next], [], rfl, by simp, by simp, hp⟩
      | cons later rest =>
        have hp : p = next.inverse n ∨ p = next.inverse (later.inverse n) := by
          simpa [backwardLocal] using h
        rcases hp with hp | hp
        · exact ⟨[next], later :: rest, rfl, by simp, by simp, hp⟩
        · exact ⟨[next, later], rest, rfl, by simp, by simp, hp⟩
  · rintro ⟨block, post, he, hne, hlen, hp⟩
    rw [he]
    cases block with
    | nil => exact False.elim (hne rfl)
    | cons next tail =>
      cases tail with
      | nil =>
        cases post <;> simp [backwardLocal, inverseEndpoint] at hp ⊢ <;> simp [hp]
      | cons later rest =>
        have hr : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        subst rest
        simp [backwardLocal, inverseEndpoint] at hp ⊢
        exact Or.inr hp

/-- The two band endpoints and at most two transports in each direction. -/
def localLayer (n : Rat) (priorRev after : List Edge) : List Rat :=
  ([n, n + 1] ++ (forwardLocal n priorRev ++ backwardLocal n after)).filter
    (fun p => decide (n ≤ p ∧ p ≤ n + 1))

theorem localLayer_length (n : Rat) (priorRev after : List Edge) :
    (localLayer n priorRev after).length ≤ 6 := by
  unfold localLayer
  apply Nat.le_trans (List.length_filter_le ..)
  have hleft : (forwardLocal n priorRev).length ≤ 2 := by
    cases priorRev with
    | nil => simp [forwardLocal]
    | cons _ rest => cases rest <;> simp [forwardLocal]
  have hright : (backwardLocal n after).length ≤ 2 := by
    cases after with
    | nil => simp [backwardLocal]
    | cons _ rest => cases rest <;> simp [backwardLocal]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- A recent odd run of length at least two excludes the second
forward candidate, so the boundary has at most five shifts. -/
theorem localLayer_length_of_recent_ge_two {n v W : Nat} {priorRev after : List Edge}
    (hv : 2 ≤ v) (hW : 0 < W) (ha : ExcursionAlphabet n priorRev) :
    (localLayer n (Edge.ofRun n v W :: priorRev) after).length ≤ 5 := by
  let inBand := fun p : Rat => decide ((n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1)
  have hright : (backwardLocal n after).length ≤ 2 := by
    cases after with
    | nil => simp [backwardLocal]
    | cons _ rest => cases rest <;> simp [backwardLocal]
  have hleft : ((forwardLocal n (Edge.ofRun n v W :: priorRev)).filter inBand).length ≤ 1 := by
    cases priorRev with
    | nil => exact List.length_filter_le ..
    | cons earlier tail =>
      obtain ⟨u, V, _, hV, rfl⟩ := ha earlier List.mem_cons_self
      let e := Edge.ofRun n v W
      let f := Edge.ofRun n u V
      have hbad : inBand (e.transport (f.transport ((n : Rat) + 1))) = false := by
        apply decide_eq_false
        intro h
        have hv1 := (two_zero_links hV (by omega : 0 < v) hW Rat.le_refl h.1).2.1
        omega
      change ([e.transport ((n : Rat) + 1), e.transport (f.transport ((n : Rat) + 1))].filter
        inBand).length ≤ 1
      simp [List.filter_cons, hbad]
      split <;> simp
  change ((([(n : Rat), (n : Rat) + 1] ++
    (forwardLocal n (Edge.ofRun n v W :: priorRev) ++ backwardLocal n after)).filter inBand).length) ≤ 5
  rw [List.filter_append, List.filter_append, List.length_append, List.length_append]
  have hends := List.length_filter_le (p := inBand) (l := [(n : Rat), (n : Rat) + 1])
  have htail := List.length_filter_le (p := inBand) (l := backwardLocal n after)
  simp only [List.length_cons, List.length_nil] at hends
  omega

/-- On an excursion word, the bounded local layer contains exactly the
same rational coordinates as the unrestricted anchor enumeration. -/
theorem localLayer_mem_iff {n : Nat} {before after : List Edge}
    (ha : ExcursionAlphabet n (before ++ after)) (p : Rat) :
    p ∈ localLayer n before.reverse after ↔
      p ∈ anchorCandidates n (before ++ after) before.length := by
  have htake : (before ++ after).take before.length = before := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _)]
  have hdrop : (before ++ after).drop before.length = after := by
    rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  rw [mem_anchorCandidates_iff, AnchoredAt, htake, hdrop]
  unfold localLayer
  rw [List.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    refine ⟨of_decide_eq_true hb, ?_⟩
    rcases List.mem_append.mp hm with hbase | hm
    · have hp : p = (n : Rat) ∨ p = (n : Rat) + 1 := by simpa using hbase
      exact Or.inl ⟨before, [], p, (List.append_nil _).symm, hp, rfl⟩
    · rcases List.mem_append.mp hm with hleft | hright
      · obtain ⟨pre, block, he, _, _, hp⟩ := (forwardLocal_iff _ _ _).mp hleft
        rw [List.reverse_reverse] at he
        exact Or.inl ⟨pre, block, (n : Rat) + 1, he, Or.inr rfl, hp⟩
      · obtain ⟨block, post, he, _, _, hp⟩ := (backwardLocal_iff _ _ _).mp hright
        exact Or.inr ⟨block, post, n, he, Or.inl rfl, hp⟩
  · rintro ⟨hband, hanchor⟩
    refine ⟨?_, decide_eq_true hband⟩
    rcases hanchor with ⟨pre, block, q, he, hq, hp⟩ | ⟨block, post, q, he, hq, hp⟩
    · have hblock : ExcursionAlphabet n block := by
        intro e h
        apply ha e (List.mem_append_left _ ?_)
        rw [he]
        exact List.mem_append_right _ h
      have hend : (n : Rat) ≤ endpoint block q := hp ▸ hband.1
      obtain ⟨hshort, hempty | hupper⟩ := forward_anchor_short hblock hq hend
      · have hbase : p = (n : Rat) ∨ p = (n : Rat) + 1 := by
          simpa [hempty, endpoint, hp] using hq
        exact List.mem_append_left _ (by simpa using hbase)
      · by_cases hempty : block = []
        · exact List.mem_append_left _ (by simp [hp, hempty, endpoint, hupper])
        · apply List.mem_append_right _
          apply List.mem_append_left _
          exact (forwardLocal_iff _ _ _).mpr
            ⟨pre, block, by simpa using he, hempty, hshort, by simpa [hupper] using hp⟩
    · have hblock : ExcursionAlphabet n block := by
        intro e h
        apply ha e (List.mem_append_right _ ?_)
        rw [he]
        exact List.mem_append_left _ h
      have hstart : (n : Rat) ≤ inverseEndpoint block q ∧ inverseEndpoint block q ≤ (n : Rat) + 1 :=
        hp ▸ hband
      obtain ⟨hshort, hempty | hlower⟩ := backward_anchor_short hblock hq hstart
      · have hbase : p = (n : Rat) ∨ p = (n : Rat) + 1 := by
          simpa [hempty, inverseEndpoint, hp] using hq
        exact List.mem_append_left _ (by simpa using hbase)
      · by_cases hempty : block = []
        · exact List.mem_append_left _ (by simp [hp, hempty, inverseEndpoint, hlower])
        · apply List.mem_append_right _
          apply List.mem_append_right _
          exact (backwardLocal_iff _ _ _).mpr
            ⟨block, post, he, hempty, hshort, by simpa [hlower] using hp⟩

private def localLayersFrom (n : Rat) (priorRev : List Edge) : List Edge → List (List Rat)
  | [] => [localLayer n priorRev []]
  | e :: rest => localLayer n priorRev (e :: rest) :: localLayersFrom n (e :: priorRev) rest

/-- One pass through the word constructs layers using only the two edges
on either side of each boundary. -/
def localLayers (n : Rat) (word : List Edge) : List (List Rat) :=
  localLayersFrom n [] word

private theorem localLayersFrom_length (n : Rat) (priorRev word : List Edge) :
    (localLayersFrom n priorRev word).length = word.length + 1 := by
  induction word generalizing priorRev with
  | nil => rfl
  | cons e rest ih => simp [localLayersFrom, ih]

theorem localLayers_length (n : Rat) (word : List Edge) :
    (localLayers n word).length = word.length + 1 :=
  localLayersFrom_length n [] word

private theorem localLayersFrom_get (n : Rat) (priorRev word : List Edge) (i : Nat)
    (hi : i ≤ word.length) :
    (localLayersFrom n priorRev word)[i]? =
      some (localLayer n ((word.take i).reverse ++ priorRev) (word.drop i)) := by
  induction word generalizing i priorRev with
  | nil =>
    have hz : i = 0 := by simpa using hi
    subst i
    rfl
  | cons e rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hle : i ≤ rest.length := by simp only [List.length_cons] at hi; omega
      rw [localLayersFrom, List.getElem?_cons_succ, ih (e :: priorRev) i hle,
        List.take_succ_cons, List.drop_succ_cons, List.reverse_cons, List.append_assoc]
      rfl

private inductive SameLayers : List (List Rat) → List (List Rat) → Prop where
  | nil : SameLayers [] []
  | cons {xs ys : List Rat} {left right : List (List Rat)} :
      (∀ p, p ∈ xs ↔ p ∈ ys) → SameLayers left right → SameLayers (xs :: left) (ys :: right)

private theorem SameLayers.of_lookup {left right : List (List Rat)}
    (hlen : left.length = right.length)
    (h : ∀ (i : Nat) (xs ys : List Rat), left[i]? = some xs → right[i]? = some ys →
      ∀ p, p ∈ xs ↔ p ∈ ys) : SameLayers left right := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp hlen.symm
    subst right
    exact .nil
  | cons xs left ih =>
    cases right with
    | nil => simp at hlen
    | cons ys right =>
      refine .cons (h 0 xs ys rfl rfl) (ih (by simpa using hlen) ?_)
      intro i a b ha hb
      exact h (i + 1) a b ha hb

private theorem localLayers_same {n : Nat} {word : List Edge} (ha : ExcursionAlphabet n word) :
    SameLayers (localLayers n word) (anchorLayers n word) := by
  apply SameLayers.of_lookup
  · simp [localLayers_length, anchorLayers]
  · intro i xs ys hx hy
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hx
    rw [localLayers_length] at hi
    have hle : i ≤ word.length := by omega
    have hlocal : (localLayers n word)[i]? =
        some (localLayer n (word.take i).reverse (word.drop i)) := by
      simpa [localLayers] using localLayersFrom_get n [] word i hle
    have horiginal : (anchorLayers n word)[i]? = some (anchorCandidates n word i) := by
      rw [anchorLayers, List.getElem?_map, List.getElem?_range hi]
      rfl
    rw [hlocal] at hx
    rw [horiginal] at hy
    cases hx
    cases hy
    intro p
    have ha' : ExcursionAlphabet n (word.take i ++ word.drop i) := by
      rwa [List.take_append_drop]
    have he := localLayer_mem_iff ha' p
    rwa [List.take_append_drop, List.length_take, Nat.min_eq_left hle] at he

private theorem min_eq_of_same_members {xs ys : List Rat} (h : ∀ p, p ∈ xs ↔ p ∈ ys) :
    xs.min? = ys.min? := by
  cases hx : xs.min? with
  | none =>
    have he : xs = [] := List.min?_eq_none_iff.mp hx
    symm
    apply List.min?_eq_none_iff.mpr
    cases ys with
    | nil => rfl
    | cons p rest =>
      have hp := (h p).mpr (List.mem_cons_self : p ∈ p :: rest)
      simp [he] at hp
  | some p =>
    obtain ⟨hp, hle⟩ := List.min?_eq_some_iff.mp hx
    symm
    exact List.min?_eq_some_iff.mpr ⟨(h p).mp hp, fun q hq => hle q ((h q).mpr hq)⟩

private theorem map_same_members {α β : Type} {xs ys : List α} (f : α → β)
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) (b : β) : b ∈ xs.map f ↔ b ∈ ys.map f := by
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map_of_mem ((h a).mp ha)
  · intro hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map_of_mem ((h a).mpr ha)

private theorem table_same_members (word : List Edge) {left right : List (List Rat)}
    (h : SameLayers left right) (entry : Rat × Rat) :
    entry ∈ productTable word left ↔ entry ∈ productTable word right := by
  induction word generalizing left right entry with
  | nil =>
    cases h with
    | nil => rfl
    | cons same tail =>
      cases tail with
      | nil => exact map_same_members (fun p => (p, (1 : Rat))) same entry
      | cons _ _ => rfl
  | cons e rest ih =>
    cases h with
    | nil => rfl
    | @cons xs ys ls rs same tail =>
      have hmin (p : Rat) :
          ((productTable rest ls).map (fun z => e.factor p z.1 * z.2)).min? =
            ((productTable rest rs).map (fun z => e.factor p z.1 * z.2)).min? :=
        min_eq_of_same_members
          (map_same_members (fun z => e.factor p z.1 * z.2) (ih tail))
      simp only [productTable, List.mem_filterMap]
      constructor
      · rintro ⟨p, hp, he⟩
        exact ⟨p, (same p).mp hp, by rwa [hmin p] at he⟩
      · rintro ⟨p, hp, he⟩
        exact ⟨p, (same p).mpr hp, by rwa [hmin p]⟩

/-- The exact minimum, computed with at most six states per boundary. -/
def localMinimum (n : Nat) (word : List Edge) : Option Rat :=
  ((productTable word (localLayers n word)).map Prod.snd).min?

/-- The six-state computation preserves the exact rational optimum. -/
theorem localMinimum_eq_anchorMinimum {n : Nat} {word : List Edge}
    (ha : ExcursionAlphabet n word) : localMinimum n word = anchorMinimum n word :=
  min_eq_of_same_members (map_same_members Prod.snd (table_same_members word (localLayers_same ha)))

theorem OrbitWord.drop_of_localMinimum {n endpoint elapsed A B word result}
    (h : OrbitWord n n word endpoint elapsed A B) (hn : 0 < n)
    (hbest : localMinimum n word = some result) (hcross : (A : Rat) * result < (B : Rat)) :
    ∃ k, k ≤ elapsed ∧ Collatz.acceleratedOrbit k n < n := by
  rw [localMinimum_eq_anchorMinimum h.alphabet] at hbest
  exact h.drop_of_anchorMinimum hn hbest hcross

private def shortWord127 : List Edge :=
  [Edge.ofRun 127 7 1, Edge.ofRun 127 1 3, Edge.ofRun 127 1 2]

/-- The short search computes the same exact value for 127 using only
the neighboring two excursions at each boundary. -/
theorem local_minimum_127 : localMinimum 127 shortWord127 = some (1343488 / 1331883) := by
  decide +kernel

end Collatz.ExcursionAnchor
