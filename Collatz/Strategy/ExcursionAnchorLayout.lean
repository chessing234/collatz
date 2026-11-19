import Collatz.Strategy.ExcursionAnchor

/-!
# Anchoring every component of an excursion word

A layout partitions a shift schedule into blocks linked internally by
zero offsets. An unanchored block can be moved to a band endpoint or
joined to a neighbor. The number of unanchored blocks strictly decreases
after a move or join, which yields a finite improvement process.
-/

namespace Collatz.ExcursionAnchor

/-- A zero-offset component is determined by its first coordinate. -/
structure Component where
  first : Rat
  inside : List Edge

def Component.last (c : Component) : Rat := endpoint c.inside c.first

def Component.band (c : Component) (n : Rat) : Prop :=
  ∀ p ∈ points c.inside c.first, n ≤ p ∧ p ≤ n + 1

def Component.anchored (c : Component) (n : Rat) : Prop :=
  ∃ p ∈ points c.inside c.first, p = n ∨ p = n + 1

noncomputable def Component.free (c : Component) (n : Rat) : Nat := by
  classical
  exact if c.anchored n then 0 else 1

private theorem Component.first_mem (c : Component) : c.first ∈ points c.inside c.first := by
  cases c.inside <;> simp [points]

private theorem Component.last_mem (c : Component) : c.last ∈ points c.inside c.first := by
  have h (word : List Edge) (p : Rat) : endpoint word p ∈ points word p := by
    induction word generalizing p with
    | nil => simp [endpoint, points]
    | cons e rest ih => exact List.mem_cons_of_mem _ (ih (e.transport p))
  exact h c.inside c.first

private theorem Component.first_pos {c : Component} {n : Rat} (hn : 0 < n) (h : c.band n) :
    0 < c.first := by
  have hp := (h _ c.first_mem).1
  grind

private theorem Component.last_pos {c : Component} {n : Rat} (hn : 0 < n) (h : c.band n) :
    0 < c.last := by
  have hp := (h _ c.last_mem).1
  grind

def Component.value (c : Component) : Rat := insideFactor c.inside c.first

private theorem Component.value_pos {c : Component} {n : Rat} (hn : 0 < n) (h : c.band n) :
    0 < c.value := by
  let block : Block := ⟨none, c.inside, none⟩
  have hb : block.inBand n c.first := (block.inBand_iff_points n c.first).mpr h
  have hp := block.allowed_of_band hn hb trivial trivial
  unfold Component.value
  rw [insideFactor_ratio hp.1, Rat.div_def]
  exact Rat.mul_pos (c.first_pos hn h) (Rat.inv_pos.mpr (c.last_pos hn h))

private def Component.join (left : Component) (e : Edge) (right : Component) : Component :=
  ⟨left.first, left.inside ++ e :: right.inside⟩

private def Joinable (left : Component) (e : Edge) (right : Component) : Prop :=
  e.b * right.first = e.a * left.last + e.drift

private theorem Component.join_points {left right : Component} {e : Edge}
    (h : Joinable left e right) :
    points (left.join e right).inside (left.join e right).first =
      points left.inside left.first ++ points right.inside right.first := by
  simp only [Component.join, points_join]
  rw [show e.transport (endpoint left.inside left.first) = right.first from
    e.transport_eq_of_zero h]

private theorem Component.join_last {left right : Component} {e : Edge}
    (h : Joinable left e right) : (left.join e right).last = right.last := by
  simp only [Component.last, Component.join, endpoint_append, endpoint]
  rw [show e.transport (endpoint left.inside left.first) = right.first from
    e.transport_eq_of_zero h]

private theorem Component.join_value {left right : Component} {e : Edge}
    (h : Joinable left e right) :
    (left.join e right).value = left.value * e.factor left.last right.first * right.value := by
  simp only [Component.value, Component.join, insideFactor_join]
  rw [show e.transport (endpoint left.inside left.first) = right.first from
    e.transport_eq_of_zero h]
  rfl

private theorem Component.join_band {left right : Component} {e : Edge} {n : Rat}
    (hz : Joinable left e right) (hl : left.band n) (hr : right.band n) :
    (left.join e right).band n := by
  unfold Component.band
  rw [Component.join_points hz]
  intro p h
  rcases List.mem_append.mp h with h | h
  · exact hl p h
  · exact hr p h

private theorem Component.join_anchored_left {left right : Component} {e : Edge} {n : Rat}
    (hz : Joinable left e right) (h : left.anchored n) :
    (left.join e right).anchored n := by
  obtain ⟨p, hp, ha⟩ := h
  refine ⟨p, ?_, ha⟩
  rw [Component.join_points hz]
  exact List.mem_append_left _ hp

private theorem Component.join_anchored_right {left right : Component} {e : Edge} {n : Rat}
    (hz : Joinable left e right) (h : right.anchored n) :
    (left.join e right).anchored n := by
  obtain ⟨p, hp, ha⟩ := h
  refine ⟨p, ?_, ha⟩
  rw [Component.join_points hz]
  exact List.mem_append_right _ hp

private theorem Component.free_eq_zero {c : Component} {n : Rat} (h : c.anchored n) :
    c.free n = 0 := by
  classical
  simp [Component.free, h]

private theorem Component.free_eq_one {c : Component} {n : Rat} (h : ¬ c.anchored n) :
    c.free n = 1 := by
  classical
  simp [Component.free, h]

private theorem Component.join_free_le_right {left right : Component} {e : Edge} {n : Rat}
    (hz : Joinable left e right) : (left.join e right).free n ≤ right.free n := by
  classical
  by_cases h : right.anchored n
  · rw [Component.free_eq_zero h, Component.free_eq_zero (Component.join_anchored_right hz h)]
    exact Nat.le_refl _
  · rw [Component.free_eq_one h]
    unfold Component.free
    split <;> decide

/-- A nonempty schedule of components with one intervening edge between
consecutive components. Intervening edges may already have zero offset. -/
inductive Layout where
  | last (head : Component)
  | more (head : Component) (separator : Edge) (tail : Layout)

def Layout.head : Layout → Component
  | .last c | .more c _ _ => c

def Layout.word : Layout → List Edge
  | .last c => c.inside
  | .more c e rest => c.inside ++ e :: rest.word

def Layout.band : Layout → Rat → Prop
  | .last c, n => c.band n
  | .more c _ rest, n => c.band n ∧ rest.band n

noncomputable def Layout.free : Layout → Rat → Nat
  | .last c, n => c.free n
  | .more c _ rest, n => c.free n + rest.free n

private noncomputable def Layout.tailFree : Layout → Rat → Nat
  | .last _, _ => 0
  | .more _ _ rest, n => rest.free n

def Layout.value : Layout → Rat
  | .last c => c.value
  | .more c e rest => c.value * e.factor c.last rest.head.first * rest.value

private def Layout.tailValue : Layout → Rat
  | .last _ => 1
  | .more _ _ rest => rest.value

private theorem Layout.head_band {p : Layout} {n : Rat} (h : p.band n) : p.head.band n := by
  cases p with
  | last _ => exact h
  | more _ _ _ => exact h.1

private theorem Layout.value_pos {p : Layout} {n : Rat} (hn : 0 < n) (h : p.band n) :
    0 < p.value := by
  induction p with
  | last c => exact c.value_pos hn h
  | more c e rest ih =>
    exact Rat.mul_pos
      (Rat.mul_pos (c.value_pos hn h.1)
        (e.factor_pos (c.last_pos hn h.1) (rest.head.first_pos hn (Layout.head_band h.2))))
      (ih h.2)

private theorem Layout.tailValue_nonneg {p : Layout} {n : Rat} (hn : 0 < n) (h : p.band n) :
    0 ≤ p.tailValue := by
  cases p with
  | last _ => exact (by decide : (0 : Rat) ≤ 1)
  | more _ _ rest => exact Rat.le_of_lt (rest.value_pos hn h.2)

private def Layout.replaceHead (p : Layout) (c : Component) : Layout :=
  match p with
  | .last _ => .last c
  | .more _ e rest => .more c e rest

private def Layout.joinFirst (left : Component) (e : Edge) (rest : Layout) : Layout :=
  rest.replaceHead (left.join e rest.head)

private theorem Layout.joinFirst_first (left : Component) (e : Edge) (rest : Layout) :
    (joinFirst left e rest).head.first = left.first := by
  cases rest <;> rfl

private theorem Layout.joinFirst_word (left : Component) (e : Edge) (rest : Layout) :
    (joinFirst left e rest).word = left.inside ++ e :: rest.word := by
  cases rest <;> simp [joinFirst, replaceHead, word, Component.join, head, List.append_assoc]

private theorem Layout.joinFirst_band {left : Component} {e : Edge} {rest : Layout} {n : Rat}
    (hz : Joinable left e rest.head) (hl : left.band n) (hr : rest.band n) :
    (joinFirst left e rest).band n := by
  cases rest with
  | last _ => exact Component.join_band hz hl hr
  | more _ _ _ => exact ⟨Component.join_band hz hl hr.1, hr.2⟩

private theorem Layout.joinFirst_value {left : Component} {e : Edge} {rest : Layout}
    (hz : Joinable left e rest.head) :
    (joinFirst left e rest).value = left.value * e.factor left.last rest.head.first * rest.value := by
  cases rest with
  | last _ => exact Component.join_value hz
  | more c f tail =>
    have hv := Component.join_value hz
    have he := Component.join_last hz
    simp only [joinFirst, replaceHead, value, head] at *
    rw [hv, he]
    grind

private theorem Layout.joinFirst_free_le {left : Component} {e : Edge} {rest : Layout} {n : Rat}
    (hz : Joinable left e rest.head) : (joinFirst left e rest).free n ≤ rest.free n := by
  cases rest with
  | last _ => exact Component.join_free_le_right hz
  | more _ _ _ => exact Nat.add_le_add_right (Component.join_free_le_right hz) _

private theorem Layout.joinFirst_free_eq {left : Component} {e : Edge} {rest : Layout} {n : Rat}
    (hz : Joinable left e rest.head) (ha : left.anchored n) :
    (joinFirst left e rest).free n = rest.tailFree n := by
  cases rest with
  | last _ => exact Component.free_eq_zero (Component.join_anchored_left hz ha)
  | more _ _ _ =>
    simp only [joinFirst, replaceHead, free, tailFree]
    rw [Component.free_eq_zero (Component.join_anchored_left hz ha), Nat.zero_add]

private theorem Edge.chosen_regime (e : Edge) (p q : Rat) :
    e.inRegime (decide (e.b * q ≤ e.a * p + e.drift)) p q := by
  by_cases h : e.b * q ≤ e.a * p + e.drift
  · simp [Edge.inRegime, h]
  · simp only [Edge.inRegime, decide_eq_false h, Bool.false_eq_true, if_false]
    exact Rat.le_of_lt ((Rat.not_le).mp h)

private def Layout.outbound (path : Layout) {n : Rat} (hn : 0 < n) (hb : path.band n) :
    Option Boundary :=
  match path with
  | .last _ => none
  | .more c e tail =>
      some ⟨e, tail.head.first, tail.head.first_pos hn (Layout.head_band hb.2),
        decide (e.b * tail.head.first ≤ e.a * c.last + e.drift)⟩

private theorem Layout.outbound_allowed (p : Layout) {n : Rat} (hn : 0 < n) (hb : p.band n) :
    rightAllowed (p.outbound hn hb) p.head.last := by
  cases p with
  | last _ => trivial
  | more c e tail => exact e.chosen_regime c.last tail.head.first

private def Layout.block (path : Layout) (ctx : Option Boundary) {n : Rat}
    (hn : 0 < n) (hb : path.band n) : Block :=
  ⟨ctx, path.head.inside, path.outbound hn hb⟩

private def Layout.withFirst (path : Layout) (p : Rat) : Layout :=
  path.replaceHead ⟨p, path.head.inside⟩

private theorem Layout.withFirst_head (path : Layout) (p : Rat) :
    (path.withFirst p).head = ⟨p, path.head.inside⟩ := by
  cases path <;> rfl

private theorem Layout.withFirst_self (path : Layout) : path.withFirst path.head.first = path := by
  cases path <;> rfl

private theorem Layout.withFirst_word (path : Layout) (p : Rat) :
    (path.withFirst p).word = path.word := by
  cases path <;> rfl

private theorem Layout.withFirst_tailFree (path : Layout) (p n : Rat) :
    (path.withFirst p).tailFree n = path.tailFree n := by
  cases path <;> rfl

private theorem Layout.free_split (path : Layout) (n : Rat) :
    path.free n = path.head.free n + path.tailFree n := by
  cases path <;> simp [free, head, tailFree]

private theorem Layout.withFirst_band {path : Layout} {p n : Rat} (h : path.band n)
    (hhead : (⟨p, path.head.inside⟩ : Component).band n) : (path.withFirst p).band n := by
  cases path with
  | last _ => exact hhead
  | more _ _ _ => exact ⟨hhead, h.2⟩

private def Layout.costWith (path : Layout) (ctx : Option Boundary) : Rat :=
  leftFactor ctx path.head.first * path.value

private theorem Layout.block_factorization (path : Layout) (ctx : Option Boundary) {n : Rat}
    (hn : 0 < n) (hband : path.band n) (p : Rat) :
    (path.block ctx hn hband).value p * path.tailValue = (path.withFirst p).costWith ctx := by
  cases path with
  | last c =>
    simp [Layout.block, Layout.outbound, Block.value, Layout.tailValue, Layout.withFirst,
      Layout.replaceHead, Layout.head, Layout.costWith, Layout.value, Component.value,
      rightFactor, Rat.mul_one]
  | more c e rest =>
    simp only [Layout.block, Layout.outbound, Block.value, Layout.tailValue, Layout.withFirst,
      Layout.replaceHead, Layout.head, Layout.costWith, Layout.value, Component.value,
      rightFactor, Component.last]
    grind

private structure Improvement (n : Rat) (ctx : Option Boundary) (old new : Layout) : Prop where
  same_word : new.word = old.word
  band : new.band n
  incoming : leftAllowed ctx new.head.first
  cheaper : new.costWith ctx ≤ old.costWith ctx
  progress : new.free n < old.free n ∨
    ∃ b, ctx = some b ∧ b.edge.b * new.head.first = b.edge.a * b.exterior + b.edge.drift ∧
      new.tailFree n < old.free n

private theorem Layout.improve_head (path : Layout) {n : Rat} (hn : 0 < n)
    (ctx : Option Boundary) (hband : path.band n) (hctx : leftAllowed ctx path.head.first)
    (hfree : ¬ path.head.anchored n) :
    ∃ improved, Improvement n ctx path improved := by
  let block := path.block ctx hn hband
  have hbb : block.inBand n path.head.first :=
    (block.inBand_iff_points n path.head.first).mpr (Layout.head_band hband)
  have hvalid : block.allowed path.head.first :=
    block.allowed_of_band hn hbb hctx (path.outbound_allowed hn hband)
  obtain ⟨q, hqb, hqv, hqle, hqt⟩ := block.anchor_or_join hn hbb hvalid
  let changed := path.withFirst q
  have hchanged : changed.band n := path.withFirst_band hband
    ((block.inBand_iff_points n q).mp hqb)
  have hallowed : leftAllowed ctx changed.head.first := by
    rw [show changed.head.first = q from congrArg Component.first (path.withFirst_head q)]
    exact hqv.2.1
  have hcost : changed.costWith ctx ≤ path.costWith ctx := calc
    _ = block.value q * path.tailValue := (path.block_factorization ctx hn hband q).symm
    _ ≤ block.value path.head.first * path.tailValue :=
      Rat.mul_le_mul_of_nonneg_right hqle (Layout.tailValue_nonneg hn hband)
    _ = _ := by
      rw [show block.value path.head.first * path.tailValue =
        (path.withFirst path.head.first).costWith ctx from path.block_factorization ctx hn hband _,
        path.withFirst_self]
  have hcount : path.free n = 1 + path.tailFree n := by
    rw [path.free_split, Component.free_eq_one hfree]
  rcases (block.touches_iff_points n q).mp hqt with ha | ⟨b, hb, hz⟩ | ⟨b, hb, hz⟩
  · have ha' : changed.head.anchored n := by
      rw [path.withFirst_head]
      exact ha
    refine ⟨changed, path.withFirst_word q, hchanged, hallowed, hcost, Or.inl ?_⟩
    rw [changed.free_split, Component.free_eq_zero ha', path.withFirst_tailFree, hcount]
    omega
  · refine ⟨changed, path.withFirst_word q, hchanged, hallowed, hcost,
      Or.inr ⟨b, hb, ?_, ?_⟩⟩
    · rw [path.withFirst_head]
      exact hz
    · rw [path.withFirst_tailFree, hcount]
      omega
  · cases path with
    | last c => simp [block, Layout.block, Layout.outbound] at hb
    | more c e rest =>
      have hb' : b =
          ⟨e, rest.head.first, rest.head.first_pos hn (Layout.head_band hband.2),
            decide (e.b * rest.head.first ≤ e.a * c.last + e.drift)⟩ := by
        exact (Option.some.inj hb).symm
      subst b
      let c' : Component := ⟨q, c.inside⟩
      have hjoin : Joinable c' e rest.head := hz
      let joined := Layout.joinFirst c' e rest
      have hw : joined.word = (Layout.more c e rest).word :=
        Layout.joinFirst_word c' e rest
      have hnew : joined.band n := Layout.joinFirst_band hjoin hchanged.1 hband.2
      have hfirst : joined.head.first = q := Layout.joinFirst_first c' e rest
      have heq : joined.costWith ctx = changed.costWith ctx := by
        unfold Layout.costWith
        rw [hfirst, Layout.joinFirst_value hjoin]
        rfl
      refine ⟨joined, hw, hnew, ?_, Rat.le_trans (by rw [heq]; exact Rat.le_refl) hcost,
        Or.inl ?_⟩
      · rw [hfirst]
        exact hqv.2.1
      · have hc := Layout.joinFirst_free_le (n := n) hjoin
        change joined.free n < (Layout.more c e rest).free n
        rw [hcount]
        exact Nat.lt_of_le_of_lt hc (by simp [Layout.tailFree])

private theorem Layout.improve (path : Layout) {n : Rat} (hn : 0 < n)
    (ctx : Option Boundary) (hband : path.band n) (hctx : leftAllowed ctx path.head.first)
    (hfree : 0 < path.free n) :
    ∃ improved, Improvement n ctx path improved := by
  induction path generalizing ctx with
  | last c =>
    apply Layout.improve_head (.last c) hn ctx hband hctx
    intro ha
    have hc : c.free n = 0 := Component.free_eq_zero ha
    change 0 < c.free n at hfree
    omega
  | more c e rest ih =>
    by_cases ha : c.anchored n
    · let incoming : Boundary := ⟨e, c.last, c.last_pos hn hband.1,
        decide (e.b * rest.head.first ≤ e.a * c.last + e.drift)⟩
      have hreg : leftAllowed (some incoming) rest.head.first := e.chosen_regime c.last _
      have hc := Component.free_eq_zero ha
      have hrest : 0 < rest.free n := by
        change 0 < c.free n + rest.free n at hfree
        omega
      obtain ⟨r, hr⟩ := ih (some incoming) hband.2 hreg hrest
      have hscale : 0 ≤ leftFactor ctx c.first * c.value := by
        apply Rat.mul_nonneg _ (Rat.le_of_lt (c.value_pos hn hband.1))
        cases ctx with
        | none => exact (by decide : (0 : Rat) ≤ 1)
        | some b => exact Rat.le_of_lt (b.edge.factor_pos b.positive (c.first_pos hn hband.1))
      have hfactor (tail : Layout) :
          (Layout.more c e tail).costWith ctx =
            (leftFactor ctx c.first * c.value) * tail.costWith (some incoming) := by
        simp only [Layout.costWith, Layout.head, Layout.value, leftFactor, incoming]
        grind
      have hcost : (Layout.more c e r).costWith ctx ≤ (Layout.more c e rest).costWith ctx := by
        rw [hfactor r, hfactor rest]
        exact Rat.mul_le_mul_of_nonneg_left hr.cheaper hscale
      rcases hr.progress with hdec | ⟨b, hb, hz, htail⟩
      · refine ⟨.more c e r, ?_, ⟨hband.1, hr.band⟩, hctx, hcost, Or.inl ?_⟩
        · simp [Layout.word, hr.same_word]
        · change c.free n + r.free n < c.free n + rest.free n
          omega
      · have hb' : incoming = b := Option.some.inj hb
        subst b
        have hjoin : Joinable c e r.head := hz
        let joined := Layout.joinFirst c e r
        have heq : joined.costWith ctx = (Layout.more c e r).costWith ctx := by
          unfold Layout.costWith
          rw [Layout.joinFirst_first, Layout.joinFirst_value hjoin]
          rfl
        refine ⟨joined, ?_, Layout.joinFirst_band hjoin hband.1 hr.band,
          ?_, by rw [heq]; exact hcost, Or.inl ?_⟩
        · rw [Layout.joinFirst_word, hr.same_word]
          rfl
        · rw [Layout.joinFirst_first]
          exact hctx
        · rw [Layout.joinFirst_free_eq hjoin ha]
          change r.tailFree n < c.free n + rest.free n
          omega
    · exact Layout.improve_head (.more c e rest) hn ctx hband hctx ha

/-- Every finite shift layout can be improved to one whose zero-offset
components all have an anchor at a band endpoint. The word is preserved. -/
theorem Layout.anchor_all (path : Layout) {n : Rat} (hn : 0 < n) (hband : path.band n) :
    ∃ anchored : Layout, anchored.word = path.word ∧ anchored.band n ∧ anchored.free n = 0 ∧
      anchored.value ≤ path.value := by
  generalize hm : path.free n = m
  induction m using Nat.strongRecOn generalizing path with
  | _ m ih =>
    by_cases hz : m = 0
    · exact ⟨path, rfl, hband, hm.trans hz, Rat.le_refl⟩
    · obtain ⟨next, hnext⟩ := path.improve hn none hband trivial (by omega)
      rcases hnext.progress with hdec | ⟨b, hb, _⟩
      · obtain ⟨result, hw, hb, hf, hv⟩ := ih (next.free n) (by omega) next hnext.band rfl
        have hc : next.value ≤ path.value := by
          simpa [Layout.costWith, leftFactor, Rat.one_mul] using hnext.cheaper
        exact ⟨result, hw.trans hnext.same_word, hb, hf, Rat.le_trans hv hc⟩
      · cases hb

private theorem points_length (word : List Edge) (p : Rat) :
    (points word p).length = word.length + 1 := by
  induction word generalizing p with
  | nil => rfl
  | cons e rest ih => simp [points, ih]

private theorem points_at (word : List Edge) (p : Rat) (i : Nat)
    (hi : i < (points word p).length) :
    (points word p)[i] = endpoint (word.take i) p := by
  induction word generalizing p i with
  | nil =>
    have hzero : i = 0 := by simpa [points] using hi
    subst i
    rfl
  | cons e rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hIndex : i + 1 < (p :: points rest (e.transport p)).length := hi
      change (p :: points rest (e.transport p))[i + 1]'hIndex =
        endpoint ((e :: rest).take (i + 1)) p
      rw [List.getElem_cons_succ, List.take_succ_cons, endpoint]
      exact ih (e.transport p) i _

private theorem take_split (word : List Edge) {i j : Nat} (h : i ≤ j) :
    word.take j = word.take i ++ (word.take j).drop i := by
  have hh := List.take_append_drop i (word.take j)
  rw [List.take_take, Nat.min_eq_left h] at hh
  exact hh.symm

private theorem drop_split (word : List Edge) {i j : Nat} (h : i ≤ j) (hj : j ≤ word.length) :
    word.drop i = (word.take j).drop i ++ word.drop j := by
  have hh := congrArg (List.drop i) (List.take_append_drop j word)
  rw [List.drop_append, List.length_take, Nat.min_eq_left hj, Nat.sub_eq_zero_of_le h,
    List.drop_zero] at hh
  exact hh.symm

private theorem Component.anchor_at {c : Component} {n : Rat} (ha : c.anchored n)
    (i : Nat) (hi : i < (points c.inside c.first).length) :
    AnchoredAt n c.inside i (points c.inside c.first)[i] := by
  obtain ⟨q, hq, hqa⟩ := ha
  obtain ⟨j, hj, hqj⟩ := List.getElem_of_mem hq
  have hjle : j ≤ c.inside.length := by rw [points_length] at hj; omega
  by_cases hji : j ≤ i
  · have hsplit := take_split c.inside hji
    refine Or.inl ⟨c.inside.take j, (c.inside.take i).drop j, q, hsplit, hqa, ?_⟩
    calc
      _ = endpoint (c.inside.take i) c.first := points_at c.inside c.first i hi
      _ = endpoint ((c.inside.take i).drop j) (endpoint (c.inside.take j) c.first) := by
        conv => lhs; rw [hsplit]
        rw [endpoint_append]
      _ = _ := by rw [← points_at c.inside c.first j hj, hqj]
  · have hij : i ≤ j := by omega
    let block := (c.inside.take j).drop i
    refine Or.inr ⟨block, c.inside.drop j, q, drop_split c.inside hij hjle, hqa, ?_⟩
    have hq' : q = endpoint block (points c.inside c.first)[i] := by
      calc
        q = (points c.inside c.first)[j] := hqj.symm
        _ = endpoint (c.inside.take j) c.first := points_at c.inside c.first j hj
        _ = endpoint block (endpoint (c.inside.take i) c.first) := by
          conv => lhs; rw [take_split c.inside hij]
          rw [endpoint_append]
        _ = _ := by rw [points_at c.inside c.first i hi]
    rw [hq', inverseEndpoint_endpoint]

private theorem AnchoredAt.pad {n p : Rat} {word : List Edge} {i : Nat}
    (h : AnchoredAt n word i p) (hi : i ≤ word.length) (prelude suffix : List Edge) :
    AnchoredAt n (prelude ++ word ++ suffix) (prelude.length + i) p := by
  have hle : prelude.length ≤ prelude.length + i := by omega
  have hsub : prelude.length + i - prelude.length = i := by omega
  rcases h with ⟨pre, block, q, hpre, hq, hp⟩ | ⟨block, post, q, hpost, hq, hp⟩
  · refine Or.inl ⟨prelude ++ pre, block, q, ?_, hq, hp⟩
    rw [List.append_assoc, List.take_append, List.take_of_length_le hle, hsub,
      List.take_append_of_le_length hi, hpre, List.append_assoc]
  · refine Or.inr ⟨block, post ++ suffix, q, ?_, hq, hp⟩
    rw [List.append_assoc, List.drop_append, List.drop_of_length_le hle, hsub,
      List.nil_append, List.drop_append_of_le_length hi, hpost, List.append_assoc]

/-- Coordinates from each component in word order. -/
def Layout.coords : Layout → List Rat
  | .last c => points c.inside c.first
  | .more c _ tail => points c.inside c.first ++ tail.coords

theorem Layout.coords_length (layout : Layout) : layout.coords.length = layout.word.length + 1 := by
  induction layout with
  | last _ => exact points_length ..
  | more _ _ _ ih =>
    simp only [coords, word, List.length_append, List.length_cons, points_length, ih]
    omega

private theorem Layout.coords_band {layout : Layout} {n : Rat} (h : layout.band n) :
    ∀ p ∈ layout.coords, n ≤ p ∧ p ≤ n + 1 := by
  induction layout with
  | last c => exact h
  | more c e rest ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.1 p hp
    · exact ih h.2 p hp

private theorem Component.anchored_of_free_zero {c : Component} {n : Rat} (h : c.free n = 0) :
    c.anchored n := by
  apply Classical.byContradiction
  intro hfree
  have he := Component.free_eq_one hfree
  omega

private theorem Layout.anchoredAt_of_free_zero {layout : Layout} {n : Rat} (h : layout.free n = 0)
    (i : Nat) (hi : i < layout.coords.length) :
    AnchoredAt n layout.word i layout.coords[i] := by
  induction layout generalizing i with
  | last c =>
    exact c.anchor_at (Component.anchored_of_free_zero h) i hi
  | more c e rest ih =>
    have hf : c.free n + rest.free n = 0 := h
    have hc : c.anchored n := Component.anchored_of_free_zero (by omega)
    have hIndex : i < (points c.inside c.first ++ rest.coords).length := hi
    change AnchoredAt n (c.inside ++ e :: rest.word) i
      ((points c.inside c.first ++ rest.coords)[i]'hIndex)
    by_cases hleft : i < (points c.inside c.first).length
    · rw [List.getElem_append_left hleft]
      have hile : i ≤ c.inside.length := by rw [points_length] at hleft; omega
      simpa using (c.anchor_at hc i hleft).pad hile [] (e :: rest.word)
    · have hindex : (points c.inside c.first).length ≤ i := by omega
      rw [List.getElem_append_right hindex]
      let j := i - (points c.inside c.first).length
      have hj : j < rest.coords.length := by
        have hi' : i < (points c.inside c.first ++ rest.coords).length := hi
        rw [List.length_append] at hi'
        dsimp [j]
        omega
      have hjle : j ≤ rest.word.length := by rw [rest.coords_length] at hj; omega
      have hright := (ih (by omega) j hj).pad hjle (c.inside ++ [e]) []
      have heq : (c.inside ++ [e]).length + j = i := by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        rw [← points_length c.inside c.first]
        dsimp [j]
        omega
      rw [heq] at hright
      simpa [List.append_assoc, j] using hright

/-- Every rational shift layout has a weakly better layout supported on the
finite anchor candidates at all its boundaries. -/
theorem Layout.finite_anchors (layout : Layout) {n : Rat} (hn : 0 < n)
    (hband : layout.band n) :
    ∃ better : Layout, better.word = layout.word ∧ better.value ≤ layout.value ∧
      ∀ i (hi : i < better.coords.length), better.coords[i] ∈ anchorCandidates n layout.word i := by
  obtain ⟨better, hword, hb, hfree, hvalue⟩ := layout.anchor_all hn hband
  refine ⟨better, hword, hvalue, ?_⟩
  intro i hi
  rw [← hword, mem_anchorCandidates_iff]
  exact ⟨Layout.coords_band hb _ (List.getElem_mem hi),
    Layout.anchoredAt_of_free_zero hfree i hi⟩

/-- Interpret a raw rational shift schedule as singleton components. -/
def Layout.ofSchedule : Rat → List (Edge × Rat) → Layout
  | p, [] => .last ⟨p, []⟩
  | p, (e, q) :: rest => .more ⟨p, []⟩ e (ofSchedule q rest)

theorem Layout.ofSchedule_word (p : Rat) (steps : List (Edge × Rat)) :
    (ofSchedule p steps).word = steps.map Prod.fst := by
  induction steps generalizing p with
  | nil => rfl
  | cons step steps ih => cases step; simp [ofSchedule, word, ih]

theorem Layout.ofSchedule_coords (p : Rat) (steps : List (Edge × Rat)) :
    (ofSchedule p steps).coords = p :: steps.map Prod.snd := by
  induction steps generalizing p with
  | nil => rfl
  | cons step steps ih => cases step; simp [ofSchedule, coords, points, ih]

/-- Multiply the normalized factors of a word along its coordinates. -/
def costOn : List Edge → List Rat → Rat
  | e :: rest, p :: q :: coordinates => e.factor p q * costOn rest (q :: coordinates)
  | _, _ => 1

private theorem points_first (word : List Edge) (p : Rat) :
    ∃ tail, points word p = p :: tail := by
  cases word with
  | nil => exact ⟨[], rfl⟩
  | cons e rest => exact ⟨points rest (e.transport p), rfl⟩

private theorem costOn_inside (word : List Edge) (p : Rat) :
    costOn word (points word p) = insideFactor word p := by
  induction word generalizing p with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨tail, h⟩ := points_first rest (e.transport p)
    rw [points, h, costOn, ← h, ih, insideFactor]

private theorem costOn_join (left right : List Edge) (e : Edge) (p q : Rat) (tail : List Rat) :
    costOn (left ++ e :: right) (points left p ++ q :: tail) =
      insideFactor left p * e.factor (endpoint left p) q * costOn right (q :: tail) := by
  induction left generalizing p with
  | nil => simp [costOn, points, insideFactor, endpoint, Rat.one_mul]
  | cons a rest ih =>
    obtain ⟨inner, h⟩ := points_first rest (a.transport p)
    simp only [List.cons_append, points]
    rw [h]
    simp only [List.cons_append, costOn]
    rw [← List.cons_append, ← h, ih]
    simp only [insideFactor, endpoint]
    grind

private theorem Layout.coords_first (layout : Layout) :
    ∃ tail, layout.coords = layout.head.first :: tail := by
  cases layout with
  | last c => exact points_first c.inside c.first
  | more c _ rest =>
    obtain ⟨tail, h⟩ := points_first c.inside c.first
    exact ⟨tail ++ rest.coords, by simp [coords, head, h]⟩

theorem Layout.costOn_eq (layout : Layout) :
    costOn layout.word layout.coords = layout.value := by
  induction layout with
  | last c => exact costOn_inside c.inside c.first
  | more c e rest ih =>
    obtain ⟨tail, he⟩ := rest.coords_first
    simp only [word, coords, value]
    rw [he, costOn_join, ← he, ih]
    rfl

end Collatz.ExcursionAnchor
