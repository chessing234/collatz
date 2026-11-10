import Collatz.Strategy.ExcursionRays

/-!
# Weighted counting for bounded excursion alphabets

For a fixed word of excursions, its realizing odd sources occupy one dyadic
residue class. Below `2^(T+1)`, a word with duration `S ≤ T` therefore has at most
`2^(T-S)` sources. Summing these weights over words of length `k` gives an
exact factorized upper bound on the number of distinct eligible sources.
-/

namespace Collatz.ExcursionAlphabetMass

open Collatz.ExcursionBudget Collatz.ExcursionRays

def cost (r : Run) : Nat := r.oddSteps + r.halvings

def words (alphabet : List Run) : Nat → List (List Run)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap (fun r => (words alphabet k).map (r :: ·))

theorem mem_words {alphabet : List Run} {rs : List Run}
    (hall : ∀ r ∈ rs, r ∈ alphabet) : rs ∈ words alphabet rs.length := by
  induction rs with
  | nil => simp [words]
  | cons r rs ih =>
    apply List.mem_flatMap.mpr
    exact ⟨r, hall r List.mem_cons_self, List.mem_map_of_mem
      (ih (fun s hs => hall s (List.mem_cons_of_mem _ hs)))⟩

def alphabetWeight (alphabet : List Run) (L : Nat) : Nat :=
  (alphabet.map (fun r => 2 ^ (L - cost r))).sum

def wordMass (alphabet : List Run) (T k : Nat) : Nat :=
  ((words alphabet k).map (fun rs => 2 ^ (T - time rs))).sum

private theorem sum_map_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → Nat) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append_nat, List.map_cons,
      List.sum_cons, ih]

private theorem sum_map_scale {α : Type} (xs : List α) (f : α → Nat) (c : Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem mass_succ (alphabet : List Run) (T k : Nat) :
    wordMass alphabet T (k + 1) =
      (alphabet.map (fun r => wordMass alphabet (T - cost r) k)).sum := by
  unfold wordMass
  rw [words, sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [List.map_map, Function.comp_def, time, cost, Nat.sub_add_eq]

/-- The weighted word count factors into the `k`th power of one alphabet
weight, as long as the interval budget covers the maximum word duration. -/
theorem wordMass_eq {alphabet : List Run} {L T k : Nat}
    (hcost : ∀ r ∈ alphabet, cost r ≤ L) (hT : L * k ≤ T) :
    wordMass alphabet T k = 2 ^ (T - L * k) * alphabetWeight alphabet L ^ k := by
  induction k generalizing T with
  | zero => simp [wordMass, words, time]
  | succ k ih =>
    rw [mass_succ]
    let common := 2 ^ (T - L * (k + 1)) * alphabetWeight alphabet L ^ k
    have hterm (r : Run) (hr : r ∈ alphabet) :
        wordMass alphabet (T - cost r) k = common * 2 ^ (L - cost r) := by
      have hL := hcost r hr
      have hTk : L * k ≤ T - cost r := by
        rw [Nat.mul_succ] at hT
        omega
      rw [ih hTk]
      have hsum : T - cost r - L * k = (T - L * (k + 1)) + (L - cost r) := by
        rw [Nat.mul_succ] at hT ⊢
        omega
      rw [hsum, Nat.pow_add]
      dsimp [common]
      ac_rfl
    rw [List.map_congr_left hterm, sum_map_scale]
    change common * alphabetWeight alphabet L = _
    dsimp only [common]
    rw [Nat.pow_succ, Nat.mul_assoc]

private noncomputable def representative (rs : List Run) : Nat := by
  classical
  exact match rs with
  | [] => 1
  | r :: rest => if h : ∃ n e, Trace n e (r :: rest) then Classical.choose h else 0

private theorem representative_mod {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hn : n % 2 = 1) :
    representative rs % (2 ^ time rs * 2) = n % (2 ^ time rs * 2) := by
  cases rs with
  | nil => simp [time, representative, hn]
  | cons r rs =>
    have hex : ∃ n e, Trace n e (r :: rs) := ⟨n, e, h⟩
    have hrep : ∃ y, Trace (representative (r :: rs)) y (r :: rs) := by
      simpa only [representative, dif_pos hex] using Classical.choose_spec hex
    obtain ⟨y, hy⟩ := hrep
    exact source_residue hy h

private noncomputable def wordCover (T : Nat) (rs : List Run) : List Nat :=
  let B := 2 ^ time rs * 2
  (List.range (2 ^ (T - time rs))).map (fun k => representative rs % B + B * k)

private noncomputable def cover (alphabet : List Run) (T k : Nat) : List Nat :=
  (words alphabet k).flatMap (wordCover T)

private theorem cover_length (alphabet : List Run) (T k : Nat) :
    (cover alphabet T k).length = wordMass alphabet T k := by
  simp [cover, List.length_flatMap, wordCover, wordMass]

private theorem mem_wordCover {n e T : Nat} {rs : List Run}
    (h : Trace n e rs) (ht : time rs ≤ T) (hn : n < 2 ^ T * 2) (ho : n % 2 = 1) :
    n ∈ wordCover T rs := by
  let B := 2 ^ time rs * 2
  have hB : 0 < B := Nat.mul_pos (Nat.two_pow_pos _) (by decide)
  have hfactor : 2 ^ (T - time rs) * B = 2 ^ T * 2 := by
    dsimp [B]
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel ht]
  have hquot : n / B < 2 ^ (T - time rs) :=
    (Nat.div_lt_iff_lt_mul hB).mpr (by rw [hfactor]; exact hn)
  apply List.mem_map.mpr
  refine ⟨n / B, List.mem_range.mpr hquot, ?_⟩
  change representative rs % B + B * (n / B) = n
  rw [representative_mod h ho]
  exact Nat.mod_add_div n B

private theorem time_le_of_alphabet {alphabet : List Run} {L : Nat} {rs : List Run}
    (hcost : ∀ r ∈ alphabet, cost r ≤ L) (hall : ∀ r ∈ rs, r ∈ alphabet) :
    time rs ≤ L * rs.length := by
  induction rs with
  | nil => simp [time]
  | cons r rs ih =>
    have hr := hcost r (hall r List.mem_cons_self)
    have ht := ih (fun r hr => hall r (List.mem_cons_of_mem _ hr))
    change cost r + time rs ≤ L * (rs.length + 1)
    rw [Nat.mul_succ]
    omega

/-- A finite sample of distinct odd sources with `k` excursions from the
alphabet occupies at most the weighted number of dyadic slots. -/
theorem bounded_alphabet_count {alphabet : List Run} {sources : List Nat} {L T k : Nat}
    (hnodup : sources.Nodup) (hcost : ∀ r ∈ alphabet, cost r ≤ L) (hT : L * k ≤ T)
    (htrace : ∀ n ∈ sources, n < 2 ^ T * 2 ∧ n % 2 = 1 ∧
      ∃ e rs, Trace n e rs ∧ rs.length = k ∧ (∀ r ∈ rs, r ∈ alphabet)) :
    sources.length ≤ 2 ^ (T - L * k) * alphabetWeight alphabet L ^ k := by
  have hsub : sources ⊆ cover alphabet T k := by
    intro n hn
    obtain ⟨hnT, ho, e, rs, h, hlen, hall⟩ := htrace n hn
    have ht := time_le_of_alphabet hcost hall
    rw [hlen] at ht
    apply List.mem_flatMap.mpr
    refine ⟨rs, ?_, mem_wordCover h (Nat.le_trans ht hT) hnT ho⟩
    rw [← hlen]
    exact mem_words hall
  have hlength := hnodup.length_le_of_subset hsub
  rwa [cover_length, wordMass_eq hcost hT] at hlength

private def axis : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: axis n

private theorem mem_axis {x n : Nat} : x ∈ axis n ↔ 1 ≤ x ∧ x ≤ n := by
  induction n with
  | zero => simp [axis]; omega
  | succ n ih =>
    simp only [axis, List.mem_cons, ih]
    omega

private theorem axisWeight (n : Nat) :
    ((axis n).map (fun v => 2 ^ (n - v))).sum = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hterms : (axis n).map (fun v => 2 ^ (n + 1 - v)) =
        (axis n).map (fun v => 2 * 2 ^ (n - v)) := by
      apply List.map_congr_left
      intro v hv
      have hle := (mem_axis.mp hv).2
      have he : n + 1 - v = (n - v) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm]
    change 2 ^ (n + 1 - (n + 1)) + ((axis n).map (fun v => 2 ^ (n + 1 - v))).sum =
      2 ^ (n + 1) - 1
    rw [hterms, sum_map_scale, ih, Nat.sub_self, Nat.pow_zero, Nat.pow_succ]
    have hp := Nat.two_pow_pos n
    omega

/-- All runs with positive odd length at most `u` and positive extra
halving count at most `w`. -/
def box (u w : Nat) : List Run :=
  (axis u).flatMap (fun v => (axis w).map (fun W => ⟨v, W⟩))

theorem mem_box {u w : Nat} {r : Run} :
    r ∈ box u w ↔ 1 ≤ r.oddSteps ∧ r.oddSteps ≤ u ∧
      1 ≤ r.halvings ∧ r.halvings ≤ w := by
  constructor
  · intro hr
    obtain ⟨v, hv, hrv⟩ := List.mem_flatMap.mp hr
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hrv
    exact ⟨(mem_axis.mp hv).1, (mem_axis.mp hv).2,
      (mem_axis.mp hW).1, (mem_axis.mp hW).2⟩
  · rintro ⟨hv, hvu, hW, hWw⟩
    exact List.mem_flatMap.mpr ⟨r.oddSteps, mem_axis.mpr ⟨hv, hvu⟩,
      List.mem_map.mpr ⟨r.halvings, mem_axis.mpr ⟨hW, hWw⟩, rfl⟩⟩

/-- The rectangular alphabet has an exact product of two geometric sums. -/
theorem alphabetWeight_box (u w : Nat) :
    alphabetWeight (box u w) (u + w) = (2 ^ u - 1) * (2 ^ w - 1) := by
  unfold alphabetWeight box
  rw [sum_map_flatMap]
  have hterm (v : Nat) (hv : v ∈ axis u) :
      (((axis w).map (fun W => (⟨v, W⟩ : Run))).map
        (fun r => 2 ^ (u + w - cost r))).sum = (2 ^ w - 1) * 2 ^ (u - v) := by
    rw [List.map_map]
    have hmap : (axis w).map ((fun r : Run => 2 ^ (u + w - cost r)) ∘
        (fun W => ⟨v, W⟩)) = (axis w).map (fun W => 2 ^ (u - v) * 2 ^ (w - W)) := by
      apply List.map_congr_left
      intro W hW
      have hv' := (mem_axis.mp hv).2
      have hW' := (mem_axis.mp hW).2
      change 2 ^ (u + w - (v + W)) = _
      rw [show u + w - (v + W) = (u - v) + (w - W) by omega, Nat.pow_add]
    rw [hmap, sum_map_scale, axisWeight, Nat.mul_comm]
  rw [List.map_congr_left hterm, sum_map_scale, axisWeight, Nat.mul_comm]

/-- Bounded odd runs and bounded halving runs give a finite density saving
at every complete block of the time budget. -/
theorem box_count {sources : List Nat} {u w T k : Nat}
    (hnodup : sources.Nodup) (hT : (u + w) * k ≤ T)
    (htrace : ∀ n ∈ sources, n < 2 ^ T * 2 ∧ n % 2 = 1 ∧
      ∃ e rs, Trace n e rs ∧ rs.length = k ∧
        (∀ r ∈ rs, 1 ≤ r.oddSteps ∧ r.oddSteps ≤ u ∧
          1 ≤ r.halvings ∧ r.halvings ≤ w)) :
    sources.length ≤ 2 ^ (T - (u + w) * k) * ((2 ^ u - 1) * (2 ^ w - 1)) ^ k := by
  rw [← alphabetWeight_box]
  refine bounded_alphabet_count hnodup ?_ hT ?_
  · intro r hr
    have h := mem_box.mp hr
    unfold cost
    omega
  · intro n hn
    obtain ⟨hnT, ho, e, rs, ht, hk, hall⟩ := htrace n hn
    exact ⟨hnT, ho, e, rs, ht, hk, fun r hr => mem_box.mpr (hall r hr)⟩

theorem box_weight_lt (u w : Nat) :
    (2 ^ u - 1) * (2 ^ w - 1) < 2 ^ (u + w) := by
  rw [Nat.pow_add]
  calc
    _ ≤ (2 ^ u - 1) * 2 ^ w := Nat.mul_le_mul_left _ (Nat.sub_le ..)
    _ < _ := Nat.mul_lt_mul_of_pos_right
      (Nat.sub_lt (Nat.two_pow_pos u) (by decide)) (Nat.two_pow_pos w)

private theorem scaled_power_advantage (a k : Nat) :
    (a + k) * a ^ k ≤ a * (a + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (a + (k + 1)) * a ≤ (a + k) * (a + 1) := by
      rw [Nat.mul_add, Nat.mul_one, show a + (k + 1) = (a + k) + 1 by omega,
        Nat.add_mul, Nat.one_mul]
      omega
    calc
      _ = ((a + (k + 1)) * a) * a ^ k := by rw [Nat.pow_succ', Nat.mul_assoc]
      _ ≤ ((a + k) * (a + 1)) * a ^ k := Nat.mul_le_mul_right _ hstep
      _ = ((a + k) * a ^ k) * (a + 1) := by ac_rfl
      _ ≤ (a * (a + 1) ^ k) * (a + 1) := Nat.mul_le_mul_right _ ih
      _ = a * (a + 1) ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- Any fixed multiplicative weight is eventually absorbed by the larger base. -/
theorem exists_weight_power {a b : Nat} (hab : a < b) (J : Nat) :
    ∃ k, J * a ^ k ≤ b ^ k := by
  by_cases ha : a = 0
  · subst a
    exact ⟨1, by simp⟩
  · let k := J * a
    have hlinear : J * a ≤ a + k := Nat.le_add_left _ _
    have h := Nat.mul_le_mul_right (a ^ k) hlinear
    have hh : a * (J * a ^ k) ≤ a * b ^ k := by
      calc
        _ = (J * a) * a ^ k := by ac_rfl
        _ ≤ (a + k) * a ^ k := h
        _ ≤ a * (a + 1) ^ k := scaled_power_advantage a k
        _ ≤ _ := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hab k)
    exact ⟨k, Nat.le_of_mul_le_mul_left hh (Nat.pos_of_ne_zero ha)⟩

/-- For any desired dyadic density bound, a finite number of excursions
from the box suffices uniformly in the size of the source interval. -/
theorem box_arbitrarily_thin (u w J : Nat) :
    ∃ k, ∀ (T : Nat) (sources : List Nat), sources.Nodup → (u + w) * k ≤ T →
      (∀ n ∈ sources, n < 2 ^ T * 2 ∧ n % 2 = 1 ∧
        ∃ e rs, Trace n e rs ∧ rs.length = k ∧ (∀ r ∈ rs, r ∈ box u w)) →
      J * sources.length ≤ 2 ^ T := by
  obtain ⟨k, hk⟩ := exists_weight_power (box_weight_lt u w) J
  refine ⟨k, ?_⟩
  intro T sources hnodup hT htrace
  have hc := box_count hnodup hT (fun n hn => by
    obtain ⟨hnT, ho, e, rs, ht, hlen, hall⟩ := htrace n hn
    exact ⟨hnT, ho, e, rs, ht, hlen, fun r hr => mem_box.mp (hall r hr)⟩)
  calc
    _ ≤ J * (2 ^ (T - (u + w) * k) * ((2 ^ u - 1) * (2 ^ w - 1)) ^ k) :=
      Nat.mul_le_mul_left _ hc
    _ = 2 ^ (T - (u + w) * k) * (J * ((2 ^ u - 1) * (2 ^ w - 1)) ^ k) :=
      Nat.mul_left_comm ..
    _ ≤ 2 ^ (T - (u + w) * k) * (2 ^ (u + w)) ^ k := Nat.mul_le_mul_left _ hk
    _ = 2 ^ T := by rw [← Nat.pow_mul, ← Nat.pow_add, Nat.sub_add_cancel hT]

/-- Every sample has arbitrarily long excursion continuations in the box. -/
def HasBoxFutures (states : Nat → Nat) (u w : Nat) : Prop :=
  ∀ i k, states i % 2 = 1 ∧
    ∃ e rs, Trace (states i) e rs ∧ rs.length = k ∧ (∀ r ∈ rs, r ∈ box u w)

/-- At equally spaced dyadic scales, the fraction of available odd
slots occupied by states with bounded futures drops by at least a
factor of two per scale. -/
theorem box_geometric_capacity {states : Nat → Nat} {u w : Nat}
    (hL : 0 < u + w) (hf : HasBoxFutures states u w) :
    ∃ P, 0 < P ∧ ∀ j (sources : List Nat), sources.Nodup →
      (∀ n ∈ sources, n < 2 ^ (P * j) * 2 ∧ ∃ i, states i = n) →
      sources.length ≤ 2 ^ ((P - 1) * j) := by
  let W := (2 ^ u - 1) * (2 ^ w - 1)
  obtain ⟨k, hk⟩ := exists_weight_power (box_weight_lt u w) 2
  have hkpos : 0 < k := by
    by_cases hz : k = 0
    · subst k
      simp at hk
    · exact Nat.pos_of_ne_zero hz
  let P := (u + w) * k
  have hP : 0 < P := Nat.mul_pos hL hkpos
  refine ⟨P, hP, ?_⟩
  intro j sources hnodup hsource
  have hT : (u + w) * (k * j) = P * j := by simp [P, Nat.mul_assoc]
  have hc := box_count hnodup (Nat.le_of_eq hT) (fun n hn => by
    obtain ⟨hnT, i, rfl⟩ := hsource n hn
    obtain ⟨ho, e, rs, ht, hlen, hall⟩ := hf i (k * j)
    exact ⟨hnT, ho, e, rs, ht, hlen, fun r hr => mem_box.mp (hall r hr)⟩)
  rw [hT, Nat.sub_self, Nat.pow_zero, Nat.one_mul] at hc
  change sources.length ≤ W ^ (k * j) at hc
  have hpower : 2 ^ j * W ^ (k * j) ≤ 2 ^ (P * j) := by
    simpa only [W, P, Nat.mul_pow, ← Nat.pow_mul] using Nat.pow_le_pow_left hk j
  apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos j)
  calc
    2 ^ j * sources.length ≤ 2 ^ j * W ^ (k * j) := Nat.mul_le_mul_left _ hc
    _ ≤ 2 ^ (P * j) := hpower
    _ = 2 ^ j * 2 ^ ((P - 1) * j) := by
      have hex : j + (P - 1) * j = P * j := by
        calc
          _ = (1 + (P - 1)) * j := by rw [Nat.add_mul, Nat.one_mul]
          _ = _ := by rw [Nat.add_sub_of_le (Nat.succ_le_of_lt hP)]
      rw [← Nat.pow_add, hex]

/-- For distinct samples with bounded excursion continuations, some
value exceeds the dyadic cutoff within an arbitrarily small fraction
of the number of available odd slots. -/
theorem box_dispersion {states : Nat → Nat} {u w J : Nat}
    (hJ : 0 < J) (hf : HasBoxFutures states u w)
    (hinj : ∀ i j, states i = states j → i = j) :
    ∃ H, ∀ T, H ≤ T → ∃ i ≤ 2 ^ T / J, 2 ^ T * 2 ≤ states i := by
  obtain ⟨k, hthin⟩ := box_arbitrarily_thin u w J
  refine ⟨(u + w) * k, ?_⟩
  intro T hT
  apply Classical.byContradiction
  intro hno
  let N := 2 ^ T / J + 1
  let sample := (List.range N).map states
  have hnodup : sample.Nodup := by
    apply List.pairwise_map.mpr
    exact List.nodup_range.imp (fun hne heq => hne (hinj _ _ heq))
  have htrace : ∀ n ∈ sample, n < 2 ^ T * 2 ∧ n % 2 = 1 ∧
      ∃ e rs, Trace n e rs ∧ rs.length = k ∧ (∀ r ∈ rs, r ∈ box u w) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    have hi' : i ≤ 2 ^ T / J := by
      have hr := List.mem_range.mp hi
      dsimp [N] at hr
      omega
    exact ⟨Nat.lt_of_not_ge (fun h => hno ⟨i, hi', h⟩), hf i k⟩
  have hcount := hthin T sample hnodup hT htrace
  have hsize : sample.length = N := by simp [sample]
  rw [hsize, Nat.mul_comm J N] at hcount
  have hstrict : 2 ^ T < N * J := (Nat.div_lt_iff_lt_mul hJ).mp (Nat.lt_succ_self _)
  omega

/-- Distinct states with bounded run and halving counts cannot remain
linearly bounded as a function of their sample index. -/
theorem box_no_linear_bound {states : Nat → Nat} {u w C : Nat}
    (hf : HasBoxFutures states u w)
    (hinj : ∀ i j, states i = states j → i = j)
    (hlinear : ∀ i, states i ≤ C * i + C) : False := by
  obtain ⟨H, hH⟩ := box_dispersion (J := C + 1) (by omega) hf hinj
  let T := H + C
  obtain ⟨i, hi, hlarge⟩ := hH T (Nat.le_add_right _ _)
  have hbudget : C * i ≤ 2 ^ T := by
    calc
      _ ≤ (C + 1) * i := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (C + 1) * (2 ^ T / (C + 1)) := Nat.mul_le_mul_left _ hi
      _ ≤ _ := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hC : C < 2 ^ T := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) Nat.lt_two_pow_self
  have h := hlinear i
  omega

end Collatz.ExcursionAlphabetMass
