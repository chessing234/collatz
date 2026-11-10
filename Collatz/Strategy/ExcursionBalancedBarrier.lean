import Collatz.Strategy.DyadicPowerBounds
import Collatz.Strategy.ExcursionRays

/-!
# A barrier for coefficient-only offset estimates

Alternate two excursion types to keep the inverse coefficient in
`(2/3, 1]`. Both types then contribute at least five twenty-fourths
per odd step to the normalized offset. The resulting word can be
terminated at the exceptional exponent pair. It is a statement
about the word and its affine offset, with no small-source claim.
-/

namespace Collatz.ExcursionBalancedBarrier

open Collatz.ExcursionBudget Collatz.DyadicPowerBounds

private def unit : Run := ⟨1, 1⟩
private def double : Run := ⟨2, 1⟩

private def balanced : Nat → List Run
  | 0 => []
  | j + 1 =>
    let rs := balanced j
    if 4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs then unit :: rs else double :: rs

private structure Spec (rs : List Run) (j : Nat) : Prop where
  length : rs.length = j
  elapsed : time rs = ExcursionBudget.oddCount rs + j
  low : 2 * 3 ^ ExcursionBudget.oddCount rs < 3 * 2 ^ time rs
  heavy : 2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs
  proper : ProperPrefixBound 1 1 rs
  offset_lower : (5 * ExcursionBudget.oddCount rs) * 3 ^ ExcursionBudget.oddCount rs ≤ 24 * offset rs

private theorem add_unit_offset {rs : List Run}
    (hlow : 2 * 3 ^ ExcursionBudget.oddCount rs < 3 * 2 ^ time rs)
    (hprev : (5 * ExcursionBudget.oddCount rs) * 3 ^ ExcursionBudget.oddCount rs ≤ 24 * offset rs) :
    (5 * ExcursionBudget.oddCount (unit :: rs)) * 3 ^ ExcursionBudget.oddCount (unit :: rs) ≤ 24 * offset (unit :: rs) := by
  let a := ExcursionBudget.oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let C := offset rs
  have he : (5 * (1 + a)) * (3 * A) = 3 * ((5 * a) * A) + 15 * A := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    ac_rfl
  have hC : 24 * (3 * C + B) = 3 * (24 * C) + 24 * B := by
    rw [Nat.mul_add, Nat.mul_left_comm 24 3]
  have hp := Nat.mul_le_mul_left 3 hprev
  change 2 * A < 3 * B at hlow
  change 3 * ((5 * a) * A) ≤ 3 * (24 * C) at hp
  simp only [unit, ExcursionBudget.oddCount, offset, Nat.pow_add, Nat.pow_one]
  change (5 * (1 + a)) * (3 * A) ≤ 24 * (3 * C + B * 1)
  rw [Nat.mul_one, he, hC]
  omega

private theorem add_double_offset {rs : List Run}
    (hhigh : 3 * 3 ^ ExcursionBudget.oddCount rs < 4 * 2 ^ time rs)
    (hprev : (5 * ExcursionBudget.oddCount rs) * 3 ^ ExcursionBudget.oddCount rs ≤ 24 * offset rs) :
    (5 * ExcursionBudget.oddCount (double :: rs)) * 3 ^ ExcursionBudget.oddCount (double :: rs) ≤ 24 * offset (double :: rs) := by
  let a := ExcursionBudget.oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let C := offset rs
  have he : (5 * (2 + a)) * (9 * A) = 9 * ((5 * a) * A) + 90 * A := by
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have hC : 24 * (9 * C + B * 5) = 9 * (24 * C) + 120 * B := by
    rw [Nat.mul_add, Nat.mul_left_comm 24 9, Nat.mul_comm B 5, ← Nat.mul_assoc 24 5 B]
  have hp := Nat.mul_le_mul_left 9 hprev
  change 3 * A < 4 * B at hhigh
  change 9 * ((5 * a) * A) ≤ 9 * (24 * C) at hp
  simp only [double, ExcursionBudget.oddCount, offset, Nat.pow_add]
  change (5 * (2 + a)) * (9 * A) ≤ 24 * (9 * C + B * 5)
  rw [he, hC]
  omega

private theorem balanced_spec (j : Nat) : Spec (balanced j) j := by
  induction j with
  | zero => exact ⟨rfl, rfl, by decide, by decide, trivial, by decide⟩
  | succ j ih =>
    let rs := balanced j
    change Spec rs j at ih
    change Spec (if 4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs then unit :: rs else double :: rs) (j + 1)
    by_cases h : 4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs
    · rw [if_pos h]
      refine ⟨by simp [ih.length], ?_, ?_, ?_, ?_, add_unit_offset ih.low ih.offset_lower⟩
      · simp only [unit, time, ExcursionBudget.oddCount, ih.elapsed]
        omega
      · have hl := ih.low
        simp only [unit, time, ExcursionBudget.oddCount, Nat.pow_add, Nat.pow_one]
        change 2 * (3 * 3 ^ ExcursionBudget.oddCount rs) < 3 * (4 * 2 ^ time rs)
        omega
      · simpa only [unit, time, ExcursionBudget.oddCount, Nat.pow_add, Nat.pow_one] using h
      · exact ⟨by simpa only [Nat.one_mul] using ih.heavy, ih.proper⟩
    · rw [if_neg h]
      have hhigh := Nat.lt_of_not_ge h
      refine ⟨by simp [ih.length], ?_, ?_, ?_, ?_, add_double_offset hhigh ih.offset_lower⟩
      · simp only [double, time, ExcursionBudget.oddCount, ih.elapsed]
        omega
      · simp only [double, time, ExcursionBudget.oddCount, Nat.pow_add]
        change 2 * (9 * 3 ^ ExcursionBudget.oddCount rs) < 3 * (8 * 2 ^ time rs)
        omega
      · have hh := ih.heavy
        simp only [double, time, ExcursionBudget.oddCount, Nat.pow_add]
        change 8 * 2 ^ time rs ≤ 9 * 3 ^ ExcursionBudget.oddCount rs
        omega
      · exact ⟨by simpa only [Nat.one_mul] using ih.heavy, ih.proper⟩

private theorem balanced_contains_earlier (k j : Nat) (hk : k ≤ j) :
    ∃ later, balanced j = later ++ balanced k := by
  induction j with
  | zero =>
    have he : k = 0 := by omega
    subst k
    exact ⟨[], rfl⟩
  | succ j ih =>
    by_cases he : k = j + 1
    · subst k
      exact ⟨[], rfl⟩
    · obtain ⟨later, hl⟩ := ih (by omega)
      rw [balanced]
      split
      · exact ⟨unit :: later, congrArg (unit :: ·) hl⟩
      · exact ⟨double :: later, congrArg (double :: ·) hl⟩

private theorem prefix_excludes_small_source {n e : Nat} (h : Trace n e (balanced 26)) :
    4697939311072332635131 ≤ n := by
  let rs := balanced 25
  have he : balanced 26 = double :: rs := by
    rw [balanced, if_neg (by decide +kernel)]
  rw [he] at h
  have ha : 3 ^ ExcursionBudget.oddCount (double :: rs) * 4697939311072332635131 +
      offset (double :: rs) = 2 ^ time (double :: rs) * 5878062133319092016947 := by
    decide +kernel
  have hr := ExcursionRays.source_residue_of_affine h ha (by decide)
  have hm : 4697939311072332635131 % (2 ^ time (double :: rs) * 2) =
      4697939311072332635131 := by decide +kernel
  rw [hm] at hr
  exact hr ▸ Nat.mod_le n _

/-- The inverse coefficients of all proper excursion prefixes
are strictly greater than two thirds. -/
def ProperPrefixLower : List Run → Prop
  | [] => True
  | _ :: rs => 2 * 3 ^ ExcursionBudget.oddCount rs < 3 * 2 ^ time rs ∧ ProperPrefixLower rs

private def twoRunShape (r : Run) : Prop :=
  r.halvings = 1 ∧ (r.oddSteps = 1 ∨ r.oddSteps = 2)

private theorem balanced_of_corridor {rs : List Run}
    (hshape : ∀ r ∈ rs, twoRunShape r)
    (hproper : ProperPrefixBound 1 1 rs) (hlower : ProperPrefixLower rs)
    (hfull : 2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs)
    (hfloor : 2 * 3 ^ ExcursionBudget.oddCount rs < 3 * 2 ^ time rs) :
    rs = balanced rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hsmall : ∀ x ∈ rs, twoRunShape x := fun x hx => hshape x (List.mem_cons_of_mem _ hx)
    have hprev : 2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have he := ih hsmall hproper.2 hlower.2 hprev hlower.1
    have htype : r = unit ∨ r = double := by
      have hh := hshape r List.mem_cons_self
      obtain ⟨v, w⟩ := r
      obtain ⟨hw, hv⟩ := hh
      change w = 1 at hw
      change v = 1 ∨ v = 2 at hv
      subst w
      rcases hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases htype with rfl | rfl
    · have hchoose : 4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs := by
        simpa only [unit, time, ExcursionBudget.oddCount, Nat.pow_add, Nat.pow_one] using hfull
      simp only [List.length_cons, balanced, ← he, if_pos hchoose]
    · have hchoose : ¬4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs := by
        have hh := hfloor
        simp only [double, time, ExcursionBudget.oddCount, Nat.pow_add] at hh
        change 2 * (9 * 3 ^ ExcursionBudget.oddCount rs) < 3 * (8 * 2 ^ time rs) at hh
        omega
      simp only [List.length_cons, balanced, ← he, if_neg hchoose]

private theorem odd_count_le_twice_length {rs : List Run}
    (hshape : ∀ r ∈ rs, twoRunShape r) : ExcursionBudget.oddCount rs ≤ 2 * rs.length := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    have htail := ih (fun r hr => hshape r (List.mem_cons_of_mem _ hr))
    have hv := (hshape r List.mem_cons_self).2
    simp only [ExcursionBudget.oddCount, List.length_cons]
    omega

/-- A genuine long crossing from inside the exceptional source
window must leave the balanced corridor or use a different run. -/
theorem trace_leaves_balanced_corridor {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hsmall : n < 3 * 2 ^ 70)
    (hodd : 53 ≤ ExcursionBudget.oddCount rs) (hproper : ProperPrefixBound 1 1 rs) :
    ¬ (ProperPrefixLower rs ∧
      ∀ r ∈ rs, r.halvings = 1 ∧ (r.oddSteps = 1 ∨ r.oddSteps = 2)) := by
  rintro ⟨hlower, hshape⟩
  have hsize := odd_count_le_twice_length hshape
  cases rs with
  | nil => simp [ExcursionBudget.oddCount] at hodd
  | cons r rs =>
    have hlen : 26 ≤ rs.length := by
      simp only [List.length_cons] at hsize
      omega
    have hfull : 2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs := by
      simpa only [Nat.one_mul] using hproper.1
    have he := balanced_of_corridor (fun x hx => hshape x (List.mem_cons_of_mem _ hx))
      hproper.2 hlower.2 hfull hlower.1
    obtain ⟨later, hl⟩ := balanced_contains_earlier 26 rs.length hlen
    have hword : r :: rs = (r :: later) ++ balanced 26 := congrArg (r :: ·) (he.trans hl)
    rw [hword] at h
    obtain ⟨f, hf, _⟩ := ExcursionRays.split_trace h
    have hlarge := prefix_excludes_small_source hf
    omega

private theorem scaled_count_mono {j a b p q : Nat} (hab : a ≤ b)
    (h : p * 2 ^ (a + j) ≤ q * 3 ^ a) : p * 2 ^ (b + j) ≤ q * 3 ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_right_comm a d j, Nat.pow_add 2 (a + j) d, Nat.pow_add 3 a d,
    ← Nat.mul_assoc p, ← Nat.mul_assoc q]
  exact Nat.mul_le_mul h (Collatz.Arith.two_pow_le_three_pow d)

/-- The balance policy can terminate just above coefficient one.
The word has the prescribed exponents and a substantial offset. -/
private theorem exists_balanced_first_crossing {a j : Nat} (hj : 0 < j)
    (hcross : 3 ^ a < 2 ^ (a + j)) (hnear : 3 * 2 ^ (a + j) < 4 * 3 ^ a) :
    ∃ rs, ExcursionBudget.oddCount rs = a ∧ time rs = a + j ∧ ProperPrefixBound 1 1 rs ∧
      (5 * a) * 3 ^ a ≤ 24 * offset rs ∧
      ∀ k, k < j → ∃ later, rs = later ++ balanced k := by
  have hspec := balanced_spec j
  have hlow : a + 1 ≤ ExcursionBudget.oddCount (balanced j) := by
    apply Nat.le_of_not_gt
    intro h
    have hheavy := hspec.heavy
    rw [hspec.elapsed] at hheavy
    have hmono := scaled_count_mono (p := 1) (q := 1) (by omega : ExcursionBudget.oddCount (balanced j) ≤ a)
      (by simpa only [Nat.one_mul] using hheavy)
    rw [Nat.one_mul, Nat.one_mul] at hmono
    exact Nat.not_le_of_gt hcross hmono
  have hhigh : ExcursionBudget.oddCount (balanced j) ≤ a + 1 := by
    apply Nat.le_of_not_gt
    intro h
    have hfar : 3 * 2 ^ ((a + 2) + j) ≤ 2 * 3 ^ (a + 2) := by
      rw [Nat.add_right_comm a 2 j, Nat.pow_add 2 (a + j) 2, Nat.pow_add 3 a 2]
      change 3 * (2 ^ (a + j) * 4) ≤ 2 * (3 ^ a * 9)
      omega
    have hmono := scaled_count_mono (by omega : a + 2 ≤ ExcursionBudget.oddCount (balanced j)) hfar
    have hs := hspec.low
    rw [hspec.elapsed] at hs
    exact Nat.not_le_of_gt hs hmono
  have hcount : ExcursionBudget.oddCount (balanced j) = a + 1 := by omega
  have hlast : 9 * 2 ^ time (balanced j) < 8 * 3 ^ ExcursionBudget.oddCount (balanced j) := by
    rw [hspec.elapsed, hcount, Nat.add_right_comm a 1 j, Nat.pow_add 2 (a + j) 1,
      Nat.pow_add 3 a 1]
    simp only [Nat.pow_one]
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  let rs := balanced k
  have hprev : Spec rs k := balanced_spec k
  have hchoose : ¬4 * 2 ^ time rs ≤ 3 * 3 ^ ExcursionBudget.oddCount rs := by
    intro hc
    have hs := hlast
    simp only [balanced, show 4 * 2 ^ time (balanced k) ≤ 3 * 3 ^ ExcursionBudget.oddCount (balanced k) from hc,
      if_true, unit, time, ExcursionBudget.oddCount, Nat.pow_add, Nat.pow_one] at hs
    change 9 * (4 * 2 ^ time rs) < 8 * (3 * 3 ^ ExcursionBudget.oddCount rs) at hs
    have hp := hprev.low
    omega
  have hd : ExcursionBudget.oddCount (double :: rs) = a + 1 := by
    have hc : ¬4 * 2 ^ time (balanced k) ≤ 3 * 3 ^ ExcursionBudget.oddCount (balanced k) := hchoose
    simpa only [balanced, if_neg hc] using hcount
  have ha : ExcursionBudget.oddCount (unit :: rs) = a := by
    simp only [unit, double, ExcursionBudget.oddCount] at hd ⊢
    omega
  have hb : time (unit :: rs) = a + (k + 1) := by
    have hs := hprev.elapsed
    simp only [unit, ExcursionBudget.oddCount, time] at ha ⊢
    omega
  refine ⟨unit :: rs, ha, hb, ⟨by simpa only [Nat.one_mul] using hprev.heavy, hprev.proper⟩, ?_, ?_⟩
  · have h := add_unit_offset hprev.low hprev.offset_lower
    rwa [ha] at h
  · intro l hl
    obtain ⟨later, hprefix⟩ := balanced_contains_earlier l k (by omega)
    exact ⟨unit :: later, congrArg (unit :: ·) hprefix⟩

private theorem barrier_at_coefficients {a b j floor : Nat} (hj : 26 < j) (hb : b = a + j)
    (hcross : 3 ^ a < 2 ^ b) (hnear : 3 * 2 ^ b < 4 * 3 ^ a)
    (hcompare : (24 * floor) * 2 ^ b < (24 * floor + 5 * a) * 3 ^ a) :
    ∃ rs, ExcursionBudget.oddCount rs = a ∧ time rs = b ∧ ProperPrefixBound 1 1 rs ∧
      3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs ∧
      (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs) * floor < offset rs ∧
      ∀ n e, Trace n e rs → 4697939311072332635131 ≤ n := by
  obtain ⟨rs, ha, ht, hp, hoff, hprefix⟩ :=
    exists_balanced_first_crossing (by omega : 0 < j) (hb ▸ hcross) (hb ▸ hnear)
  have ht' := ht.trans hb.symm
  refine ⟨rs, ha, ht', hp, ?_, ?_, ?_⟩
  · rwa [ha, ht']
  · have hsum : 3 ^ a + (2 ^ b - 3 ^ a) = 2 ^ b := Nat.add_sub_of_le (Nat.le_of_lt hcross)
    have hh : (24 * floor) * (2 ^ b - 3 ^ a) < (5 * a) * 3 ^ a := by
      rw [← hsum, Nat.mul_add, Nat.add_mul] at hcompare
      omega
    rw [ha, ht']
    apply Nat.lt_of_mul_lt_mul_left (a := 24)
    calc
      _ = (24 * floor) * (2 ^ b - 3 ^ a) := by ac_rfl
      _ < (5 * a) * 3 ^ a := hh
      _ ≤ _ := hoff
  · intro n e h
    obtain ⟨later, hl⟩ := hprefix 26 hj
    rw [hl] at h
    obtain ⟨f, hf, _⟩ := ExcursionRays.split_trace h
    exact prefix_excludes_small_source hf

private def oddExponent : Nat := 72057431991
private def elapsedExponent : Nat := 114208327604
private def excursionCount : Nat := 42150895613

private theorem special_contracts : (3 : Nat) ^ oddExponent < 2 ^ elapsedExponent := by
  have h := strict_upper_comparison 3 oddExponent 192 1 1 elapsedExponent (by decide +kernel)
  simpa only [Nat.one_mul] using h

private theorem special_near : 3 * 2 ^ elapsedExponent < 4 * (3 : Nat) ^ oddExponent :=
  scaled_lower_comparison 3 oddExponent 192 3 4 elapsedExponent (by decide +kernel)

private theorem special_offset_comparison :
    (24 * 2 ^ 71) * 2 ^ elapsedExponent < (24 * 2 ^ 71 + 5 * oddExponent) * (3 : Nat) ^ oddExponent :=
  scaled_lower_comparison 3 oddExponent 192 (24 * 2 ^ 71)
    (24 * 2 ^ 71 + 5 * oddExponent) elapsedExponent (by decide +kernel)

/-- Proper-prefix heaviness alone cannot make the normalized offset
small enough to exclude the exceptional pair at the verified floor. -/
theorem exceptional_pair_has_large_word_offset :
    ∃ rs, ExcursionBudget.oddCount rs = 72057431991 ∧ time rs = 114208327604 ∧ ProperPrefixBound 1 1 rs ∧
      3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs ∧
      (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs) * 2 ^ 71 < offset rs ∧
      ∀ n e, Trace n e rs → 4697939311072332635131 ≤ n :=
  barrier_at_coefficients (a := oddExponent) (b := elapsedExponent)
    (j := excursionCount) (floor := 2 ^ 71) (by decide) (by decide)
    special_contracts special_near special_offset_comparison

end Collatz.ExcursionBalancedBarrier
