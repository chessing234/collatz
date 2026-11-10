import Collatz.Strategy.SuffixResidueObstruction

/-!
# Integer separation for bounded even-step defects

Fix an even-step budget. The shifted defects, divided by their
dyadic scale, cannot approximate a nonzero integer arbitrarily
closely in the ternary metric. Peeling off the last even step
preserves a nonzero integer comparison and lowers the budget.
-/

namespace Collatz.BoundedEvenDefect

open Collatz.RunAlgebra

private theorem last_even_with_parity (x j : Nat) :
    (oddCount x j = j ∧ runA j x = 0) ∨
      ∃ i t, j = i + 1 + t ∧ oddCount x j = oddCount x i + t ∧
        runA j x = 3 ^ t * (runA i x + 2 ^ i) ∧ acceleratedOrbit i x % 2 = 0 := by
  induction j with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ j ih =>
    have hcount := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · exact Or.inr ⟨j, 0, by omega, by omega, by rw [runA_even he]; simp, he⟩
    · rcases ih with ⟨ha, hzero⟩ | ⟨i, t, hlen, ha, hA, he'⟩
      · exact Or.inl ⟨by omega, by rw [runA_odd ho, hzero, Nat.mul_zero]⟩
      · refine Or.inr ⟨i, t + 1, by omega, by omega, ?_, he'⟩
        rw [runA_odd ho, hA, Nat.pow_succ', Nat.mul_assoc]

/-- The shifted defect is zero for an all-odd word. Otherwise its
last even step separates the previous defect from the trailing odds. -/
theorem last_even (x j : Nat) :
    (oddCount x j = j ∧ runA j x = 0) ∨
      ∃ i t, j = i + 1 + t ∧ oddCount x j = oddCount x i + t ∧
        runA j x = 3 ^ t * (runA i x + 2 ^ i) := by
  rcases last_even_with_parity x j with h | ⟨i, t, hj, ha, hA, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, t, hj, ha, hA⟩

theorem runA_zero_of_full_oddCount {x j : Nat} (h : oddCount x j = j) : runA j x = 0 := by
  rcases last_even x j with ⟨_, hA⟩ | ⟨i, t, hj, hc, _⟩
  · exact hA
  · have hcap := AffineExact.oddCount_le_self x i
    omega

private theorem three_pow_dvd {a b : Nat} (h : a ≤ b) : (3 : Int) ^ a ∣ 3 ^ b := by
  simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
    (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 3 h))

private theorem cancel_dyadic {C : Int} {p j : Nat}
    (h : (3 : Int) ^ p ∣ (2 : Int) ^ j * C) : (3 : Int) ^ p ∣ C := by
  have hnat := Int.natAbs_dvd_natAbs.mpr h
  apply Int.natAbs_dvd_natAbs.mp
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hnat ⊢
  exact ((by decide : Nat.Coprime 3 2).pow p j).dvd_of_dvd_mul_left hnat

private theorem integer_precision {C : Int} {p : Nat} (hC : C ≠ 0) (hsize : C.natAbs < 3 ^ p) :
    ¬ (3 : Int) ^ p ∣ C := by
  intro h
  have hd := Int.natAbs_dvd_natAbs.mpr h
  have hn : 0 < C.natAbs := by omega
  simp only [Int.natAbs_pow] at hd
  exact Nat.not_le_of_gt hsize (Nat.le_of_dvd hn hd)

private def residual (C : Int) (t : Nat) : Int := (2 : Int) ^ (t + 1) * (C / 3 ^ t) - 1

private theorem residual_ne_zero (C : Int) (t : Nat) : residual C t ≠ 0 := by
  unfold residual
  rw [Int.pow_succ, Int.mul_right_comm ((2 : Int) ^ t) 2, Int.mul_comm _ 2]
  omega

private theorem residual_size {C : Int} {t : Nat} (hC : C ≠ 0)
    (hdiv : (3 : Int) ^ t ∣ C) :
    3 ^ t * (residual C t).natAbs ≤ (3 * 2 ^ t) * C.natAbs := by
  let R := C / (3 : Int) ^ t
  have hCR : C = (3 : Int) ^ t * R := (Int.mul_ediv_cancel' hdiv).symm
  have habs : C.natAbs = 3 ^ t * R.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, show (3 : Int).natAbs = 3 by rfl] using
      congrArg Int.natAbs hCR
  have hpos : 0 < R.natAbs := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at habs
    omega
  have hproduct := Nat.mul_pos (Nat.two_pow_pos t) hpos
  have hR : (residual C t).natAbs ≤ 3 * (2 ^ t * R.natAbs) := by
    calc
      _ ≤ ((2 : Int) ^ (t + 1) * R).natAbs + (1 : Int).natAbs := Int.natAbs_sub_le _ _
      _ = 2 * (2 ^ t * R.natAbs) + 1 := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        change 2 ^ (t + 1) * R.natAbs + 1 = _
        rw [Nat.pow_succ', Nat.mul_assoc]
      _ ≤ _ := by omega
  calc
    _ ≤ 3 ^ t * (3 * (2 ^ t * R.natAbs)) := Nat.mul_le_mul_left _ hR
    _ = _ := by rw [habs]; ac_rfl

private theorem precision_of_size {d p : Nat} {C : Int} (hC : C ≠ 0)
    (hsize : 2 ^ p * (3 ^ d * C.natAbs) < 3 ^ p) : ¬ (3 : Int) ^ p ∣ C := by
  have hle : C.natAbs ≤ 2 ^ p * (3 ^ d * C.natAbs) :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  exact integer_precision hC (Nat.lt_of_le_of_lt hle hsize)

private theorem avoids_at_precision (d p : Nat) {C : Int} (hC : C ≠ 0)
    (hsize : 2 ^ p * (3 ^ d * C.natAbs) < 3 ^ p) :
    ∀ x j, j - d ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (2 : Int) ^ j * C - (runA j x : Int) := by
  induction d generalizing p C with
  | zero =>
    intro x j hodd hdvd
    have hprec := precision_of_size hC hsize
    rcases last_even x j with ⟨_, hzero⟩ | ⟨i, t, hlen, ha, _⟩
    · rw [hzero] at hdvd
      simp only [Int.ofNat_zero, Int.sub_zero] at hdvd
      exact hprec (cancel_dyadic hdvd)
    · have hcap := AffineExact.oddCount_le_self x i
      omega
  | succ d ih =>
    intro x j hodd hdvd
    have hprec := precision_of_size hC hsize
    rcases last_even x j with ⟨_, hzero⟩ | ⟨i, t, hlen, ha, hA⟩
    · rw [hzero] at hdvd
      simp only [Int.ofNat_zero, Int.sub_zero] at hdvd
      exact hprec (cancel_dyadic hdvd)
    · have hAint : (runA j x : Int) = (3 : Int) ^ t * ((runA i x : Int) + 2 ^ i) := by
        simpa only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow,
          show ((3 : Nat) : Int) = 3 by rfl, show ((2 : Nat) : Int) = 2 by rfl] using
          congrArg (fun n : Nat => (n : Int)) hA
      have hCsmall (b : Nat) (hb : b ≤ p) (hbt : b ≤ t) : (3 : Int) ^ b ∣ C := by
        have hdiff := Int.dvd_trans (three_pow_dvd hb) hdvd
        have hpart : (3 : Int) ^ b ∣ (runA j x : Int) := by
          rw [hAint]
          exact Int.dvd_trans (three_pow_dvd hbt) (Int.dvd_mul_right _ _)
        have hprod := Int.dvd_add hdiff hpart
        rw [Int.sub_add_cancel] at hprod
        exact cancel_dyadic hprod
      have ht : t < p := by
        apply Nat.lt_of_not_ge
        intro ht
        exact hprec (hCsmall p (Nat.le_refl _) ht)
      have hCt : (3 : Int) ^ t ∣ C := hCsmall t (by omega) (Nat.le_refl _)
      let R := C / (3 : Int) ^ t
      have hCR : C = (3 : Int) ^ t * R :=
        (Int.mul_ediv_cancel' hCt).symm
      have h₂ : (2 : Int) ^ j = 2 ^ i * 2 ^ (t + 1) := by
        rw [hlen, Nat.add_assoc, Nat.add_comm 1 t, Int.pow_add]
      have hfactor : (2 : Int) ^ j * C - (runA j x : Int) =
          (3 : Int) ^ t * ((2 : Int) ^ i * residual C t - (runA i x : Int)) := by
        calc
          _ = 3 ^ t * (2 ^ i * 2 ^ (t + 1) * R - ((runA i x : Int) + 2 ^ i)) := by
            rw [h₂, hAint, hCR, Int.mul_sub]
            congr 1
            ac_rfl
          _ = _ := by
            unfold residual
            change 3 ^ t * (2 ^ i * 2 ^ (t + 1) * R - ((runA i x : Int) + 2 ^ i)) =
              3 ^ t * (2 ^ i * (2 ^ (t + 1) * R - 1) - (runA i x : Int))
            congr 1
            rw [Int.mul_sub, Int.mul_one, Int.mul_assoc]
            omega
      let q := p - t
      have htp : t + q = p := Nat.add_sub_of_le (Nat.le_of_lt ht)
      have hqp : q + t = p := Nat.sub_add_cancel (Nat.le_of_lt ht)
      have hdiv := hdvd
      conv at hdiv => lhs; rw [← htp, Int.pow_add]
      rw [hfactor] at hdiv
      have hnon : (3 : Int) ^ t ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide : (0 : Int) < 3))
      have hpre : i - d ≤ oddCount x i := by omega
      have hsize' : 2 ^ q * (3 ^ d * (residual C t).natAbs) < 3 ^ q := by
        apply Nat.lt_of_mul_lt_mul_left (a := 3 ^ t)
        calc
          _ = (2 ^ q * 3 ^ d) * (3 ^ t * (residual C t).natAbs) := by ac_rfl
          _ ≤ (2 ^ q * 3 ^ d) * ((3 * 2 ^ t) * C.natAbs) :=
            Nat.mul_le_mul_left _ (residual_size hC hCt)
          _ = 2 ^ p * (3 ^ (d + 1) * C.natAbs) := by
            calc
              _ = (2 ^ q * 2 ^ t) * ((3 ^ d * 3) * C.natAbs) := by ac_rfl
              _ = _ := by rw [← Nat.pow_add, hqp, ← Nat.pow_succ]
          _ < 3 ^ p := hsize
          _ = 3 ^ t * 3 ^ q := by rw [← Nat.pow_add, htp]
      exact ih q (residual_ne_zero C t) hsize'
        x i hpre (Int.dvd_of_mul_dvd_mul_left hnon hdiv)

/-- An explicit linear ternary precision separates every nonzero integer
of absolute value below 2^B from defects with at most d even steps. -/
theorem avoids_bounded_integer (d B : Nat) {C : Int} (hC : C ≠ 0) (hsize : C.natAbs < 2 ^ B) :
    ∀ x j, j - d ≤ oddCount x j →
      ¬ (3 : Int) ^ (2 * B + 3 * d) ∣ (2 : Int) ^ j * C - (runA j x : Int) := by
  let p := 2 * B + 3 * d
  apply avoids_at_precision d p hC
  calc
    _ < 2 ^ p * (3 ^ d * 2 ^ B) :=
      Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hsize (Nat.pow_pos (by decide)))
        (Nat.two_pow_pos _)
    _ = 8 ^ B * 24 ^ d := by
      dsimp only [p]
      rw [Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
      have h₈ : ((2 : Nat) ^ 2) ^ B * 2 ^ B = 8 ^ B := by rw [← Nat.mul_pow]
      have h₂₄ : ((2 : Nat) ^ 3) ^ d * 3 ^ d = 24 ^ d := by rw [← Nat.mul_pow]
      calc
        _ = (((2 : Nat) ^ 2) ^ B * 2 ^ B) * (((2 : Nat) ^ 3) ^ d * 3 ^ d) := by ac_rfl
        _ = _ := by rw [h₈, h₂₄]
    _ ≤ 9 ^ B * 27 ^ d := Nat.mul_le_mul
      (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by dsimp only [p]; rw [Nat.pow_add, Nat.pow_mul, Nat.pow_mul]

/-- For every nonzero integer, a fixed precision works for all orbit
segments with the same even-step budget. -/
theorem avoids_nonzero_integer (d : Nat) (C : Int) (hC : C ≠ 0) :
    ∃ p, ∀ x j, j - d ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (2 : Int) ^ j * C - (runA j x : Int) := by
  refine ⟨2 * (C.natAbs.log2 + 1) + 3 * d, ?_⟩
  exact avoids_bounded_integer d _ hC ((Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _))

private theorem excludes_of_defect {p x j : Nat} {c : Int} (hcount : p ≤ oddCount x j)
    (havoid : ¬ (3 : Int) ^ p ∣ (2 : Int) ^ j * (1 - c) - (runA j x : Int)) :
    ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + c := by
  intro hdiv
  apply havoid
  let y : Int := acceleratedOrbit j x
  have hshift : (2 : Int) ^ j * (y + 1) =
      (3 : Int) ^ oddCount x j * ((x : Int) + 1) + (runA j x : Int) := by
    simpa only [y, Int.natCast_mul, Int.natCast_add, Int.natCast_pow,
      show ((3 : Nat) : Int) = 3 by rfl, show ((2 : Nat) : Int) = 2 by rfl,
      show ((1 : Nat) : Int) = 1 by rfl] using
      congrArg (fun n : Nat => (n : Int)) (shifted_affine_exact x j)
  have hfirst : (3 : Int) ^ p ∣ (3 : Int) ^ oddCount x j * ((x : Int) + 1) :=
    Int.dvd_trans (three_pow_dvd hcount) (Int.dvd_mul_right _ _)
  have hsecond : (3 : Int) ^ p ∣ (2 : Int) ^ j * (y + c) :=
    Int.dvd_trans hdiv (Int.dvd_mul_left _ _)
  have hdiff := Int.dvd_sub hfirst hsecond
  have he : (2 : Int) ^ j * (1 - c) - (runA j x : Int) =
      (3 : Int) ^ oddCount x j * ((x : Int) + 1) - (2 : Int) ^ j * (y + c) := by
    rw [Int.mul_sub, Int.mul_one, Int.mul_add (2 ^ j) y]
    rw [Int.mul_add, Int.mul_one] at hshift
    omega
  rw [he]
  exact hdiff

/-- A ternary precision whose scaled budget dominates the integer
offset excludes that displacement from the prefix image. -/
theorem excludes_displacement_with_budget (d p : Nat) (c : Int) (hc : c ≠ 1)
    (hsize : 2 ^ p * (3 ^ d * (1 - c).natAbs) < 3 ^ p) :
    ∀ x j, j - d ≤ oddCount x j → p ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + c := by
  intro x j hbudget hcount
  exact excludes_of_defect hcount
    (avoids_at_precision d p (by omega : (1 : Int) - c ≠ 0) hsize x j hbudget)

/-- An explicit precision excludes a signed displacement different
from one in a prefix with a bounded even-step budget. -/
theorem excludes_displacement_at_precision (d B : Nat) (c : Int) (hc : c ≠ 1)
    (hsize : (1 - c).natAbs < 2 ^ B) :
    ∀ x j, j - d ≤ oddCount x j → 2 * B + 3 * d ≤ oddCount x j →
      ¬ (3 : Int) ^ (2 * B + 3 * d) ∣ (acceleratedOrbit j x : Int) + c := by
  intro x j hbudget hcount
  exact excludes_of_defect hcount
    (avoids_bounded_integer d B (by omega : (1 : Int) - c ≠ 0) hsize x j hbudget)

/-- For every signed displacement other than one, a fixed precision
works uniformly in the prefix length. -/
theorem excludes_displacement (d : Nat) (c : Int) (hc : c ≠ 1) :
    ∃ p, ∀ x j, j - d ≤ oddCount x j → p ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + c := by
  let B := (1 - c).natAbs.log2 + 1
  have hsize : (1 - c).natAbs < 2 ^ B :=
    (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  exact ⟨2 * B + 3 * d, excludes_displacement_at_precision d B c hc hsize⟩

private theorem minus_one_precision (d : Nat) :
    2 ^ (3 * d + 1) * (3 ^ d * (-1 : Int).natAbs) < 3 ^ (3 * d + 1) := by
  change 2 ^ (3 * d + 1) * (3 ^ d * 1) < 3 ^ (3 * d + 1)
  rw [Nat.mul_one, Nat.pow_add 2, Nat.pow_add 3, Nat.pow_mul 2, Nat.pow_mul 3]
  change (8 ^ d * 2) * 3 ^ d < 27 ^ d * 3
  calc
    _ = 24 ^ d * 2 := by rw [Nat.mul_right_comm, ← Nat.mul_pow]
    _ < 24 ^ d * 3 := Nat.mul_lt_mul_of_pos_left (by decide) (Nat.pow_pos (by decide))
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)

/-- If the shifted defect is divisible by the full required ternary
power, all even steps occur in a short initial segment. -/
theorem trailing_odds_of_divisible_defect {d j x : Nat} (hd : 0 < d)
    (hbudget : j - d ≤ oddCount x j) (hdiv : 3 ^ (j - d) ∣ runA j x) :
    ∃ s, s ≤ j ∧ s ≤ 4 * d - 3 ∧ oddCount (acceleratedOrbit s x) (j - s) = j - s := by
  rcases last_even_with_parity x j with ⟨hodd, _⟩ | ⟨i, t, hlen, hcount, hA, he⟩
  · exact ⟨0, Nat.zero_le _, Nat.zero_le _, by simpa using hodd⟩
  · have hshort : i + 1 ≤ 4 * d - 3 := by
      apply Nat.le_of_not_gt
      intro hbad
      let P := 3 * (d - 1) + 1
      have hP : t + P ≤ j - d := by dsimp only [P]; omega
      have htarget := Nat.dvd_trans (Nat.pow_dvd_pow 3 hP) hdiv
      rw [hA, Nat.pow_add] at htarget
      have hn : 3 ^ P ∣ runA i x + 2 ^ i :=
        Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide : 0 < 3)) htarget
      have hint : (3 : Int) ^ P ∣ (runA i x : Int) + 2 ^ i := by
        simpa only [Int.natCast_pow, Int.natCast_add,
          show ((3 : Nat) : Int) = 3 by rfl, show ((2 : Nat) : Int) = 2 by rfl] using
          (Int.ofNat_dvd.mpr hn)
      have hneg := Int.dvd_neg.mpr hint
      have hpre : i - (d - 1) ≤ oddCount x i := by omega
      apply avoids_at_precision (d - 1) P (C := -1) (by decide) (minus_one_precision _)
        x i hpre
      have heq : (2 : Int) ^ i * (-1) - (runA i x : Int) = -((runA i x : Int) + 2 ^ i) := by
        rw [Int.mul_neg, Int.mul_one]
        omega
      rwa [heq]
    refine ⟨i + 1, by omega, hshort, ?_⟩
    have hpre : oddCount x (i + 1) = oddCount x i := by
      rw [Density.oddCount_succ_last, he, Nat.add_zero]
    have htail := AccumulatorArith.oddCount_add x (i + 1) t
    rw [← hlen, hpre, hcount] at htail
    rw [show j - (i + 1) = t by omega]
    exact (Nat.add_left_cancel htail).symm

end Collatz.BoundedEvenDefect
