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

/-- The shifted defect is zero for an all-odd word. Otherwise its
last even step separates the previous defect from the trailing odds. -/
theorem last_even (x j : Nat) :
    (oddCount x j = j ∧ runA j x = 0) ∨
      ∃ i t, j = i + 1 + t ∧ oddCount x j = oddCount x i + t ∧
        runA j x = 3 ^ t * (runA i x + 2 ^ i) := by
  induction j with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ j ih =>
    have hcount := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · exact Or.inr ⟨j, 0, by omega, by omega, by rw [runA_even he]; simp⟩
    · rcases ih with ⟨ha, hzero⟩ | ⟨i, t, hlen, ha, hA⟩
      · exact Or.inl ⟨by omega, by rw [runA_odd ho, hzero, Nat.mul_zero]⟩
      · refine Or.inr ⟨i, t + 1, by omega, by omega, ?_⟩
        rw [runA_odd ho, hA, Nat.pow_succ', Nat.mul_assoc]

private theorem bounded (f : Nat → Nat) (B : Nat) :
    ∃ K, ∀ t, t < B → f t ≤ K := by
  induction B with
  | zero => exact ⟨0, fun t ht => (Nat.not_lt_zero t ht).elim⟩
  | succ B ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max K (f B), fun t ht => ?_⟩
    by_cases he : t = B
    · rw [he]
      exact Nat.le_max_right _ _
    · exact Nat.le_trans (hK t (by omega)) (Nat.le_max_left _ _)

private theorem three_pow_dvd {a b : Nat} (h : a ≤ b) : (3 : Int) ^ a ∣ 3 ^ b := by
  simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
    (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 3 h))

private theorem cancel_dyadic {C : Int} {p j : Nat}
    (h : (3 : Int) ^ p ∣ (2 : Int) ^ j * C) : (3 : Int) ^ p ∣ C := by
  have hnat := Int.natAbs_dvd_natAbs.mpr h
  apply Int.natAbs_dvd_natAbs.mp
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hnat ⊢
  exact ((by decide : Nat.Coprime 3 2).pow p j).dvd_of_dvd_mul_left hnat

private theorem integer_precision (C : Int) (hC : C ≠ 0) :
    ¬ (3 : Int) ^ C.natAbs ∣ C := by
  intro h
  have hd := Int.natAbs_dvd_natAbs.mpr h
  have hn : 0 < C.natAbs := by omega
  simp only [Int.natAbs_pow] at hd
  exact Nat.not_le_of_gt (Nat.lt_pow_self (by decide : 1 < 3)) (Nat.le_of_dvd hn hd)

private def residual (C : Int) (t : Nat) : Int := (2 : Int) ^ (t + 1) * (C / 3 ^ t) - 1

private theorem residual_ne_zero (C : Int) (t : Nat) : residual C t ≠ 0 := by
  unfold residual
  rw [Int.pow_succ, Int.mul_right_comm ((2 : Int) ^ t) 2, Int.mul_comm _ 2]
  omega

/-- With a fixed even-step budget, the normalized shifted defect
stays away from every nonzero integer modulo a sufficiently large
power of three, uniformly over the length of the orbit segment. -/
theorem avoids_nonzero_integer (d : Nat) :
    ∀ C : Int, C ≠ 0 → ∃ p, ∀ x j, j - d ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (2 : Int) ^ j * C - (runA j x : Int) := by
  induction d with
  | zero =>
    intro C hC
    refine ⟨C.natAbs, fun x j hodd hdvd => ?_⟩
    rcases last_even x j with ⟨_, hzero⟩ | ⟨i, t, hlen, ha, _⟩
    · rw [hzero] at hdvd
      simp only [Int.ofNat_zero, Int.sub_zero] at hdvd
      exact integer_precision C hC (cancel_dyadic hdvd)
    · have hcap := AffineExact.oddCount_le_self x i
      omega
  | succ d ih =>
    intro C hC
    let B := C.natAbs
    let precision := fun t => Classical.choose (ih (residual C t) (residual_ne_zero C t))
    have hprecision (t : Nat) := Classical.choose_spec (ih (residual C t) (residual_ne_zero C t))
    obtain ⟨K, hK⟩ := bounded precision B
    refine ⟨B + K, fun x j hodd hdvd => ?_⟩
    have hdB := Int.dvd_trans (three_pow_dvd (show B ≤ B + K by omega)) hdvd
    rcases last_even x j with ⟨_, hzero⟩ | ⟨i, t, hlen, ha, hA⟩
    · rw [hzero] at hdB
      simp only [Int.ofNat_zero, Int.sub_zero] at hdB
      exact integer_precision C hC (cancel_dyadic hdB)
    · have hAint : (runA j x : Int) = (3 : Int) ^ t * ((runA i x : Int) + 2 ^ i) := by
        simpa only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow,
          show ((3 : Nat) : Int) = 3 by rfl, show ((2 : Nat) : Int) = 2 by rfl] using
          congrArg (fun n : Nat => (n : Int)) hA
      have hCsmall (b : Nat) (hb : b ≤ B + K) (hbt : b ≤ t) : (3 : Int) ^ b ∣ C := by
        have hdiff := Int.dvd_trans (three_pow_dvd hb) hdvd
        have hpart : (3 : Int) ^ b ∣ (runA j x : Int) := by
          rw [hAint]
          exact Int.dvd_trans (three_pow_dvd hbt) (Int.dvd_mul_right _ _)
        have hprod := Int.dvd_add hdiff hpart
        rw [Int.sub_add_cancel] at hprod
        exact cancel_dyadic hprod
      have ht : t < B := by
        apply Nat.lt_of_not_ge
        intro ht
        exact integer_precision C hC (hCsmall B (by omega) ht)
      let R := C / (3 : Int) ^ t
      have hCR : C = (3 : Int) ^ t * R :=
        (Int.mul_ediv_cancel' (hCsmall t (by omega) (Nat.le_refl _))).symm
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
      have hbound := hK t ht
      have hp : t + precision t ≤ B + K := by omega
      have hdiv := Int.dvd_trans (three_pow_dvd hp) hdvd
      rw [hfactor, Int.pow_add] at hdiv
      have hnon : (3 : Int) ^ t ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide : (0 : Int) < 3))
      have hpre : i - d ≤ oddCount x i := by omega
      exact hprecision t x i hpre (Int.dvd_of_mul_dvd_mul_left hnon hdiv)

/-- For every signed integer displacement other than one, a fixed
ternary precision excludes that displacement in a sufficiently
odd prefix with a fixed even-step budget. -/
theorem excludes_displacement (d : Nat) (c : Int) (hc : c ≠ 1) :
    ∃ p, ∀ x j, j - d ≤ oddCount x j → p ≤ oddCount x j →
      ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + c := by
  obtain ⟨p, hp⟩ := avoids_nonzero_integer d (1 - c) (by omega)
  refine ⟨p, fun x j hbudget hcount hdiv => ?_⟩
  apply hp x j hbudget
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

end Collatz.BoundedEvenDefect
