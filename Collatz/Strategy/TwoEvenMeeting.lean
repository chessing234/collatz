import Collatz.Strategy.OddPrefixValuation

/-!
# Three even steps are necessary at a ternary-multiple odd prefix

For a path with one or two even steps, the first nonzero ternary
digit of its shifted defect has a fixed sign relative to the
dyadic clock. A smaller source meeting an odd prefix of a multiple
of three requires the opposite sign.
-/

namespace Collatz.TwoEvenMeeting

open Collatz.BoundedEvenDefect Collatz.RunAlgebra Collatz.OddRuns
  Collatz.OddPrefixValuation

private theorem two_pow_mod_ne_zero (j : Nat) : 2 ^ j % 3 ≠ 0 := by
  intro h
  have hd := Nat.dvd_of_mod_eq_zero h
  have hg : Nat.gcd 3 (2 ^ j) = 1 := (by decide : Nat.Coprime 3 2).pow_right j
  have he := Nat.gcd_eq_one_iff.mp hg 3 (Nat.dvd_refl _) hd
  contradiction

private theorem one_even_shape {j x : Nat} (hc : j - 1 ≤ oddCount x j) :
    runA j x = 0 ∨ ∃ p t, j = p + 1 + t ∧ runA j x = 3 ^ t * 2 ^ p := by
  rcases last_even x j with ⟨_, hzero⟩ | ⟨p, t, hj, hcount, hA⟩
  · exact Or.inl hzero
  · have hcap := AffineExact.oddCount_le_self x p
    have hfull : oddCount x p = p := by omega
    rw [runA_zero_of_full_oddCount hfull, Nat.zero_add] at hA
    exact Or.inr ⟨p, t, hj, hA⟩

/-- With at most two even steps, the leading ternary digit of the
nonzero defect is determined by its length and ternary valuation. -/
theorem leading_ternary_digit {j x : Nat} (hc : j - 2 ≤ oddCount x j) :
    runA j x = 0 ∨ ∃ t q, t < j ∧ runA j x = 3 ^ t * q ∧
      q % 3 = 2 ^ (j - t - 1) % 3 := by
  rcases last_even x j with ⟨_, hzero⟩ | ⟨i, t, hj, hcount, hA⟩
  · exact Or.inl hzero
  · rcases one_even_shape (show i - 1 ≤ oddCount x i by omega) with hzero | ⟨p, r, hi, hprev⟩
    · rw [hzero, Nat.zero_add] at hA
      exact Or.inr ⟨t, 2 ^ i, by omega, hA, by rw [show j - t - 1 = i by omega]⟩
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · rw [hr, Nat.pow_zero, Nat.one_mul] at hprev
        have hip : i = p + 1 := by omega
        have hsum : runA i x + 2 ^ i = 3 * 2 ^ p := by
          rw [hprev, hip, Nat.pow_succ']
          omega
        rw [hsum, ← Nat.mul_assoc, ← Nat.pow_succ] at hA
        exact Or.inr ⟨t + 1, 2 ^ p, by omega, hA, by
          rw [show j - (t + 1) - 1 = p by omega]⟩
      · let q := runA i x + 2 ^ i
        have hmod : runA i x % 3 = 0 := by
          rw [hprev]
          exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd
            (Nat.pow_dvd_pow 3 (show 1 ≤ r by omega)) _)
        refine Or.inr ⟨t, q, by omega, hA, ?_⟩
        dsimp only [q]
        rw [Nat.add_mod, hmod, Nat.zero_add, Nat.mod_mod, show j - t - 1 = i by omega]

private theorem leading_digit_unique {p t q b : Nat} (hq : q % 3 ≠ 0) (hb : b % 3 ≠ 0)
    (h : (3 ^ t * q) % 3 ^ (p + 1) = (3 ^ p * b) % 3 ^ (p + 1)) :
    t = p ∧ q % 3 = b % 3 := by
  have hpos (k : Nat) : 0 < 3 ^ k := Nat.pow_pos (by decide)
  rcases Nat.lt_trichotomy t p with hl | he | hr
  · have hmod := congrArg (· % 3 ^ (t + 1)) h
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega)),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega)),
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega : t + 1 ≤ p)) _),
      Nat.pow_succ, Nat.mul_mod_mul_left] at hmod
    exact (hq (Nat.mul_left_cancel (hpos t) (by simpa using hmod))).elim
  · subst t
    rw [Nat.pow_succ, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h
    exact ⟨rfl, Nat.mul_left_cancel (hpos p) h⟩
  · rw [Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega : p + 1 ≤ t)) _),
      Nat.pow_succ, Nat.mul_mod_mul_left] at h
    exact (hb (Nat.mul_left_cancel (hpos p) (by simpa using h.symm))).elim

/-- Any smaller source joining the odd prefix of a multiple of
three has at least three even steps, regardless of its time overhead. -/
theorem at_least_three_evens {i s n m : Nat} (hodd : OddRun n i) (hthree : 3 ∣ n)
    (hsmall : m < n) (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) :
    3 ≤ i + s - oddCount m (i + s) := by
  apply Nat.le_of_not_gt
  intro hbad
  have hcount := odd_count_gt_of_smaller_meeting hodd hsmall hmeet
  have hhom : 3 ^ (i + 1) ∣ 3 ^ oddCount m (i + s) * (m + 1) :=
    Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega)) _
  have hshift := shifted_affine_exact m (i + s)
  have hnshift := shifted_affine_exact n i
  rw [TwoRunOrder.oddCount_oddRun hodd, runA_zero_of_full_oddCount
    (TwoRunOrder.oddCount_oddRun hodd)] at hnshift
  simp only [Nat.add_zero] at hnshift
  rw [hmeet, Nat.pow_add, Nat.mul_right_comm, hnshift, Nat.mul_right_comm, Nat.mul_assoc] at hshift
  have hmod := congrArg (· % 3 ^ (i + 1)) hshift
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hhom, Nat.zero_add, Nat.mod_mod] at hmod
  have hnmod : n % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
  have hright : (3 ^ i * (2 ^ s * (n + 1))) % 3 ^ (i + 1) =
      (3 ^ i * 2 ^ s) % 3 ^ (i + 1) := by
    rw [Nat.pow_succ, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
      Nat.mul_mod, Nat.add_mod, hnmod]
    simp
  rw [hright] at hmod
  rcases leading_ternary_digit (x := m) (j := i + s) (by omega) with hz | ⟨t, q, ht, hA, hq⟩
  · rw [hz, Nat.zero_mod, Nat.pow_succ, Nat.mul_mod_mul_left] at hmod
    have hzero : 2 ^ s % 3 = 0 := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 3) (n := i))
      (by simpa using hmod)
    exact two_pow_mod_ne_zero s hzero
  · rw [hA] at hmod
    obtain ⟨hti, hdigit⟩ := leading_digit_unique (by rw [hq]; exact two_pow_mod_ne_zero _)
      (two_pow_mod_ne_zero s) hmod.symm
    subst t
    rw [show i + s - i - 1 = s - 1 by omega] at hq
    have hs : 0 < s := by have hc := AffineExact.oddCount_le_self m (i + s); omega
    have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
      calc
        _ = 2 ^ ((s - 1) + 1) := by congr 1; omega
        _ = _ := Nat.pow_succ'
    rw [hq, hpow, Nat.mul_mod] at hdigit
    have hsmallMod := Nat.mod_lt (2 ^ (s - 1)) (by decide : 0 < 3)
    have hnon := two_pow_mod_ne_zero (s - 1)
    omega

/-- Three even steps suffice on this entire arithmetic progression.
The smaller source meets after ten steps at the original first step. -/
theorem three_even_meeting (t : Nat) :
    0 < 1024 * t + 191 ∧ 1024 * t + 191 < 1458 * t + 273 ∧
      3 ∣ 1458 * t + 273 ∧
      oddCount (1024 * t + 191) 10 = 7 ∧
      acceleratedOrbit 10 (1024 * t + 191) = acceleratedOrbit 1 (1458 * t + 273) := by
  have hcount : oddCount (1024 * t + 191) 10 = 7 := by
    rw [Density.oddCount_mod, show (1024 * t + 191) % 2 ^ 10 = 191 by omega]
    decide
  have hleft : acceleratedOrbit 10 (1024 * t + 191) = 2187 * t + 410 := by
    have h := Congruence.accOrbit_pow_two_mul_add 10 t 191
    have ha : oddCount 191 10 = 7 := by decide
    have hx : acceleratedOrbit 10 191 = 410 := by decide
    simpa only [ha, hx] using h
  have hright : acceleratedOrbit 1 (1458 * t + 273) = 2187 * t + 410 := by
    change acceleratedStep (1458 * t + 273) = _
    rw [acceleratedStep, if_neg (by omega)]
    omega
  exact ⟨by omega, by omega, ⟨486 * t + 91, by omega⟩, hcount, hleft.trans hright.symm⟩

/-- The valuation and the compulsory three even steps give a lower
bound on the total shortcut-clock overhead. -/
theorem overhead_ge_valuation_add_four {i s t n m : Nat} (ht : 0 < t)
    (hodd : OddRun n i) (hdiv : 3 ^ t ∣ n) (hsmall : m < n)
    (hmeet : acceleratedOrbit (i + s) m = acceleratedOrbit i n) : t + 4 ≤ s := by
  have hthree : 3 ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 3 ht) hdiv
  have hevens := at_least_three_evens hodd hthree hsmall hmeet
  have ha := AffineExact.oddCount_le_self m (i + s)
  have hfail := excess_odd_steps_exceed_valuation hodd hsmall hmeet
  apply Nat.le_of_not_gt
  intro hbad
  exact hfail (Nat.dvd_trans (Nat.pow_dvd_pow 3 (by omega)) hdiv)

end Collatz.TwoEvenMeeting
