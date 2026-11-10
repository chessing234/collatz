import Collatz.Strategy.SynchronousClasses
import Collatz.Strategy.HercherMerge
import Collatz.Strategy.ShiftedAffine

/-!
# Earliest equal-time meetings after an odd run

A target outside the residue two modulo three has one predecessor.
Such a step cannot create a new equal-time meeting. After two
halvings, Hercher's meeting has a synchronized form, and the
shifted accumulator distinguishes its possible smaller sources.
-/

namespace Collatz.SynchronousExcursion

open Collatz.SynchronousClasses Collatz.OrbitCapacity Collatz.RunAlgebra

private theorem even_preimage_only {x y : Nat} (hmod : y % 3 ≠ 2)
    (h : acceleratedStep x = y) : x = 2 * y := by
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · rw [acceleratedStep, if_pos he] at h
    omega
  · rw [acceleratedStep, if_neg (by omega)] at h
    omega

/-- A last step with a unique predecessor cannot improve the
finite least representative. -/
theorem leastAt_succ_of_non_two {n k : Nat}
    (hmod : acceleratedOrbit (k + 1) n % 3 ≠ 2) :
    leastAt (k + 1) n = leastAt k n := by
  let m := leastAt (k + 1) n
  let y := acceleratedOrbit (k + 1) n
  have hn : acceleratedStep (acceleratedOrbit k n) = y :=
    (acceleratedOrbit_succ_step k n).symm
  have hm : acceleratedStep (acceleratedOrbit k m) = y := by
    rw [← acceleratedOrbit_succ_step]
    exact leastAt_meets (k + 1) n
  have he : acceleratedOrbit k n = acceleratedOrbit k m :=
    (even_preimage_only hmod hn).trans (even_preimage_only hmod hm).symm
  exact Nat.le_antisymm (leastAt_antitone (Nat.le_succ k)) (leastAt_le he)

private theorem three_dvd_positive_pow {j : Nat} (hj : 0 < j) : 3 ∣ 3 ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [Nat.pow_succ']
  exact Nat.dvd_mul_right _ _

/-- The first halving after the initial odd run still cannot
produce a smaller equal-time partner. -/
theorem leastAt_first_halving {n u v : Nat} (hv : 0 < v) (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ v * u) : leastAt (v + 1) n = n := by
  have hupos : 0 < u := by omega
  let A := 3 ^ v * u
  have hpeak : acceleratedOrbit v n + 1 = A := DeviceSwap.run_climb v u n hupos hfac
  have hodd : A % 2 = 1 := by
    dsimp [A]
    rw [Nat.mul_mod, Arith.three_pow_odd, hu]
  have hthree : A % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (three_dvd_positive_pow hv) _)
  have hy : acceleratedOrbit (v + 1) n = (A - 1) / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos (by omega)]
    omega
  have hmod : acceleratedOrbit (v + 1) n % 3 ≠ 2 := by rw [hy]; omega
  rw [leastAt_succ_of_non_two hmod]
  have he : n = u * 2 ^ v - 1 := by rw [Nat.mul_comm]; omega
  rw [he]
  exact leastAt_last_in_period v u hupos

private theorem runA_all_odd {n k : Nat} (h : oddCount n k = k) : runA k n = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlast := Density.oddCount_succ_last n k
    have hcap := AffineExact.oddCount_le_self n k
    have ho : acceleratedOrbit k n % 2 = 1 := by omega
    rw [runA_odd ho, ih (by omega), Nat.mul_zero]

private theorem runA_one_even {n k : Nat} (h : oddCount n (k + 1) = k) :
    ∃ e, e ≤ k ∧ runA (k + 1) n = 3 ^ (k - e) * 2 ^ e := by
  induction k with
  | zero =>
    have hlast := Density.oddCount_succ_last n 0
    have he : acceleratedOrbit 0 n % 2 = 0 := by omega
    exact ⟨0, Nat.le_refl _, by rw [runA_even he]; simp⟩
  | succ k ih =>
    have hlast := Density.oddCount_succ_last n (k + 1)
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (k + 1) n) with he | ho
    · have hk : oddCount n (k + 1) = k + 1 := by omega
      exact ⟨k + 1, Nat.le_refl _, by rw [runA_even he, runA_all_odd hk]; simp⟩
    · have hk : oddCount n (k + 1) = k := by omega
      obtain ⟨e, hle, hA⟩ := ih hk
      refine ⟨e, Nat.le_trans hle (Nat.le_succ _), ?_⟩
      rw [runA_odd ho, hA, show k + 1 - e = k - e + 1 by omega, Nat.pow_succ']
      exact (Nat.mul_assoc ..).symm

private theorem runA_one_even_at_front {n k : Nat} (h : oddCount n (k + 1) = k)
    (hdiv : 3 ^ k ∣ runA (k + 1) n) : runA (k + 1) n = 3 ^ k := by
  obtain ⟨e, hle, hA⟩ := runA_one_even h
  have he : e = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hep
    obtain ⟨d, hd⟩ := hdiv
    have hsplit : 3 ^ k = 3 ^ (k - e) * 3 ^ e := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hle]
    rw [hA, hsplit, Nat.mul_assoc] at hd
    have hcancel : 2 ^ e = 3 ^ e * d :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hd
    have h3 : 3 ∣ 2 ^ e := by
      rw [hcancel]
      exact Nat.dvd_mul_right_of_dvd (three_dvd_positive_pow hep) _
    have hcop : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by decide : Nat.Coprime 3 2)
    have hbad := hcop.eq_one_of_dvd h3
    omega
  rw [hA, he]
  simp

private theorem pre_peak_sources {j u m : Nat} (hu : 0 < u)
    (hm : m < 2 ^ (j + 1) * u)
    (htarget : acceleratedOrbit (j + 1) m + 1 = 3 ^ j * u) :
    (3 ∣ u ∧ m + 1 = 2 ^ (j + 1) * (u / 3)) ∨ m + 2 = 2 ^ (j + 1) * u := by
  have hlow : j ≤ oddCount m (j + 1) := by
    apply Nat.le_of_not_gt
    intro hbad
    have himage := image_lt (k := j + 1) (c := u) (x := m) (by
      simpa only [Nat.mul_comm u (2 ^ (j + 1))] using hm)
    have hp := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mpr hbad
    have hlt : u * 3 ^ oddCount m (j + 1) < 3 ^ j * u := by
      rw [Nat.mul_comm (3 ^ j) u]
      exact Nat.mul_lt_mul_of_pos_left hp hu
    have hup := Nat.succ_le_of_lt himage
    omega
  have hmax := AffineExact.oddCount_le_self m (j + 1)
  have hshift := shifted_affine_exact m (j + 1)
  rw [htarget] at hshift
  have hpj : 0 < 3 ^ j := Nat.pow_pos (by decide)
  by_cases hfull : oddCount m (j + 1) = j + 1
  · have hEq : 3 ^ j * (2 ^ (j + 1) * u) = 3 ^ j * (3 * (m + 1)) := by
      calc
        _ = 2 ^ (j + 1) * (3 ^ j * u) := by ac_rfl
        _ = 3 ^ oddCount m (j + 1) * (m + 1) + runA (j + 1) m := hshift
        _ = _ := by rw [hfull, runA_all_odd hfull, Nat.add_zero, Nat.pow_succ, Nat.mul_assoc]
    have he := Nat.eq_of_mul_eq_mul_left hpj hEq
    have hdiv : 3 ∣ 2 ^ (j + 1) * u := by rw [he]; exact Nat.dvd_mul_right _ _
    have hcop : Nat.Coprime 3 (2 ^ (j + 1)) :=
      Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    have hdu := hcop.dvd_of_dvd_mul_left hdiv
    have hmul : 3 * (2 ^ (j + 1) * (u / 3)) = 2 ^ (j + 1) * u := by
      rw [Nat.mul_left_comm, Nat.mul_div_cancel' hdu]
    exact Or.inl ⟨hdu, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) (he.symm.trans hmul.symm)⟩
  · have hcount : oddCount m (j + 1) = j := by omega
    rw [hcount] at hshift
    have hdiv : 3 ^ j ∣ runA (j + 1) m := by
      apply (Nat.dvd_add_iff_right (Nat.dvd_mul_right (3 ^ j) (m + 1))).2
      rw [← hshift, Nat.mul_left_comm]
      exact Nat.dvd_mul_right _ _
    have hA := runA_one_even_at_front hcount hdiv
    rw [hA] at hshift
    have heq : 3 ^ j * (m + 2) = 3 ^ j * (2 ^ (j + 1) * u) := by
      calc
        _ = 3 ^ j * (m + 1) + 3 ^ j := by
          rw [show m + 2 = (m + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
        _ = 2 ^ (j + 1) * (3 ^ j * u) := hshift.symm
        _ = _ := by ac_rfl
    exact Or.inr (Nat.eq_of_mul_eq_mul_left hpj heq)

private theorem power_mul_succ (j u : Nat) : 3 ^ (j + 1) * u = 3 * (3 ^ j * u) := by
  rw [Nat.pow_succ']
  exact Nat.mul_assoc ..

private theorem two_halving_values {n u j : Nat} (hu : 0 < u)
    (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hmod : (3 ^ (j + 1) * u) % 4 = 1) :
    acceleratedOrbit (j + 2) n = (3 * (3 ^ j * u) - 1) / 2 ∧
      acceleratedOrbit (j + 3) n = (3 * (3 ^ j * u) - 1) / 4 := by
  have hpeak := DeviceSwap.run_climb (j + 1) u n hu hfac
  rw [power_mul_succ] at hpeak hmod
  have hfirst : acceleratedOrbit (j + 2) n = (3 * (3 ^ j * u) - 1) / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos (by omega)]
    omega
  refine ⟨hfirst, ?_⟩
  rw [acceleratedOrbit_succ_step, hfirst, acceleratedStep, if_pos (by omega)]
  omega

private theorem half_then_odd_values {m k A : Nat} (hA : A % 4 = 3)
    (hpeak : acceleratedOrbit k m + 1 = A) :
    acceleratedOrbit (k + 1) m = (A - 1) / 2 ∧
      acceleratedOrbit (k + 2) m = (3 * A - 1) / 4 := by
  have hmid : acceleratedOrbit (k + 1) m = (A - 1) / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos (by omega)]
    omega
  refine ⟨hmid, ?_⟩
  rw [acceleratedOrbit_succ_step, hmid, acceleratedStep, if_neg (by omega)]
  omega

private theorem hercher_synchronized {n u j : Nat} (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ (j + 1) * u) (hmod : (3 ^ (j + 1) * u) % 4 = 1) :
    acceleratedOrbit (j + 3) n = acceleratedOrbit (j + 3) (n - 1) := by
  have hmeet := HercherMerge.merge hu hfac hmod
  have hfac' : n + 1 = 2 * (2 ^ j * u) := by
    rw [hfac, Nat.pow_succ', Nat.mul_assoc]
  have hdouble : n - 1 = 2 * ((n - 1) / 2) := by omega
  have hstep : acceleratedOrbit 1 (n - 1) = (n - 1) / 2 := by
    conv => lhs; rw [hdouble]
    exact shortcut_double _
  calc
    _ = acceleratedOrbit (j + 2) ((n - 1) / 2) := hmeet
    _ = _ := by rw [← acceleratedOrbit_add (j + 2) 1, hstep]

private theorem smaller_second_halving_mates {n m u j : Nat} (hj : 0 < j)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hmod : (3 ^ (j + 1) * u) % 4 = 1) (hlt : m < n)
    (hmeet : acceleratedOrbit (j + 3) n = acceleratedOrbit (j + 3) m) :
    (3 ∣ u ∧ m + 1 = 2 ^ (j + 1) * (u / 3)) ∨ m + 2 = 2 ^ (j + 1) * u := by
  let A := 3 ^ j * u
  have huPos : 0 < u := by omega
  have ⟨hfirst, hsecond⟩ := two_halving_values huPos hfac hmod
  have hA4 : A % 4 = 3 := by rw [power_mul_succ] at hmod; omega
  have hA3 : A % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (three_dvd_positive_pow hj) _)
  let z := acceleratedOrbit (j + 2) m
  have hz : acceleratedStep z = (3 * A - 1) / 4 := by
    calc
      _ = acceleratedOrbit (j + 3) m := (acceleratedOrbit_succ_step (j + 2) m).symm
      _ = acceleratedOrbit (j + 3) n := hmeet.symm
      _ = _ := hsecond
  rcases Arith.mod_two_eq_zero_or_one z with he | ho
  · rw [acceleratedStep, if_pos he] at hz
    have hsame : acceleratedOrbit (j + 2) n = z := by rw [hfirst]; omega
    have hle := leastAt_le hsame
    have hleast := leastAt_first_halving (by omega : 0 < j + 1) hu hfac
    rw [hleast] at hle
    exact (Nat.not_le_of_gt hlt hle).elim
  · rw [acceleratedStep, if_neg (by omega)] at hz
    have hzval : z = (A - 1) / 2 := by omega
    have hzmod : z % 3 ≠ 2 := by rw [hzval]; omega
    have hprev : acceleratedStep (acceleratedOrbit (j + 1) m) = z :=
      (acceleratedOrbit_succ_step (j + 1) m).symm
    have hp := even_preimage_only hzmod hprev
    rw [hzval] at hp
    exact pre_peak_sources huPos (by omega) (by omega)

/-- At the second halving, the least equal-time partner is exact.
The usual partner is the predecessor `n-1`. When the cofactor
contains three, a longer odd run gives a still smaller partner. -/
theorem leastAt_second_halving {n u j : Nat} (hj : 0 < j)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ (j + 1) * u)
    (hmod : (3 ^ (j + 1) * u) % 4 = 1) :
    leastAt (j + 3) n =
      if 3 ∣ u then 2 ^ (j + 1) * (u / 3) - 1 else n - 1 := by
  let m := leastAt (j + 3) n
  let D := 2 ^ (j + 1)
  have hD : 0 < D := Nat.two_pow_pos _
  have hfac' : n + 1 = 2 * (2 ^ j * u) := by rw [hfac, Nat.pow_succ', Nat.mul_assoc]
  have hn : 0 < n := by omega
  have hmle : m ≤ n - 1 := leastAt_le (hercher_synchronized hu hfac hmod)
  have hm := smaller_second_halving_mates hj hu hfac hmod (by omega : m < n)
    (leastAt_meets (j + 3) n).symm
  change m = if 3 ∣ u then D * (u / 3) - 1 else n - 1
  by_cases hu3 : 3 ∣ u
  · rw [if_pos hu3]
    let p := D * (u / 3) - 1
    have hu' : 0 < u / 3 := by
      obtain ⟨t, ht⟩ := hu3
      rw [ht, Nat.mul_div_cancel_left _ (by decide)]
      omega
    have hp : p + 1 = D * (u / 3) := Nat.sub_add_cancel
      (Nat.succ_le_of_lt (Nat.mul_pos hD hu'))
    have hpeak := DeviceSwap.run_climb (j + 1) (u / 3) p hu' hp
    rw [Nat.pow_succ', Nat.mul_assoc, Nat.mul_left_comm 3, Nat.mul_div_cancel' hu3] at hpeak
    have hA : (3 ^ j * u) % 4 = 3 := by rw [power_mul_succ] at hmod; omega
    have hpath := (half_then_odd_values hA hpeak).2
    have htarget := (two_halving_values (by omega : 0 < u) hfac hmod).2
    have hpm : m ≤ p := leastAt_le (htarget.trans hpath.symm)
    have hthird : D * (u / 3) * 3 = D * u := by
      rw [Nat.mul_assoc, Nat.mul_comm (u / 3), Nat.mul_div_cancel' hu3]
    have hgreater : D * (u / 3) < D * u := by
      have hpositive := Nat.mul_pos hD hu'
      omega
    have hstrict : p < n - 1 := by
      change n + 1 = D * u at hfac
      have hpositive := Nat.mul_pos hD hu'
      omega
    rcases hm with ⟨_, hm'⟩ | hm'
    · change m = p
      exact Nat.add_right_cancel (hm'.trans hp.symm)
    · have he : m = n - 1 := by
        have heq := hm'.trans hfac.symm
        omega
      rw [he] at hpm
      exact (Nat.not_le_of_gt hstrict hpm).elim
  · rw [if_neg hu3]
    rcases hm with ⟨hbad, _⟩ | hm'
    · exact (hu3 hbad).elim
    · omega

/-- When the first halving is followed by an odd step, the two
steps after the initial run still give no smaller partner. -/
theorem leastAt_after_single_halving {n u v : Nat} (hv : 0 < v) (hu : u % 2 = 1)
    (hfac : n + 1 = 2 ^ v * u) (hmod : (3 ^ v * u) % 4 = 3) :
    leastAt (v + 2) n = n := by
  let A := 3 ^ v * u
  let m := leastAt (v + 2) n
  have huPos : 0 < u := by omega
  have hApos : 0 < A := Nat.mul_pos (Nat.pow_pos (by decide)) huPos
  have hpeak := DeviceSwap.run_climb v u n huPos hfac
  have ⟨hmid, htarget⟩ := half_then_odd_values hmod hpeak
  have hmeet := leastAt_meets (v + 2) n
  apply Nat.le_antisymm (leastAt_le rfl)
  apply Nat.le_of_not_gt
  intro hsmall
  let z := acceleratedOrbit (v + 1) m
  have hz : acceleratedStep z = (3 * A - 1) / 4 := by
    calc
      _ = acceleratedOrbit (v + 2) m := (acceleratedOrbit_succ_step (v + 1) m).symm
      _ = acceleratedOrbit (v + 2) n := hmeet
      _ = _ := htarget
  rcases Arith.mod_two_eq_zero_or_one z with he | ho
  · rw [acceleratedStep, if_pos he] at hz
    have hzval : z = (3 * A - 1) / 2 := by omega
    have hzmod : z % 3 ≠ 2 := by rw [hzval]; omega
    have hp : acceleratedStep (acceleratedOrbit v m) = z := (acceleratedOrbit_succ_step v m).symm
    have hprev := even_preimage_only hzmod hp
    rw [hzval] at hprev
    have hms : m < u * 2 ^ v := by rw [Nat.mul_comm]; omega
    have himage := image_lt (c := u) (k := v) (x := m) hms
    have hle : u * 3 ^ oddCount m v ≤ A := by
      dsimp [A]
      rw [Nat.mul_comm (3 ^ v) u]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (AffineExact.oddCount_le_self m v))
    have hbad := Nat.lt_of_lt_of_le himage hle
    omega
  · rw [acceleratedStep, if_neg (by omega)] at hz
    have hs : acceleratedOrbit (v + 1) n = z := by rw [hmid]; omega
    have hle := leastAt_le hs
    rw [leastAt_first_halving hv hu hfac] at hle
    exact Nat.not_le_of_gt hsmall hle

/-- The next halving also preserves the least source when the first
peak is three modulo eight in the shifted coordinate. -/
theorem leastAt_after_single_halving_mod_eight {n u v : Nat} (hv : 0 < v)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ v * u)
    (hmod : (3 ^ v * u) % 8 = 3) : leastAt (v + 3) n = n := by
  let A := 3 ^ v * u
  have hA4 : A % 4 = 3 := by omega
  have hpeak := DeviceSwap.run_climb v u n (by omega : 0 < u) hfac
  have hsecond := (half_then_odd_values hA4 hpeak).2
  have hthird : acceleratedOrbit (v + 3) n = (3 * A - 1) / 8 := by
    rw [acceleratedOrbit_succ_step, hsecond, acceleratedStep, if_pos (by omega)]
    omega
  have hnon : acceleratedOrbit (v + 3) n % 3 ≠ 2 := by rw [hthird]; omega
  rw [leastAt_succ_of_non_two hnon, leastAt_after_single_halving hv hu hfac hA4]

end Collatz.SynchronousExcursion
