import Collatz.Strategy.SynchronousClasses
import Collatz.Exploration.ThreePowerUnits

/-!
# Compressing backward Collatz paths modulo a progression

If a backward path uses a odd steps, congruence modulo a modulus
enlarged by 3^a preserves all of its odd inverses. Long stretches
of doubling can therefore be reduced modulo a single period.
-/

namespace Collatz.BacktraceCompression

open Collatz.SynchronousClasses Collatz.Exploration.ThreePowerUnits

private theorem initial_block (x L : Nat) :
    (oddCount x L = 0 ∧ x = 2 ^ L * acceleratedOrbit L x) ∨
      ∃ e r u, L = e + 1 + r ∧ x = 2 ^ e * u ∧ u % 2 = 1 ∧
        acceleratedOrbit r (acceleratedStep u) = acceleratedOrbit L x ∧
        oddCount x L = oddCount (acceleratedStep u) r + 1 := by
  induction L generalizing x with
  | zero => exact Or.inl ⟨by simp, by simp⟩
  | succ L ih =>
    rcases Arith.mod_two_eq_zero_or_one x with he | ho
    · let z := acceleratedStep x
      have hx : x = 2 * z := by
        dsimp only [z]
        rw [acceleratedStep, if_pos he]
        omega
      have hc : oddCount x (L + 1) = oddCount z L := Congruence.oddCount_succ_of_even he L
      rcases ih z with ⟨hzero, hform⟩ | ⟨e, r, u, hlen, hstart, hu, hend, ha⟩
      · refine Or.inl ⟨hc.trans hzero, ?_⟩
        rw [acceleratedOrbit_succ, Nat.pow_succ', Nat.mul_assoc]
        exact hx.trans (congrArg (2 * ·) hform)
      · refine Or.inr ⟨e + 1, r, u, by omega, ?_, hu, hend, hc.trans ha⟩
        rw [Nat.pow_succ', Nat.mul_assoc]
        exact hx.trans (congrArg (2 * ·) hstart)
    · refine Or.inr ⟨0, L, x, by omega, by simp, ho, rfl, ?_⟩
      rw [Congruence.oddCount_succ_of_odd ho]

private theorem oddCount_halvings (e z : Nat) : oddCount (2 ^ e * z) e = 0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.pow_succ', Nat.mul_assoc, Congruence.oddCount_succ_of_even (by omega)]
    have h := shortcut_double (2 ^ e * z)
    change acceleratedStep (2 * (2 ^ e * z)) = 2 ^ e * z at h
    rw [h, ih]

private theorem residue_factor {d m u v : Nat} (h : d ∣ m)
    (hp : u % m = v % m) : u % d = v % d := by
  have hp' := congrArg (· % d) hp
  rwa [Nat.mod_mod_of_dvd _ h, Nat.mod_mod_of_dvd _ h] at hp'

private theorem reduce_doublings {m P e : Nat} (hm : 0 < m)
    (hp : 2 ^ P % m = 1 % m) : 2 ^ e % m = 2 ^ (e % P) % m := by
  by_cases he : m = 1
  · simp [he, Nat.mod_one]
  · have h := power_period_shift m P (e % P) (e / P) (by omega)
      (by simpa only [Nat.mod_eq_of_lt (by omega : 1 < m)] using hp)
    rwa [Nat.mod_add_div] at h

private theorem odd_preimage_transport {m u z : Nat} (hm : 0 < m) (hu : u % 2 = 1)
    (hres : z % (3 * m) = acceleratedStep u % (3 * m)) :
    ∃ u', u' % 2 = 1 ∧ acceleratedStep u' = z ∧ u' % m = u % m := by
  have hstep : 2 * acceleratedStep u = 3 * u + 1 := by
    rw [acceleratedStep, if_neg (by omega)]
    omega
  have hmod := congrArg (· % 3) hres
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 3 m),
    Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 3 m)] at hmod
  have hz : z % 3 = 2 := by omega
  let u' := (2 * z - 1) / 3
  have hnew : 3 * u' + 1 = 2 * z := by dsimp [u']; omega
  have hodd : u' % 2 = 1 := by omega
  have horbit : acceleratedStep u' = z := by
    rw [acceleratedStep, if_neg (by omega)]
    omega
  have hmatch : (3 * u' + 1) % (3 * m) = (3 * u + 1) % (3 * m) := by
    rw [hnew, ← hstep, Nat.mul_mod 2 z, Nat.mul_mod 2 (acceleratedStep u), hres]
  have reduce (t : Nat) : (3 * t + 1) % (3 * m) = 3 * (t % m) + 1 := by
    have hs : 3 * t + 1 = (3 * m) * (t / m) + (3 * (t % m) + 1) := by
      conv => lhs; rw [← Nat.div_add_mod t m, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
    rw [hs, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt t hm; omega)]
  rw [reduce u', reduce u] at hmatch
  exact ⟨u', hodd, horbit, by omega⟩

private theorem choose_not_greater {m B p e : Nat}
    (h : ∃ f < B, 2 ^ f % m = 2 ^ e % m ∧ f % p = e % p) :
    ∃ f < B, f ≤ e ∧ 2 ^ f % m = 2 ^ e % m ∧ f % p = e % p := by
  by_cases he : e < B
  · exact ⟨e, he, Nat.le_refl _, rfl, rfl⟩
  · obtain ⟨f, hf, hmod, hclock⟩ := h
    exact ⟨f, hf, by omega, hmod, hclock⟩

private theorem compress_of_representatives {m B p x L : Nat} (hm : 0 < m)
    (hp : ∀ e, ∃ f < B, 2 ^ f % (3 ^ oddCount x L * m) = 2 ^ e % (3 ^ oddCount x L * m) ∧
      f % p = e % p) :
    ∃ y K, y ≤ x ∧ K ≤ L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x ∧
      oddCount y K = oddCount x L ∧ K % p = L % p ∧ K < (oddCount x L + 1) * B := by
  generalize ha : oddCount x L = a at hp ⊢
  induction a generalizing x L m with
  | zero =>
    rcases initial_block x L with ⟨_, hx⟩ | ⟨e, r, u, _, _, _, _, hcount⟩
    · obtain ⟨e, hlt, hshort, hmod, hclock⟩ := choose_not_greater (hp L)
      let z := acceleratedOrbit L x
      let y := 2 ^ e * z
      have he : 2 ^ e % m = 2 ^ L % m := by simpa only [Nat.pow_zero, Nat.one_mul] using hmod
      have hres : y % m = x % m := by
        rw [hx]
        change (2 ^ e * z) % m = (2 ^ L * z) % m
        rw [Nat.mul_mod (2 ^ e), Nat.mul_mod (2 ^ L), he]
      have hsize : y ≤ x := by
        rw [hx]
        exact Nat.mul_le_mul_right z (Nat.pow_le_pow_right (by decide) hshort)
      exact ⟨y, e, hsize, hshort, hres, orbit_halvings e z, oddCount_halvings e z, hclock,
        by simpa using hlt⟩
    · omega
  | succ a ih =>
    rcases initial_block x L with ⟨hzero, _⟩ | ⟨e, r, u, htotal, hx, hu, hend, hcount⟩
    · omega
    · have hcount' : oddCount (acceleratedStep u) r = a := by omega
      have hp' : ∀ e, ∃ f < B, 2 ^ f % (3 ^ a * (3 * m)) = 2 ^ e % (3 ^ a * (3 * m)) ∧
          f % p = e % p := by
        simpa only [Nat.pow_succ, Nat.mul_assoc] using hp
      obtain ⟨z, K, hzle, hKle, hz, hval, hodd, hKclock, hlen⟩ :=
        ih (x := acceleratedStep u) (L := r) (m := 3 * m) (by omega) hcount' hp'
      obtain ⟨u', hu', hstep, huMod⟩ := odd_preimage_transport hm hu hz
      obtain ⟨f, hf, hfle, hfmod, hfclock⟩ := choose_not_greater (hp e)
      let y := 2 ^ f * u'
      let N := (K + 1) + f
      have hemod := residue_factor (Nat.dvd_mul_left _ _) hfmod
      have hres : y % m = x % m := by
        rw [hx]
        change (2 ^ f * u') % m = (2 ^ e * u) % m
        rw [Nat.mul_mod (2 ^ f), Nat.mul_mod (2 ^ e), hemod, huMod]
      have hy : acceleratedOrbit f y = u' := orbit_halvings f u'
      have hmeet : acceleratedOrbit N y = acceleratedOrbit L x := by
        change acceleratedOrbit ((K + 1) + f) y = _
        rw [← acceleratedOrbit_add, hy, acceleratedOrbit_succ, hstep, hval, hend]
      have hnew : oddCount y N = a + 1 := by
        rw [show N = f + (K + 1) by omega, AccumulatorArith.oddCount_add,
          hy, Congruence.oddCount_succ_of_odd hu', hstep, hodd, oddCount_halvings]
        omega
      have hule : u' ≤ u := by
        have odd_image (n : Nat) (hn : n % 2 = 1) : 2 * acceleratedStep n = 3 * n + 1 := by
          rw [acceleratedStep, if_neg (by omega)]
          omega
        have hfirst := odd_image u hu
        have hsecond := odd_image u' hu'
        rw [hstep] at hsecond
        omega
      have hsize : y ≤ x := by
        rw [hx]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hfle) hule
      have hclock : N % p = L % p := by
        change (K + 1 + f) % p = L % p
        rw [Nat.add_mod (K + 1) f, Nat.add_mod K 1, hKclock, hfclock,
          ← Nat.add_mod r 1, ← Nat.add_mod (r + 1) e,
          show r + 1 + e = L by omega]
      refine ⟨y, N, hsize, by omega, hres, hmeet, hnew, hclock, ?_⟩
      change K + 1 + f < (a + 1 + 1) * B
      rw [Nat.succ_mul]
      omega

/-- A positive doubling period modulo 3^a m bounds the compressed
depth by fewer than (a+1) periods. -/
theorem compress_ancestor_of_period {m P x L : Nat} (hm : 0 < m) (hP : 0 < P)
    (hp : 2 ^ P % (3 ^ oddCount x L * m) = 1 % (3 ^ oddCount x L * m)) :
    ∃ y K, y ≤ x ∧ K ≤ L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x ∧
      oddCount y K = oddCount x L ∧ K < (oddCount x L + 1) * P := by
  have hrep (e : Nat) : ∃ f < P,
      2 ^ f % (3 ^ oddCount x L * m) = 2 ^ e % (3 ^ oddCount x L * m) ∧ f % 1 = e % 1 := by
    exact ⟨e % P, Nat.mod_lt e hP,
      (reduce_doublings (Nat.mul_pos (Nat.pow_pos (by decide)) hm) hp).symm,
      by simp only [Nat.mod_one]⟩
  obtain ⟨y, K, hy, hK, hres, htarget, hodd, _, hbound⟩ := compress_of_representatives hm hrep
  exact ⟨y, K, hy, hK, hres, htarget, hodd, hbound⟩

private theorem repeated_power (m p : Nat) (hm : 0 < m) (hp : 0 < p) :
    ∃ i j, i < j ∧ j ≤ p * m ∧ 2 ^ i % m = 2 ^ j % m ∧ i % p = j % p := by
  let encode := fun e => p * (2 ^ e % m) + e % p
  let xs := (List.range (p * m + 1)).map encode
  have value (e : Nat) : encode e / p = 2 ^ e % m := by
    dsimp only [encode]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]
  have clock (e : Nat) : encode e % p = e % p := by
    dsimp only [encode]
    rw [Nat.mul_add_mod, Nat.mod_mod]
  by_cases he : ∃ i j, i < j ∧ j ≤ p * m ∧ 2 ^ i % m = 2 ^ j % m ∧ i % p = j % p
  · exact he
  exfalso
  have hnd : xs.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hlt hsame
    have hj' : j < p * m + 1 := by simpa [xs] using hj
    have hval (k : Nat) (hk : k < xs.length) : xs[k] = encode k := by
      simp [xs]
    rw [hval i hi, hval j hj] at hsame
    have hv := congrArg (· / p) hsame
    have hc := congrArg (· % p) hsame
    rw [value, value] at hv
    rw [clock, clock] at hc
    exact he ⟨i, j, hlt, by omega, hv, hc⟩
  have hsub : xs ⊆ List.range (p * m) := by
    intro u hu
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hu
    apply List.mem_range.mpr
    have hval := Nat.mul_le_mul_left p (Nat.succ_le_of_lt (Nat.mod_lt (2 ^ e) hm))
    rw [Nat.mul_succ] at hval
    have hclock := Nat.mod_lt e hp
    dsimp only [encode]
    omega
  have hlen := hnd.length_le_of_subset hsub
  simp [xs] at hlen
  omega

private theorem power_representative (m p e : Nat) (hm : 0 < m) (hp : 0 < p) :
    ∃ f < p * m, 2 ^ f % m = 2 ^ e % m ∧ f % p = e % p := by
  obtain ⟨i, j, hlt, hj, hcollision, hclock⟩ := repeated_power m p hm hp
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e < p * m
    · exact ⟨e, he, rfl, rfl⟩
    · have hshort : e - j + i < e := by omega
      have hres : 2 ^ (e - j + i) % m = 2 ^ e % m := by
        conv => rhs; rw [← Nat.sub_add_cancel (by omega : j ≤ e)]
        rw [Nat.pow_add, Nat.pow_add, Nat.mul_mod (2 ^ (e - j)),
          Nat.mul_mod (2 ^ (e - j)) (2 ^ j), hcollision]
      have htime : (e - j + i) % p = e % p := by
        conv => rhs; rw [← Nat.sub_add_cancel (by omega : j ≤ e)]
        rw [Nat.add_mod (e - j) i, Nat.add_mod (e - j) j, hclock]
      obtain ⟨f, hf, hval, hmod⟩ := ih (e - j + i) hshort
      exact ⟨f, hf, hval.trans hres, hmod.trans htime⟩

/-- A shortened backtrace can preserve the time residue as well as
the source residue, target and number of odd steps. -/
theorem compress_ancestor_with_clock {m p x L : Nat} (hm : 0 < m) (hp : 0 < p) :
    ∃ y K, y ≤ x ∧ K ≤ L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x ∧
      oddCount y K = oddCount x L ∧ K % p = L % p ∧
      K < (oddCount x L + 1) * (p * (3 ^ oddCount x L * m)) := by
  apply compress_of_representatives hm
  intro e
  exact power_representative _ p e (Nat.mul_pos (Nat.pow_pos (by decide)) hm) hp

/-- Every finite backtrace can be shortened while keeping both its
endpoint and its source residue, including for even moduli. -/
theorem compress_ancestor {m x L : Nat} (hm : 0 < m) :
    ∃ y K, y ≤ x ∧ K ≤ L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x ∧
      oddCount y K = oddCount x L ∧ K < (oddCount x L + 1) * (3 ^ oddCount x L * m) := by
  obtain ⟨y, K, hy, hK, hres, htarget, hodd, _, hbound⟩ :=
    compress_ancestor_with_clock (p := 1) (x := x) (L := L) hm (by decide)
  exact ⟨y, K, hy, hK, hres, htarget, hodd, by simpa only [Nat.one_mul] using hbound⟩

/-- At a periodic target, preserving the time residue also preserves
the equal-time meeting class of the source. -/
theorem compress_periodic_target {m p x L : Nat} (hm : 0 < m) (hp : 0 < p)
    (hcycle : acceleratedOrbit p (acceleratedOrbit L x) = acceleratedOrbit L x) :
    ∃ y K, y ≤ x ∧ K ≤ L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x ∧
      acceleratedOrbit L y = acceleratedOrbit L x ∧
      K < (oddCount x L + 1) * (p * (3 ^ oddCount x L * m)) := by
  obtain ⟨y, K, hy, hK, hres, htarget, _, hclock, hbound⟩ :=
    compress_ancestor_with_clock (x := x) (L := L) hm hp
  have hd : p ∣ L - K := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hclock.symm)
  obtain ⟨t, ht⟩ := hd
  have repeat_cycle (r : Nat) :
      acceleratedOrbit (p * r) (acceleratedOrbit L x) = acceleratedOrbit L x := by
    induction r with
    | zero => simp
    | succ r ih => rw [Nat.mul_succ, ← acceleratedOrbit_add, hcycle, ih]
  have hmeet : acceleratedOrbit L y = acceleratedOrbit L x := by
    calc
      _ = acceleratedOrbit (L - K) (acceleratedOrbit K y) := by
        rw [acceleratedOrbit_add, Nat.sub_add_cancel hK]
      _ = _ := by rw [htarget, ht, repeat_cycle]
  exact ⟨y, K, hy, hK, hres, htarget, hmeet, hbound⟩

/-- On a repeat-free orbit segment, shortening below its length
forces a genuinely smaller source in the same progression. -/
theorem strictly_smaller_of_long_backtrace {m x L : Nat} (hm : 0 < m)
    (hinj : ∀ i, i < L → acceleratedOrbit i x ≠ acceleratedOrbit L x)
    (hlong : (oddCount x L + 1) * (3 ^ oddCount x L * m) ≤ L) :
    ∃ y K, y < x ∧ K < L ∧ y % m = x % m ∧ acceleratedOrbit K y = acceleratedOrbit L x := by
  obtain ⟨y, K, hle, _, hres, he, _, hK⟩ := compress_ancestor (x := x) (L := L) hm
  have hlt := Nat.lt_of_lt_of_le hK hlong
  have hne : y ≠ x := by
    intro hbad
    rw [hbad] at he
    exact hinj K hlt he
  exact ⟨y, K, Nat.lt_of_le_of_ne hle hne, hlt, hres, he⟩

end Collatz.BacktraceCompression
