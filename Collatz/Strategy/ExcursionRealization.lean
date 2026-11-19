import Collatz.Strategy.ExcursionRays
import Collatz.Strategy.AccumulatorArith

/-!
# Affine reconstruction of an excursion word

An odd endpoint and the affine identity are sufficient for a
word with positive run lengths. Coprimality lets the proof
recover the preceding integer at each boundary. This gives
a canonical realization for every such word.
-/

namespace Collatz.ExcursionRays

open Collatz.ExcursionBudget Collatz.ExcursionMap

/-- Every run has both an odd part and a halving part. -/
def PositiveProfile (rs : List Run) : Prop :=
  ∀ r ∈ rs, 0 < r.oddSteps ∧ 0 < r.halvings

private theorem two_pow_even {k : Nat} (hk : 0 < k) : (2 : Nat) ^ k % 2 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  simpa only [Nat.pow_one] using Nat.pow_dvd_pow 2 (show 1 ≤ k from hk)

private theorem excursion_of_affine {x y v W : Nat} (hv : 0 < v) (hW : 0 < W)
    (hy : y % 2 = 1) (h : 3 ^ v * x + (3 ^ v - 2 ^ v) = 2 ^ (v + W) * y) :
    ∃ u, IsExcursion x v u W y := by
  have hA : 2 ^ v + (3 ^ v - 2 ^ v) = 3 ^ v :=
    Nat.add_sub_of_le (Collatz.Arith.two_pow_le_three_pow v)
  have hR : 2 ^ v * (2 ^ W * y + 1) = 2 ^ (v + W) * y + 2 ^ v := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc]
  have hshift : 3 ^ v * (x + 1) = 2 ^ v * (2 ^ W * y + 1) := by
    rw [Nat.mul_add, Nat.mul_one, hR]
    omega
  have hdiv : 2 ^ v ∣ 3 ^ v * (x + 1) := ⟨_, hshift⟩
  have hcop := (by decide : Nat.Coprime 2 3).pow v v
  obtain ⟨u, hu⟩ := hcop.dvd_of_dvd_mul_left hdiv
  have hpeak : 3 ^ v * u = 2 ^ W * y + 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos v)
    rwa [hu, Nat.mul_left_comm (3 ^ v)] at hshift
  have hmod : (3 ^ v * u) % 2 = u % 2 := by
    rw [Nat.mul_mod, Collatz.Arith.three_pow_odd, Nat.one_mul, Nat.mod_mod]
  have hr : (2 ^ W * y + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, two_pow_even hW]
    simp
  have huodd : u % 2 = 1 := hmod.symm.trans ((congrArg (· % 2) hpeak).trans hr)
  have hx : (x + 1) % 2 = 0 := by
    rw [hu, Nat.mul_mod, two_pow_even hv]
    simp
  exact ⟨u, by omega, huodd, hy, hv, hW, hu, hpeak⟩

/-- The affine identity with an odd endpoint reconstructs the
entire excursion trace, including every intermediate boundary. -/
theorem trace_of_affine {n e : Nat} {rs : List Run} (hvalid : PositiveProfile rs)
    (hodd : e % 2 = 1)
    (ha : 3 ^ ExcursionBudget.oddCount rs * n + offset rs = 2 ^ time rs * e) :
    Trace n e rs := by
  induction rs generalizing e with
  | nil =>
    have he : n = e := by simpa [ExcursionBudget.oddCount, offset, time] using ha
    subst e
    exact .nil
  | cons r rs ih =>
    let v := r.oddSteps
    let W := r.halvings
    let P := 3 ^ ExcursionBudget.oddCount rs * n + offset rs
    let B := 2 ^ time rs
    let A := 3 ^ v
    have hvW := hvalid r List.mem_cons_self
    have hstep : A * P + B * (A - 2 ^ v) = B * (2 ^ (v + W) * e) := by
      calc
        _ = 3 ^ ExcursionBudget.oddCount (r :: rs) * n + offset (r :: rs) := by
          simp only [A, P, B, v, ExcursionBudget.oddCount, offset, Nat.pow_add, Nat.mul_add]
          ac_rfl
        _ = 2 ^ time (r :: rs) * e := ha
        _ = _ := by
          simp only [B, v, W, time, Nat.pow_add]
          ac_rfl
    have hdiv : B ∣ A * P := by
      apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right B (A - 2 ^ v))).mpr
      exact hstep.symm ▸ Nat.dvd_mul_right B _
    have hcop : Nat.Coprime B A := (by decide : Nat.Coprime 2 3).pow _ _
    obtain ⟨x, hx⟩ := hcop.dvd_of_dvd_mul_left hdiv
    have hs : A * x + (A - 2 ^ v) = 2 ^ (v + W) * e := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (time rs))
      rw [hx, Nat.mul_left_comm A B, ← Nat.mul_add] at hstep
      exact hstep
    obtain ⟨u, hu⟩ := excursion_of_affine hvW.1 hvW.2 hodd hs
    have hpre := ih (fun r hr => hvalid r (List.mem_cons_of_mem _ hr)) hu.1 hx
    exact .step hpre hu

private def powerModLoop (base modulus : Nat) : Nat → Nat → Nat
  | 0, _ => 1 % modulus
  | fuel + 1, exponent =>
    let half := powerModLoop base modulus fuel (exponent / 2)
    let square := (half * half) % modulus
    if exponent % 2 = 0 then square else (base * square) % modulus

private theorem powerModLoop_spec (base modulus fuel exponent : Nat)
    (h : exponent < 2 ^ fuel) :
    powerModLoop base modulus fuel exponent = base ^ exponent % modulus := by
  induction fuel generalizing exponent with
  | zero =>
    have he : exponent = 0 := by simpa using h
    subst exponent
    rfl
  | succ fuel ih =>
    have hh : exponent / 2 < 2 ^ fuel := by
      rw [Nat.pow_succ] at h
      omega
    rw [powerModLoop, ih _ hh]
    have hs : ((base ^ (exponent / 2) % modulus) * (base ^ (exponent / 2) % modulus)) % modulus =
        base ^ (exponent / 2 + exponent / 2) % modulus := by
      rw [← Nat.mul_mod, ← Nat.pow_add]
    rw [hs]
    have hsplit := Nat.div_add_mod exponent 2
    by_cases he : exponent % 2 = 0
    · rw [if_pos he, show exponent / 2 + exponent / 2 = exponent by omega]
    · rw [if_neg he, Nat.mul_mod_mod, ← Nat.pow_succ']
      have hi : (exponent / 2 + exponent / 2).succ = exponent := by omega
      rw [hi]

private def powerMod (base modulus exponent : Nat) : Nat :=
  powerModLoop base modulus (exponent.log2 + 1) exponent

private theorem powerMod_spec (base modulus exponent : Nat) :
    powerMod base modulus exponent = base ^ exponent % modulus := by
  apply powerModLoop_spec
  exact Nat.lt_log2_self

private def inverseThree (modulus : Nat) : Nat :=
  if modulus % 3 = 1 then (2 * modulus + 1) / 3 else (modulus + 1) / 3

private theorem inverseThree_spec (k : Nat) :
    (3 * inverseThree (2 ^ k)) % 2 ^ k = 1 % 2 ^ k := by
  let M := 2 ^ k
  change (3 * inverseThree M) % M = 1 % M
  rcases AccumulatorArith.two_pow_mod_three k with h | h
  · change M % 3 = 1 at h
    rw [inverseThree, if_pos h, show 3 * ((2 * M + 1) / 3) = 2 * M + 1 by omega,
      Nat.add_comm (2 * M), Nat.mul_comm 2 M, Nat.add_mul_mod_self_left]
  · have hne : M % 3 ≠ 1 := by omega
    rw [inverseThree, if_neg hne, show 3 * ((M + 1) / 3) = M + 1 by omega,
      Nat.add_comm M, Nat.add_mod_right]

/-- Compute the canonical source by modular exponentiation. The
inverse of three modulo the dyadic period has a closed form. -/
def canonicalSource (rs : List Run) : Nat :=
  let B := 2 ^ time rs
  let M := B * 2
  let target := B + M - offset rs % M
  (powerMod (inverseThree M) M (ExcursionBudget.oddCount rs) * target) % M

/-- The endpoint given by the affine identity at the canonical source. -/
def canonicalLanding (rs : List Run) : Nat :=
  (3 ^ ExcursionBudget.oddCount rs * canonicalSource rs + offset rs) / 2 ^ time rs

theorem canonical_source_spec (rs : List Run) :
    canonicalSource rs < 2 ^ time rs * 2 ∧ canonicalLanding rs % 2 = 1 ∧
      3 ^ ExcursionBudget.oddCount rs * canonicalSource rs + offset rs =
        2 ^ time rs * canonicalLanding rs := by
  let a := ExcursionBudget.oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let M := B * 2
  let C := offset rs
  let target := B + M - C % M
  let inverse := powerMod (inverseThree M) M a
  let n := canonicalSource rs
  have hB : 0 < B := Nat.two_pow_pos _
  have hM : 0 < M := Nat.mul_pos hB (by decide)
  have hinv3 : (3 * inverseThree M) % M = 1 % M := by
    have h : M = 2 ^ (time rs + 1) := (Nat.pow_succ ..).symm
    rw [h]
    exact inverseThree_spec _
  have hinv : (A * inverse) % M = 1 % M := by
    dsimp only [A, inverse]
    rw [powerMod_spec, Nat.mul_mod_mod, ← Nat.mul_pow, Nat.pow_mod (3 * inverseThree M), hinv3,
      ← Nat.pow_mod 1, Nat.one_pow]
  have htarget : target + C % M = B + M :=
    Nat.sub_add_cancel (by have := Nat.mod_lt C hM; omega)
  have hn : n = (inverse * target) % M := rfl
  have hmul : (A * n) % M = target % M := by
    rw [hn, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod (A * inverse),
      hinv, Nat.mod_mul_mod, Nat.one_mul]
  have hres : (A * n + C) % M = B := by
    calc
      _ = (target % M + C % M) % M := by rw [Nat.add_mod, hmul]
      _ = (target + C % M) % M := by
        rw [Nat.add_mod target (C % M), Nat.mod_mod]
      _ = _ := by
        rw [htarget, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
  let q := (A * n + C) / M
  have h : B + (B * 2) * q = A * n + C := by
    have h := Nat.mod_add_div (A * n + C) M
    rwa [hres] at h
  have ha : A * n + C = B * (2 * q + 1) := by
    rw [← h, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
    exact Nat.add_comm _ _
  have he : canonicalLanding rs = 2 * q + 1 := by
    change (A * n + C) / B = 2 * q + 1
    rw [ha, Nat.mul_div_cancel_left _ hB]
  refine ⟨?_, by rw [he]; omega, ?_⟩
  · change n < M
    rw [hn]
    exact Nat.mod_lt _ hM
  · rw [he]
    exact ha

/-- Each positive excursion profile has a computable canonical
realization with an odd landing. -/
theorem canonical_trace_of_positive_profile {rs : List Run} (h : PositiveProfile rs) :
    Trace (canonicalSource rs) (canonicalLanding rs) rs := by
  have hs := canonical_source_spec rs
  exact trace_of_affine h hs.2.1 hs.2.2

/-- The executable source residue describes every realization of a
positive nonempty profile. -/
theorem realizes_iff_canonical_source {n : Nat} {r : Run} {rs : List Run}
    (h : PositiveProfile (r :: rs)) :
    (∃ e, Trace n e (r :: rs)) ↔ n % (2 ^ time (r :: rs) * 2) = canonicalSource (r :: rs) := by
  rw [realizes_iff_mod (canonical_trace_of_positive_profile h)]
  rw [Nat.mod_eq_of_lt (canonical_source_spec (r :: rs)).1]

end Collatz.ExcursionRays
