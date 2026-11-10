import Collatz.Strategy.SynchronousExcursion
import Collatz.Strategy.LiftExponent

/-!
# Uniform reductions between odd-run lengths

When two shifted peaks differ by a power of three, a finite parity
calculation can certify that their tails meet across an entire dyadic
residue class. This gives reductions between different odd-run lengths.
-/

namespace Collatz.PeakContraction

open Collatz.Reach Collatz.SynchronousClasses

/-- A meeting at the low part, with the multiplier identity needed to
preserve it as the common high part varies. -/
def Certificate (k d r : Nat) : Prop :=
  oddCount (r - 1) k = oddCount (3 ^ d * r - 1) k + d ∧
    acceleratedOrbit k (3 ^ d * r - 1) = acceleratedOrbit k (r - 1)

instance (k d r : Nat) : Decidable (Certificate k d r) := by
  unfold Certificate
  infer_instance

private theorem lift_peaks (k d r q : Nat) (hr : 0 < r) :
    3 ^ d * (2 ^ k * q + r) - 1 = 2 ^ k * (3 ^ d * q) + (3 ^ d * r - 1) ∧
      2 ^ k * q + r - 1 = 2 ^ k * q + (r - 1) := by
  have hpos : 1 ≤ 3 ^ d * r := Nat.mul_pos (Nat.pow_pos (by decide)) hr
  constructor
  · rw [Nat.mul_add, Nat.add_sub_assoc hpos]
    congr 1
    ac_rfl
  · omega

/-- A single certificate proves a meeting for every lift of the small peak. -/
theorem meet_of_certificate {k d r B : Nat} (hr : 0 < r)
    (hB : B % 2 ^ k = r) (hc : Certificate k d r) :
    acceleratedOrbit k (3 ^ d * B - 1) = acceleratedOrbit k (B - 1) := by
  let q := B / 2 ^ k
  have hsplit : 2 ^ k * q + r = B := by
    rw [← hB]
    exact Nat.div_add_mod B (2 ^ k)
  have ⟨hbig, hsmall⟩ := lift_peaks k d r q hr
  rw [hsplit] at hbig hsmall
  rw [hbig, hsmall, Congruence.accOrbit_pow_two_mul_add,
    Congruence.accOrbit_pow_two_mul_add, hc.1, hc.2, Nat.pow_add, Nat.mul_assoc]

/-- Two distinct lifts with meetings already force the full certificate.
Thus a dyadic residue without a certificate can meet at most once. -/
theorem certificate_of_two_lifts {k d r p q : Nat} (hr : 0 < r) (hpq : p < q)
    (hp : acceleratedOrbit k (3 ^ d * (2 ^ k * p + r) - 1) =
      acceleratedOrbit k (2 ^ k * p + r - 1))
    (hq : acceleratedOrbit k (3 ^ d * (2 ^ k * q + r) - 1) =
      acceleratedOrbit k (2 ^ k * q + r - 1)) : Certificate k d r := by
  let a := oddCount (3 ^ d * r - 1) k
  let b := oddCount (r - 1) k
  let x := acceleratedOrbit k (3 ^ d * r - 1)
  let y := acceleratedOrbit k (r - 1)
  have equations (t : Nat)
      (h : acceleratedOrbit k (3 ^ d * (2 ^ k * t + r) - 1) =
        acceleratedOrbit k (2 ^ k * t + r - 1)) :
      3 ^ (a + d) * t + x = 3 ^ b * t + y := by
    have ⟨hbig, hsmall⟩ := lift_peaks k d r t hr
    rw [hbig, hsmall, Congruence.accOrbit_pow_two_mul_add,
      Congruence.accOrbit_pow_two_mul_add] at h
    simpa only [a, b, x, y, Nat.pow_add, Nat.mul_assoc] using h
  have hfirst := equations p hp
  have hsecond := equations q hq
  rw [show q = p + (q - p) by omega, Nat.mul_add, Nat.mul_add] at hsecond
  have hmul : 3 ^ (a + d) * (q - p) = 3 ^ b * (q - p) := by omega
  have hcoeff := Nat.mul_right_cancel (by omega : 0 < q - p) hmul
  have hexp := (Nat.pow_right_inj (by decide : 1 < 3)).mp hcoeff
  change b = a + d ∧ x = y
  rw [hcoeff] at hfirst
  exact ⟨hexp.symm, by omega⟩

private theorem odd_run_peak (e u : Nat) (hu : 0 < u) :
    acceleratedOrbit e (2 ^ e * u - 1) = 3 ^ e * u - 1 := by
  have hpos : 0 < 2 ^ e * u := Nat.mul_pos (Nat.two_pow_pos _) hu
  have hfac := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  have hp := DeviceSwap.run_climb e u (2 ^ e * u - 1) hu hfac
  omega

private theorem leading_halvings (d x : Nat) : acceleratedOrbit d (2 ^ d * x) = x := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.pow_succ', Nat.mul_assoc, ← acceleratedOrbit_add d 1, shortcut_double, ih]

/-- The long odd run and the short odd run with leading halvings have
equal-time tails whenever the peaks meet in the given suffix. -/
theorem synchronized_drop {k d e u : Nat} (hu : 0 < u)
    (h : acceleratedOrbit k (3 ^ (e + d) * u - 1) =
      acceleratedOrbit k (3 ^ e * u - 1)) :
    acceleratedOrbit (k + (e + d)) (2 ^ (e + d) * u - 1) =
      acceleratedOrbit (k + (e + d)) (2 ^ d * (2 ^ e * u - 1)) := by
  rw [← acceleratedOrbit_add k (e + d), ← acceleratedOrbit_add k (e + d),
    odd_run_peak (e + d) u hu, ← acceleratedOrbit_add e d, leading_halvings,
    odd_run_peak e u hu]
  exact h

/-- A positive exponent drop yields a strictly smaller equal-time
representative, including the cost of the leading halvings. -/
theorem leastAt_lt_of_peak_meet {k d e u : Nat} (hu : 0 < u) (hd : 0 < d)
    (h : acceleratedOrbit k (3 ^ (e + d) * u - 1) =
      acceleratedOrbit k (3 ^ e * u - 1)) :
    leastAt (k + (e + d)) (2 ^ (e + d) * u - 1) < 2 ^ (e + d) * u - 1 := by
  have hrep := leastAt_le (synchronized_drop hu h)
  have hshift : 2 ^ d * (2 ^ e * u - 1) + 2 ^ d = 2 ^ (e + d) * u := by
    calc
      _ = 2 ^ d * ((2 ^ e * u - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by
        rw [Nat.sub_add_cancel (Nat.mul_pos (Nat.two_pow_pos e) hu), Nat.pow_add]
        ac_rfl
  have hpow : 2 ≤ 2 ^ d := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ d by omega)
  omega

/-- For positive starts, a certified peak meeting transfers reachability
to the shorter odd-run length. -/
theorem reaches_one_drop {k d e u : Nat} (hu : 0 < u) (he : 0 < e)
    (h : acceleratedOrbit k (3 ^ (e + d) * u - 1) =
      acceleratedOrbit k (3 ^ e * u - 1)) :
    ReachesOne (2 ^ (e + d) * u - 1) ↔ ReachesOne (2 ^ e * u - 1) := by
  have hpos (a : Nat) (ha : 0 < a) : 0 < 2 ^ a * u - 1 := by
    have hp := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (show 0 < a from ha)
    have hle := Nat.le_mul_of_pos_right (2 ^ a) hu
    simp only [Nat.pow_zero] at hp
    omega
  rw [reachesOne_accOrbit_iff (hpos (e + d) (by omega)) (k + (e + d)),
    reachesOne_accOrbit_iff (hpos e he) (k + e), ← acceleratedOrbit_add k (e + d),
    ← acceleratedOrbit_add k e, odd_run_peak (e + d) u hu, odd_run_peak e u hu, h]

private theorem exponent_lift {k e : Nat} (hk : 3 ≤ k) (t : Nat) :
    3 ^ (e + 2 ^ (k - 2) * t) % 2 ^ k = 3 ^ e % 2 ^ k := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, LiftExponent.three_pow_period hk, ih]

/-- A power-of-three residue certificate proves a whole progression of
odd-run reductions. The cofactor may itself vary within its dyadic class. -/
theorem periodic_peak_meet {k d e u r : Nat} (hk : 3 ≤ k)
    (hr : 0 < r) (hres : (3 ^ e * u) % 2 ^ k = r) (hc : Certificate k d r) (t : Nat) :
    acceleratedOrbit k (3 ^ (e + 2 ^ (k - 2) * t + d) * u - 1) =
      acceleratedOrbit k (3 ^ (e + 2 ^ (k - 2) * t) * u - 1) := by
  rw [Nat.pow_add (n := d), Nat.mul_right_comm, Nat.mul_comm _ (3 ^ d)]
  apply meet_of_certificate hr _ hc
  rw [Nat.mul_mod, exponent_lift hk t, ← Nat.mul_mod]
  exact hres

/-- For exponents congruent to 31 modulo 64, the smaller odd-run start
with exponent two less reaches exactly the same tail. -/
theorem mersenne_31_meet (t : Nat) :
    acceleratedOrbit 8 (3 ^ (29 + 64 * t + 2) - 1) =
      acceleratedOrbit 8 (3 ^ (29 + 64 * t) - 1) := by
  have h := periodic_peak_meet (k := 8) (d := 2) (e := 29) (u := 1) (r := 147)
    (by decide) (by decide) (by decide) (by decide) t
  simpa only [Nat.mul_one] using h

theorem mersenne_31_reaches_one (t : Nat) :
    ReachesOne (2 ^ (29 + 64 * t + 2) - 1) ↔
      ReachesOne (2 ^ (29 + 64 * t) - 1) := by
  have h := reaches_one_drop (u := 1) (e := 29 + 64 * t) (d := 2)
    (by decide) (by omega) (by simpa only [Nat.mul_one] using mersenne_31_meet t)
  simpa only [Nat.mul_one] using h

/-- Two other progressions whose first eight steps do not yet give
the same certificate, but which meet by nine and ten steps. -/
theorem mersenne_79_reaches_one (t : Nat) :
    ReachesOne (2 ^ (77 + 128 * t + 2) - 1) ↔
      ReachesOne (2 ^ (77 + 128 * t) - 1) := by
  have hm := periodic_peak_meet (k := 9) (d := 2) (e := 77) (u := 1) (r := 211)
    (by decide) (by decide) (by decide) (by decide) t
  have h := reaches_one_drop (k := 9) (u := 1) (e := 77 + 128 * t) (d := 2)
    (by decide) (by omega) hm
  simpa only [Nat.mul_one] using h

theorem mersenne_111_reaches_one (t : Nat) :
    ReachesOne (2 ^ (109 + 256 * t + 2) - 1) ↔
      ReachesOne (2 ^ (109 + 256 * t) - 1) := by
  have hm := periodic_peak_meet (k := 10) (d := 2) (e := 109) (u := 1) (r := 595)
    (by decide) (by decide) (by decide) (by decide) t
  have h := reaches_one_drop (k := 10) (u := 1) (e := 109 + 256 * t) (d := 2)
    (by decide) (by omega) hm
  simpa only [Nat.mul_one] using h

set_option exponentiation.threshold 2048 in
private theorem three_pow_2043_residue : 3 ^ 2043 % 2 ^ 14 = 14395 := by decide

/-- A four-exponent reduction in a progression outside the two-exponent
certificate at the same depth. -/
theorem mersenne_2047_reaches_one (t : Nat) :
    ReachesOne (2 ^ (2043 + 4096 * t + 4) - 1) ↔
      ReachesOne (2 ^ (2043 + 4096 * t) - 1) := by
  have hm := periodic_peak_meet (k := 14) (d := 4) (e := 2043) (u := 1) (r := 14395)
    (by decide) (by decide) (by simpa only [Nat.mul_one] using three_pow_2043_residue)
    (by decide) t
  have h := reaches_one_drop (k := 14) (u := 1) (e := 2043 + 4096 * t) (d := 4)
    (by decide) (by omega) hm
  simpa only [Nat.mul_one] using h

end Collatz.PeakContraction
