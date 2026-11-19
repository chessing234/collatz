import Collatz.Strategy.ExcursionCofactor

/-!
# Telescoping drop criteria for a chain of two or three excursions

`drop_iff` is one step: `e < n` iff `3^v u + 2^W ≤ 2^{v+W} u`.  The
cofactor identity `3^v u + 2^W − 1 = 2^{W+v'} u'` pushes the next odd
state into `(v, W, u)` of the start.  Composing once or twice gives
exact `Nat` landing formulae, and the comparison with the *original*
`n` (not merely with the previous landing) as an inequality in the
letters of the chain.

This is not Collatz.  A light word can grow at every finite length
(`71 → 121 → 91 → 103`); the criterion says when a mixed word does
not.

Specialisations:

* `(3, 1)` then `(1, W' ≥ 2)` recovers LandOne heavy;
* `(2, 1)` then `(4, W' ≥ 3)` recovers RemTwo;
* `(3, 1)` then `(1, 1)` always grows (two-step negative law);
* `(3, 1)` then `(1, 1)` then `v'' = 1` drops (three-step, any `W''`);
* `(2, 1)` then leftover `v' = 6`, `W' ≥ 4` is a drop RemTwo missed;
* `(4, 1)` then `(1, 1)` always grows; `(4, 1)` then `(1, W' ≥ 2)` drops;
* `(v, 1)` with `v ≥ 2`, followed by any run whose extra halvings reach
  the binary ceiling of `3^{v+v'}`, drops below the original start;
* a light run of length `v ≥ 4`, any extra-halving count, followed by a
  run meeting `3^{v+v'} < 2^{v+v'+W+W'−1}`, drops below the original start;
* the same light run, when that second step misses the exponent and the
  third meets `3^{v+v'+v''} < 2^{v+v'+v''+W+W'+W''−1}`, drops in three steps;
* the same light run, when the second and third both miss their exponents
  and the fourth meets `3^{v+v'+v''+v'''} < 2^{v+v'+v''+v'''+W+W'+W''+W'''−1}`,
  drops in four steps.  Eight copies of each of the three earlier errors
  fit in `3` to that total length, and the coefficient `12` still sits
  under `16`.  When the fourth also misses and the fifth meets the next
  ceiling, the spare-bit budget drops the start in five steps.
-/

namespace Collatz
namespace ExcursionTelescope

open Collatz.Arith Collatz.ExcursionMap Collatz.ExcursionCofactor


/-! ## 1.  Two-step landing, and `drop_iff_two` -/

/-- **Exact two-step landing.**  After excursions `(v, W)` and
`(v', W')`,

  `3^{v'} (3^v u + 2^W − 1) = 2^{W+v'+W'} e' + 2^{W+v'}`. -/
theorem two_step_landing {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    3 ^ v' * (3 ^ v * u + 2 ^ W - 1) =
      2 ^ (W + v' + W') * e' + 2 ^ (W + v') := by
  have hid := next_cofactor_of_excursions h h'
  have hpeak : 3 ^ v' * u' = 2 ^ W' * e' + 1 := h'.2.2.2.2.2.2
  have hcomm : 3 ^ v' * (2 ^ (W + v') * u') =
      2 ^ (W + v') * (3 ^ v' * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hid, hcomm, hpeak, Nat.mul_add, Nat.mul_one]
  have hL : 2 ^ (W + v') * (2 ^ W' * e') = 2 ^ (W + v' + W') * e' := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  rw [hL]

/-- **Two-step drop against the original start**, in the next cofactor.

  `e' < n` iff `3^{v'} u' + 2^{W'} ≤ 2^{v+W'} u`. -/
theorem drop_iff_two {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔ 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ (v + W') * u := by
  have hWpos : 0 < 2 ^ W' := two_pow_pos W'
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W' * e' + 1 = 3 ^ v' * u' := h'.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W') * u = 2 ^ W' * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W' * e' < 2 ^ W' * n := Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W' * e' + 1 ≤ 2 ^ W' * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v' * u' ≤ 2 ^ W' * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ W' * n + 2 ^ W' :=
      Nat.add_le_add_right h2 _
    have h4 : 2 ^ W' * n + 2 ^ W' = 2 ^ W' * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v' * u' + 2 ^ W' ≤ 2 ^ W' * (n + 1) := by
      rw [← hpow]; exact hle
    have h4 : 2 ^ W' * (n + 1) = 2 ^ W' * n + 2 ^ W' := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v' * u' ≤ 2 ^ W' * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W' * e' + 1 ≤ 2 ^ W' * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W' * e' < 2 ^ W' * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- Scaling an inequality by a positive factor is an iff. -/
private theorem mul_le_iff {a b c : Nat} (ha : 0 < a) : b ≤ c ↔ a * b ≤ a * c :=
  ⟨fun h => Nat.mul_le_mul_left a h, fun h => Nat.le_of_mul_le_mul_left h ha⟩

/-- Left-hand side of the expanded two-step criterion. -/
private theorem two_scale_left {W v' u' W' : Nat} :
    2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W') =
      3 ^ v' * (2 ^ (W + v') * u') + 2 ^ (W + v' + W') := by
  rw [Nat.mul_add]
  have h1 : 2 ^ (W + v') * (3 ^ v' * u') = 3 ^ v' * (2 ^ (W + v') * u') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2 : 2 ^ (W + v') * 2 ^ W' = 2 ^ (W + v' + W') := by
    rw [← Nat.pow_add]
  rw [h1, h2]

/-- Right-hand side of the expanded two-step criterion. -/
private theorem two_scale_right (v u W v' W' : Nat) :
    2 ^ (W + v') * (2 ^ (v + W') * u) = 2 ^ (v + W + v' + W') * u := by
  have hexp : W + v' + (v + W') = v + W + v' + W' := by omega
  rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]

/-- **Two-step drop**, expanded in `(v, W, u)` of each step.

  `e' < n` iff
  `3^{v'} (3^v u + 2^W − 1) + 2^{W+v'+W'} ≤ 2^{v+W+v'+W'} u`. -/
theorem drop_iff_two_expanded {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔
      3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + 2 ^ (W + v' + W') ≤
        2 ^ (v + W + v' + W') * u := by
  have hid := next_cofactor_of_excursions h h'
  rw [drop_iff_two h h', mul_le_iff (two_pow_pos (W + v')),
      two_scale_left, two_scale_right, ← hid]


/-! ## 2.  Three-step landing, and `drop_iff_three` -/

/-- Rewrite `x + 2^k − 1` as `x + (2^k − 1)`. -/
private theorem add_two_pow_pred (x k : Nat) :
    x + 2 ^ k - 1 = x + (2 ^ k - 1) :=
  Nat.add_sub_assoc (one_le_two_pow k) x

/-- **Exact three-step landing.**  After `(v, W)`, `(v', W')`, `(v'', W'')`,

  `3^{v''} ( 3^{v'} (3^v u + 2^W − 1) + (2^{W'} − 1) 2^{W+v'} )`

  `= 2^{W+v'+W'+v''+W''} e'' + 2^{W+v'+W'+v''}`. -/
theorem three_step_landing {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    3 ^ v'' *
        (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
          (2 ^ W' - 1) * 2 ^ (W + v')) =
      2 ^ (W + v' + W' + v'' + W'') * e'' +
        2 ^ (W + v' + W' + v'') := by
  have hid1 := next_cofactor_of_excursions h h'
  have hid2 := next_cofactor_of_excursions h' h''
  have hpeak : 3 ^ v'' * u'' = 2 ^ W'' * e'' + 1 := h''.2.2.2.2.2.2
  have hmid :
      3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + (2 ^ W' - 1) * 2 ^ (W + v') =
        2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W' - 1) := by
    rw [hid1]
    have hdist :
        3 ^ v' * (2 ^ (W + v') * u') + (2 ^ W' - 1) * 2 ^ (W + v') =
          2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1)) := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hrew := add_two_pow_pred (3 ^ v' * u') W'
    rw [hdist, hrew]
  rw [hmid]
  have hcomm : 3 ^ v'' * (2 ^ (W + v') * (3 ^ v' * u' + 2 ^ W' - 1)) =
      2 ^ (W + v') * (3 ^ v'' * (3 ^ v' * u' + 2 ^ W' - 1)) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [hcomm, hid2]
  have hcomm2 : 3 ^ v'' * (2 ^ (W' + v'') * u'') =
      2 ^ (W' + v'') * (3 ^ v'' * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hcomm2, hpeak]
  have hinner : 2 ^ (W' + v'') * (2 ^ W'' * e'' + 1) =
      2 ^ (W' + v'' + W'') * e'' + 2 ^ (W' + v'') := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add]
  rw [hinner, Nat.mul_add]
  have hL : 2 ^ (W + v') * (2 ^ (W' + v'' + W'') * e'') =
      2 ^ (W + v' + W' + v'' + W'') * e'' := by
    have hexp : W + v' + (W' + v'' + W'') = W + v' + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  have hR : 2 ^ (W + v') * 2 ^ (W' + v'') = 2 ^ (W + v' + W' + v'') := by
    have hexp : W + v' + (W' + v'') = W + v' + W' + v'' := by omega
    rw [← Nat.pow_add, hexp]
  rw [hL, hR]

/-- **Three-step drop against the original start**, in the last cofactor.

  `e'' < n` iff `3^{v''} u'' + 2^{W''} ≤ 2^{v+W''} u`. -/
theorem drop_iff_three {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    e'' < n ↔ 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ (v + W'') * u := by
  have hWpos : 0 < 2 ^ W'' := two_pow_pos W''
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W'' * e'' + 1 = 3 ^ v'' * u'' := h''.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W'') * u = 2 ^ W'' * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W'' * e'' < 2 ^ W'' * n :=
      Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W'' * e'' + 1 ≤ 2 ^ W'' * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v'' * u'' ≤ 2 ^ W'' * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ W'' * n + 2 ^ W'' :=
      Nat.add_le_add_right h2 _
    have h4 : 2 ^ W'' * n + 2 ^ W'' = 2 ^ W'' * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v'' * u'' + 2 ^ W'' ≤ 2 ^ W'' * (n + 1) := by
      rw [← hpow]; exact hle
    have h4 : 2 ^ W'' * (n + 1) = 2 ^ W'' * n + 2 ^ W'' := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v'' * u'' ≤ 2 ^ W'' * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W'' * e'' + 1 ≤ 2 ^ W'' * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W'' * e'' < 2 ^ W'' * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- Left-hand side of the expanded three-step criterion, after one
cofactor substitution. -/
private theorem three_scale_left {W' v'' u'' W'' : Nat} :
    2 ^ (W' + v'') * (3 ^ v'' * u'' + 2 ^ W'') =
      3 ^ v'' * (2 ^ (W' + v'') * u'') + 2 ^ (W' + v'' + W'') := by
  rw [Nat.mul_add]
  have h1 : 2 ^ (W' + v'') * (3 ^ v'' * u'') =
      3 ^ v'' * (2 ^ (W' + v'') * u'') := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h2 : 2 ^ (W' + v'') * 2 ^ W'' = 2 ^ (W' + v'' + W'') := by
    rw [← Nat.pow_add]
  rw [h1, h2]

private theorem three_scale_mid {W v' u' W' v'' W'' : Nat} :
    2 ^ (W + v') *
        (3 ^ v'' * (3 ^ v' * u' + (2 ^ W' - 1)) + 2 ^ (W' + v'' + W'')) =
      3 ^ v'' * (3 ^ v' * (2 ^ (W + v') * u') +
          (2 ^ W' - 1) * 2 ^ (W + v')) +
        2 ^ (W + v' + W' + v'' + W'') := by
  rw [Nat.mul_add]
  have hc1 : 2 ^ (W + v') * (3 ^ v'' * (3 ^ v' * u' + (2 ^ W' - 1))) =
      3 ^ v'' * (2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1))) := by
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hd : 2 ^ (W + v') * (3 ^ v' * u' + (2 ^ W' - 1)) =
      3 ^ v' * (2 ^ (W + v') * u') + (2 ^ W' - 1) * 2 ^ (W + v') := by
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hc2 : 2 ^ (W + v') * 2 ^ (W' + v'' + W'') =
      2 ^ (W + v' + W' + v'' + W'') := by
    have hexp : W + v' + (W' + v'' + W'') = W + v' + W' + v'' + W'' := by omega
    rw [← Nat.pow_add, hexp]
  rw [hc1, hd, hc2]

/-- **Three-step drop**, expanded in `(v, W, u)` of each step. -/
theorem drop_iff_three_expanded {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'') :
    e'' < n ↔
      3 ^ v'' *
          (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
            (2 ^ W' - 1) * 2 ^ (W + v')) +
        2 ^ (W + v' + W' + v'' + W'') ≤
        2 ^ (v + W + v' + W' + v'' + W'') * u := by
  have hid1 := next_cofactor_of_excursions h h'
  have hid2 := next_cofactor_of_excursions h' h''
  have hR1 : 2 ^ (W' + v'') * (2 ^ (v + W'') * u) =
      2 ^ (v + W' + v'' + W'') * u := by
    have hexp : W' + v'' + (v + W'') = v + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  have hR0 : 2 ^ (W + v') * (2 ^ (v + W' + v'' + W'') * u) =
      2 ^ (v + W + v' + W' + v'' + W'') * u := by
    have hexp : W + v' + (v + W' + v'' + W'') =
        v + W + v' + W' + v'' + W'' := by omega
    rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
  rw [drop_iff_three h h' h'', mul_le_iff (two_pow_pos (W' + v'')),
      three_scale_left, hR1, ← hid2, add_two_pow_pred (3 ^ v' * u') W',
      mul_le_iff (two_pow_pos (W + v')), three_scale_mid, hR0, ← hid1]


/-! ## 3.  The two-step criterion as a peak comparison -/

/-- `a * (b * u) = b * (a * u)`. -/
private theorem mul_swap (a b u : Nat) : a * (b * u) = b * (a * u) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b, Nat.mul_assoc]

/-- `a + 2^W ≤ 2^{v+W} u` iff `a ≤ 2^W (2^v u − 1)`. -/
private theorem add_pow_le_iff {a v u W : Nat} (hu : 1 ≤ u) :
    a + 2 ^ W ≤ 2 ^ (v + W) * u ↔ a ≤ 2 ^ W * (2 ^ v * u - 1) := by
  have hpow : (2 : Nat) ^ (v + W) * u = 2 ^ W * (2 ^ v * u) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ v), Nat.mul_assoc]
  have hpos : 1 ≤ 2 ^ v * u :=
    Nat.le_trans hu (Nat.le_mul_of_pos_left u (two_pow_pos v))
  have hsplit : 2 ^ W * (2 ^ v * u - 1) + 2 ^ W = 2 ^ W * (2 ^ v * u) := by
    have h : 2 ^ W * (2 ^ v * u - 1) + 2 ^ W * 1 =
        2 ^ W * (2 ^ v * u - 1 + 1) := by rw [← Nat.mul_add]
    rw [Nat.mul_one] at h
    rw [h, Nat.sub_add_cancel hpos]
  rw [hpow, ← hsplit]
  constructor
  · exact Nat.le_of_add_le_add_right
  · intro h; exact Nat.add_le_add_right h _

/-- If the comparison holds at the minimum extra-halving count `K`, it
holds for every larger power of two. -/
private theorem le_of_min_pow {a K b W : Nat}
    (hcore : a ≤ K * b) (hk : K ≤ 2 ^ W) : a ≤ 2 ^ W * b :=
  Nat.le_trans hcore (Nat.mul_le_mul_right b hk)

private theorem four_le_two_pow {W : Nat} (h : 2 ≤ W) : 4 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this

private theorem eight_le_two_pow {W : Nat} (h : 3 ≤ W) : 8 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 3 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this

private theorem sixteen_le_two_pow {W : Nat} (h : 4 ≤ W) : 16 ≤ 2 ^ W := by
  have : (2 : Nat) ^ 4 ≤ 2 ^ W := two_pow_le_two_pow h
  simpa using this


/-! ## 4.  Mixed light words: `(3, 1)` then `(1, ·)` -/

private theorem eqs_three_one {n u e : Nat} (h : IsExcursion n 3 u 1 e) :
    n + 1 = 8 * u ∧ 27 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 3 = 8 by decide] at hnu
  rw [show (3 : Nat) ^ 3 = 27 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

private theorem one_le_u_of {n v u W e : Nat} (h : IsExcursion n v u W e) :
    1 ≤ u := by
  have : u % 2 = 1 := h.2.1
  omega

private theorem eight_e'_add {u u' e' k : Nat}
    (hrel : 4 * u' = k * u + 1) (hpeak : 2 * e' + 1 = 3 * u') :
    8 * e' + 4 = 3 * (k * u + 1) := by
  have h12u : 8 * e' + 4 = 12 * u' := by omega
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h12u, h12, hrel]

private theorem eight_e'_eq {u e' k : Nat}
    (_hu : 1 ≤ u) (h : 8 * e' + 4 = 3 * (k * u + 1)) :
    8 * e' = 3 * k * u - 1 := by
  have : 3 * (k * u + 1) = 3 * k * u + 3 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have h' : 8 * e' + 4 = 3 * k * u + 3 := by rwa [this] at h
  omega

private theorem four_u'_of_three_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 27 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_three_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega

/-- Core of LandOne heavy: the `W' = 2` comparison `3 u' ≤ 4 (8u − 1)`. -/
private theorem three_one_v_one_core {u u' : Nat}
    (hu : 1 ≤ u) (hrel : 4 * u' = 27 * u + 1) :
    3 * u' ≤ 4 * (8 * u - 1) := by
  have h12 : 12 * u' = 81 * u + 3 := by
    have h : 12 * u' = 3 * (4 * u') := by
      have : (12 : Nat) = 3 * 4 := by decide
      rw [this, Nat.mul_assoc]
    rw [h, hrel, Nat.mul_add, Nat.mul_one]
    have : (3 : Nat) * 27 = 81 := by decide
    rw [← Nat.mul_assoc, this]
  have hL : 4 * (3 * u') = 12 * u' := by
    have : (4 : Nat) * 3 = 12 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 4 * (4 * (8 * u - 1)) = 16 * (8 * u - 1) := by
    have : (4 : Nat) * 4 = 16 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 16 * (8 * u - 1) = 128 * u - 16 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (16 : Nat) * 8 = 128 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 81 * u + 3 ≤ 128 * u - 16 := by
    have : 19 ≤ 47 * u := by omega
    exact Nat.le_sub_of_add_le (by omega : 81 * u + 3 + 16 ≤ 128 * u)
  have : 4 * (3 * u') ≤ 4 * (4 * (8 * u - 1)) := by
    rw [hL, h12, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **Sanity: LandOne heavy.**  `(3, 1)` then `(1, W' ≥ 2)` drops below
the original start.  The two-step criterion at `W' = 2` is
`3 u' ≤ 4 (8u − 1)`, i.e. `81u + 19 ≤ 128u`. -/
theorem drop_of_three_one_then_v_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' W' e')
    (hW : 2 ≤ W') : e' < n := by
  have hu := one_le_u_of h
  have hrel := four_u'_of_three_one h h'
  have hcore := three_one_v_one_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  rw [h3, add_pow_le_iff hu]
  rw [show (2 : Nat) ^ 3 = 8 by decide]
  exact le_of_min_pow hcore (four_le_two_pow hW)

/-- **Negative law.**  `(3, 1)` then `(1, 1)` always grows:
`8 e' = 81u − 1 > 64u − 8 = 8 n`. -/
theorem grows_of_three_one_then_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hu := one_le_u_of h
  have ⟨hnu, _⟩ := eqs_three_one h
  have hrel := four_u'_of_three_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this.symm
  have h8e : 8 * e' = 81 * u - 1 := by
    have := eight_e'_eq hu (eight_e'_add hrel hpeak)
    have hk : (3 : Nat) * 27 = 81 := by decide
    rwa [hk] at this
  clear h h' hrel hpeak
  have hn8 : 8 * n = 64 * u - 8 := by omega
  have hcmp : 64 * u - 8 < 81 * u - 1 := by
    have : 7 < 17 * u := by omega
    omega
  have : 8 * n < 8 * e' := by
    rw [hn8, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this

/-- After `(3, 1)` then `(1, 1)` the cofactor satisfies `u ≥ 9`. -/
private theorem nine_le_u_of_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e') : 9 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have hu' : u' % 2 = 1 := h'.2.1
  have he' : e' % 2 = 1 := h'.2.2.1
  have hrel := four_u'_of_three_one h h'
  have hpeak : 3 * u' = 2 * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this
  omega

private theorem sixteen_u''_of_three_light {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') :
    16 * u'' = 81 * u + 7 := by
  have hrel := four_u'_of_three_one h h'
  have hpeak' : 3 * u' = 2 * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this
  have hnu'' : e' + 1 = 2 * u'' := by
    have := h''.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have h4 : 4 * u'' = 3 * u' + 1 := by
    have : 2 * (e' + 1) = 3 * u' + 1 := by omega
    rw [hnu''] at this
    have : 2 * 2 * u'' = 3 * u' + 1 := by
      rwa [← Nat.mul_assoc] at this
    simpa using this
  have h16 : 16 * u'' = 4 * (4 * u'') := by
    have : (16 : Nat) = 4 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h16, h4]
  have : 4 * (3 * u' + 1) = 12 * u' + 4 := by omega
  rw [this]
  have h12 : 12 * u' = 3 * (4 * u') := by
    have : (12 : Nat) = 3 * 4 := by decide
    rw [this, Nat.mul_assoc]
  rw [h12, hrel]
  have : 3 * (27 * u + 1) + 4 = 81 * u + 7 := by
    have : (3 : Nat) * 27 = 81 := by decide
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, this]
  omega

/-- Core of the three-step drop: `3 u'' ≤ 2 (8u − 1)` once `u ≥ 9`. -/
private theorem three_one_one_one_core {u u'' : Nat}
    (hu : 9 ≤ u) (hrel : 16 * u'' = 81 * u + 7) :
    3 * u'' ≤ 2 * (8 * u - 1) := by
  have hL : 16 * (3 * u'') = 243 * u + 21 := by
    have : 16 * (3 * u'') = 3 * (16 * u'') := mul_swap 16 3 u''
    rw [this, hrel, Nat.mul_add]
    have h243 : (3 : Nat) * 81 = 243 := by decide
    have h21 : (3 : Nat) * 7 = 21 := by decide
    rw [← Nat.mul_assoc, h243, h21]
  have hR : 16 * (2 * (8 * u - 1)) = 32 * (8 * u - 1) := by
    have : (16 : Nat) * 2 = 32 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 32 * (8 * u - 1) = 256 * u - 32 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (32 : Nat) * 8 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 243 * u + 21 ≤ 256 * u - 32 := by
    have : 53 ≤ 13 * u := by omega
    exact Nat.le_sub_of_add_le (by omega : 243 * u + 21 + 32 ≤ 256 * u)
  have : 16 * (3 * u'') ≤ 16 * (2 * (8 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **`(3, 1)` then `(1, 1)` then `v'' = 1`.**  The third excursion
drops below the original start for every `W'' ≥ 1`.  The criterion at
`W'' = 1` is `3 u'' ≤ 2 (8u − 1)`, and the two-light family has `u ≥ 9`. -/
theorem drop_of_three_one_one_one_then_v_one {n u e u' e' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 1 u' 1 e')
    (h'' : IsExcursion e' 1 u'' W'' e'') : e'' < n := by
  have hu := nine_le_u_of_one_one h h'
  have hrel := sixteen_u''_of_three_light h h' h''
  have hcore := three_one_one_one_core hu hrel
  refine (drop_iff_three h h' h'').mpr ?_
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 9) hu
  rw [h3, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 3 = 8 by decide]
  exact le_of_min_pow hcore (two_le_two_pow (IsExcursion.one_le_W h''))


/-! ## 5.  Mixed light words: `(2, 1)` then leftover `v' ≥ 3` -/

private theorem eqs_two_one {n u e : Nat} (h : IsExcursion n 2 u 1 e) :
    n + 1 = 4 * u ∧ 9 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 2 = 4 by decide] at hnu
  rw [show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- A genuine `(2, 1)` start has `u ≥ 3` (`u = 1` forces an even landing). -/
private theorem three_le_u_of_two_one {n u e : Nat}
    (h : IsExcursion n 2 u 1 e) : 3 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have he : e % 2 = 1 := h.2.2.1
  have ⟨_, hpeak⟩ := eqs_two_one h
  omega

/-- Specialised two-step criterion after a `(2, 1)` step:

  `e' < n` iff `3^{v'} (9u + 1) + 2^{v'+W'+1} ≤ 2^{v'+W'+3} u`. -/
theorem drop_iff_two_one {n u e v' u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e v' u' W' e') :
    e' < n ↔
      3 ^ v' * (9 * u + 1) + 2 ^ (v' + W' + 1) ≤ 2 ^ (v' + W' + 3) * u := by
  have h9 : (3 : Nat) ^ 2 = 9 := by decide
  have h2 : (2 : Nat) ^ 1 = 2 := Nat.pow_one 2
  have hpeak_plus : 9 * u + 2 - 1 = 9 * u + 1 := by omega
  have hexL : 1 + v' + W' = v' + W' + 1 := by omega
  have hexR : 2 + 1 + v' + W' = v' + W' + 3 := by omega
  rw [drop_iff_two_expanded h h', h9, h2, hpeak_plus, hexL, hexR]

/-- Core of RemTwo: `81 u' ≤ 8 (4u − 1)` once `u ≥ 3`. -/
private theorem remtwo_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 32 * u' = 9 * u + 1) :
    81 * u' ≤ 8 * (4 * u - 1) := by
  have hL : 32 * (81 * u') = 729 * u + 81 := by
    have : 32 * (81 * u') = 81 * (32 * u') := mul_swap 32 81 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (81 : Nat) * 9 = 729 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 32 * (8 * (4 * u - 1)) = 256 * (4 * u - 1) := by
    have : (32 : Nat) * 8 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 256 * (4 * u - 1) = 1024 * u - 256 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (256 : Nat) * 4 = 1024 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 729 * u + 81 ≤ 1024 * u - 256 := by
    have : 337 ≤ 295 * u := by
      have hmin : 295 * 3 ≤ 295 * u := Nat.mul_le_mul_left 295 hu
      have : (337 : Nat) ≤ 295 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le (by omega : 729 * u + 81 + 256 ≤ 1024 * u)
  have : 32 * (81 * u') ≤ 32 * (8 * (4 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **Sanity: RemTwo.**  `(2, 1)` then `(4, W' ≥ 3)` drops below the
original start.  The criterion at `W' = 3` is `81 u' ≤ 8 (4u − 1)`,
i.e. `295u ≥ 337`. -/
theorem drop_of_two_one_then_v_four {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 4 u' W' e')
    (hW : 3 ≤ W') : e' < n := by
  have hu := three_le_u_of_two_one h
  have hnu' : e + 1 = 16 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 4 = 16 by decide] at this
    exact this
  have ⟨_, hpeak⟩ := eqs_two_one h
  have hrel : 32 * u' = 9 * u + 1 := by omega
  have hcore := remtwo_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  rw [show (3 : Nat) ^ 4 = 81 by decide, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 2 = 4 by decide]
  exact le_of_min_pow hcore (eight_le_two_pow hW)

/-- Core of the new `v' = 6` drop: `729 u' ≤ 16 (4u − 1)` once `u ≥ 3`. -/
private theorem v_six_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 128 * u' = 9 * u + 1) :
    729 * u' ≤ 16 * (4 * u - 1) := by
  have hL : 128 * (729 * u') = 6561 * u + 729 := by
    have : 128 * (729 * u') = 729 * (128 * u') := mul_swap 128 729 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (729 : Nat) * 9 = 6561 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 128 * (16 * (4 * u - 1)) = 2048 * (4 * u - 1) := by
    have : (128 : Nat) * 16 = 2048 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 2048 * (4 * u - 1) = 8192 * u - 2048 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (2048 : Nat) * 4 = 8192 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 6561 * u + 729 ≤ 8192 * u - 2048 := by
    have : 2777 ≤ 1631 * u := by
      have hmin : 1631 * 3 ≤ 1631 * u := Nat.mul_le_mul_left 1631 hu
      have : (2777 : Nat) ≤ 1631 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le
      (by omega : 6561 * u + 729 + 2048 ≤ 8192 * u)
  have : 128 * (729 * u') ≤ 128 * (16 * (4 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **New drop.**  `(2, 1)` then leftover `(6, W' ≥ 4)` lands below the
original start.  RemTwo closed `v' = 4`; RemTwoLeft closed `v' = 3, 5`.
The criterion at `W' = 4` is `729 u' ≤ 16 (4u − 1)`, i.e. `1631u ≥ 2777`. -/
theorem lemmaX_of_two_one_then_v_six {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 6 u' W' e')
    (hW : 4 ≤ W') : e' < n := by
  have hu := three_le_u_of_two_one h
  have hnu' : e + 1 = 64 * u' := by
    have := h'.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 6 = 64 by decide] at this
    exact this
  have ⟨_, hpeak⟩ := eqs_two_one h
  have hrel : 128 * u' = 9 * u + 1 := by omega
  have hcore := v_six_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  rw [show (3 : Nat) ^ 6 = 729 by decide, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 2 = 4 by decide]
  exact le_of_min_pow hcore (sixteen_le_two_pow hW)

/-- Packaged Lemma X witness. -/
theorem lemmaX_chain_of_two_one_then_v_six {n u e u' W' e' : Nat}
    (h : IsExcursion n 2 u 1 e) (h' : IsExcursion e 6 u' W' e')
    (hW : 4 ≤ W') : ExChain n e' ∧ e' < n :=
  ⟨ExChain.cons ⟨2, u, 1, h⟩ (ExChain.one ⟨6, u', W', h'⟩),
    lemmaX_of_two_one_then_v_six h h' hW⟩


/-! ## 6.  Mixed light words: `(4, 1)` then `(1, ·)` -/

private theorem eqs_four_one {n u e : Nat} (h : IsExcursion n 4 u 1 e) :
    n + 1 = 16 * u ∧ 81 * u = 2 * e + 1 := by
  have hnu := h.2.2.2.2.2.1
  have hpeak := h.2.2.2.2.2.2
  rw [show (2 : Nat) ^ 4 = 16 by decide] at hnu
  rw [show (3 : Nat) ^ 4 = 81 by decide, Nat.pow_one] at hpeak
  exact ⟨hnu, hpeak⟩

/-- A genuine `(4, 1)` start has `u ≥ 3`. -/
private theorem three_le_u_of_four_one {n u e : Nat}
    (h : IsExcursion n 4 u 1 e) : 3 ≤ u := by
  have hu : u % 2 = 1 := h.2.1
  have he : e % 2 = 1 := h.2.2.1
  have ⟨_, hpeak⟩ := eqs_four_one h
  omega

private theorem four_u'_of_four_one {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' W' e') :
    4 * u' = 81 * u + 1 := by
  have ⟨_, hpeak⟩ := eqs_four_one h
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  omega

/-- Core: `3 u' ≤ 4 (16u − 1)` once `u ≥ 3`. -/
private theorem four_one_v_one_core {u u' : Nat}
    (hu : 3 ≤ u) (hrel : 4 * u' = 81 * u + 1) :
    3 * u' ≤ 4 * (16 * u - 1) := by
  have hL : 4 * (3 * u') = 243 * u + 3 := by
    have : 4 * (3 * u') = 3 * (4 * u') := mul_swap 4 3 u'
    rw [this, hrel, Nat.mul_add, Nat.mul_one]
    have : (3 : Nat) * 81 = 243 := by decide
    rw [← Nat.mul_assoc, this]
  have hR : 4 * (4 * (16 * u - 1)) = 16 * (16 * u - 1) := by
    have : (4 : Nat) * 4 = 16 := by decide
    rw [← Nat.mul_assoc, this]
  have hR' : 16 * (16 * u - 1) = 256 * u - 16 := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : (16 : Nat) * 16 = 256 := by decide
    rw [← Nat.mul_assoc, this]
  have hcmp : 243 * u + 3 ≤ 256 * u - 16 := by
    have : 19 ≤ 13 * u := by
      have hmin : 13 * 3 ≤ 13 * u := Nat.mul_le_mul_left 13 hu
      have : (19 : Nat) ≤ 13 * 3 := by decide
      omega
    exact Nat.le_sub_of_add_le (by omega : 243 * u + 3 + 16 ≤ 256 * u)
  have : 4 * (3 * u') ≤ 4 * (4 * (16 * u - 1)) := by
    rw [hL, hR, hR']
    exact hcmp
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **`(4, 1)` then `(1, W' ≥ 2)` drops** below the original start.  The
criterion at `W' = 2` is `3 u' ≤ 4 (16u − 1)`, i.e. `13u ≥ 19`. -/
theorem drop_of_four_one_then_v_one_heavy {n u e u' W' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' W' e')
    (hW : 2 ≤ W') : e' < n := by
  have hu := three_le_u_of_four_one h
  have hrel := four_u'_of_four_one h h'
  have hcore := four_one_v_one_core hu hrel
  refine (drop_iff_two h h').mpr ?_
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  have h3 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  rw [h3, add_pow_le_iff hu1]
  rw [show (2 : Nat) ^ 4 = 16 by decide]
  exact le_of_min_pow hcore (four_le_two_pow hW)

/-- **Negative law.**  `(4, 1)` then `(1, 1)` always grows:
`8 e' = 243u − 1 > 128u − 8 = 8 n`. -/
theorem grows_of_four_one_then_one_one {n u e u' e' : Nat}
    (h : IsExcursion n 4 u 1 e) (h' : IsExcursion e 1 u' 1 e') : n < e' := by
  have hu := three_le_u_of_four_one h
  have ⟨hnu, _⟩ := eqs_four_one h
  have hrel := four_u'_of_four_one h h'
  have hpeak : 2 * e' + 1 = 3 * u' := by
    have := h'.2.2.2.2.2.2
    rw [Nat.pow_one, Nat.pow_one] at this
    exact this.symm
  have hu1 : 1 ≤ u := Nat.le_trans (by omega : (1 : Nat) ≤ 3) hu
  have h8e : 8 * e' = 243 * u - 1 := by
    have := eight_e'_eq hu1 (eight_e'_add hrel hpeak)
    have hk : (3 : Nat) * 81 = 243 := by decide
    rwa [hk] at this
  clear h h' hrel hpeak
  have hn8 : 8 * n = 128 * u - 8 := by omega
  have hcmp : 128 * u - 8 < 243 * u - 1 := by
    have : 7 < 115 * u := by omega
    omega
  have : 8 * n < 8 * e' := by
    rw [hn8, h8e]
    exact hcmp
  exact Nat.lt_of_mul_lt_mul_left this


/-! ## 6b.  One light step, then a run past the combined ceiling -/

/-- Nine copies of `3^{v'}` fit inside `3^{v+v'}` once `v ≥ 2`. -/
private theorem nine_le_pow_of_two {v v' : Nat} (hv : 2 ≤ v) :
    9 * 3 ^ v' ≤ 3 ^ (v + v') := by
  have hpow : (9 : Nat) * 3 ^ v' = 3 ^ (v' + 2) := by
    calc
      (9 : Nat) * 3 ^ v' = 3 ^ 2 * 3 ^ v' := by rw [show (9 : Nat) = 3 ^ 2 by decide]
      _ = 3 ^ (2 + v') := by rw [← Nat.pow_add]
      _ = 3 ^ (v' + 2) := by rw [Nat.add_comm]
  rw [hpow]
  exact Nat.pow_le_pow_right (by decide : (1 : Nat) ≤ 3) (by omega)

/-- If `A + C ≤ B` and `A ≤ B`, the same gap absorbs every larger cofactor. -/
private theorem add_le_mul_of_add_le {A B C u : Nat} (hAB : A ≤ B) (hC : A + C ≤ B)
    (hu : 1 ≤ u) : A * u + C ≤ B * u := by
  have hsplit : A * u + C = A * (u - 1) + (A + C) := by
    calc
      A * u + C = A * ((u - 1) + 1) + C :=
        congrArg (fun t => A * t + C) (Nat.sub_add_cancel hu).symm
      _ = A * (u - 1) + A * 1 + C := by rw [Nat.mul_add]
      _ = A * (u - 1) + A + C := by rw [Nat.mul_one]
      _ = A * (u - 1) + (A + C) := by rw [Nat.add_assoc]
  rw [hsplit]
  have h1 : A * (u - 1) ≤ B * (u - 1) := Nat.mul_le_mul_right _ hAB
  have h2 : A * (u - 1) + (A + C) ≤ B * (u - 1) + B := Nat.add_le_add h1 hC
  have h3 : B * (u - 1) + B = B * u := by
    calc
      B * (u - 1) + B = B * (u - 1) + B * 1 := by rw [Nat.mul_one]
      _ = B * ((u - 1) + 1) := by rw [← Nat.mul_add]
      _ = B * u := congrArg (fun t => B * t) (Nat.sub_add_cancel hu)
  rwa [h3] at h2

/-- **Coefficient form.**  For `v ≥ 2` and a single extra halving, if
`3^{v+v'} < 2^{v+v'+W'}`, every positive cofactor satisfies the two-step
drop inequality. -/
private theorem one_then_long_coeff {v v' W' u : Nat} (hv : 2 ≤ v) (hu : 1 ≤ u)
    (hpow : 3 ^ (v + v') < 2 ^ (v + v' + W')) :
    3 ^ v' * (3 ^ v * u + 1) + 2 ^ (v' + W' + 1) ≤
      2 ^ (v + v' + W' + 1) * u := by
  have hone : 3 ^ (v + v') + 1 ≤ 2 ^ (v + v' + W') := Nat.succ_le_of_lt hpow
  have hAm : 3 ^ (v + v') ≤ 2 ^ (v + v' + W') - 1 := Nat.le_sub_of_add_le hone
  have hnine := nine_le_pow_of_two (v' := v') hv
  have hexp : v' + W' + 1 ≤ v + v' + W' - 1 :=
    Nat.le_sub_of_add_le (by omega : v' + W' + 1 + 1 ≤ v + v' + W')
  have h2le : 2 ^ (v' + W' + 1) ≤ 2 ^ (v + v' + W' - 1) := two_pow_le_two_pow hexp
  have hq : (v + v' + W' - 1) + 1 = v + v' + W' := by omega
  have hdouble : 2 ^ (v + v' + W') = 2 * 2 ^ (v + v' + W' - 1) := by
    calc
      2 ^ (v + v' + W') = 2 ^ ((v + v' + W' - 1) + 1) :=
        congrArg (fun t => 2 ^ t) hq.symm
      _ = 2 * 2 ^ (v + v' + W' - 1) := two_pow_succ _
  have hten : 9 * 3 ^ (v + v') + 3 ^ (v + v') = 10 * 3 ^ (v + v') := by
    calc
      9 * 3 ^ (v + v') + 3 ^ (v + v')
          = 9 * 3 ^ (v + v') + 1 * 3 ^ (v + v') := by rw [Nat.one_mul]
      _ = (9 + 1) * 3 ^ (v + v') := by rw [← Nat.add_mul]
      _ = 10 * 3 ^ (v + v') := by rw [show (9 + 1 : Nat) = 10 by decide]
  have hpair : 9 * 3 ^ (v + v') + 9 * 3 ^ v' ≤ 10 * 3 ^ (v + v') := by
    have hle : 9 * 3 ^ (v + v') + 9 * 3 ^ v' ≤
        9 * 3 ^ (v + v') + 3 ^ (v + v') := Nat.add_le_add_left hnine _
    rwa [hten] at hle
  have h10 : 10 * 3 ^ (v + v') ≤ 10 * 2 ^ (v + v' + W') - 10 := by
    have hmul := Nat.mul_le_mul_left 10 hAm
    have hdist : 10 * (2 ^ (v + v' + W') - 1) =
        10 * 2 ^ (v + v' + W') - 10 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rwa [hdist] at hmul
  have h20 : 10 * 2 ^ (v + v' + W') = 20 * 2 ^ (v + v' + W' - 1) := by
    rw [hdouble, ← Nat.mul_assoc]
  have h29 : 10 * 2 ^ (v + v' + W') + 9 * 2 ^ (v + v' + W' - 1) =
      29 * 2 ^ (v + v' + W' - 1) := by
    rw [h20, ← Nat.add_mul, show (20 + 9 : Nat) = 29 by decide]
  have h36 : 36 * 2 ^ (v + v' + W' - 1) = 9 * 2 ^ (v + v' + W' + 1) := by
    have hadd : (v + v' + W' - 1) + 2 = v + v' + W' + 1 := by omega
    calc
      36 * 2 ^ (v + v' + W' - 1)
          = (9 * 4) * 2 ^ (v + v' + W' - 1) := by
            rw [show (36 : Nat) = 9 * 4 by decide]
      _ = 9 * (4 * 2 ^ (v + v' + W' - 1)) := by rw [Nat.mul_assoc]
      _ = 9 * (2 ^ 2 * 2 ^ (v + v' + W' - 1)) := by
            rw [show (4 : Nat) = 2 ^ 2 by decide]
      _ = 9 * 2 ^ (2 + (v + v' + W' - 1)) := by rw [← Nat.pow_add]
      _ = 9 * 2 ^ ((v + v' + W' - 1) + 2) := by rw [Nat.add_comm]
      _ = 9 * 2 ^ (v + v' + W' + 1) := by rw [hadd]
  have hscaled : 9 * (3 ^ (v + v') + 3 ^ v' + 2 ^ (v' + W' + 1)) ≤
      9 * 2 ^ (v + v' + W' + 1) := by
    have hleft : 9 * (3 ^ (v + v') + 3 ^ v' + 2 ^ (v' + W' + 1)) =
        9 * 3 ^ (v + v') + 9 * 3 ^ v' + 9 * 2 ^ (v' + W' + 1) := by
      calc
        9 * (3 ^ (v + v') + 3 ^ v' + 2 ^ (v' + W' + 1))
            = 9 * (3 ^ (v + v') + 3 ^ v') + 9 * 2 ^ (v' + W' + 1) := by
              rw [Nat.mul_add]
        _ = 9 * 3 ^ (v + v') + 9 * 3 ^ v' + 9 * 2 ^ (v' + W' + 1) := by
              rw [Nat.mul_add]
    rw [hleft]
    have hstep1 : 9 * 3 ^ (v + v') + 9 * 3 ^ v' + 9 * 2 ^ (v' + W' + 1) ≤
        10 * 3 ^ (v + v') + 9 * 2 ^ (v' + W' + 1) :=
      Nat.add_le_add_right hpair _
    have hstep2 : 10 * 3 ^ (v + v') + 9 * 2 ^ (v' + W' + 1) ≤
        10 * 2 ^ (v + v' + W') - 10 + 9 * 2 ^ (v' + W' + 1) :=
      Nat.add_le_add_right h10 _
    have hstep3 : 10 * 2 ^ (v + v' + W') - 10 + 9 * 2 ^ (v' + W' + 1) ≤
        10 * 2 ^ (v + v' + W') - 10 + 9 * 2 ^ (v + v' + W' - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 9 h2le) _
    have hstep4 : 10 * 2 ^ (v + v' + W') - 10 + 9 * 2 ^ (v + v' + W' - 1) ≤
        10 * 2 ^ (v + v' + W') + 9 * 2 ^ (v + v' + W' - 1) :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hstep5 : 10 * 2 ^ (v + v' + W') + 9 * 2 ^ (v + v' + W' - 1) ≤
        9 * 2 ^ (v + v' + W' + 1) := by
      rw [h29, ← h36]
      exact Nat.mul_le_mul_right _ (by decide : (29 : Nat) ≤ 36)
    exact Nat.le_trans hstep1 (Nat.le_trans hstep2
      (Nat.le_trans hstep3 (Nat.le_trans hstep4 hstep5)))
  have hC : 3 ^ (v + v') + (3 ^ v' + 2 ^ (v' + W' + 1)) ≤
      2 ^ (v + v' + W' + 1) := by
    have h9pos : 0 < (9 : Nat) := by decide
    have hle := Nat.le_of_mul_le_mul_left hscaled h9pos
    simpa [Nat.add_assoc] using hle
  have hAB : 3 ^ (v + v') ≤ 2 ^ (v + v' + W' + 1) :=
    Nat.le_trans hAm (Nat.le_trans (Nat.sub_le _ _)
      (two_pow_le_two_pow (Nat.le_succ _)))
  have hmul := add_le_mul_of_add_le hAB hC hu
  calc
    3 ^ v' * (3 ^ v * u + 1) + 2 ^ (v' + W' + 1)
        = 3 ^ v' * (3 ^ v * u) + 3 ^ v' + 2 ^ (v' + W' + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
    _ = 3 ^ v' * 3 ^ v * u + 3 ^ v' + 2 ^ (v' + W' + 1) := by
          rw [← Nat.mul_assoc]
    _ = 3 ^ (v' + v) * u + 3 ^ v' + 2 ^ (v' + W' + 1) := by
          rw [← Nat.pow_add]
    _ = 3 ^ (v + v') * u + (3 ^ v' + 2 ^ (v' + W' + 1)) := by
          rw [Nat.add_comm v' v, ← Nat.add_assoc]
    _ ≤ 2 ^ (v + v' + W' + 1) * u := hmul

/-- **One light step, then a long run.**  An excursion with a single extra
halving and run length at least `2`, followed by a run whose extra halvings
meet `⌈log₂(3^{v+v'})⌉ − (v + v')`, lands strictly below the original
start. -/
theorem drop_of_W_one_then_long {n v u e v' u' W' e' : Nat}
    (h : IsExcursion n v u 1 e) (h' : IsExcursion e v' u' W' e')
    (hv : 2 ≤ v) (hpow : 3 ^ (v + v') < 2 ^ (v + v' + W')) : e' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  refine (drop_iff_two_expanded h h').mpr ?_
  have hineq := one_then_long_coeff hv hu hpow
  have hsub : 3 ^ v * u + 2 ^ 1 - 1 = 3 ^ v * u + 1 := by
    rw [Nat.pow_one]
    omega
  have hexp1 : 1 + v' + W' = v' + W' + 1 := by omega
  have hexp2 : v + 1 + v' + W' = v + v' + W' + 1 := by omega
  rw [hsub, hexp1, hexp2]
  exact hineq

/-- Nine copies of the light error `3^{v'} (2^W − 1)` fit in `3^{v+v'}`. -/
private theorem nine_light_error {v W v' : Nat} (hv : 4 ≤ v)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v) :
    9 * (3 ^ v' * (2 ^ W - 1)) ≤ 3 ^ (v + v') := by
  have h16 : (16 : Nat) ≤ 2 ^ v := by
    simpa using two_pow_le_two_pow hv
  have h9mod : (9 : Nat) ≤ 2 ^ v - 1 := by
    have h15 : (15 : Nat) ≤ 2 ^ v - 1 := Nat.le_sub_of_add_le h16
    exact Nat.le_trans (by decide : (9 : Nat) ≤ 15) h15
  have hprod : 2 ^ W * (2 ^ v - 1) ≤ 3 ^ v - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlight)
  have h9W : 9 * 2 ^ W ≤ 3 ^ v - 1 := by
    have hmul : 9 * 2 ^ W ≤ (2 ^ v - 1) * 2 ^ W :=
      Nat.mul_le_mul_right _ h9mod
    have hcomm : (2 ^ v - 1) * 2 ^ W = 2 ^ W * (2 ^ v - 1) := Nat.mul_comm _ _
    exact Nat.le_trans hmul (hcomm ▸ hprod)
  have h81 : (81 : Nat) ≤ 3 ^ v := by
    simpa using Nat.pow_le_pow_right (by decide : (1 : Nat) ≤ 3) hv
  have h9base : (9 : Nat) ≤ 3 ^ v - 1 :=
    Nat.le_sub_of_add_le (Nat.le_trans (by decide : (10 : Nat) ≤ 81) h81)
  have hsub : 9 * (2 ^ W - 1) ≤ 3 ^ v := by
    have hdist : 9 * (2 ^ W - 1) = 9 * 2 ^ W - 9 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hdist]
    have hle : 9 * 2 ^ W - 9 ≤ 3 ^ v - 1 - 9 := Nat.sub_le_sub_right h9W 9
    have hten : 3 ^ v - 1 - 9 = 3 ^ v - 10 := by rw [Nat.sub_sub]
    exact Nat.le_trans (hten ▸ hle) (Nat.sub_le _ _)
  have hmul := Nat.mul_le_mul_left (3 ^ v') hsub
  have hre : 3 ^ v' * (9 * (2 ^ W - 1)) = 9 * (3 ^ v' * (2 ^ W - 1)) := by
    calc
      3 ^ v' * (9 * (2 ^ W - 1)) = 3 ^ v' * 9 * (2 ^ W - 1) := by
        rw [← Nat.mul_assoc]
      _ = 9 * 3 ^ v' * (2 ^ W - 1) := by rw [Nat.mul_comm (3 ^ v')]
      _ = 9 * (3 ^ v' * (2 ^ W - 1)) := by rw [Nat.mul_assoc]
  have hpow : 3 ^ v' * 3 ^ v = 3 ^ (v + v') := by
    rw [← Nat.pow_add, Nat.add_comm]
  exact hpow ▸ hre ▸ hmul

/-- **Coefficient form.**  A light run of length at least `4`, followed by a
run meeting `3^{v+v'} < 2^{v+v'+W+W'−1}`, satisfies the two-step drop
inequality for every positive cofactor. -/
private theorem light_then_long_coeff {v u W v' W' : Nat}
    (hv : 4 ≤ v) (hu : 1 ≤ u)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hpow : 3 ^ (v + v') < 2 ^ (v + v' + W + W' - 1)) :
    3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + 2 ^ (W + v' + W') ≤
      2 ^ (v + W + v' + W') * u := by
  have hone : 3 ^ (v + v') + 1 ≤ 2 ^ (v + v' + W + W' - 1) :=
    Nat.succ_le_of_lt hpow
  have hAm : 3 ^ (v + v') ≤ 2 ^ (v + v' + W + W' - 1) - 1 :=
    Nat.le_sub_of_add_le hone
  have herr := nine_light_error (v' := v') hv hlight
  have hexp : W + v' + W' ≤ v + v' + W + W' - 4 :=
    Nat.le_sub_of_add_le (by omega : W + v' + W' + 4 ≤ v + v' + W + W')
  have h2le : 2 ^ (W + v' + W') ≤ 2 ^ (v + v' + W + W' - 4) :=
    two_pow_le_two_pow hexp
  have hq3 : v + v' + W + W' - 4 + 3 = v + v' + W + W' - 1 := by omega
  have hq4 : v + v' + W + W' - 4 + 4 = v + v' + W + W' := by omega
  have h8 : 2 ^ (v + v' + W + W' - 1) = 8 * 2 ^ (v + v' + W + W' - 4) := by
    calc
      2 ^ (v + v' + W + W' - 1)
          = 2 ^ (v + v' + W + W' - 4 + 3) :=
            congrArg (fun t => 2 ^ t) hq3.symm
      _ = 2 ^ (v + v' + W + W' - 4) * 2 ^ 3 := Nat.pow_add _ _ _
      _ = 2 ^ (v + v' + W + W' - 4) * 8 := by rw [show 2 ^ 3 = 8 by decide]
      _ = 8 * 2 ^ (v + v' + W + W' - 4) := Nat.mul_comm _ _
  have h16 : 2 ^ (v + v' + W + W') = 16 * 2 ^ (v + v' + W + W' - 4) := by
    calc
      2 ^ (v + v' + W + W')
          = 2 ^ (v + v' + W + W' - 4 + 4) :=
            congrArg (fun t => 2 ^ t) hq4.symm
      _ = 2 ^ (v + v' + W + W' - 4) * 2 ^ 4 := Nat.pow_add _ _ _
      _ = 2 ^ (v + v' + W + W' - 4) * 16 := by rw [show 2 ^ 4 = 16 by decide]
      _ = 16 * 2 ^ (v + v' + W + W' - 4) := Nat.mul_comm _ _
  have hten : 9 * 3 ^ (v + v') + 3 ^ (v + v') = 10 * 3 ^ (v + v') := by
    calc
      9 * 3 ^ (v + v') + 3 ^ (v + v')
          = 9 * 3 ^ (v + v') + 1 * 3 ^ (v + v') := by rw [Nat.one_mul]
      _ = (9 + 1) * 3 ^ (v + v') := by rw [← Nat.add_mul]
      _ = 10 * 3 ^ (v + v') := by rw [show (9 + 1 : Nat) = 10 by decide]
  have hpair : 9 * 3 ^ (v + v') + 9 * (3 ^ v' * (2 ^ W - 1)) ≤
      10 * 3 ^ (v + v') := by
    have hle : 9 * 3 ^ (v + v') + 9 * (3 ^ v' * (2 ^ W - 1)) ≤
        9 * 3 ^ (v + v') + 3 ^ (v + v') := Nat.add_le_add_left herr _
    rwa [hten] at hle
  have h10 : 10 * 3 ^ (v + v') ≤ 10 * 2 ^ (v + v' + W + W' - 1) - 10 := by
    have hmul := Nat.mul_le_mul_left 10 hAm
    have hdist : 10 * (2 ^ (v + v' + W + W' - 1) - 1) =
        10 * 2 ^ (v + v' + W + W' - 1) - 10 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rwa [hdist] at hmul
  have h80 : 10 * 2 ^ (v + v' + W + W' - 1) =
      80 * 2 ^ (v + v' + W + W' - 4) := by
    rw [h8, ← Nat.mul_assoc]
  have h89 : 10 * 2 ^ (v + v' + W + W' - 1) + 9 * 2 ^ (v + v' + W + W' - 4) =
      89 * 2 ^ (v + v' + W + W' - 4) := by
    rw [h80, ← Nat.add_mul, show (80 + 9 : Nat) = 89 by decide]
  have h144 : 144 * 2 ^ (v + v' + W + W' - 4) =
      9 * 2 ^ (v + v' + W + W') := by
    calc
      144 * 2 ^ (v + v' + W + W' - 4)
          = (9 * 16) * 2 ^ (v + v' + W + W' - 4) := by
            rw [show (144 : Nat) = 9 * 16 by decide]
      _ = 9 * (16 * 2 ^ (v + v' + W + W' - 4)) := by rw [Nat.mul_assoc]
      _ = 9 * 2 ^ (v + v' + W + W') := by rw [← h16]
  have hscaled : 9 * (3 ^ (v + v') + 3 ^ v' * (2 ^ W - 1) +
      2 ^ (W + v' + W')) ≤ 9 * 2 ^ (v + v' + W + W') := by
    have hleft : 9 * (3 ^ (v + v') + 3 ^ v' * (2 ^ W - 1) +
        2 ^ (W + v' + W')) =
        9 * 3 ^ (v + v') + 9 * (3 ^ v' * (2 ^ W - 1)) +
          9 * 2 ^ (W + v' + W') := by
      calc
        9 * (3 ^ (v + v') + 3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W'))
            = 9 * (3 ^ (v + v') + 3 ^ v' * (2 ^ W - 1)) +
                9 * 2 ^ (W + v' + W') := by rw [Nat.mul_add]
        _ = 9 * 3 ^ (v + v') + 9 * (3 ^ v' * (2 ^ W - 1)) +
              9 * 2 ^ (W + v' + W') := by rw [Nat.mul_add]
    rw [hleft]
    have hstep1 : 9 * 3 ^ (v + v') + 9 * (3 ^ v' * (2 ^ W - 1)) +
        9 * 2 ^ (W + v' + W') ≤
        10 * 3 ^ (v + v') + 9 * 2 ^ (W + v' + W') :=
      Nat.add_le_add_right hpair _
    have hstep2 : 10 * 3 ^ (v + v') + 9 * 2 ^ (W + v' + W') ≤
        10 * 2 ^ (v + v' + W + W' - 1) - 10 + 9 * 2 ^ (W + v' + W') :=
      Nat.add_le_add_right h10 _
    have hstep3 : 10 * 2 ^ (v + v' + W + W' - 1) - 10 +
        9 * 2 ^ (W + v' + W') ≤
        10 * 2 ^ (v + v' + W + W' - 1) - 10 +
          9 * 2 ^ (v + v' + W + W' - 4) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 9 h2le) _
    have hstep4 : 10 * 2 ^ (v + v' + W + W' - 1) - 10 +
        9 * 2 ^ (v + v' + W + W' - 4) ≤
        10 * 2 ^ (v + v' + W + W' - 1) +
          9 * 2 ^ (v + v' + W + W' - 4) :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hstep5 : 10 * 2 ^ (v + v' + W + W' - 1) +
        9 * 2 ^ (v + v' + W + W' - 4) ≤
        9 * 2 ^ (v + v' + W + W') := by
      rw [h89, ← h144]
      exact Nat.mul_le_mul_right _ (by decide : (89 : Nat) ≤ 144)
    exact Nat.le_trans hstep1 (Nat.le_trans hstep2
      (Nat.le_trans hstep3 (Nat.le_trans hstep4 hstep5)))
  have hC : 3 ^ (v + v') + (3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W')) ≤
      2 ^ (v + v' + W + W') := by
    have h9pos : 0 < (9 : Nat) := by decide
    have hle := Nat.le_of_mul_le_mul_left hscaled h9pos
    simpa [Nat.add_assoc] using hle
  have hAB : 3 ^ (v + v') ≤ 2 ^ (v + v' + W + W') :=
    Nat.le_trans hAm (Nat.le_trans (Nat.sub_le _ _)
      (two_pow_le_two_pow (Nat.sub_le _ _)))
  have hmul := add_le_mul_of_add_le hAB hC hu
  have hsplit : 3 ^ v * u + 2 ^ W - 1 = 3 ^ v * u + (2 ^ W - 1) :=
    Nat.add_sub_assoc (Nat.one_le_pow W 2 (by decide)) _
  calc
    3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + 2 ^ (W + v' + W')
        = 3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) + 2 ^ (W + v' + W') := by
          rw [hsplit]
    _ = 3 ^ v' * (3 ^ v * u) + 3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W') := by
          rw [Nat.mul_add]
    _ = 3 ^ v' * 3 ^ v * u + 3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W') := by
          rw [← Nat.mul_assoc]
    _ = 3 ^ (v' + v) * u + 3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W') := by
          rw [← Nat.pow_add]
    _ = 3 ^ (v + v') * u + (3 ^ v' * (2 ^ W - 1) + 2 ^ (W + v' + W')) := by
          rw [Nat.add_comm v' v, ← Nat.add_assoc]
    _ ≤ 2 ^ (v + v' + W + W') * u := hmul
    _ = 2 ^ (v + W + v' + W') * u := by
          rw [show v + v' + W + W' = v + W + v' + W' by omega]

/-- **A light step, then a long run.**  Run length at least `4`, a light
extra-halving count, and a next run meeting
`3^{v+v'} < 2^{v+v'+W+W'−1}`, land strictly below the original start. -/
theorem drop_of_light_then_long {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hpow : 3 ^ (v + v') < 2 ^ (v + v' + W + W' - 1)) : e' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  exact (drop_iff_two_expanded h h').mpr
    (light_then_long_coeff hv hu hlight hpow)

/-- Eight copies of the first-step error still fit in `3^{v+v'+v''}`. -/
private theorem eight_first_error {v W v' v'' : Nat} (hv : 4 ≤ v)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v) :
    8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) ≤ 3 ^ (v + v' + v'') := by
  have h9 := nine_light_error (v' := v') hv hlight
  have hmul := Nat.mul_le_mul_left (3 ^ v'') h9
  have hre : 3 ^ v'' * (9 * (3 ^ v' * (2 ^ W - 1))) =
      9 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) := by
    calc
      3 ^ v'' * (9 * (3 ^ v' * (2 ^ W - 1)))
          = 3 ^ v'' * 9 * (3 ^ v' * (2 ^ W - 1)) := by rw [← Nat.mul_assoc]
      _ = 9 * 3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) := by rw [Nat.mul_comm (3 ^ v'')]
      _ = 9 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) := by rw [Nat.mul_assoc]
  have hpow : 3 ^ v'' * 3 ^ (v + v') = 3 ^ (v + v' + v'') := by
    rw [← Nat.pow_add, Nat.add_comm]
  have h9m : 9 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) ≤
      3 ^ (v + v' + v'') := by
    rw [← hre, ← hpow]
    exact hmul
  exact Nat.le_trans (Nat.mul_le_mul_right _ (by decide : (8 : Nat) ≤ 9)) h9m

/-- A short second step keeps eight copies of its error inside `3^{v+v'+v''}`. -/
private theorem eight_middle_error {v W v' W' v'' : Nat} (hv : 4 ≤ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v')) :
    8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) ≤ 3 ^ (v + v' + v'') := by
  have h3 : 3 ≤ v - 1 := Nat.le_sub_of_add_le (by omega : (3 : Nat) + 1 ≤ v)
  have h8le : (8 : Nat) ≤ 2 ^ (v - 1) := by
    simpa using two_pow_le_two_pow h3
  have hmul8 : 8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) ≤
      2 ^ (v - 1) * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) :=
    Nat.mul_le_mul_right _ h8le
  have hadd : v - 1 + (W + v') = v + v' + W - 1 := by omega
  have hjoin : 2 ^ (v - 1) * 2 ^ (W + v') = 2 ^ (v + v' + W - 1) := by
    rw [← Nat.pow_add, hadd]
  have hexp : v + v' + W - 1 + W' = v + v' + W + W' - 1 :=
    (Nat.sub_add_comm (by omega : (1 : Nat) ≤ v + v' + W)).symm
  have hdist : 2 ^ (v + v' + W - 1) * (2 ^ W' - 1) =
      2 ^ (v + v' + W + W' - 1) - 2 ^ (v + v' + W - 1) := by
    calc
      2 ^ (v + v' + W - 1) * (2 ^ W' - 1)
          = 2 ^ (v + v' + W - 1) * 2 ^ W' - 2 ^ (v + v' + W - 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (v + v' + W - 1 + W') - 2 ^ (v + v' + W - 1) := by
            rw [← Nat.pow_add]
      _ = 2 ^ (v + v' + W + W' - 1) - 2 ^ (v + v' + W - 1) := by rw [hexp]
  have hhalf : (2 ^ W' - 1) * 2 ^ (v + v' + W - 1) ≤ 3 ^ (v + v') := by
    have hcomm : (2 ^ W' - 1) * 2 ^ (v + v' + W - 1) =
        2 ^ (v + v' + W - 1) * (2 ^ W' - 1) := Nat.mul_comm _ _
    have hle : 2 ^ (v + v' + W - 1) * (2 ^ W' - 1) ≤
        2 ^ (v + v' + W + W' - 1) := by
      rw [hdist]
      exact Nat.sub_le _ _
    exact Nat.le_trans (hcomm ▸ hle) hshort
  exact Nat.le_trans hmul8 (by
    have hpush : 2 ^ (v - 1) * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) =
        3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (v + v' + W - 1)) := by
      calc
        2 ^ (v - 1) * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))
            = 3 ^ v'' * (2 ^ (v - 1) * ((2 ^ W' - 1) * 2 ^ (W + v'))) :=
              Nat.mul_left_comm _ _ _
        _ = 3 ^ v'' * ((2 ^ W' - 1) * (2 ^ (v - 1) * 2 ^ (W + v'))) :=
              congrArg (fun t => 3 ^ v'' * t) (Nat.mul_left_comm _ _ _)
        _ = 3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (v + v' + W - 1)) := by
              rw [hjoin]
    have hpow : 3 ^ v'' * 3 ^ (v + v') = 3 ^ (v + v' + v'') := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hle : 3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (v + v' + W - 1)) ≤
        3 ^ (v + v' + v'') := by
      rw [← hpow]
      exact Nat.mul_le_mul_left _ hhalf
    rwa [hpush])

/-- **Coefficient form.**  A light length of at least `4`, a second run
short of `3^{v+v'} < 2^{v+v'+W+W'−1}`, and a third run meeting
`3^{v+v'+v''} < 2^{v+v'+v''+W+W'+W''−1}`, satisfy the three-step drop
inequality for every positive cofactor. -/
private theorem short_then_long_coeff {v u W v' W' v'' W'' : Nat}
    (hv : 4 ≤ v) (hu : 1 ≤ u)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hpow : 3 ^ (v + v' + v'') < 2 ^ (v + v' + v'' + W + W' + W'' - 1)) :
    3 ^ v'' * (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
        (2 ^ W' - 1) * 2 ^ (W + v')) +
      2 ^ (W + v' + W' + v'' + W'') ≤
      2 ^ (v + W + v' + W' + v'' + W'') * u := by
  have hone : 3 ^ (v + v' + v'') + 1 ≤
      2 ^ (v + v' + v'' + W + W' + W'' - 1) := Nat.succ_le_of_lt hpow
  have hAm : 3 ^ (v + v' + v'') ≤
      2 ^ (v + v' + v'' + W + W' + W'' - 1) - 1 := Nat.le_sub_of_add_le hone
  have hE1 := eight_first_error (v' := v') (v'' := v'') hv hlight
  have hE2 := eight_middle_error (v' := v') (v'' := v'') hv hshort
  have hexp : W + v' + W' + v'' + W'' ≤
      v + v' + v'' + W + W' + W'' - 4 :=
    Nat.le_sub_of_add_le (by omega :
      W + v' + W' + v'' + W'' + 4 ≤ v + v' + v'' + W + W' + W'')
  have h2le : 2 ^ (W + v' + W' + v'' + W'') ≤
      2 ^ (v + v' + v'' + W + W' + W'' - 4) := two_pow_le_two_pow hexp
  have hq : v + v' + v'' + W + W' + W'' - 4 + 3 =
      v + v' + v'' + W + W' + W'' - 1 := by omega
  have hfull : v + v' + v'' + W + W' + W'' - 1 + 1 =
      v + v' + v'' + W + W' + W'' := by omega
  have h8pow : 8 * 2 ^ (v + v' + v'' + W + W' + W'' - 4) =
      2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
    calc
      8 * 2 ^ (v + v' + v'' + W + W' + W'' - 4)
          = 2 ^ 3 * 2 ^ (v + v' + v'' + W + W' + W'' - 4) := by
            rw [show (8 : Nat) = 2 ^ 3 by decide]
      _ = 2 ^ (3 + (v + v' + v'' + W + W' + W'' - 4)) := by rw [← Nat.pow_add]
      _ = 2 ^ (v + v' + v'' + W + W' + W'' - 4 + 3) := by rw [Nat.add_comm]
      _ = 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by rw [hq]
  have h2p : 8 * 2 ^ (W + v' + W' + v'' + W'') ≤
      2 ^ (v + v' + v'' + W + W' + W'' - 1) :=
    Nat.le_trans (Nat.mul_le_mul_left 8 h2le) (Nat.le_of_eq h8pow)
  have hten : 8 * 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'') +
      3 ^ (v + v' + v'') = 10 * 3 ^ (v + v' + v'') := by
    calc
      8 * 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'')
          = 8 * 3 ^ (v + v' + v'') + 1 * 3 ^ (v + v' + v'') +
              3 ^ (v + v' + v'') := by rw [Nat.one_mul]
      _ = (8 + 1) * 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'') := by
            rw [← Nat.add_mul]
      _ = (8 + 1) * 3 ^ (v + v' + v'') + 1 * 3 ^ (v + v' + v'') := by
            rw [Nat.one_mul]
      _ = (8 + 1 + 1) * 3 ^ (v + v' + v'') := by rw [← Nat.add_mul]
      _ = 10 * 3 ^ (v + v' + v'') := by
            rw [show (8 + 1 + 1 : Nat) = 10 by decide]
  have hboth : 8 * 3 ^ (v + v' + v'') +
      8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
      8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) ≤
      10 * 3 ^ (v + v' + v'') := by
    have h1 : 8 * 3 ^ (v + v' + v'') +
        8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) ≤
        8 * 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'') :=
      Nat.add_le_add_left hE1 _
    have h2 : 8 * 3 ^ (v + v' + v'') +
        8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
        8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) ≤
        8 * 3 ^ (v + v' + v'') + 3 ^ (v + v' + v'') +
          3 ^ (v + v' + v'') :=
      Nat.add_le_add h1 hE2
    rwa [hten] at h2
  have h10 : 10 * 3 ^ (v + v' + v'') ≤
      10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 := by
    have hmul := Nat.mul_le_mul_left 10 hAm
    have hdist : 10 * (2 ^ (v + v' + v'' + W + W' + W'' - 1) - 1) =
        10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rwa [hdist] at hmul
  have h11 : 10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) +
      2 ^ (v + v' + v'' + W + W' + W'' - 1) =
      11 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
    calc
      10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) +
          2 ^ (v + v' + v'' + W + W' + W'' - 1)
          = 10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) +
              1 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by rw [Nat.one_mul]
      _ = (10 + 1) * 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
            rw [← Nat.add_mul]
      _ = 11 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
            rw [show (10 + 1 : Nat) = 11 by decide]
  have h16 : 16 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) =
      8 * 2 ^ (v + v' + v'' + W + W' + W'') := by
    calc
      16 * 2 ^ (v + v' + v'' + W + W' + W'' - 1)
          = 8 * 2 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
            rw [show (16 : Nat) = 8 * 2 by decide]
      _ = 8 * (2 * 2 ^ (v + v' + v'' + W + W' + W'' - 1)) := by
            rw [Nat.mul_assoc]
      _ = 8 * 2 ^ (v + v' + v'' + W + W' + W'' - 1 + 1) := by
            rw [← two_pow_succ]
      _ = 8 * 2 ^ (v + v' + v'' + W + W' + W'') := by rw [hfull]
  have hscaled : 8 * (3 ^ (v + v' + v'') +
      3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
      3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
      2 ^ (W + v' + W' + v'' + W'')) ≤
      8 * 2 ^ (v + v' + v'' + W + W' + W'') := by
    have hleft : 8 * (3 ^ (v + v' + v'') +
        3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
        3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
        2 ^ (W + v' + W' + v'' + W'')) =
        8 * 3 ^ (v + v' + v'') +
          8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          8 * 2 ^ (W + v' + W' + v'' + W'') := by
      calc
        8 * (3 ^ (v + v' + v'') + 3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
            3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
            2 ^ (W + v' + W' + v'' + W''))
            = 8 * (3 ^ (v + v' + v'') + 3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
                3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
              8 * 2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
        _ = 8 * (3 ^ (v + v' + v'') + 3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
              8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
              8 * 2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
        _ = 8 * 3 ^ (v + v' + v'') + 8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
              8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
              8 * 2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
    rw [hleft]
    have hstep1 : 8 * 3 ^ (v + v' + v'') +
        8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
        8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
        8 * 2 ^ (W + v' + W' + v'' + W'') ≤
        10 * 3 ^ (v + v' + v'') + 8 * 2 ^ (W + v' + W' + v'' + W'') :=
      Nat.add_le_add_right hboth _
    have hstep2 : 10 * 3 ^ (v + v' + v'') +
        8 * 2 ^ (W + v' + W' + v'' + W'') ≤
        10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 +
          8 * 2 ^ (W + v' + W' + v'' + W'') :=
      Nat.add_le_add_right h10 _
    have hstep3 : 10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 +
        8 * 2 ^ (W + v' + W' + v'' + W'') ≤
        10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 +
          2 ^ (v + v' + v'' + W + W' + W'' - 1) :=
      Nat.add_le_add_left h2p _
    have hstep4 : 10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) - 10 +
        2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤
        10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) +
          2 ^ (v + v' + v'' + W + W' + W'' - 1) :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hstep5 : 10 * 2 ^ (v + v' + v'' + W + W' + W'' - 1) +
        2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤
        8 * 2 ^ (v + v' + v'' + W + W' + W'') := by
      rw [h11, ← h16]
      exact Nat.mul_le_mul_right _ (by decide : (11 : Nat) ≤ 16)
    exact Nat.le_trans hstep1 (Nat.le_trans hstep2
      (Nat.le_trans hstep3 (Nat.le_trans hstep4 hstep5)))
  have hC : 3 ^ (v + v' + v'') +
      (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
        (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W''))) ≤
      2 ^ (v + v' + v'' + W + W' + W'') := by
    have h8pos : 0 < (8 : Nat) := by decide
    have hle := Nat.le_of_mul_le_mul_left hscaled h8pos
    simpa [Nat.add_assoc] using hle
  have hAB : 3 ^ (v + v' + v'') ≤ 2 ^ (v + v' + v'' + W + W' + W'') :=
    Nat.le_trans hAm (Nat.le_trans (Nat.sub_le _ _)
      (two_pow_le_two_pow (Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq hfull))))
  have hmul := add_le_mul_of_add_le hAB hC hu
  have hsplit : 3 ^ v * u + 2 ^ W - 1 = 3 ^ v * u + (2 ^ W - 1) :=
    Nat.add_sub_assoc (Nat.one_le_pow W 2 (by decide)) _
  calc
    3 ^ v'' * (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
        (2 ^ W' - 1) * 2 ^ (W + v')) + 2 ^ (W + v' + W' + v'' + W'')
        = 3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) +
            (2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [hsplit]
    _ = 3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1))) +
          3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
    _ = 3 ^ v'' * (3 ^ v' * (3 ^ v * u) + 3 ^ v' * (2 ^ W - 1)) +
          3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
    _ = 3 ^ v'' * (3 ^ v' * (3 ^ v * u)) +
          3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
          3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_add]
    _ = 3 ^ v'' * 3 ^ v' * 3 ^ v * u +
          3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
          3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.mul_assoc, Nat.mul_assoc]
    _ = 3 ^ (v'' + v' + v) * u +
          3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
          3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
          2 ^ (W + v' + W' + v'' + W'') := by rw [← Nat.pow_add, ← Nat.pow_add]
    _ = 3 ^ (v + v' + v'') * u +
          (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)) +
            (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')) +
              2 ^ (W + v' + W' + v'' + W''))) := by
            rw [show v'' + v' + v = v + v' + v'' by omega, ← Nat.add_assoc,
              ← Nat.add_assoc]
    _ ≤ 2 ^ (v + v' + v'' + W + W' + W'') * u := hmul
    _ = 2 ^ (v + W + v' + W' + v'' + W'') * u := by
          rw [show v + v' + v'' + W + W' + W'' =
            v + W + v' + W' + v'' + W'' by omega]

/-- **A short second step, then a long third.**  A light run of length at
least `4` whose next run misses `3^{v+v'} < 2^{v+v'+W+W'−1}`, followed by
a third run meeting `3^{v+v'+v''} < 2^{v+v'+v''+W+W'+W''−1}`, lands strictly
below the original start. -/
theorem drop_of_short_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hpow : 3 ^ (v + v' + v'') < 2 ^ (v + v' + v'' + W + W' + W'' - 1)) :
    e'' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  exact (drop_iff_three_expanded h h' h'').mpr
    (short_then_long_coeff hv hu hlight hshort hpow)


/-! ## 7.  Four steps: two misses, then a long run -/

/-- **Exact four-step landing.**  After `(v, W)`, `(v', W')`, `(v'', W'')`,
`(v''', W''')`,

  `3^{v'''} ( 3^{v''} ( 3^{v'} (3^v u + 2^W − 1) + (2^{W'} − 1) 2^{W+v'} )
    + (2^{W''} − 1) 2^{W+v'+W'+v''} )`

  `= 2^{W+v'+W'+v''+W''+v'''+W'''} e''' + 2^{W+v'+W'+v''+W''+v'''}`. -/
theorem four_step_landing
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e''' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''') :
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
        2 ^ (W + v' + W' + v'' + W'' + v''') := by
  have h3 := three_step_landing h h' h''
  have he1 : e'' + 1 = 2 ^ v''' * u''' := h'''.2.2.2.2.2.1
  have hpeak : 3 ^ v''' * u''' = 2 ^ W''' * e''' + 1 := h'''.2.2.2.2.2.2
  have hW'' : 1 ≤ 2 ^ W'' := Nat.one_le_pow W'' 2 (by decide)
  have hsum : 2 ^ (W + v' + W' + v'') +
      (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'') =
      2 ^ (W + v' + W' + v'' + W'') := by
    calc
      2 ^ (W + v' + W' + v'') + (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')
          = 2 ^ (W + v' + W' + v'') * 1 +
              2 ^ (W + v' + W' + v'') * (2 ^ W'' - 1) := by
            rw [Nat.mul_one, Nat.mul_comm (2 ^ W'' - 1)]
      _ = 2 ^ (W + v' + W' + v'') * (1 + (2 ^ W'' - 1)) := by rw [← Nat.mul_add]
      _ = 2 ^ (W + v' + W' + v'') * 2 ^ W'' := by
            rw [Nat.add_sub_of_le hW'']
      _ = 2 ^ (W + v' + W' + v'' + W'') := by rw [← Nat.pow_add]
  have hinner :
      3 ^ v'' *
          (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
            (2 ^ W' - 1) * 2 ^ (W + v')) +
        (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'') =
      2 ^ (W + v' + W' + v'' + W'' + v''') * u''' := by
    rw [h3]
    calc
      2 ^ (W + v' + W' + v'' + W'') * e'' + 2 ^ (W + v' + W' + v'') +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')
          = 2 ^ (W + v' + W' + v'' + W'') * e'' +
              2 ^ (W + v' + W' + v'' + W'') := by rw [Nat.add_assoc, hsum]
      _ = 2 ^ (W + v' + W' + v'' + W'') * (e'' + 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = 2 ^ (W + v' + W' + v'' + W'') * (2 ^ v''' * u''') := by rw [he1]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * u''' := by
            rw [← Nat.mul_assoc, ← Nat.pow_add]
  calc
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))
        = 3 ^ v''' * (2 ^ (W + v' + W' + v'' + W'' + v''') * u''') := by rw [hinner]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * (3 ^ v''' * u''') := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * (2 ^ W''' * e''' + 1) := by
          rw [hpeak]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * (2 ^ W''' * e''') +
          2 ^ (W + v' + W' + v'' + W'' + v''') := by
          rw [Nat.mul_add, Nat.mul_one]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
          2 ^ (W + v' + W' + v'' + W'' + v''') := by
          rw [← Nat.mul_assoc, ← Nat.pow_add]

/-- **Four-step drop against the original start**, in the last cofactor. -/
theorem drop_iff_four
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e''' : Nat}
    (h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e')
    (_h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''') :
    e''' < n ↔ 3 ^ v''' * u''' + 2 ^ W''' ≤ 2 ^ (v + W''') * u := by
  have hWpos : 0 < 2 ^ W''' := two_pow_pos W'''
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W''' * e''' + 1 = 3 ^ v''' * u''' := h'''.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W''') * u = 2 ^ W''' * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W''' * e''' < 2 ^ W''' * n :=
      Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W''' * e''' + 1 ≤ 2 ^ W''' * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v''' * u''' ≤ 2 ^ W''' * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v''' * u''' + 2 ^ W''' ≤ 2 ^ W''' * n + 2 ^ W''' :=
      Nat.add_le_add_right h2 _
    have h4 : 2 ^ W''' * n + 2 ^ W''' = 2 ^ W''' * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v''' * u''' + 2 ^ W''' ≤ 2 ^ W''' * (n + 1) := by
      rw [← hpow]; exact hle
    have h4 : 2 ^ W''' * (n + 1) = 2 ^ W''' * n + 2 ^ W''' := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v''' * u''' ≤ 2 ^ W''' * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W''' * e''' + 1 ≤ 2 ^ W''' * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W''' * e''' < 2 ^ W''' * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Four-step drop**, expanded in `(v, W, u)` of each step. -/
theorem drop_iff_four_expanded
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e''' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''') :
    e''' < n ↔
      3 ^ v''' *
          (3 ^ v'' *
              (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                (2 ^ W' - 1) * 2 ^ (W + v')) +
            (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
        2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''') * u := by
  have hland := four_step_landing h h' h'' h'''
  have hn1 : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hsum : W + v' + W' + v'' + W'' + v''' + W''' =
      (W + v' + W' + v'' + W'' + v''') + W''' := by omega
  have htot : v + W + v' + W' + v'' + W'' + v''' + W''' =
      v + (W + v' + W' + v'' + W'' + v''' + W''') := by omega
  have hL :
      3 ^ v''' *
          (3 ^ v'' *
              (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                (2 ^ W' - 1) * 2 ^ (W + v')) +
            (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''') =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (e''' + 1) +
        2 ^ (W + v' + W' + v'' + W'' + v''') := by
    rw [hland]
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
          2 ^ (W + v' + W' + v'' + W'' + v''') +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''')
          = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
              2 ^ (W + v' + W' + v'' + W'' + v''' + W''') +
              2 ^ (W + v' + W' + v'' + W'' + v''') := by
            rw [Nat.add_right_comm]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
            2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * 1 +
            2 ^ (W + v' + W' + v'' + W'' + v''') := by rw [Nat.mul_one]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (e''' + 1) +
            2 ^ (W + v' + W' + v'' + W'' + v''') := by
            rw [← Nat.mul_add, Nat.add_assoc]
  have hR : 2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''') * u =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (n + 1) := by
    rw [htot, Nat.pow_add, hn1]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hsplit : 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (e''' + 1) +
      2 ^ (W + v' + W' + v'' + W'' + v''') =
      2 ^ (W + v' + W' + v'' + W'' + v''') *
        (2 ^ W''' * (e''' + 1) + 1) := by
    rw [hsum, Nat.pow_add]
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''') * 2 ^ W''' * (e''' + 1) +
          2 ^ (W + v' + W' + v'' + W'' + v''')
          = 2 ^ (W + v' + W' + v'' + W'' + v''') * (2 ^ W''' * (e''' + 1)) +
              2 ^ (W + v' + W' + v'' + W'' + v''') * 1 := by
            rw [Nat.mul_assoc, Nat.mul_one]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''') *
            (2 ^ W''' * (e''' + 1) + 1) := by rw [← Nat.mul_add]
  have hsplitR : 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (n + 1) =
      2 ^ (W + v' + W' + v'' + W'' + v''') * (2 ^ W''' * (n + 1)) := by
    rw [hsum, Nat.pow_add, Nat.mul_assoc]
  rw [hL, hR, hsplit, hsplitR,
    (mul_le_iff (two_pow_pos (W + v' + W' + v'' + W'' + v'''))).symm]
  have hpeak : 2 ^ W''' * e''' + 1 = 3 ^ v''' * u''' := h'''.2.2.2.2.2.2.symm
  have hleft : 2 ^ W''' * (e''' + 1) + 1 = 3 ^ v''' * u''' + 2 ^ W''' := by
    calc
      2 ^ W''' * (e''' + 1) + 1
          = 2 ^ W''' * e''' + 2 ^ W''' + 1 := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ W''' * e''' + 1 + 2 ^ W''' := by omega
      _ = 3 ^ v''' * u''' + 2 ^ W''' := by rw [hpeak]
  have hright' : 2 ^ W''' * (n + 1) = 2 ^ (v + W''') * u := by
    rw [Nat.pow_add, hn1]
    simp [Nat.mul_assoc, Nat.mul_comm]
  rw [hleft, hright']
  exact drop_iff_four h h' h'' h'''

/-- Eight copies of the third-step error fit when that step missed its exponent. -/
private theorem eight_third_error {v W v' W' v'' W'' v''' : Nat} (hv : 4 ≤ v)
    (hshort : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v'')) :
    8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) ≤
      3 ^ (v + v' + v'' + v''') := by
  have h3 : 3 ≤ v - 1 := Nat.le_sub_of_add_le (by omega : (3 : Nat) + 1 ≤ v)
  have h8le : (8 : Nat) ≤ 2 ^ (v - 1) := by
    simpa using two_pow_le_two_pow h3
  have hmul8 : 8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) ≤
      2 ^ (v - 1) * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) :=
    Nat.mul_le_mul_right _ h8le
  have hadd : v - 1 + (W + v' + W' + v'') = v + v' + v'' + W + W' - 1 := by omega
  have hjoin : 2 ^ (v - 1) * 2 ^ (W + v' + W' + v'') =
      2 ^ (v + v' + v'' + W + W' - 1) := by
    rw [← Nat.pow_add, hadd]
  have hexp : v + v' + v'' + W + W' - 1 + W'' =
      v + v' + v'' + W + W' + W'' - 1 :=
    (Nat.sub_add_comm (by omega : (1 : Nat) ≤ v + v' + v'' + W + W')).symm
  have hdist : 2 ^ (v + v' + v'' + W + W' - 1) * (2 ^ W'' - 1) =
      2 ^ (v + v' + v'' + W + W' + W'' - 1) -
        2 ^ (v + v' + v'' + W + W' - 1) := by
    calc
      2 ^ (v + v' + v'' + W + W' - 1) * (2 ^ W'' - 1)
          = 2 ^ (v + v' + v'' + W + W' - 1) * 2 ^ W'' -
              2 ^ (v + v' + v'' + W + W' - 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (v + v' + v'' + W + W' - 1 + W'') -
            2 ^ (v + v' + v'' + W + W' - 1) := by rw [← Nat.pow_add]
      _ = 2 ^ (v + v' + v'' + W + W' + W'' - 1) -
            2 ^ (v + v' + v'' + W + W' - 1) := by rw [hexp]
  have hhalf : (2 ^ W'' - 1) * 2 ^ (v + v' + v'' + W + W' - 1) ≤
      3 ^ (v + v' + v'') := by
    have hcomm : (2 ^ W'' - 1) * 2 ^ (v + v' + v'' + W + W' - 1) =
        2 ^ (v + v' + v'' + W + W' - 1) * (2 ^ W'' - 1) := Nat.mul_comm _ _
    have hle : 2 ^ (v + v' + v'' + W + W' - 1) * (2 ^ W'' - 1) ≤
        2 ^ (v + v' + v'' + W + W' + W'' - 1) := by
      rw [hdist]
      exact Nat.sub_le _ _
    exact Nat.le_trans (hcomm ▸ hle) hshort
  exact Nat.le_trans hmul8 (by
    have hpush : 2 ^ (v - 1) * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) =
        3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (v + v' + v'' + W + W' - 1)) := by
      calc
        2 ^ (v - 1) * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))
            = 3 ^ v''' * (2 ^ (v - 1) * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) :=
              Nat.mul_left_comm _ _ _
        _ = 3 ^ v''' * ((2 ^ W'' - 1) * (2 ^ (v - 1) * 2 ^ (W + v' + W' + v''))) :=
              congrArg (fun t => 3 ^ v''' * t) (Nat.mul_left_comm _ _ _)
        _ = 3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (v + v' + v'' + W + W' - 1)) := by
              rw [hjoin]
    have hpow : 3 ^ v''' * 3 ^ (v + v' + v'') = 3 ^ (v + v' + v'' + v''') := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hle : 3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (v + v' + v'' + W + W' - 1)) ≤
        3 ^ (v + v' + v'' + v''') := by
      rw [← hpow]
      exact Nat.mul_le_mul_left _ hhalf
    rwa [hpush])

/-- Lift the first-step error bound across the fourth run. -/
private theorem eight_first_error_four {v W v' v'' v''' : Nat} (hv : 4 ≤ v)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v) :
    8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) ≤
      3 ^ (v + v' + v'' + v''') := by
  have h := eight_first_error (v' := v') (v'' := v'') hv hlight
  have hmul := Nat.mul_le_mul_left (3 ^ v''') h
  have hre : 3 ^ v''' * (8 * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) =
      8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpow : 3 ^ v''' * 3 ^ (v + v' + v'') = 3 ^ (v + v' + v'' + v''') := by
    rw [← Nat.pow_add, Nat.add_comm]
  rwa [← hre, ← hpow]

/-- Lift the second-step error bound across the fourth run. -/
private theorem eight_middle_error_four {v W v' W' v'' v''' : Nat} (hv : 4 ≤ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v')) :
    8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) ≤
      3 ^ (v + v' + v'' + v''') := by
  have h := eight_middle_error (v' := v') (v'' := v'') hv hshort
  have hmul := Nat.mul_le_mul_left (3 ^ v''') h
  have hre : 3 ^ v''' * (8 * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) =
      8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpow : 3 ^ v''' * 3 ^ (v + v' + v'') = 3 ^ (v + v' + v'' + v''') := by
    rw [← Nat.pow_add, Nat.add_comm]
  rwa [← hre, ← hpow]

/-- **Coefficient form.**  A light length of at least `4`, second and third
runs short of their cumulative exponents, and a fourth run meeting
`3^{v+v'+v''+v'''} < 2^{v+v'+v''+v'''+W+W'+W''+W'''−1}`, satisfy the
four-step drop inequality for every positive cofactor. -/
private theorem two_misses_then_long_coeff
    {v u W v' W' v'' W'' v''' W''' : Nat}
    (hv : 4 ≤ v) (hu : 1 ≤ u)
    (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hpow : 3 ^ (v + v' + v'' + v''') <
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1)) :
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
      2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''') * u := by
  have hone : 3 ^ (v + v' + v'' + v''') + 1 ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) :=
    Nat.succ_le_of_lt hpow
  have hAm : 3 ^ (v + v' + v'' + v''') ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 1 :=
    Nat.le_sub_of_add_le hone
  have hE1 := eight_first_error_four (v' := v') (v'' := v'') (v''' := v''') hv hlight
  have hE2 := eight_middle_error_four (v' := v') (v'' := v'') (v''' := v''') hv hshort
  have hE3 := eight_third_error (v' := v') (v'' := v'') (v''' := v''') hv hshort3
  have hexp : W + v' + W' + v'' + W'' + v''' + W''' ≤
      v + v' + v'' + v''' + W + W' + W'' + W''' - 4 :=
    Nat.le_sub_of_add_le (by omega :
      W + v' + W' + v'' + W'' + v''' + W''' + 4 ≤
        v + v' + v'' + v''' + W + W' + W'' + W''')
  have h2le : 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 4) :=
    two_pow_le_two_pow hexp
  have hq : v + v' + v'' + v''' + W + W' + W'' + W''' - 4 + 3 =
      v + v' + v'' + v''' + W + W' + W'' + W''' - 1 := by omega
  have hfull : v + v' + v'' + v''' + W + W' + W'' + W''' - 1 + 1 =
      v + v' + v'' + v''' + W + W' + W'' + W''' := by omega
  have h8pow : 8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 4) =
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
    calc
      8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 4)
          = 2 ^ 3 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 4) := by
            rw [show (8 : Nat) = 2 ^ 3 by decide]
      _ = 2 ^ (3 + (v + v' + v'' + v''' + W + W' + W'' + W''' - 4)) := by
            rw [← Nat.pow_add]
      _ = 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 4 + 3) := by
            rw [Nat.add_comm]
      _ = 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by rw [hq]
  have h2p : 8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) :=
    Nat.le_trans (Nat.mul_le_mul_left 8 h2le) (Nat.le_of_eq h8pow)
  have h11a : 8 * 3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') +
      3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') =
      11 * 3 ^ (v + v' + v'' + v''') := by
    let P := 3 ^ (v + v' + v'' + v''')
    change 8 * P + P + P + P = 11 * P
    calc
      8 * P + P + P + P
          = 8 * P + 1 * P + P + P := by rw [Nat.one_mul]
      _ = (8 + 1) * P + P + P := by rw [← Nat.add_mul]
      _ = (8 + 1) * P + 1 * P + P := by rw [Nat.one_mul]
      _ = (8 + 1 + 1) * P + P := by rw [← Nat.add_mul]
      _ = (8 + 1 + 1) * P + 1 * P := by rw [Nat.one_mul]
      _ = (8 + 1 + 1 + 1) * P := by rw [← Nat.add_mul]
      _ = 11 * P := by rw [show (8 + 1 + 1 + 1 : Nat) = 11 by decide]
  have hthree : 8 * 3 ^ (v + v' + v'' + v''') +
      8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
      8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
      8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) ≤
      11 * 3 ^ (v + v' + v'' + v''') := by
    have h1 : 8 * 3 ^ (v + v' + v'' + v''') +
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) ≤
        8 * 3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') :=
      Nat.add_le_add_left hE1 _
    have h2 : 8 * 3 ^ (v + v' + v'' + v''') +
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) ≤
        8 * 3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') +
          3 ^ (v + v' + v'' + v''') :=
      Nat.add_le_add h1 hE2
    have h3 : 8 * 3 ^ (v + v' + v'' + v''') +
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
        8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) ≤
        8 * 3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') +
          3 ^ (v + v' + v'' + v''') + 3 ^ (v + v' + v'' + v''') :=
      Nat.add_le_add h2 hE3
    rwa [h11a] at h3
  have h11b : 11 * 3 ^ (v + v' + v'' + v''') ≤
      11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 := by
    have hmul := Nat.mul_le_mul_left 11 hAm
    have hdist : 11 * (2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 1) =
        11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rwa [hdist] at hmul
  have h12 : 11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) +
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) =
      12 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
    calc
      11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) +
          2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1)
          = 11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) +
              1 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
            rw [Nat.one_mul]
      _ = (11 + 1) * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
            rw [← Nat.add_mul]
      _ = 12 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
            rw [show (11 + 1 : Nat) = 12 by decide]
  have h16 : 16 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) =
      8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') := by
    calc
      16 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1)
          = 8 * 2 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
            rw [show (16 : Nat) = 8 * 2 by decide]
      _ = 8 * (2 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1)) := by
            rw [Nat.mul_assoc]
      _ = 8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1 + 1) := by
            rw [← two_pow_succ]
      _ = 8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') := by rw [hfull]
  have hscaled : 8 * (3 ^ (v + v' + v'' + v''') +
      3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
      3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
      3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''')) ≤
      8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') := by
    have hleft : 8 * (3 ^ (v + v' + v'' + v''') +
        3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
        3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
        3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''')) =
        8 * 3 ^ (v + v' + v'' + v''') +
          8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
          8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
          8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) +
          8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
      simp [Nat.mul_add, Nat.add_assoc]
    rw [hleft]
    have hstep1 : 8 * 3 ^ (v + v' + v'' + v''') +
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
        8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) +
        8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
        11 * 3 ^ (v + v' + v'' + v''') +
          8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') :=
      Nat.add_le_add_right hthree _
    have hstep2 : 11 * 3 ^ (v + v' + v'' + v''') +
        8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
        11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 +
          8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') :=
      Nat.add_le_add_right h11b _
    have hstep3 : 11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 +
        8 * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') ≤
        11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 +
          2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) :=
      Nat.add_le_add_left h2p _
    have hstep4 : 11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) - 11 +
        2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
        11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) +
          2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hstep5 : 11 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) +
        2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
        8 * 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') := by
      rw [h12, ← h16]
      exact Nat.mul_le_mul_right _ (by decide : (12 : Nat) ≤ 16)
    exact Nat.le_trans hstep1 (Nat.le_trans hstep2
      (Nat.le_trans hstep3 (Nat.le_trans hstep4 hstep5)))
  have hC : 3 ^ (v + v' + v'' + v''') +
      (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
        (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
            2 ^ (W + v' + W' + v'' + W'' + v''' + W''')))) ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') := by
    have h8pos : 0 < (8 : Nat) := by decide
    have hle := Nat.le_of_mul_le_mul_left hscaled h8pos
    simpa [Nat.add_assoc] using hle
  have hAB : 3 ^ (v + v' + v'' + v''') ≤
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') :=
    Nat.le_trans hAm (Nat.le_trans (Nat.sub_le _ _)
      (two_pow_le_two_pow (Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq hfull))))
  have hmul := add_le_mul_of_add_le hAB hC hu
  have hsplit : 3 ^ v * u + 2 ^ W - 1 = 3 ^ v * u + (2 ^ W - 1) :=
    Nat.add_sub_assoc (Nat.one_le_pow W 2 (by decide)) _
  calc
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''')
        = 3 ^ v''' *
            (3 ^ v'' *
                (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) +
                  (2 ^ W' - 1) * 2 ^ (W + v')) +
              (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by rw [hsplit]
    _ = 3 ^ v''' *
          (3 ^ v'' *
              (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) +
                (2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' *
          (3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1))) +
            3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u) + 3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u)) +
            3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u))) +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * 3 ^ v'' * 3 ^ v' * 3 ^ v * u +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
    _ = 3 ^ (v''' + v'' + v' + v) * u +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    _ = 3 ^ (v + v' + v'' + v''') * u +
          (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
            (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
              (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
                2 ^ (W + v' + W' + v'' + W'' + v''' + W''')))) := by
          rw [show v''' + v'' + v' + v = v + v' + v'' + v''' by omega]
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ ≤ 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''') * u := hmul
    _ = 2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''') * u := by
          rw [show v + v' + v'' + v''' + W + W' + W'' + W''' =
            v + W + v' + W' + v'' + W'' + v''' + W''' by omega]

/-- **Two short steps, then a long fourth.**  A light run of length at
least `4` whose next two runs miss their cumulative exponents, followed by
a fourth run meeting
`3^{v+v'+v''+v'''} < 2^{v+v'+v''+v'''+W+W'+W''+W'''−1}`, lands strictly
below the original start. -/
theorem drop_of_two_misses_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e''' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hpow : 3 ^ (v + v' + v'' + v''') <
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1)) :
    e''' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  exact (drop_iff_four_expanded h h' h'' h''').mpr
    (two_misses_then_long_coeff hv hu hlight hshort hshort3 hpow)


/-! ## 8.  Spare-bit budget, then five steps -/

/-- Sum of the earlier-run errors fed to the spare-bit budget. -/
def errSum : List Nat → Nat
  | [] => 0
  | e :: t => e + errSum t

/-- Eight copies of a list of errors are at most one copy of `A` per entry. -/
private theorem eight_errSum_le {A : Nat} {errs : List Nat}
    (h : ∀ e, e ∈ errs → 8 * e ≤ A) :
    8 * errSum errs ≤ errs.length * A := by
  induction errs with
  | nil => simp [errSum]
  | cons e t ih =>
    have ht : ∀ x, x ∈ t → 8 * x ≤ A := by
      intro x hx
      exact h x (List.mem_cons_of_mem e hx)
    have ih' := ih ht
    have he : 8 * e ≤ A := h e (by simp)
    calc
      8 * errSum (e :: t)
          = 8 * (e + errSum t) := by simp [errSum]
      _ = 8 * e + 8 * errSum t := by rw [Nat.mul_add]
      _ ≤ A + t.length * A := Nat.add_le_add he ih'
      _ = (e :: t).length * A := by
          simp [List.length_cons, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_mul,
            Nat.one_mul]

/-- **Spare-bit budget.**  Length at least `4` supplies a factor `8`.
Up to seven earlier errors, each fitting eight times in `A`, together with
a terminal power fitting eight times in `2^{S-1}`, stay under `2^S`.
Four errors are the five-step case.  Seven errors are the last length this
factor can absorb. -/
private theorem spare_budget {A T S : Nat} {errs : List Nat}
    (hA : A ≤ 2 ^ (S - 1) - 1) (hS : 1 ≤ S)
    (hlen : errs.length ≤ 7) (h : ∀ e, e ∈ errs → 8 * e ≤ A)
    (hT : 8 * T ≤ 2 ^ (S - 1)) :
    A + errSum errs + T ≤ 2 ^ S := by
  have hsum := eight_errSum_le h
  have hlenA : errs.length * A ≤ 7 * A := Nat.mul_le_mul_right A hlen
  have h15 : 8 * A + 8 * errSum errs ≤ 15 * A := by
    calc
      8 * A + 8 * errSum errs ≤ 8 * A + errs.length * A := Nat.add_le_add_left hsum _
      _ ≤ 8 * A + 7 * A := Nat.add_le_add_left hlenA _
      _ = 15 * A := by rw [← Nat.add_mul, show (8 + 7 : Nat) = 15 by decide]
  have hone : 1 ≤ 2 ^ (S - 1) := Nat.one_le_pow _ _ (by decide)
  have hdist : 15 * (2 ^ (S - 1) - 1) = 15 * 2 ^ (S - 1) - 15 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hAm : 15 * A ≤ 15 * 2 ^ (S - 1) - 15 := by
    have hmul := Nat.mul_le_mul_left 15 hA
    rwa [hdist] at hmul
  have hfull : S - 1 + 1 = S := by omega
  have h16 : 16 * 2 ^ (S - 1) = 8 * 2 ^ S := by
    calc
      16 * 2 ^ (S - 1) = 8 * 2 * 2 ^ (S - 1) := by rw [show (16 : Nat) = 8 * 2 by decide]
      _ = 8 * (2 * 2 ^ (S - 1)) := by rw [Nat.mul_assoc]
      _ = 8 * 2 ^ (S - 1 + 1) := by rw [← two_pow_succ]
      _ = 8 * 2 ^ S := by rw [hfull]
  have hscaled : 8 * (A + errSum errs + T) ≤ 8 * 2 ^ S := by
    calc
      8 * (A + errSum errs + T)
          = 8 * A + 8 * errSum errs + 8 * T := by
            rw [Nat.mul_add, Nat.mul_add]
      _ ≤ 15 * A + 8 * T := Nat.add_le_add_right h15 _
      _ ≤ 15 * 2 ^ (S - 1) - 15 + 8 * T := Nat.add_le_add_right hAm _
      _ ≤ 15 * 2 ^ (S - 1) - 15 + 2 ^ (S - 1) := Nat.add_le_add_left hT _
      _ ≤ 15 * 2 ^ (S - 1) + 2 ^ (S - 1) := Nat.add_le_add_right (Nat.sub_le _ _) _
      _ = 15 * 2 ^ (S - 1) + 1 * 2 ^ (S - 1) := by rw [Nat.one_mul]
      _ = (15 + 1) * 2 ^ (S - 1) := by rw [← Nat.add_mul]
      _ = 16 * 2 ^ (S - 1) := by rw [show (15 + 1 : Nat) = 16 by decide]
      _ = 8 * 2 ^ S := h16
  exact Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < (8 : Nat))

/-- Eight copies of the fourth-step error fit when that step missed its exponent. -/
private theorem eight_fourth_error
    {v W v' W' v'' W'' v''' W''' v4 : Nat} (hv : 4 ≤ v)
    (hshort : 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
      3 ^ (v + v' + v'' + v''')) :
    8 * (3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) ≤
      3 ^ (v + v' + v'' + v''' + v4) := by
  have h3 : 3 ≤ v - 1 := Nat.le_sub_of_add_le (by omega : (3 : Nat) + 1 ≤ v)
  have h8le : (8 : Nat) ≤ 2 ^ (v - 1) := by
    simpa using two_pow_le_two_pow h3
  have hmul8 :
      8 * (3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) ≤
        2 ^ (v - 1) *
          (3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) :=
    Nat.mul_le_mul_right _ h8le
  have hadd : v - 1 + (W + v' + W' + v'' + W'' + v''') =
      v + v' + v'' + v''' + W + W' + W'' - 1 := by omega
  have hjoin : 2 ^ (v - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''') =
      2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) := by
    rw [← Nat.pow_add, hadd]
  have hexp : v + v' + v'' + v''' + W + W' + W'' - 1 + W''' =
      v + v' + v'' + v''' + W + W' + W'' + W''' - 1 :=
    (Nat.sub_add_comm
      (by omega : (1 : Nat) ≤ v + v' + v'' + v''' + W + W' + W'')).symm
  have hdist : 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) * (2 ^ W''' - 1) =
      2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) -
        2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) := by
    calc
      2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) * (2 ^ W''' - 1)
          = 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) * 2 ^ W''' -
              2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1 + W''') -
            2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) := by rw [← Nat.pow_add]
      _ = 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) -
            2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) := by rw [hexp]
  have hhalf : (2 ^ W''' - 1) * 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) ≤
      3 ^ (v + v' + v'' + v''') := by
    have hcomm : (2 ^ W''' - 1) * 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) =
        2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) * (2 ^ W''' - 1) :=
      Nat.mul_comm _ _
    have hle : 2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1) * (2 ^ W''' - 1) ≤
        2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) := by
      rw [hdist]
      exact Nat.sub_le _ _
    exact Nat.le_trans (hcomm ▸ hle) hshort
  exact Nat.le_trans hmul8 (by
    have hpush :
        2 ^ (v - 1) *
            (3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) =
          3 ^ v4 * ((2 ^ W''' - 1) *
            2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1)) := by
      calc
        2 ^ (v - 1) *
            (3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')))
            = 3 ^ v4 * (2 ^ (v - 1) *
                ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) :=
              Nat.mul_left_comm _ _ _
        _ = 3 ^ v4 * ((2 ^ W''' - 1) *
              (2 ^ (v - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))) :=
              congrArg (fun t => 3 ^ v4 * t) (Nat.mul_left_comm _ _ _)
        _ = 3 ^ v4 * ((2 ^ W''' - 1) *
              2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1)) := by rw [hjoin]
    have hpow : 3 ^ v4 * 3 ^ (v + v' + v'' + v''') =
        3 ^ (v + v' + v'' + v''' + v4) := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hle : 3 ^ v4 * ((2 ^ W''' - 1) *
          2 ^ (v + v' + v'' + v''' + W + W' + W'' - 1)) ≤
        3 ^ (v + v' + v'' + v''' + v4) := by
      rw [← hpow]
      exact Nat.mul_le_mul_left _ hhalf
    rwa [hpush])

/-- The four-step product, without its terminal power, is the main term plus
three earlier errors. -/
private theorem four_inner_poly {v u W v' W' v'' W'' v''' : Nat} :
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) =
      3 ^ (v + v' + v'' + v''') * u +
        (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
            3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) := by
  have hsplit : 3 ^ v * u + 2 ^ W - 1 = 3 ^ v * u + (2 ^ W - 1) :=
    Nat.add_sub_assoc (Nat.one_le_pow W 2 (by decide)) _
  calc
    3 ^ v''' *
        (3 ^ v'' *
            (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
              (2 ^ W' - 1) * 2 ^ (W + v')) +
          (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))
        = 3 ^ v''' *
            (3 ^ v'' *
                (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) +
                  (2 ^ W' - 1) * 2 ^ (W + v')) +
              (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by rw [hsplit]
    _ = 3 ^ v''' *
          (3 ^ v'' *
              (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)) +
                (2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' *
          (3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1))) +
            3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u + (2 ^ W - 1)))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u) + 3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u)) +
            3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (3 ^ v * u))) +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_add]
    _ = 3 ^ v''' * 3 ^ v'' * 3 ^ v' * 3 ^ v * u +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
    _ = 3 ^ (v''' + v'' + v' + v) * u +
          3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
          3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
          3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    _ = 3 ^ (v + v' + v'' + v''') * u +
          (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
            (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
              3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) := by
          rw [show v''' + v'' + v' + v = v + v' + v'' + v''' by omega]
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- **Exact five-step landing.** -/
theorem five_step_landing
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4) :
    3 ^ v4 *
        (3 ^ v''' *
            (3 ^ v'' *
                (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                  (2 ^ W' - 1) * 2 ^ (W + v')) +
              (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * e4 +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by
  have hprev := four_step_landing h h' h'' h'''
  have he1 : e''' + 1 = 2 ^ v4 * u4 := h4.2.2.2.2.2.1
  have hpeak : 3 ^ v4 * u4 = 2 ^ W4 * e4 + 1 := h4.2.2.2.2.2.2
  have hW : 1 ≤ 2 ^ W''' := Nat.one_le_pow W''' 2 (by decide)
  have hsum : 2 ^ (W + v' + W' + v'' + W'' + v''') +
      (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''') =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''') +
          (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')
          = 2 ^ (W + v' + W' + v'' + W'' + v''') * 1 +
              2 ^ (W + v' + W' + v'' + W'' + v''') * (2 ^ W''' - 1) := by
            rw [Nat.mul_one, Nat.mul_comm (2 ^ W''' - 1)]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * (1 + (2 ^ W''' - 1)) := by
            rw [← Nat.mul_add]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''') * 2 ^ W''' := by
            rw [Nat.add_sub_of_le hW]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by rw [← Nat.pow_add]
  have hinner :
      3 ^ v''' *
          (3 ^ v'' *
              (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                (2 ^ W' - 1) * 2 ^ (W + v')) +
            (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
        (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''') =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * u4 := by
    rw [hprev]
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
          2 ^ (W + v' + W' + v'' + W'' + v''') +
          (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')
          = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * e''' +
              2 ^ (W + v' + W' + v'' + W'' + v''' + W''') := by
            rw [Nat.add_assoc, hsum]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (e''' + 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''') * (2 ^ v4 * u4) := by rw [he1]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * u4 := by
            rw [← Nat.mul_assoc, ← Nat.pow_add]
  calc
    3 ^ v4 *
        (3 ^ v''' *
            (3 ^ v'' *
                (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                  (2 ^ W' - 1) * 2 ^ (W + v')) +
              (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
          (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))
        = 3 ^ v4 * (2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * u4) := by
          rw [hinner]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * (3 ^ v4 * u4) := by
          rw [Nat.mul_left_comm]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * (2 ^ W4 * e4 + 1) := by
          rw [hpeak]
    _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * e4 +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add]

/-- **Five-step drop against the original start**, in the last cofactor. -/
theorem drop_iff_five
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 : Nat}
    (h : IsExcursion n v u W e) (_h' : IsExcursion e v' u' W' e')
    (_h'' : IsExcursion e' v'' u'' W'' e'')
    (_h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4) :
    e4 < n ↔ 3 ^ v4 * u4 + 2 ^ W4 ≤ 2 ^ (v + W4) * u := by
  have hWpos : 0 < 2 ^ W4 := two_pow_pos W4
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W4 * e4 + 1 = 3 ^ v4 * u4 := h4.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W4) * u = 2 ^ W4 * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W4 * e4 < 2 ^ W4 * n := Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W4 * e4 + 1 ≤ 2 ^ W4 * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v4 * u4 ≤ 2 ^ W4 * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v4 * u4 + 2 ^ W4 ≤ 2 ^ W4 * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right h2 _
    rwa [← hpow] at h3
  · intro hle
    have h3 : 3 ^ v4 * u4 + 2 ^ W4 ≤ 2 ^ W4 * (n + 1) := by rw [← hpow]; exact hle
    have h4eq : 2 ^ W4 * (n + 1) = 2 ^ W4 * n + 2 ^ W4 := by rw [Nat.mul_add, Nat.mul_one]
    rw [h4eq] at h3
    have h2 : 3 ^ v4 * u4 ≤ 2 ^ W4 * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W4 * e4 + 1 ≤ 2 ^ W4 * n := by rw [hpeak]; exact h2
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_succ_le h1)

/-- **Five-step drop**, expanded in `(v, W, u)` of each step. -/
theorem drop_iff_five_expanded
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4) :
    e4 < n ↔
      3 ^ v4 *
          (3 ^ v''' *
              (3 ^ v'' *
                  (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                    (2 ^ W' - 1) * 2 ^ (W + v')) +
                (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
            (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) ≤
        2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * u := by
  have hland := five_step_landing h h' h'' h''' h4
  have hn1 : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hsum : W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 =
      (W + v' + W' + v'' + W'' + v''' + W''' + v4) + W4 := by omega
  have htot : v + W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 =
      v + (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) := by omega
  have hL :
      3 ^ v4 *
          (3 ^ v''' *
              (3 ^ v'' *
                  (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                    (2 ^ W' - 1) * 2 ^ (W + v')) +
                (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
            (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * (e4 + 1) +
        2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by
    rw [hland]
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * e4 +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4)
          = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * e4 +
              2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) +
              2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by
            rw [Nat.add_right_comm]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * e4 +
            2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * 1 +
            2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by rw [Nat.mul_one]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * (e4 + 1) +
            2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) := by
            rw [← Nat.mul_add]
  have hR : 2 ^ (v + W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * u =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * (n + 1) := by
    rw [htot, Nat.pow_add, hn1]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hsplit : 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * (e4 + 1) +
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) *
        (2 ^ W4 * (e4 + 1) + 1) := by
    rw [hsum, Nat.pow_add]
    calc
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * 2 ^ W4 * (e4 + 1) +
          2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4)
          = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * (2 ^ W4 * (e4 + 1)) +
              2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * 1 := by
            rw [Nat.mul_assoc, Nat.mul_one]
      _ = 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) *
            (2 ^ W4 * (e4 + 1) + 1) := by rw [← Nat.mul_add]
  have hsplitR : 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4) * (n + 1) =
      2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4) * (2 ^ W4 * (n + 1)) := by
    rw [hsum, Nat.pow_add, Nat.mul_assoc]
  rw [hL, hR, hsplit, hsplitR,
    (mul_le_iff (two_pow_pos (W + v' + W' + v'' + W'' + v''' + W''' + v4))).symm]
  have hpeak : 2 ^ W4 * e4 + 1 = 3 ^ v4 * u4 := h4.2.2.2.2.2.2.symm
  have hleft : 2 ^ W4 * (e4 + 1) + 1 = 3 ^ v4 * u4 + 2 ^ W4 := by
    calc
      2 ^ W4 * (e4 + 1) + 1 = 2 ^ W4 * e4 + 2 ^ W4 + 1 := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ W4 * e4 + 1 + 2 ^ W4 := by omega
      _ = 3 ^ v4 * u4 + 2 ^ W4 := by rw [hpeak]
  have hright : 2 ^ W4 * (n + 1) = 2 ^ (v + W4) * u := by
    rw [Nat.pow_add, hn1]
    simp [Nat.mul_assoc, Nat.mul_comm]
  rw [hleft, hright]
  exact drop_iff_five h h' h'' h''' h4

/-- **Three misses, then a long fifth.**  A light run of length at least `4`
whose next three runs miss their cumulative exponents, followed by a fifth
run meeting the combined ceiling, lands strictly below the original start. -/
theorem drop_of_three_misses_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4)
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hshort4 : 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
      3 ^ (v + v' + v'' + v'''))
    (hpow : 3 ^ (v + v' + v'' + v''' + v4) <
      2 ^ (v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1)) :
    e4 < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  let A := 3 ^ (v + v' + v'' + v''' + v4)
  let E1 := 3 ^ v4 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))))
  let E2 := 3 ^ v4 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))))
  let E3 := 3 ^ v4 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))
  let E4 := 3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v'''))
  let T := 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4)
  let S := v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4
  have hE1 : 8 * E1 ≤ A := by
    have h0 := eight_first_error_four (v' := v') (v'' := v'') (v''' := v''') hv hlight
    have hmul := Nat.mul_le_mul_left (3 ^ v4) h0
    have hre : 3 ^ v4 * (8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))))) = 8 * E1 := by
      simp [E1, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hpow : 3 ^ v4 * 3 ^ (v + v' + v'' + v''') = A := by
      rw [← Nat.pow_add, Nat.add_comm]
    rw [hre, hpow] at hmul
    exact hmul
  have hE2 : 8 * E2 ≤ A := by
    have h0 := eight_middle_error_four (v' := v') (v'' := v'') (v''' := v''') hv hshort
    have hmul := Nat.mul_le_mul_left (3 ^ v4) h0
    have hre : 3 ^ v4 * (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))))) =
        8 * E2 := by
      simp [E2, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hpow : 3 ^ v4 * 3 ^ (v + v' + v'' + v''') = A := by
      rw [← Nat.pow_add, Nat.add_comm]
    rw [hre, hpow] at hmul
    exact hmul
  have hE3 : 8 * E3 ≤ A := by
    have h0 := eight_third_error (v' := v') (v'' := v'') (v''' := v''') hv hshort3
    have hmul := Nat.mul_le_mul_left (3 ^ v4) h0
    have hre : 3 ^ v4 * (8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) =
        8 * E3 := by
      simp [E3, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hpow : 3 ^ v4 * 3 ^ (v + v' + v'' + v''') = A := by
      rw [← Nat.pow_add, Nat.add_comm]
    rw [hre, hpow] at hmul
    exact hmul
  have hE4 : 8 * E4 ≤ A := eight_fourth_error (v4 := v4) hv hshort4
  have hone : A + 1 ≤ 2 ^ (S - 1) := by
    simpa [A, S] using Nat.succ_le_of_lt hpow
  have hAm : A ≤ 2 ^ (S - 1) - 1 := Nat.le_sub_of_add_le hone
  have hexp : W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 ≤ S - 4 := by
    have : W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 + 4 ≤ S := by
      simp [S]; omega
    exact Nat.le_sub_of_add_le this
  have hT : 8 * T ≤ 2 ^ (S - 1) := by
    have h2le : T ≤ 2 ^ (S - 4) := by
      simpa [T] using two_pow_le_two_pow hexp
    have h8 : 8 * 2 ^ (S - 4) = 2 ^ (S - 1) := by
      have hq : S - 4 + 3 = S - 1 := by omega
      calc
        8 * 2 ^ (S - 4) = 2 ^ 3 * 2 ^ (S - 4) := by rw [show (8 : Nat) = 2 ^ 3 by decide]
        _ = 2 ^ (3 + (S - 4)) := by rw [← Nat.pow_add]
        _ = 2 ^ (S - 4 + 3) := by rw [Nat.add_comm]
        _ = 2 ^ (S - 1) := by rw [hq]
    exact Nat.le_trans (Nat.mul_le_mul_left 8 h2le) (Nat.le_of_eq h8)
  have hbud := spare_budget (errs := [E1, E2, E3, E4]) hAm (by omega : 1 ≤ S)
    (by
      have hlen4 : [E1, E2, E3, E4].length = 4 := rfl
      omega)
    (by
      intro e he
      simp [List.mem_cons] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact hE1
      · exact hE2
      · exact hE3
      · exact hE4)
    hT
  have hC : A + (E1 + (E2 + (E3 + (E4 + T)))) ≤ 2 ^ S := by
    have hsum : errSum [E1, E2, E3, E4] + T = E1 + (E2 + (E3 + (E4 + T))) := by
      simp [errSum, Nat.add_assoc]
    simpa [hsum, Nat.add_assoc] using hbud
  have hAB : A ≤ 2 ^ S := by
    have hstep : A ≤ 2 ^ (S - 1) := Nat.le_trans hAm (Nat.sub_le _ _)
    exact Nat.le_trans hstep (two_pow_le_two_pow (Nat.sub_le _ _))
  have hmul := add_le_mul_of_add_le hAB hC hu
  have hpoly :
      3 ^ v4 *
          (3 ^ v''' *
              (3 ^ v'' *
                  (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                    (2 ^ W' - 1) * 2 ^ (W + v')) +
                (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
            (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) +
        T =
      A * u + (E1 + (E2 + (E3 + (E4 + T)))) := by
    have h4p := four_inner_poly (v := v) (u := u) (W := W) (v' := v') (W' := W')
      (v'' := v'') (W'' := W'') (v''' := v''')
    calc
      3 ^ v4 *
          (3 ^ v''' *
              (3 ^ v'' *
                  (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) +
                    (2 ^ W' - 1) * 2 ^ (W + v')) +
                (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')) +
            (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) + T
          = 3 ^ v4 *
              (3 ^ (v + v' + v'' + v''') * u +
                (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
                  (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
                    3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) +
                (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) + T := by
            rw [h4p]
      _ = 3 ^ v4 *
            (3 ^ (v + v' + v'' + v''') * u +
              (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
                (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
                  3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))))) +
            3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) + T := by
            rw [Nat.mul_add]
      _ = 3 ^ v4 * 3 ^ (v + v' + v'' + v''') * u +
            3 ^ v4 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
            3 ^ v4 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
            3 ^ v4 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))) +
            3 ^ v4 * ((2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')) + T := by
            simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      _ = A * u + (E1 + (E2 + (E3 + (E4 + T)))) := by
            rw [← Nat.pow_add, show v4 + (v + v' + v'' + v''') =
              v + v' + v'' + v''' + v4 by omega]
            simp [A, E1, E2, E3, E4, Nat.add_assoc]
  rw [← hpoly] at hmul
  have hSexp : S = v + W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 := by
    simp [S]; omega
  exact (drop_iff_five_expanded h h' h'' h''' h4).mpr (by
    simpa [T, hSexp] using hmul)

/-- `303 → 769 → 577 → 433 → 325 → 61`.  The second, third, and fourth
exponents miss, and the fifth meets `3^8 = 6561 < 16384 = 2^{14}`. -/
theorem three_oh_three_five_step_drops :
    IsExcursion 303 4 19 1 769 ∧
    IsExcursion 769 1 385 1 577 ∧
    IsExcursion 577 1 289 1 433 ∧
    IsExcursion 433 1 217 1 325 ∧
    IsExcursion 325 1 163 3 61 ∧ 61 < 303 ∧
    2 ^ 1 * (2 ^ 4 - 1) < 3 ^ 4 ∧
    2 ^ (4 + 1 + 1 + 1 - 1) ≤ 3 ^ (4 + 1) ∧
    2 ^ (4 + 1 + 1 + 1 + 1 + 1 - 1) ≤ 3 ^ (4 + 1 + 1) ∧
    2 ^ (4 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1) ≤ 3 ^ (4 + 1 + 1 + 1) ∧
    3 ^ (4 + 1 + 1 + 1 + 1) < 2 ^ (4 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 3 - 1) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   by omega, by decide, by decide, by decide, by decide, by decide⟩


/-! ## 9.  One more miss, inside the same spare-bit budget -/

/-- Attach one excursion to a landing identity.  `inner` is the product
through the previous run, equal to `2^{P+W} e + 2^P`. -/
private theorem compose_step {inner P W e vNext uNext WNext eNext : Nat}
    (hprev : inner = 2 ^ (P + W) * e + 2 ^ P)
    (he1 : e + 1 = 2 ^ vNext * uNext)
    (hpeak : 3 ^ vNext * uNext = 2 ^ WNext * eNext + 1) :
    3 ^ vNext * (inner + (2 ^ W - 1) * 2 ^ P) =
      2 ^ (P + W + vNext + WNext) * eNext + 2 ^ (P + W + vNext) := by
  have hW : 1 ≤ 2 ^ W := Nat.one_le_pow W 2 (by decide)
  have hsum : 2 ^ P + (2 ^ W - 1) * 2 ^ P = 2 ^ (P + W) := by
    calc
      2 ^ P + (2 ^ W - 1) * 2 ^ P
          = 2 ^ P * 1 + 2 ^ P * (2 ^ W - 1) := by
            rw [Nat.mul_one, Nat.mul_comm (2 ^ W - 1)]
      _ = 2 ^ P * (1 + (2 ^ W - 1)) := by rw [← Nat.mul_add]
      _ = 2 ^ P * 2 ^ W := by rw [Nat.add_sub_of_le hW]
      _ = 2 ^ (P + W) := by rw [← Nat.pow_add]
  have hinner : inner + (2 ^ W - 1) * 2 ^ P = 2 ^ (P + W + vNext) * uNext := by
    rw [hprev]
    calc
      2 ^ (P + W) * e + 2 ^ P + (2 ^ W - 1) * 2 ^ P
          = 2 ^ (P + W) * e + 2 ^ (P + W) := by rw [Nat.add_assoc, hsum]
      _ = 2 ^ (P + W) * (e + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = 2 ^ (P + W) * (2 ^ vNext * uNext) := by rw [he1]
      _ = 2 ^ (P + W + vNext) * uNext := by rw [← Nat.mul_assoc, ← Nat.pow_add]
  calc
    3 ^ vNext * (inner + (2 ^ W - 1) * 2 ^ P)
        = 3 ^ vNext * (2 ^ (P + W + vNext) * uNext) := by rw [hinner]
    _ = 2 ^ (P + W + vNext) * (3 ^ vNext * uNext) := by rw [Nat.mul_left_comm]
    _ = 2 ^ (P + W + vNext) * (2 ^ WNext * eNext + 1) := by rw [hpeak]
    _ = 2 ^ (P + W + vNext + WNext) * eNext + 2 ^ (P + W + vNext) := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add]

/-- The expanded comparison depends on the landing identity only through
the previous product. -/
private theorem expanded_iff {n v u inner sum vLast uLast WLast eLast : Nat}
    (hn : n + 1 = 2 ^ v * u)
    (hpeak : 2 ^ WLast * eLast + 1 = 3 ^ vLast * uLast)
    (hland : 3 ^ vLast * inner = 2 ^ (sum + WLast) * eLast + 2 ^ sum) :
    eLast < n ↔ 3 ^ vLast * inner + 2 ^ (sum + WLast) ≤ 2 ^ (v + sum + WLast) * u := by
  have hsum : sum + WLast = sum + WLast := rfl
  have hL : 3 ^ vLast * inner + 2 ^ (sum + WLast) =
      2 ^ (sum + WLast) * (eLast + 1) + 2 ^ sum := by
    rw [hland]
    calc
      2 ^ (sum + WLast) * eLast + 2 ^ sum + 2 ^ (sum + WLast)
          = 2 ^ (sum + WLast) * eLast + 2 ^ (sum + WLast) + 2 ^ sum := by
            rw [Nat.add_right_comm]
      _ = 2 ^ (sum + WLast) * eLast + 2 ^ (sum + WLast) * 1 + 2 ^ sum := by
            rw [Nat.mul_one]
      _ = 2 ^ (sum + WLast) * (eLast + 1) + 2 ^ sum := by rw [← Nat.mul_add]
  have hR : 2 ^ (v + sum + WLast) * u = 2 ^ (sum + WLast) * (n + 1) := by
    have hexp : v + sum + WLast = v + (sum + WLast) := by omega
    rw [hexp, Nat.pow_add, hn]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hsplit : 2 ^ (sum + WLast) * (eLast + 1) + 2 ^ sum =
      2 ^ sum * (2 ^ WLast * (eLast + 1) + 1) := by
    rw [Nat.pow_add]
    calc
      2 ^ sum * 2 ^ WLast * (eLast + 1) + 2 ^ sum
          = 2 ^ sum * (2 ^ WLast * (eLast + 1)) + 2 ^ sum * 1 := by
            rw [Nat.mul_assoc, Nat.mul_one]
      _ = 2 ^ sum * (2 ^ WLast * (eLast + 1) + 1) := by rw [← Nat.mul_add]
  have hsplitR : 2 ^ (sum + WLast) * (n + 1) =
      2 ^ sum * (2 ^ WLast * (n + 1)) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  rw [hL, hR, hsplit, hsplitR, (mul_le_iff (two_pow_pos sum)).symm]
  have hleft : 2 ^ WLast * (eLast + 1) + 1 = 3 ^ vLast * uLast + 2 ^ WLast := by
    calc
      2 ^ WLast * (eLast + 1) + 1
          = 2 ^ WLast * eLast + 2 ^ WLast + 1 := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ WLast * eLast + 1 + 2 ^ WLast := by omega
      _ = 3 ^ vLast * uLast + 2 ^ WLast := by rw [hpeak]
  have hright : 2 ^ WLast * (n + 1) = 2 ^ (v + WLast) * u := by
    rw [Nat.pow_add, hn]
    simp [Nat.mul_assoc, Nat.mul_comm]
  rw [hleft, hright]
  refine Iff.intro ?_ ?_
  · intro hlt
    have hWpos : 0 < 2 ^ WLast := two_pow_pos WLast
    have hmul : 2 ^ WLast * eLast < 2 ^ WLast * n :=
      Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ WLast * eLast + 1 ≤ 2 ^ WLast * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ vLast * uLast ≤ 2 ^ WLast * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ vLast * uLast + 2 ^ WLast ≤ 2 ^ WLast * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right h2 _
    rw [hright] at h3
    exact h3
  · intro hle
    rw [← hright] at hle
    have h4eq : 2 ^ WLast * (n + 1) = 2 ^ WLast * n + 2 ^ WLast := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4eq] at hle
    have h2 : 3 ^ vLast * uLast ≤ 2 ^ WLast * n := Nat.le_of_add_le_add_right hle
    have h1 : 2 ^ WLast * eLast + 1 ≤ 2 ^ WLast * n := by rw [hpeak]; exact h2
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_succ_le h1)

/-- Scaling a list of errors by a positive factor. -/
private theorem mul_errSum (a : Nat) (l : List Nat) :
    a * errSum l = errSum (l.map (fun e => a * e)) := by
  induction l with
  | nil => simp [errSum]
  | cons e t ih =>
    simp [errSum, List.map, Nat.mul_add, ih]

/-- Push one factor of `3^q` through an inner polynomial `A u + C`. -/
private theorem push_closed {body u A C q err T : Nat}
    (h : body = A * u + C) :
    3 ^ q * (body + err) + T =
      3 ^ q * A * u + (3 ^ q * C + (3 ^ q * err + T)) := by
  calc
    3 ^ q * (body + err) + T
        = 3 ^ q * (A * u + C + err) + T := by rw [h, Nat.add_assoc]
    _ = 3 ^ q * (A * u + C) + 3 ^ q * err + T := by rw [Nat.mul_add]
    _ = 3 ^ q * (A * u) + 3 ^ q * C + 3 ^ q * err + T := by rw [Nat.mul_add]
    _ = 3 ^ q * A * u + (3 ^ q * C + (3 ^ q * err + T)) := by
          rw [Nat.mul_assoc]
          simp [Nat.add_assoc]

/-- A missed step's error fits eight times once the first run has length `≥ 4`.
`gap` is every exponent after the first `v` and before this `W`. -/
private theorem eight_of_miss {v gap W base tail : Nat} (hv : 4 ≤ v)
    (hshort : 2 ^ (v + gap + W - 1) ≤ 3 ^ base) :
    8 * (3 ^ tail * ((2 ^ W - 1) * 2 ^ gap)) ≤ 3 ^ base * 3 ^ tail := by
  have h3 : 3 ≤ v - 1 := Nat.le_sub_of_add_le (by omega : (3 : Nat) + 1 ≤ v)
  have h8le : (8 : Nat) ≤ 2 ^ (v - 1) := by simpa using two_pow_le_two_pow h3
  have hmul8 : 8 * (3 ^ tail * ((2 ^ W - 1) * 2 ^ gap)) ≤
      2 ^ (v - 1) * (3 ^ tail * ((2 ^ W - 1) * 2 ^ gap)) :=
    Nat.mul_le_mul_right _ h8le
  have hadd : v - 1 + gap = v + gap - 1 := by omega
  have hjoin : 2 ^ (v - 1) * 2 ^ gap = 2 ^ (v + gap - 1) := by rw [← Nat.pow_add, hadd]
  have hexp : v + gap - 1 + W = v + gap + W - 1 :=
    (Nat.sub_add_comm (by omega : (1 : Nat) ≤ v + gap)).symm
  have hdist : 2 ^ (v + gap - 1) * (2 ^ W - 1) =
      2 ^ (v + gap + W - 1) - 2 ^ (v + gap - 1) := by
    calc
      2 ^ (v + gap - 1) * (2 ^ W - 1)
          = 2 ^ (v + gap - 1) * 2 ^ W - 2 ^ (v + gap - 1) := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = 2 ^ (v + gap - 1 + W) - 2 ^ (v + gap - 1) := by rw [← Nat.pow_add]
      _ = 2 ^ (v + gap + W - 1) - 2 ^ (v + gap - 1) := by rw [hexp]
  have hhalf : (2 ^ W - 1) * 2 ^ (v + gap - 1) ≤ 3 ^ base := by
    have hcomm : (2 ^ W - 1) * 2 ^ (v + gap - 1) =
        2 ^ (v + gap - 1) * (2 ^ W - 1) := Nat.mul_comm _ _
    have hle : 2 ^ (v + gap - 1) * (2 ^ W - 1) ≤ 2 ^ (v + gap + W - 1) := by
      rw [hdist]; exact Nat.sub_le _ _
    exact Nat.le_trans (hcomm ▸ hle) hshort
  exact Nat.le_trans hmul8 (by
    have hpush : 2 ^ (v - 1) * (3 ^ tail * ((2 ^ W - 1) * 2 ^ gap)) =
        3 ^ tail * ((2 ^ W - 1) * 2 ^ (v + gap - 1)) := by
      calc
        2 ^ (v - 1) * (3 ^ tail * ((2 ^ W - 1) * 2 ^ gap))
            = 3 ^ tail * (2 ^ (v - 1) * ((2 ^ W - 1) * 2 ^ gap)) :=
              Nat.mul_left_comm _ _ _
        _ = 3 ^ tail * ((2 ^ W - 1) * (2 ^ (v - 1) * 2 ^ gap)) :=
              congrArg (fun t => 3 ^ tail * t) (Nat.mul_left_comm _ _ _)
        _ = 3 ^ tail * ((2 ^ W - 1) * 2 ^ (v + gap - 1)) := by rw [hjoin]
    have hle : 3 ^ tail * ((2 ^ W - 1) * 2 ^ (v + gap - 1)) ≤ 3 ^ base * 3 ^ tail := by
      exact Nat.le_trans (Nat.mul_le_mul_left _ hhalf) (Nat.le_of_eq (Nat.mul_comm _ _))
    rwa [hpush])

/-- The terminal power sits at least four bits below `S` when `v ≥ 4`. -/
private theorem terminal_room {v S : Nat} (hv : 4 ≤ v) (hS : S = v + (S - v))
    (hexp : S - v ≤ S - 4) :
    8 * 2 ^ (S - v) ≤ 2 ^ (S - 1) := by
  have h2le : 2 ^ (S - v) ≤ 2 ^ (S - 4) := two_pow_le_two_pow hexp
  have hq : S - 4 + 3 = S - 1 := by omega
  have h8 : 8 * 2 ^ (S - 4) = 2 ^ (S - 1) := by
    calc
      8 * 2 ^ (S - 4) = 2 ^ 3 * 2 ^ (S - 4) := by rw [show (8 : Nat) = 2 ^ 3 by decide]
      _ = 2 ^ (3 + (S - 4)) := by rw [← Nat.pow_add]
      _ = 2 ^ (S - 4 + 3) := by rw [Nat.add_comm]
      _ = 2 ^ (S - 1) := by rw [hq]
  exact Nat.le_trans (Nat.mul_le_mul_left 8 h2le) (Nat.le_of_eq h8)

/-- Close one long run after a polynomial `A u + C` whose debt is at most
`k` copies of `A`, with `k ≤ 6`.  The new miss contributes one more copy,
and `10 + k` still sits at or under `16`. -/
private theorem close_one_long
    {n v u body A C err P Wprev ePrev vNext uNext WNext eNext k : Nat}
    (hn1 : n + 1 = 2 ^ v * u) (hu : 1 ≤ u) (hv : 4 ≤ v)
    (hbody : body = A * u + C) (hC : 8 * C ≤ k * A) (hk : k ≤ 6)
    (hprev : body = 2 ^ (P + Wprev) * ePrev + 2 ^ P)
    (hnext : IsExcursion ePrev vNext uNext WNext eNext)
    (herr : 8 * (3 ^ vNext * err) ≤ 3 ^ vNext * A)
    (herrForm : err = (2 ^ Wprev - 1) * 2 ^ P)
    (hpow : 3 ^ vNext * A + 1 ≤
      2 ^ (v + P + Wprev + vNext + WNext - 1)) :
    eNext < n := by
  let Anew := 3 ^ vNext * A
  let D := 3 ^ vNext * C + 3 ^ vNext * err
  let S := v + P + Wprev + vNext + WNext
  let T := 2 ^ (P + Wprev + vNext + WNext)
  have hD : 8 * D ≤ (k + 1) * Anew := by
    calc
      8 * D = 8 * (3 ^ vNext * C) + 8 * (3 ^ vNext * err) := by
        simp [D, Nat.mul_add]
      _ = 3 ^ vNext * (8 * C) + 8 * (3 ^ vNext * err) := by
        rw [Nat.mul_left_comm]
      _ ≤ 3 ^ vNext * (k * A) + Anew := Nat.add_le_add
        (Nat.mul_le_mul_left _ hC) herr
      _ = k * Anew + Anew := by
        rw [show 3 ^ vNext * (k * A) = k * (3 ^ vNext * A) from Nat.mul_left_comm _ _ _]
      _ = k * Anew + 1 * Anew := by rw [Nat.one_mul]
      _ = (k + 1) * Anew := by rw [← Nat.add_mul]
  have hAm : Anew ≤ 2 ^ (S - 1) - 1 := by
    have hexp : v + P + Wprev + vNext + WNext - 1 = S - 1 := by simp [S]
    exact Nat.le_sub_of_add_le (by simpa [Anew, hexp] using hpow)
  have hT : 8 * T ≤ 2 ^ (S - 1) := by
    have hexp : S - v ≤ S - 4 := Nat.sub_le_sub_left hv _
    have hTv : T = 2 ^ (S - v) := by
      have hsub : S - v = P + Wprev + vNext + WNext := by simp [S]; omega
      simp [T, hsub]
    rw [hTv]
    exact terminal_room hv (by simp [S]; omega) hexp
  have hbudget : Anew + (3 ^ vNext * C + (3 ^ vNext * err + T)) ≤ 2 ^ S := by
    have h8 : 8 * (Anew + D + T) ≤ 8 * 2 ^ S := by
      have htop : 10 + k ≤ 16 := by omega
      have hdist : (9 + k) * (2 ^ (S - 1) - 1) =
          (9 + k) * 2 ^ (S - 1) - (9 + k) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have hmain : (9 + k) * Anew ≤ (9 + k) * 2 ^ (S - 1) - (9 + k) := by
        have hmul := Nat.mul_le_mul_left (9 + k) hAm
        rwa [hdist] at hmul
      have hfull : S - 1 + 1 = S := by omega
      have hsumA : 8 * Anew + (k + 1) * Anew = (9 + k) * Anew := by
        rw [← Nat.add_mul, show (8 + (k + 1)) = 9 + k by omega]
      calc
        8 * (Anew + D + T) = 8 * Anew + 8 * D + 8 * T := by
          rw [Nat.mul_add, Nat.mul_add]
        _ ≤ 8 * Anew + (k + 1) * Anew + 2 ^ (S - 1) :=
          Nat.add_le_add (Nat.add_le_add_left hD _) hT
        _ = (9 + k) * Anew + 2 ^ (S - 1) := by rw [hsumA]
        _ ≤ (9 + k) * 2 ^ (S - 1) - (9 + k) + 2 ^ (S - 1) :=
          Nat.add_le_add_right hmain _
        _ ≤ (9 + k) * 2 ^ (S - 1) + 2 ^ (S - 1) :=
          Nat.add_le_add_right (Nat.sub_le _ _) _
        _ = (9 + k) * 2 ^ (S - 1) + 1 * 2 ^ (S - 1) := by rw [Nat.one_mul]
        _ = (10 + k) * 2 ^ (S - 1) := by
          rw [← Nat.add_mul, show (9 + k) + 1 = 10 + k by omega]
        _ ≤ 16 * 2 ^ (S - 1) := Nat.mul_le_mul_right _ htop
        _ = 8 * 2 ^ S := by
          calc
            16 * 2 ^ (S - 1) = 8 * 2 * 2 ^ (S - 1) := by
              rw [show (16 : Nat) = 8 * 2 by decide]
            _ = 8 * 2 ^ (S - 1 + 1) := by rw [Nat.mul_assoc, ← two_pow_succ]
            _ = 8 * 2 ^ S := by rw [hfull]
    have hassoc : Anew + (3 ^ vNext * C + (3 ^ vNext * err + T)) =
        Anew + D + T := by simp [D, Nat.add_assoc]
    rw [hassoc]
    exact Nat.le_of_mul_le_mul_left h8 (by decide : 0 < (8 : Nat))
  have hAB : Anew ≤ 2 ^ S := Nat.le_trans hAm
    (Nat.le_trans (Nat.sub_le _ _) (two_pow_le_two_pow (Nat.sub_le _ _)))
  have hmul := add_le_mul_of_add_le hAB hbudget hu
  have hland := compose_step (inner := body) (P := P) (W := Wprev) (e := ePrev)
    (vNext := vNext) (uNext := uNext) (WNext := WNext) (eNext := eNext)
    hprev hnext.2.2.2.2.2.1 hnext.2.2.2.2.2.2
  have hiff := expanded_iff (n := n) (v := v) (u := u) (inner := body + err)
    (sum := P + Wprev + vNext) (vLast := vNext) (uLast := uNext)
    (WLast := WNext) (eLast := eNext) hn1 hnext.2.2.2.2.2.2.symm (by
      simpa [herrForm] using hland)
  have hpoly : 3 ^ vNext * (body + err) + T =
      Anew * u + (3 ^ vNext * C + (3 ^ vNext * err + T)) := by
    simpa [Anew, T] using
      push_closed (body := body) (u := u) (A := A) (C := C) (q := vNext)
        (err := err) (T := T) hbody
  rw [← hpoly] at hmul
  exact hiff.mpr (by
    have hSexp : S = v + (P + Wprev + vNext) + WNext := by
      simp [S]; omega
    rw [hSexp] at hmul
    simpa [T] using hmul)

/-- **Four misses, then a long sixth.**  The spare-bit budget still has
room for a fifth error. -/
theorem drop_of_four_misses_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 v5 u5 W5 e5 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4)
    (h5 : IsExcursion e4 v5 u5 W5 e5)
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hshort4 : 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
      3 ^ (v + v' + v'' + v'''))
    (hshort5 : 2 ^ (v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1) ≤
      3 ^ (v + v' + v'' + v''' + v4))
    (hpow : 3 ^ (v + v' + v'' + v''' + v4 + v5) <
      2 ^ (v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1)) :
    e5 < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  let A4 := 3 ^ (v + v' + v'' + v''')
  let C4 := 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
    (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
      3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))
  let err4 := (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')
  let body4 := 3 ^ v''' *
    (3 ^ v'' * (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + (2 ^ W' - 1) * 2 ^ (W + v')) +
      (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))
  have hbody4 : body4 = A4 * u + C4 := by
    simpa [body4, A4, C4] using
      four_inner_poly (v := v) (u := u) (W := W) (v' := v') (W' := W')
        (v'' := v'') (W'' := W'') (v''' := v''')
  let body5 := 3 ^ v4 * (body4 + err4)
  let A5 := 3 ^ v4 * A4
  let C5 := 3 ^ v4 * C4 + 3 ^ v4 * err4
  have hbody5 : body5 = A5 * u + C5 := by
    have hpush := push_closed (body := body4) (u := u) (A := A4) (C := C4)
      (q := v4) (err := err4) (T := 0) hbody4
    simpa [body5, A5, C5, Nat.add_zero, Nat.mul_zero] using hpush
  let err5 := (2 ^ W4 - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4)
  let sum := W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 + v5
  let T := 2 ^ (sum + W5)
  let A := 3 ^ (v + v' + v'' + v''' + v4 + v5)
  let S := v + sum + W5
  have hAeq : 3 ^ v5 * A5 = A := by
    simp [A, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm, Nat.add_left_comm]
  have hclosed := push_closed (body := body5) (u := u) (A := A5) (C := C5)
    (q := v5) (err := err5) (T := T) hbody5
  have hC4 : 8 * C4 ≤ 3 * A4 := by
    have h1 := eight_first_error_four (v' := v') (v'' := v'') (v''' := v''') hv hlight
    have h2 := eight_middle_error_four (v' := v') (v'' := v'') (v''' := v''') hv hshort
    have h3 := eight_third_error (v' := v') (v'' := v'') (v''' := v''') hv hshort3
    have hsum : 8 * C4 = 8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
          8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) := by
      simp [C4, Nat.mul_add, Nat.add_assoc]
    rw [hsum]
    calc
      8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
          (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
            8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))))
          ≤ A4 + (A4 + A4) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
      _ = 1 * A4 + (1 * A4 + 1 * A4) := by simp [Nat.one_mul]
      _ = 1 * A4 + (1 + 1) * A4 := by rw [← Nat.add_mul]
      _ = (1 + (1 + 1)) * A4 := by rw [← Nat.add_mul]
      _ = 3 * A4 := by rw [show (1 + (1 + 1) : Nat) = 3 by decide]
  have herr4 : 8 * (3 ^ v4 * err4) ≤ A5 := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''') + W''' - 1 =
        v + v' + v'' + v''' + W + W' + W'' + W''' - 1 := by omega
    have hmiss := eight_of_miss (v := v) (gap := W + v' + W' + v'' + W'' + v''')
      (W := W''') (base := v + v' + v'' + v''') (tail := v4) hv
      (by simpa [hgap] using hshort4)
    simpa [err4, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hE5 : 8 * (3 ^ v5 * err5) ≤ A := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''' + W''' + v4) + W4 - 1 =
        v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1 := by omega
    have hmiss := eight_of_miss (v := v)
      (gap := W + v' + W' + v'' + W'' + v''' + W''' + v4) (W := W4)
      (base := v + v' + v'' + v''' + v4) (tail := v5) hv
      (by simpa [hgap] using hshort5)
    simpa [err5, A, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hD : 8 * (3 ^ v5 * C5 + 3 ^ v5 * err5) ≤ 5 * A := by
    have hC5 : 8 * C5 ≤ 4 * A5 := by
      have hscale : 8 * (3 ^ v4 * C4) ≤ 3 * A5 := by
        calc
          8 * (3 ^ v4 * C4) = 3 ^ v4 * (8 * C4) := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ ≤ 3 ^ v4 * (3 * A4) := Nat.mul_le_mul_left _ hC4
          _ = 3 * A5 := by simp [A5, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      calc
        8 * C5 = 8 * (3 ^ v4 * C4) + 8 * (3 ^ v4 * err4) := by
          simp [C5, Nat.mul_add]
        _ ≤ 3 * A5 + A5 := Nat.add_le_add hscale herr4
        _ = 3 * A5 + 1 * A5 := by rw [Nat.one_mul]
        _ = 4 * A5 := by rw [← Nat.add_mul, show (3 + 1 : Nat) = 4 by decide]
    calc
      8 * (3 ^ v5 * C5 + 3 ^ v5 * err5)
          = 8 * (3 ^ v5 * C5) + 8 * (3 ^ v5 * err5) := by rw [Nat.mul_add]
      _ = 3 ^ v5 * (8 * C5) + 8 * (3 ^ v5 * err5) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ v5 * (4 * A5) + A := Nat.add_le_add (Nat.mul_le_mul_left _ hC5) hE5
      _ = 4 * (3 ^ v5 * A5) + A := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 4 * A + A := by rw [hAeq]
      _ = 4 * A + 1 * A := by rw [Nat.one_mul]
      _ = 5 * A := by rw [← Nat.add_mul, show (4 + 1 : Nat) = 5 by decide]
  have hone : A + 1 ≤ 2 ^ (S - 1) := by
    have hexp : v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1 =
        S - 1 := by simp [S, sum]; omega
    simpa [A, hexp] using Nat.succ_le_of_lt hpow
  have hAm : A ≤ 2 ^ (S - 1) - 1 := Nat.le_sub_of_add_le hone
  have hT : 8 * T ≤ 2 ^ (S - 1) := by
    have hexp : S - v ≤ S - 4 := Nat.sub_le_sub_left hv _
    have hTv : T = 2 ^ (S - v) := by
      have hsub : S - v = sum + W5 := by simp [S]; omega
      simp [T, hsub]
    rw [hTv]
    exact terminal_room hv (by simp [S]; omega) hexp
  have hbudget : A + (3 ^ v5 * C5 + (3 ^ v5 * err5 + T)) ≤ 2 ^ S := by
    have h8 : 8 * (A + (3 ^ v5 * C5 + 3 ^ v5 * err5) + T) ≤ 8 * 2 ^ S := by
      have hdist : 13 * (2 ^ (S - 1) - 1) = 13 * 2 ^ (S - 1) - 13 := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have h13 : 13 * A ≤ 13 * 2 ^ (S - 1) - 13 := by
        have hmul := Nat.mul_le_mul_left 13 hAm
        rwa [hdist] at hmul
      have hfull : S - 1 + 1 = S := by omega
      calc
        8 * (A + (3 ^ v5 * C5 + 3 ^ v5 * err5) + T)
            = 8 * A + 8 * (3 ^ v5 * C5 + 3 ^ v5 * err5) + 8 * T := by
              rw [Nat.mul_add, Nat.mul_add]
        _ ≤ 8 * A + 5 * A + 2 ^ (S - 1) :=
              Nat.add_le_add (Nat.add_le_add_left hD _) hT
        _ = 13 * A + 2 ^ (S - 1) := by
              rw [← Nat.add_mul, show (8 + 5 : Nat) = 13 by decide]
        _ ≤ 13 * 2 ^ (S - 1) - 13 + 2 ^ (S - 1) := Nat.add_le_add_right h13 _
        _ ≤ 13 * 2 ^ (S - 1) + 2 ^ (S - 1) := Nat.add_le_add_right (Nat.sub_le _ _) _
        _ = 13 * 2 ^ (S - 1) + 1 * 2 ^ (S - 1) := by rw [Nat.one_mul]
        _ = 14 * 2 ^ (S - 1) := by
              rw [← Nat.add_mul, show (13 + 1 : Nat) = 14 by decide]
        _ ≤ 16 * 2 ^ (S - 1) := Nat.mul_le_mul_right _ (by decide)
        _ = 8 * 2 ^ S := by
              calc
                16 * 2 ^ (S - 1) = 8 * 2 * 2 ^ (S - 1) := by
                  rw [show (16 : Nat) = 8 * 2 by decide]
                _ = 8 * 2 ^ (S - 1 + 1) := by rw [Nat.mul_assoc, ← two_pow_succ]
                _ = 8 * 2 ^ S := by rw [hfull]
    have hassoc : A + (3 ^ v5 * C5 + (3 ^ v5 * err5 + T)) =
        A + (3 ^ v5 * C5 + 3 ^ v5 * err5) + T := by
      simp [Nat.add_assoc]
    rw [hassoc]
    exact Nat.le_of_mul_le_mul_left h8 (by decide : 0 < (8 : Nat))
  have hAB : A ≤ 2 ^ S := Nat.le_trans hAm
    (Nat.le_trans (Nat.sub_le _ _) (two_pow_le_two_pow (Nat.sub_le _ _)))
  have hmul := add_le_mul_of_add_le hAB hbudget hu
  have hland5 := five_step_landing h h' h'' h''' h4
  have hland6 := compose_step (inner := body5) (P := W + v' + W' + v'' + W'' + v''' + W''' + v4)
    (W := W4) (e := e4) (vNext := v5) (uNext := u5) (WNext := W5) (eNext := e5)
    (by
      simpa [body5, body4, err4] using hland5)
    h5.2.2.2.2.2.1 h5.2.2.2.2.2.2
  have hiff := expanded_iff (n := n) (v := v) (u := u) (inner := body5 + err5)
    (sum := sum) (vLast := v5) (uLast := u5) (WLast := W5) (eLast := e5)
    h.2.2.2.2.2.1 h5.2.2.2.2.2.2.symm (by
      simpa [sum] using hland6)
  have hpoly : 3 ^ v5 * (body5 + err5) + T =
      A * u + (3 ^ v5 * C5 + (3 ^ v5 * err5 + T)) := by
    simpa [A, hAeq] using hclosed
  rw [← hpoly] at hmul
  exact hiff.mpr (by simpa [T, S, sum] using hmul)

/-- **Five misses, then a long seventh.**  The debt is six copies of `A`,
and `10 + 5 = 15` still sits under `16`. -/
theorem drop_of_five_misses_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 v5 u5 W5 e5 v6 u6 W6 e6 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4)
    (h5 : IsExcursion e4 v5 u5 W5 e5)
    (h6 : IsExcursion e5 v6 u6 W6 e6)
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hshort4 : 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
      3 ^ (v + v' + v'' + v'''))
    (hshort5 : 2 ^ (v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1) ≤
      3 ^ (v + v' + v'' + v''' + v4))
    (hshort6 : 2 ^ (v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1) ≤
      3 ^ (v + v' + v'' + v''' + v4 + v5))
    (hpow : 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6) <
      2 ^ (v + v' + v'' + v''' + v4 + v5 + v6 + W + W' + W'' + W''' + W4 + W5 + W6 - 1)) :
    e6 < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  let A4 := 3 ^ (v + v' + v'' + v''')
  let C4 := 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
    (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
      3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))
  let err4 := (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')
  let body4 := 3 ^ v''' *
    (3 ^ v'' * (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + (2 ^ W' - 1) * 2 ^ (W + v')) +
      (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))
  have hbody4 : body4 = A4 * u + C4 := by
    simpa [body4, A4, C4] using
      four_inner_poly (v := v) (u := u) (W := W) (v' := v') (W' := W')
        (v'' := v'') (W'' := W'') (v''' := v''')
  let body5 := 3 ^ v4 * (body4 + err4)
  let A5 := 3 ^ v4 * A4
  let C5 := 3 ^ v4 * C4 + 3 ^ v4 * err4
  have hbody5 : body5 = A5 * u + C5 := by
    have hpush := push_closed (body := body4) (u := u) (A := A4) (C := C4)
      (q := v4) (err := err4) (T := 0) hbody4
    simpa [body5, A5, C5, Nat.add_zero, Nat.mul_zero] using hpush
  let err5 := (2 ^ W4 - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4)
  let A6 := 3 ^ (v + v' + v'' + v''' + v4 + v5)
  have hC4 : 8 * C4 ≤ 3 * A4 := by
    have h1 := eight_first_error_four (v' := v') (v'' := v'') (v''' := v''') hv hlight
    have h2 := eight_middle_error_four (v' := v') (v'' := v'') (v''' := v''') hv hshort
    have h3 := eight_third_error (v' := v') (v'' := v'') (v''' := v''') hv hshort3
    have hsum : 8 * C4 =
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
          8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) := by
      simp [C4, Nat.mul_add, Nat.add_assoc]
    rw [hsum]
    calc
      8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
          (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
            8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))))
          ≤ A4 + (A4 + A4) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
      _ = 1 * A4 + (1 * A4 + 1 * A4) := by simp [Nat.one_mul]
      _ = 1 * A4 + (1 + 1) * A4 := by rw [← Nat.add_mul]
      _ = (1 + (1 + 1)) * A4 := by rw [← Nat.add_mul]
      _ = 3 * A4 := by rw [show (1 + (1 + 1) : Nat) = 3 by decide]
  have herr4 : 8 * (3 ^ v4 * err4) ≤ A5 := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''') + W''' - 1 =
        v + v' + v'' + v''' + W + W' + W'' + W''' - 1 := by omega
    have hmiss := eight_of_miss (v := v) (gap := W + v' + W' + v'' + W'' + v''')
      (W := W''') (base := v + v' + v'' + v''') (tail := v4) hv
      (by simpa [hgap] using hshort4)
    simpa [err4, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hE5 : 8 * (3 ^ v5 * err5) ≤ A6 := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''' + W''' + v4) + W4 - 1 =
        v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1 := by omega
    have hmiss := eight_of_miss (v := v)
      (gap := W + v' + W' + v'' + W'' + v''' + W''' + v4) (W := W4)
      (base := v + v' + v'' + v''' + v4) (tail := v5) hv
      (by simpa [hgap] using hshort5)
    simpa [err5, A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hC5 : 8 * C5 ≤ 4 * A5 := by
    have hscale : 8 * (3 ^ v4 * C4) ≤ 3 * A5 := by
      calc
        8 * (3 ^ v4 * C4) = 3 ^ v4 * (8 * C4) := by rw [Nat.mul_left_comm]
        _ ≤ 3 ^ v4 * (3 * A4) := Nat.mul_le_mul_left _ hC4
        _ = 3 * A5 := by simp [A5, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    calc
      8 * C5 = 8 * (3 ^ v4 * C4) + 8 * (3 ^ v4 * err4) := by simp [C5, Nat.mul_add]
      _ ≤ 3 * A5 + A5 := Nat.add_le_add hscale herr4
      _ = 3 * A5 + 1 * A5 := by rw [Nat.one_mul]
      _ = 4 * A5 := by rw [← Nat.add_mul, show (3 + 1 : Nat) = 4 by decide]
  let C6 := 3 ^ v5 * C5 + 3 ^ v5 * err5
  let body6 := 3 ^ v5 * (body5 + err5)
  have hA6 : 3 ^ v5 * A5 = A6 := by
    simp [A6, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm, Nat.add_left_comm]
  have hC6 : 8 * C6 ≤ 5 * A6 := by
    calc
      8 * C6 = 8 * (3 ^ v5 * C5) + 8 * (3 ^ v5 * err5) := by simp [C6, Nat.mul_add]
      _ = 3 ^ v5 * (8 * C5) + 8 * (3 ^ v5 * err5) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ v5 * (4 * A5) + A6 := Nat.add_le_add (Nat.mul_le_mul_left _ hC5) hE5
      _ = 4 * (3 ^ v5 * A5) + A6 := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 4 * A6 + A6 := by rw [hA6]
      _ = 4 * A6 + 1 * A6 := by rw [Nat.one_mul]
      _ = 5 * A6 := by rw [← Nat.add_mul, show (4 + 1 : Nat) = 5 by decide]
  have hbody6 : body6 = A6 * u + C6 := by
    have hpush := push_closed (body := body5) (u := u) (A := A5) (C := C5)
      (q := v5) (err := err5) (T := 0) hbody5
    simpa [body6, C6, hA6, Nat.add_zero, Nat.mul_zero] using hpush
  let P6 := W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 + v5
  let err6 := (2 ^ W5 - 1) * 2 ^ P6
  have hprev : body6 = 2 ^ (P6 + W5) * e5 + 2 ^ P6 := by
    have hland5 := five_step_landing h h' h'' h''' h4
    have hcomp := compose_step (inner := body5)
      (P := W + v' + W' + v'' + W'' + v''' + W''' + v4) (W := W4) (e := e4)
      (vNext := v5) (uNext := u5) (WNext := W5) (eNext := e5)
      (by simpa [body5, body4, err4] using hland5)
      h5.2.2.2.2.2.1 h5.2.2.2.2.2.2
    simpa [body6, P6] using hcomp
  have herr6 : 8 * (3 ^ v6 * err6) ≤ 3 ^ v6 * A6 := by
    have hgap : v + P6 + W5 - 1 =
        v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1 := by
      simp [P6]; omega
    have hmiss := eight_of_miss (v := v) (gap := P6) (W := W5)
      (base := v + v' + v'' + v''' + v4 + v5) (tail := v6) hv
      (by simpa [hgap] using hshort6)
    simpa [err6, A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hpow' : 3 ^ v6 * A6 + 1 ≤
      2 ^ (v + P6 + W5 + v6 + W6 - 1) := by
    have hA : 3 ^ v6 * A6 = 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6) := by
      simp [A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm, Nat.add_left_comm]
    have hexp : v + v' + v'' + v''' + v4 + v5 + v6 + W + W' + W'' + W''' +
        W4 + W5 + W6 - 1 = v + P6 + W5 + v6 + W6 - 1 := by simp [P6]; omega
    rw [hA]
    have hlt := Nat.succ_le_of_lt hpow
    rw [hexp] at hlt
    exact hlt
  exact close_one_long (n := n) (v := v) (u := u) (body := body6) (A := A6)
    (C := C6) (err := err6) (P := P6) (Wprev := W5) (ePrev := e5)
    (vNext := v6) (uNext := u6) (WNext := W6) (eNext := e6) (k := 5)
    h.2.2.2.2.2.1 hu hv hbody6 hC6 (by decide) hprev h6 herr6 rfl hpow'

/-- **Six misses, then a long eighth.**  This is the last length of the
spare-bit budget: `k = 6` makes the leading coefficient exactly `16`. -/
theorem drop_of_six_misses_then_long
    {n v u W e v' u' W' e' v'' u'' W'' e'' v''' u''' W''' e'''
      v4 u4 W4 e4 v5 u5 W5 e5 v6 u6 W6 e6 v7 u7 W7 e7 : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion e v' u' W' e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (h''' : IsExcursion e'' v''' u''' W''' e''')
    (h4 : IsExcursion e''' v4 u4 W4 e4)
    (h5 : IsExcursion e4 v5 u5 W5 e5)
    (h6 : IsExcursion e5 v6 u6 W6 e6)
    (h7 : IsExcursion e6 v7 u7 W7 e7)
    (hv : 4 ≤ v) (hlight : 2 ^ W * (2 ^ v - 1) < 3 ^ v)
    (hshort : 2 ^ (v + v' + W + W' - 1) ≤ 3 ^ (v + v'))
    (hshort3 : 2 ^ (v + v' + v'' + W + W' + W'' - 1) ≤ 3 ^ (v + v' + v''))
    (hshort4 : 2 ^ (v + v' + v'' + v''' + W + W' + W'' + W''' - 1) ≤
      3 ^ (v + v' + v'' + v'''))
    (hshort5 : 2 ^ (v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1) ≤
      3 ^ (v + v' + v'' + v''' + v4))
    (hshort6 : 2 ^ (v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1) ≤
      3 ^ (v + v' + v'' + v''' + v4 + v5))
    (hshort7 : 2 ^ (v + v' + v'' + v''' + v4 + v5 + v6 + W + W' + W'' + W''' +
        W4 + W5 + W6 - 1) ≤ 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6))
    (hpow : 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6 + v7) <
      2 ^ (v + v' + v'' + v''' + v4 + v5 + v6 + v7 + W + W' + W'' + W''' +
        W4 + W5 + W6 + W7 - 1)) :
    e7 < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  let A4 := 3 ^ (v + v' + v'' + v''')
  let C4 := 3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1))) +
    (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v'))) +
      3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))
  let err4 := (2 ^ W''' - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''')
  let body4 := 3 ^ v''' *
    (3 ^ v'' * (3 ^ v' * (3 ^ v * u + 2 ^ W - 1) + (2 ^ W' - 1) * 2 ^ (W + v')) +
      (2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))
  have hbody4 : body4 = A4 * u + C4 := by
    simpa [body4, A4, C4] using
      four_inner_poly (v := v) (u := u) (W := W) (v' := v') (W' := W')
        (v'' := v'') (W'' := W'') (v''' := v''')
  let body5 := 3 ^ v4 * (body4 + err4)
  let A5 := 3 ^ v4 * A4
  let C5 := 3 ^ v4 * C4 + 3 ^ v4 * err4
  have hbody5 : body5 = A5 * u + C5 := by
    have hpush := push_closed (body := body4) (u := u) (A := A4) (C := C4)
      (q := v4) (err := err4) (T := 0) hbody4
    simpa [body5, A5, C5, Nat.add_zero, Nat.mul_zero] using hpush
  let err5 := (2 ^ W4 - 1) * 2 ^ (W + v' + W' + v'' + W'' + v''' + W''' + v4)
  let A6 := 3 ^ (v + v' + v'' + v''' + v4 + v5)
  have hC4 : 8 * C4 ≤ 3 * A4 := by
    have h1 := eight_first_error_four (v' := v') (v'' := v'') (v''' := v''') hv hlight
    have h2 := eight_middle_error_four (v' := v') (v'' := v'') (v''' := v''') hv hshort
    have h3 := eight_third_error (v' := v') (v'' := v'') (v''' := v''') hv hshort3
    have hsum : 8 * C4 =
        8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
        (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
          8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v'')))) := by
      simp [C4, Nat.mul_add, Nat.add_assoc]
    rw [hsum]
    calc
      8 * (3 ^ v''' * (3 ^ v'' * (3 ^ v' * (2 ^ W - 1)))) +
          (8 * (3 ^ v''' * (3 ^ v'' * ((2 ^ W' - 1) * 2 ^ (W + v')))) +
            8 * (3 ^ v''' * ((2 ^ W'' - 1) * 2 ^ (W + v' + W' + v''))))
          ≤ A4 + (A4 + A4) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
      _ = 1 * A4 + (1 * A4 + 1 * A4) := by simp [Nat.one_mul]
      _ = 1 * A4 + (1 + 1) * A4 := by rw [← Nat.add_mul]
      _ = (1 + (1 + 1)) * A4 := by rw [← Nat.add_mul]
      _ = 3 * A4 := by rw [show (1 + (1 + 1) : Nat) = 3 by decide]
  have herr4 : 8 * (3 ^ v4 * err4) ≤ A5 := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''') + W''' - 1 =
        v + v' + v'' + v''' + W + W' + W'' + W''' - 1 := by omega
    have hmiss := eight_of_miss (v := v) (gap := W + v' + W' + v'' + W'' + v''')
      (W := W''') (base := v + v' + v'' + v''') (tail := v4) hv
      (by simpa [hgap] using hshort4)
    simpa [err4, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hE5 : 8 * (3 ^ v5 * err5) ≤ A6 := by
    have hgap : v + (W + v' + W' + v'' + W'' + v''' + W''' + v4) + W4 - 1 =
        v + v' + v'' + v''' + v4 + W + W' + W'' + W''' + W4 - 1 := by omega
    have hmiss := eight_of_miss (v := v)
      (gap := W + v' + W' + v'' + W'' + v''' + W''' + v4) (W := W4)
      (base := v + v' + v'' + v''' + v4) (tail := v5) hv
      (by simpa [hgap] using hshort5)
    simpa [err5, A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  have hC5 : 8 * C5 ≤ 4 * A5 := by
    have hscale : 8 * (3 ^ v4 * C4) ≤ 3 * A5 := by
      calc
        8 * (3 ^ v4 * C4) = 3 ^ v4 * (8 * C4) := by rw [Nat.mul_left_comm]
        _ ≤ 3 ^ v4 * (3 * A4) := Nat.mul_le_mul_left _ hC4
        _ = 3 * A5 := by simp [A5, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    calc
      8 * C5 = 8 * (3 ^ v4 * C4) + 8 * (3 ^ v4 * err4) := by simp [C5, Nat.mul_add]
      _ ≤ 3 * A5 + A5 := Nat.add_le_add hscale herr4
      _ = 3 * A5 + 1 * A5 := by rw [Nat.one_mul]
      _ = 4 * A5 := by rw [← Nat.add_mul, show (3 + 1 : Nat) = 4 by decide]
  let C6 := 3 ^ v5 * C5 + 3 ^ v5 * err5
  let body6 := 3 ^ v5 * (body5 + err5)
  have hA6 : 3 ^ v5 * A5 = A6 := by
    simp [A6, A5, A4, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm, Nat.add_left_comm]
  have hC6 : 8 * C6 ≤ 5 * A6 := by
    calc
      8 * C6 = 8 * (3 ^ v5 * C5) + 8 * (3 ^ v5 * err5) := by simp [C6, Nat.mul_add]
      _ = 3 ^ v5 * (8 * C5) + 8 * (3 ^ v5 * err5) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ v5 * (4 * A5) + A6 := Nat.add_le_add (Nat.mul_le_mul_left _ hC5) hE5
      _ = 4 * (3 ^ v5 * A5) + A6 := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 4 * A6 + A6 := by rw [hA6]
      _ = 4 * A6 + 1 * A6 := by rw [Nat.one_mul]
      _ = 5 * A6 := by rw [← Nat.add_mul, show (4 + 1 : Nat) = 5 by decide]
  have hbody6 : body6 = A6 * u + C6 := by
    have hpush := push_closed (body := body5) (u := u) (A := A5) (C := C5)
      (q := v5) (err := err5) (T := 0) hbody5
    simpa [body6, C6, hA6, Nat.add_zero, Nat.mul_zero] using hpush
  let P6 := W + v' + W' + v'' + W'' + v''' + W''' + v4 + W4 + v5
  let err6 := (2 ^ W5 - 1) * 2 ^ P6
  have herr6 : 8 * (3 ^ v6 * err6) ≤ 3 ^ v6 * A6 := by
    have hgap : v + P6 + W5 - 1 =
        v + v' + v'' + v''' + v4 + v5 + W + W' + W'' + W''' + W4 + W5 - 1 := by
      simp [P6]; omega
    have hmiss := eight_of_miss (v := v) (gap := P6) (W := W5)
      (base := v + v' + v'' + v''' + v4 + v5) (tail := v6) hv
      (by simpa [hgap] using hshort6)
    simpa [err6, A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm] using hmiss
  let A7 := 3 ^ v6 * A6
  let C7 := 3 ^ v6 * C6 + 3 ^ v6 * err6
  let body7 := 3 ^ v6 * (body6 + err6)
  have hC7 : 8 * C7 ≤ 6 * A7 := by
    calc
      8 * C7 = 8 * (3 ^ v6 * C6) + 8 * (3 ^ v6 * err6) := by simp [C7, Nat.mul_add]
      _ = 3 ^ v6 * (8 * C6) + 8 * (3 ^ v6 * err6) := by rw [Nat.mul_left_comm]
      _ ≤ 3 ^ v6 * (5 * A6) + A7 := Nat.add_le_add (Nat.mul_le_mul_left _ hC6) herr6
      _ = 5 * A7 + A7 := by
        rw [show 3 ^ v6 * (5 * A6) = 5 * (3 ^ v6 * A6) from Nat.mul_left_comm _ _ _]
      _ = 5 * A7 + 1 * A7 := by rw [Nat.one_mul]
      _ = 6 * A7 := by rw [← Nat.add_mul, show (5 + 1 : Nat) = 6 by decide]
  have hbody7 : body7 = A7 * u + C7 := by
    have hpush := push_closed (body := body6) (u := u) (A := A6) (C := C6)
      (q := v6) (err := err6) (T := 0) hbody6
    simpa [body7, A7, C7, Nat.add_zero, Nat.mul_zero] using hpush
  let P7 := P6 + W5 + v6
  let err7 := (2 ^ W6 - 1) * 2 ^ P7
  have hprev : body7 = 2 ^ (P7 + W6) * e6 + 2 ^ P7 := by
    have hland6 : body6 = 2 ^ (P6 + W5) * e5 + 2 ^ P6 := by
      have hland5 := five_step_landing h h' h'' h''' h4
      have hcomp := compose_step (inner := body5)
        (P := W + v' + W' + v'' + W'' + v''' + W''' + v4) (W := W4) (e := e4)
        (vNext := v5) (uNext := u5) (WNext := W5) (eNext := e5)
        (by simpa [body5, body4, err4] using hland5)
        h5.2.2.2.2.2.1 h5.2.2.2.2.2.2
      simpa [body6, P6] using hcomp
    have hcomp := compose_step (inner := body6) (P := P6) (W := W5) (e := e5)
      (vNext := v6) (uNext := u6) (WNext := W6) (eNext := e6)
      hland6 h6.2.2.2.2.2.1 h6.2.2.2.2.2.2
    simpa [body7, P7] using hcomp
  have herr7 : 8 * (3 ^ v7 * err7) ≤ 3 ^ v7 * A7 := by
    have hgap : v + P7 + W6 - 1 =
        v + v' + v'' + v''' + v4 + v5 + v6 + W + W' + W'' + W''' + W4 + W5 + W6 - 1 := by
      simp [P7, P6]; omega
    have hmiss := eight_of_miss (v := v) (gap := P7) (W := W6)
      (base := v + v' + v'' + v''' + v4 + v5 + v6) (tail := v7) hv
      (by simpa [hgap] using hshort7)
    have hA : 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6) * 3 ^ v7 = 3 ^ v7 * A7 := by
      simp [A7, A6, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, ← Nat.pow_add,
        Nat.add_comm, Nat.add_left_comm]
    simpa [err7, hA] using hmiss
  have hpow' : 3 ^ v7 * A7 + 1 ≤ 2 ^ (v + P7 + W6 + v7 + W7 - 1) := by
    have hA : 3 ^ v7 * A7 = 3 ^ (v + v' + v'' + v''' + v4 + v5 + v6 + v7) := by
      simp [A7, A6, Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm, Nat.add_left_comm]
    have hexp : v + v' + v'' + v''' + v4 + v5 + v6 + v7 + W + W' + W'' + W''' +
        W4 + W5 + W6 + W7 - 1 = v + P7 + W6 + v7 + W7 - 1 := by
      simp [P7, P6]; omega
    rw [hA]
    have hlt := Nat.succ_le_of_lt hpow
    rw [hexp] at hlt
    exact hlt
  exact close_one_long (n := n) (v := v) (u := u) (body := body7) (A := A7)
    (C := C7) (err := err7) (P := P7) (Wprev := W6) (ePrev := e6)
    (vNext := v7) (uNext := u7) (WNext := W7) (eNext := e7) (k := 6)
    h.2.2.2.2.2.1 hu hv hbody7 hC7 (by decide) hprev h7 herr7 rfl hpow'

/-- `111 → 283 → 319 → 911 → 577 → 433 → 325 → 61 → 23`. -/
theorem one_eleven_eight_step_drops :
    IsExcursion 111 4 7 1 283 ∧
    IsExcursion 283 2 71 1 319 ∧
    IsExcursion 319 6 5 2 911 ∧
    IsExcursion 911 4 57 3 577 ∧
    IsExcursion 577 1 289 1 433 ∧
    IsExcursion 433 1 217 1 325 ∧
    IsExcursion 325 1 163 3 61 ∧
    IsExcursion 61 1 31 2 23 ∧ 23 < 111 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `223 → 425 → 319 → 911 → 577 → 433 → 325 → 61`. -/
theorem two_twenty_three_seven_step_drops :
    IsExcursion 223 5 7 2 425 ∧
    IsExcursion 425 1 213 1 319 ∧
    IsExcursion 319 6 5 2 911 ∧
    IsExcursion 911 4 57 3 577 ∧
    IsExcursion 577 1 289 1 433 ∧
    IsExcursion 433 1 217 1 325 ∧
    IsExcursion 325 1 163 3 61 ∧ 61 < 223 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `639 → 5467 → 6151 → 10381 → 3893 → 365 → 137`. -/
theorem six_thirty_nine_six_step_drops :
    IsExcursion 639 7 5 1 5467 ∧
    IsExcursion 5467 2 1367 1 6151 ∧
    IsExcursion 6151 3 769 1 10381 ∧
    IsExcursion 10381 1 5191 2 3893 ∧
    IsExcursion 3893 1 1947 4 365 ∧
    IsExcursion 365 1 183 2 137 ∧ 137 < 639 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- **Two `(3, 1)` steps, then a long third.**  Length `3` leaves a factor
`4`.  Four copies of each of the two fixed errors `27` and `16` fit in
`3^6`, and `7` still sits under `8`. -/
theorem drop_of_two_three_one_then_long
    {n u e u' e' v'' u'' W'' e'' : Nat}
    (h : IsExcursion n 3 u 1 e) (h' : IsExcursion e 3 u' 1 e')
    (h'' : IsExcursion e' v'' u'' W'' e'')
    (hpow : 3 ^ (6 + v'') < 2 ^ (7 + v'' + W'')) : e'' < n := by
  have hu : 1 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hA : 3 ^ (6 + v'') = 729 * 3 ^ v'' := by
    rw [Nat.pow_add, show (3 : Nat) ^ 6 = 729 by decide]
  have hE1 : 4 * (3 ^ v'' * 27) ≤ 3 ^ (6 + v'') := by
    rw [hA]
    have : (4 * 27 : Nat) ≤ 729 := by decide
    calc
      4 * (3 ^ v'' * 27) = (4 * 27) * 3 ^ v'' := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 729 * 3 ^ v'' := Nat.mul_le_mul_right _ this
  have hE2 : 4 * (3 ^ v'' * 16) ≤ 3 ^ (6 + v'') := by
    rw [hA]
    have : (4 * 16 : Nat) ≤ 729 := by decide
    calc
      4 * (3 ^ v'' * 16) = (4 * 16) * 3 ^ v'' := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 729 * 3 ^ v'' := Nat.mul_le_mul_right _ this
  have hT : 4 * 2 ^ (5 + v'' + W'') = 2 ^ (7 + v'' + W'') := by
    calc
      4 * 2 ^ (5 + v'' + W'') = 2 ^ 2 * 2 ^ (5 + v'' + W'') := by
        rw [show (4 : Nat) = 2 ^ 2 by decide]
      _ = 2 ^ (2 + (5 + v'' + W'')) := by rw [← Nat.pow_add]
      _ = 2 ^ (7 + v'' + W'') := by rw [show 2 + (5 + v'' + W'') = 7 + v'' + W'' by omega]
  have hone : 3 ^ (6 + v'') + 1 ≤ 2 ^ (7 + v'' + W'') := Nat.succ_le_of_lt hpow
  have hAm : 3 ^ (6 + v'') ≤ 2 ^ (7 + v'' + W'') - 1 := Nat.le_sub_of_add_le hone
  have hpair : 4 * (3 ^ v'' * 27) + 4 * (3 ^ v'' * 16) ≤
      3 ^ (6 + v'') + 3 ^ (6 + v'') := Nat.add_le_add hE1 hE2
  have hsix : 4 * 3 ^ (6 + v'') + 4 * (3 ^ v'' * 27) + 4 * (3 ^ v'' * 16) ≤
      6 * 3 ^ (6 + v'') := by
    have htwo : 3 ^ (6 + v'') + 3 ^ (6 + v'') = 2 * 3 ^ (6 + v'') := by
      rw [← Nat.two_mul]
    have hle := Nat.add_le_add_left hpair (4 * 3 ^ (6 + v''))
    rw [← Nat.add_assoc] at hle
    calc
      4 * 3 ^ (6 + v'') + 4 * (3 ^ v'' * 27) + 4 * (3 ^ v'' * 16)
          ≤ 4 * 3 ^ (6 + v'') + (3 ^ (6 + v'') + 3 ^ (6 + v'')) := hle
      _ = 4 * 3 ^ (6 + v'') + 2 * 3 ^ (6 + v'') := by rw [htwo]
      _ = 6 * 3 ^ (6 + v'') := by
        rw [← Nat.add_mul, show (4 + 2 : Nat) = 6 by decide]
  have h6A : 6 * 3 ^ (6 + v'') ≤ 6 * 2 ^ (7 + v'' + W'') - 6 := by
    have hmul := Nat.mul_le_mul_left 6 hAm
    have hdist : 6 * (2 ^ (7 + v'' + W'') - 1) = 6 * 2 ^ (7 + v'' + W'') - 6 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rwa [hdist] at hmul
  have hscaled : 4 * (3 ^ (6 + v'') + 3 ^ v'' * 27 + 3 ^ v'' * 16 +
      2 ^ (5 + v'' + W'')) ≤ 4 * 2 ^ (8 + v'' + W'') := by
    have hleft : 4 * (3 ^ (6 + v'') + 3 ^ v'' * 27 + 3 ^ v'' * 16 +
        2 ^ (5 + v'' + W'')) =
        4 * 3 ^ (6 + v'') + 4 * (3 ^ v'' * 27) + 4 * (3 ^ v'' * 16) +
          4 * 2 ^ (5 + v'' + W'') := by
      simp [Nat.mul_add, Nat.add_assoc]
    rw [hleft, hT]
    have hstep : 4 * 3 ^ (6 + v'') + 4 * (3 ^ v'' * 27) + 4 * (3 ^ v'' * 16) +
        2 ^ (7 + v'' + W'') ≤ 6 * 3 ^ (6 + v'') + 2 ^ (7 + v'' + W'') :=
      Nat.add_le_add_right hsix _
    have hstep2 : 6 * 3 ^ (6 + v'') + 2 ^ (7 + v'' + W'') ≤
        6 * 2 ^ (7 + v'' + W'') - 6 + 2 ^ (7 + v'' + W'') :=
      Nat.add_le_add_right h6A _
    have hstep3 : 6 * 2 ^ (7 + v'' + W'') - 6 + 2 ^ (7 + v'' + W'') ≤
        6 * 2 ^ (7 + v'' + W'') + 2 ^ (7 + v'' + W'') :=
      Nat.add_le_add_right (Nat.sub_le _ _) _
    have hstep4 : 6 * 2 ^ (7 + v'' + W'') + 2 ^ (7 + v'' + W'') =
        7 * 2 ^ (7 + v'' + W'') := by
      have hp : 2 ^ (7 + v'' + W'') = 1 * 2 ^ (7 + v'' + W'') :=
        (Nat.one_mul _).symm
      calc
        6 * 2 ^ (7 + v'' + W'') + 2 ^ (7 + v'' + W'')
            = 6 * 2 ^ (7 + v'' + W'') + 1 * 2 ^ (7 + v'' + W'') := by rw [← hp]
        _ = (6 + 1) * 2 ^ (7 + v'' + W'') := by rw [← Nat.add_mul]
        _ = 7 * 2 ^ (7 + v'' + W'') := by rw [show (6 + 1 : Nat) = 7 by decide]
    have hstep5 : 7 * 2 ^ (7 + v'' + W'') ≤ 4 * 2 ^ (8 + v'' + W'') := by
      have h8 : 4 * 2 ^ (8 + v'' + W'') = 8 * 2 ^ (7 + v'' + W'') := by
        calc
          4 * 2 ^ (8 + v'' + W'')
              = 4 * 2 ^ ((7 + v'' + W'') + 1) := by
                rw [show 8 + v'' + W'' = (7 + v'' + W'') + 1 by omega]
          _ = 4 * (2 * 2 ^ (7 + v'' + W'')) := by rw [two_pow_succ]
          _ = 8 * 2 ^ (7 + v'' + W'') := by
            rw [← Nat.mul_assoc, show (4 * 2 : Nat) = 8 by decide]
      rw [h8]
      exact Nat.mul_le_mul_right _ (by decide : (7 : Nat) ≤ 8)
    exact Nat.le_trans hstep (Nat.le_trans hstep2 (Nat.le_trans hstep3
      (hstep4 ▸ hstep5)))
  have hC : 3 ^ (6 + v'') + (3 ^ v'' * 27 + (3 ^ v'' * 16 + 2 ^ (5 + v'' + W''))) ≤
      2 ^ (8 + v'' + W'') := by
    have hle := Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < (4 : Nat))
    simpa [Nat.add_assoc] using hle
  have hAB : 3 ^ (6 + v'') ≤ 2 ^ (8 + v'' + W'') := by
    exact Nat.le_trans hAm (Nat.le_trans (Nat.sub_le _ _)
      (two_pow_le_two_pow (by omega : 7 + v'' + W'' ≤ 8 + v'' + W'')))
  have hmul := add_le_mul_of_add_le hAB hC hu
  have hgoal : 3 ^ v'' * (3 ^ 3 * (3 ^ 3 * u + 2 ^ 1 - 1) + (2 ^ 1 - 1) * 2 ^ (1 + 3)) +
      2 ^ (1 + 3 + 1 + v'' + W'') ≤ 2 ^ (3 + 1 + 3 + 1 + v'' + W'') * u := by
    have hsplit : 3 ^ 3 * u + 2 ^ 1 - 1 = 3 ^ 3 * u + 1 := by
      rw [Nat.pow_one]; omega
    have h27 : (3 : Nat) ^ 3 = 27 := by decide
    have h2 : (2 : Nat) ^ 1 = 2 := by decide
    have h16 : (2 : Nat) ^ (1 + 3) = 16 := by decide
    have hEq : 3 ^ v'' * (3 ^ 3 * (3 ^ 3 * u + 2 ^ 1 - 1) + (2 ^ 1 - 1) * 2 ^ (1 + 3)) +
        2 ^ (1 + 3 + 1 + v'' + W'') =
        3 ^ (6 + v'') * u + (3 ^ v'' * 27 + (3 ^ v'' * 16 + 2 ^ (5 + v'' + W''))) := by
      calc
        3 ^ v'' * (3 ^ 3 * (3 ^ 3 * u + 2 ^ 1 - 1) + (2 ^ 1 - 1) * 2 ^ (1 + 3)) +
            2 ^ (1 + 3 + 1 + v'' + W'')
            = 3 ^ v'' * (27 * (27 * u + 1) + 1 * 16) + 2 ^ (5 + v'' + W'') := by
              rw [hsplit, h27, h2, h16]
        _ = 3 ^ v'' * (27 * (27 * u + 1) + 16) + 2 ^ (5 + v'' + W'') := by
              rw [Nat.one_mul]
        _ = 3 ^ v'' * ((27 * (27 * u) + 27 * 1) + 16) + 2 ^ (5 + v'' + W'') := by
              rw [Nat.mul_add (n := 27)]
        _ = 3 ^ v'' * (27 * (27 * u) + (27 + 16)) + 2 ^ (5 + v'' + W'') := by
              rw [Nat.mul_one, Nat.add_assoc]
        _ = 3 ^ v'' * (27 * (27 * u) + 43) + 2 ^ (5 + v'' + W'') := by
              rw [show (27 + 16 : Nat) = 43 by decide]
        _ = 3 ^ v'' * ((27 * 27) * u + 43) + 2 ^ (5 + v'' + W'') := by
              rw [← Nat.mul_assoc (n := 27) (m := 27) (k := u)]
        _ = 3 ^ v'' * (729 * u + 43) + 2 ^ (5 + v'' + W'') := by
              rw [show (27 * 27 : Nat) = 729 by decide]
        _ = 3 ^ v'' * (729 * u) + 3 ^ v'' * 43 + 2 ^ (5 + v'' + W'') := by
              rw [Nat.mul_add]
        _ = (3 ^ v'' * 729) * u + 43 * 3 ^ v'' + 2 ^ (5 + v'' + W'') := by
              rw [Nat.mul_assoc, Nat.mul_comm (3 ^ v'') 43]
        _ = (729 * 3 ^ v'') * u + (27 + 16) * 3 ^ v'' + 2 ^ (5 + v'' + W'') := by
              rw [Nat.mul_comm (3 ^ v'') 729, show (43 : Nat) = 27 + 16 by decide]
        _ = 729 * 3 ^ v'' * u + (27 * 3 ^ v'' + 16 * 3 ^ v'') + 2 ^ (5 + v'' + W'') := by
              rw [Nat.add_mul]
        _ = 3 ^ (6 + v'') * u + (27 * 3 ^ v'' + 16 * 3 ^ v'' + 2 ^ (5 + v'' + W'')) := by
              rw [← hA, Nat.add_assoc]
        _ = 3 ^ (6 + v'') * u + (27 * 3 ^ v'' + (16 * 3 ^ v'' + 2 ^ (5 + v'' + W''))) := by
              rw [Nat.add_assoc (27 * 3 ^ v'') (16 * 3 ^ v'')]
        _ = 3 ^ (6 + v'') * u + (3 ^ v'' * 27 + (3 ^ v'' * 16 + 2 ^ (5 + v'' + W''))) := by
              rw [Nat.mul_comm 27, Nat.mul_comm 16]
    rw [hEq]
    have hpow : 2 ^ (8 + v'' + W'') = 2 ^ (3 + 1 + 3 + 1 + v'' + W'') := by
      congr 1
    rw [← hpow]
    exact hmul
  exact (drop_iff_three_expanded h h' h'').mpr hgoal

/-- Two `(3, 1)` steps then a long third: `231 → 391 → 661 → 31`.
`3^7 = 2187 < 8192 = 2^{13}`. -/
theorem two_thirty_one_three_step_drops :
    IsExcursion 231 3 29 1 391 ∧
    IsExcursion 391 3 49 1 661 ∧
    IsExcursion 661 1 331 5 31 ∧
    31 < 231 ∧
    3 ^ (6 + 1) < 2 ^ (7 + 1 + 5) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩

/-- `(3, 1)` fuel 7 then a long run of length `5`: `12647 → 21343 → 5065`.
`3^8 = 6561 < 8192 = 2^{13}`. -/
theorem twelve_six_four_seven_two_step_drops :
    IsExcursion 12647 3 1581 1 21343 ∧
    IsExcursion 21343 5 667 5 5065 ∧ 5065 < 12647 ∧
    3 ^ (3 + 5) < 2 ^ (3 + 5 + 5) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩

/-- `(2, 1)` then a long run of length `7`: `62235 → 70015 → 4673`.
`3^9 = 19683 < 131072 = 2^{17}`. -/
theorem six_two_two_three_five_two_step_drops :
    IsExcursion 62235 2 15559 1 70015 ∧
    IsExcursion 70015 7 547 8 4673 ∧ 4673 < 62235 ∧
    3 ^ (2 + 7) < 2 ^ (2 + 7 + 8) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩

/-! ## 10.  Witnesses -/

/-- LandOne heavy, recovered: `7 → 13 → 5`. -/
theorem seven_two_step_drops :
    IsExcursion 7 3 1 1 13 ∧ IsExcursion 13 1 7 2 5 ∧ 5 < 7 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- RemTwo, recovered: `1947 → 2191 → 1387`. -/
theorem nineteen_forty_seven_two_step_drops :
    IsExcursion 1947 2 487 1 2191 ∧
    IsExcursion 2191 4 137 3 1387 ∧ 1387 < 1947 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Two-step `(3, 1)` then `(1, 1)` grows: `71 → 121 → 91`. -/
theorem seventy_one_two_step_grows :
    IsExcursion 71 3 9 1 121 ∧ IsExcursion 121 1 61 1 91 ∧ 71 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- Three-step `(3, 1)` then `(1, 1)` then `v'' = 1` drops:
`455 → 769 → 577 → 433`. -/
theorem four_fifty_five_three_step_drops :
    IsExcursion 455 3 57 1 769 ∧
    IsExcursion 769 1 385 1 577 ∧
    IsExcursion 577 1 289 1 433 ∧ 433 < 455 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- **New witness.**  The `W' = 4` bound after leftover `v' = 6` is
attained and still drops: `10523 → 11839 → 8429`. -/
theorem ten_five_twenty_three_v_six :
    IsExcursion 10523 2 2631 1 11839 ∧
    IsExcursion 11839 6 185 4 8429 ∧ 8429 < 10523 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `(4, 1)` then `(1, W' ≥ 2)` drops: `175 → 445 → 167`. -/
theorem one_seventy_five_two_step_drops :
    IsExcursion 175 4 11 1 445 ∧
    IsExcursion 445 1 223 2 167 ∧ 167 < 175 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `(4, 1)` then a run on the combined ceiling: `431 → 1093 → 205`.
`3^5 = 243 < 256 = 2^{5+3}`. -/
theorem four_thirty_one_two_step_drops :
    IsExcursion 431 4 27 1 1093 ∧
    IsExcursion 1093 1 547 3 205 ∧ 205 < 431 ∧
    3 ^ (4 + 1) < 2 ^ (4 + 1 + 3) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide⟩

/-- Light `(4, 2)` then a run on the shifted ceiling: `79 → 101 → 19`.
`3^5 = 243 < 512 = 2^{4+1+2+3−1}`. -/
theorem seventy_nine_two_step_drops :
    IsExcursion 79 4 5 2 101 ∧
    IsExcursion 101 1 51 3 19 ∧ 19 < 79 ∧
    2 ^ 2 * (2 ^ 4 - 1) < 3 ^ 4 ∧
    3 ^ (4 + 1) < 2 ^ (4 + 1 + 2 + 3 - 1) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega, by decide, by decide⟩

/-- Short second step, long third: `463 → 587 → 661 → 31`.
`2^8 = 256 ≤ 729 = 3^6`, and `3^7 = 2187 < 16384 = 2^{14}`. -/
theorem four_sixty_three_three_step_drops :
    IsExcursion 463 4 29 2 587 ∧
    IsExcursion 587 2 147 1 661 ∧
    IsExcursion 661 1 331 5 31 ∧ 31 < 463 ∧
    2 ^ 2 * (2 ^ 4 - 1) < 3 ^ 4 ∧
    2 ^ (4 + 2 + 2 + 1 - 1) ≤ 3 ^ (4 + 2) ∧
    3 ^ (4 + 2 + 1) < 2 ^ (4 + 2 + 1 + 2 + 1 + 5 - 1) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   by omega, by decide, by decide, by decide⟩

/-- Two misses, then a long fourth: `623 → 1579 → 1777 → 1333 → 125`.
`2^7 = 128 ≤ 729 = 3^6`, `2^9 = 512 ≤ 2187 = 3^7`, and
`3^8 = 6561 < 16384 = 2^{14}`. -/
theorem six_twenty_three_four_step_drops :
    IsExcursion 623 4 39 1 1579 ∧
    IsExcursion 1579 2 395 1 1777 ∧
    IsExcursion 1777 1 889 1 1333 ∧
    IsExcursion 1333 1 667 4 125 ∧ 125 < 623 ∧
    2 ^ 1 * (2 ^ 4 - 1) < 3 ^ 4 ∧
    2 ^ (4 + 2 + 1 + 1 - 1) ≤ 3 ^ (4 + 2) ∧
    2 ^ (4 + 2 + 1 + 1 + 1 + 1 - 1) ≤ 3 ^ (4 + 2 + 1) ∧
    3 ^ (4 + 2 + 1 + 1) < 2 ^ (4 + 2 + 1 + 1 + 1 + 1 + 1 + 4 - 1) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
   by omega, by decide, by decide, by decide, by decide⟩

/-- `(4, 1)` then `(1, 1)` grows: `47 → 121 → 91`. -/
theorem forty_seven_two_step_grows :
    IsExcursion 47 4 3 1 121 ∧ IsExcursion 121 1 61 1 91 ∧ 47 < 91 :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

end ExcursionTelescope
end Collatz

section AxiomAudit
open Collatz.ExcursionTelescope
#print axioms two_step_landing
#print axioms drop_iff_two
#print axioms drop_iff_two_expanded
#print axioms three_step_landing
#print axioms drop_iff_three
#print axioms drop_iff_three_expanded
#print axioms drop_of_three_one_then_v_one_heavy
#print axioms grows_of_three_one_then_one_one
#print axioms drop_of_three_one_one_one_then_v_one
#print axioms drop_iff_two_one
#print axioms drop_of_two_one_then_v_four
#print axioms lemmaX_of_two_one_then_v_six
#print axioms drop_of_four_one_then_v_one_heavy
#print axioms grows_of_four_one_then_one_one
#print axioms drop_of_W_one_then_long
#print axioms four_thirty_one_two_step_drops
#print axioms drop_of_light_then_long
#print axioms seventy_nine_two_step_drops
#print axioms drop_of_short_then_long
#print axioms four_sixty_three_three_step_drops
#print axioms four_step_landing
#print axioms drop_iff_four
#print axioms drop_iff_four_expanded
#print axioms drop_of_two_misses_then_long
#print axioms six_twenty_three_four_step_drops
end AxiomAudit
