import Collatz.Strategy.PhasePolynomial
import Collatz.Strategy.PowerSeparation
import Collatz.Strategy.CycleLength1539

/-! Integer norms for the two cubic phase polynomials. Multiplication in
the ring with relation `z³ = z - 1` gives a three-term coefficient recurrence. -/

namespace Collatz.CubicPhaseNorm

open Collatz.Arith Collatz.AccCycle Collatz.CyclicOrder Collatz.OneExtraCycle

private structure Triple where
  u : Int
  v : Int
  w : Int

private def Triple.shift (c : Triple) : Triple := ⟨-c.w, c.u + c.w, c.v⟩

private def coeff : Nat → Triple
  | 0 => ⟨1, 0, 0⟩
  | a + 1 => (coeff a).shift

private def Triple.eval (c : Triple) (z : Int) : Int := c.u + c.v * z + c.w * z ^ 2

private def Triple.q₀ (c : Triple) : Int := (c.u + c.w) ^ 2 - c.v * (c.v - c.w)
private def Triple.q₁ (c : Triple) : Int := c.w * (c.v - c.w) - c.v * (c.u + c.w)
private def Triple.q₂ (c : Triple) : Int := c.v ^ 2 - c.w * (c.u + c.w)

private def Triple.norm (c : Triple) : Int := c.u * c.q₀ - c.w * c.q₁ - c.v * c.q₂

private def Triple.twiceMinusOne (c : Triple) : Triple := ⟨2 * c.u - 1, 2 * c.v, 2 * c.w⟩
private def Triple.minusTwo (c : Triple) : Triple := ⟨c.u - 2, c.v, c.w⟩

private theorem eval_power {d z : Int} (hz : d ∣ z ^ 3 - z + 1) (a : Nat) :
    d ∣ (coeff a).eval z - z ^ a := by
  induction a with
  | zero => simp [coeff, Triple.eval]
  | succ a ih =>
    have h := Int.dvd_sub (Int.dvd_trans ih (Int.dvd_mul_right _ z))
      (Int.dvd_trans hz (Int.dvd_mul_left (coeff a).w _))
    rw [show ((coeff a).eval z - z ^ a) * z - (coeff a).w * (z ^ 3 - z + 1) =
      (coeff (a + 1)).eval z - z ^ (a + 1) by
        simp only [coeff, Triple.shift, Triple.eval, Int.pow_succ]
        grind] at h
    exact h

private theorem dvd_norm {d z : Int} (c : Triple) (hf : d ∣ z ^ 3 - z + 1)
    (hp : d ∣ c.eval z) : d ∣ c.norm := by
  let q := Triple.mk c.q₀ c.q₁ c.q₂
  let r := c.v * c.q₂ + c.w * c.q₁ + z * c.w * c.q₂
  have h := Int.dvd_sub (Int.dvd_trans hp (Int.dvd_mul_right _ (q.eval z)))
    (Int.dvd_trans hf (Int.dvd_mul_left r _))
  rw [show c.eval z * q.eval z - r * (z ^ 3 - z + 1) = c.norm by
    simp only [q, r, Triple.eval, Triple.norm, Triple.q₀, Triple.q₁, Triple.q₂]
    grind] at h
  exact h

private theorem dvd_of_inverse {d x y w : Int} (hi : d ∣ x * w - 1) (h : d ∣ x * y) :
    d ∣ y := by
  have hh := Int.dvd_sub (Int.dvd_trans h (Int.dvd_mul_left w _))
    (Int.dvd_trans hi (Int.dvd_mul_right _ y))
  rw [show w * (x * y) - (x * w - 1) * y = y by grind] at hh
  exact hh

private theorem dvd_power_relation_of_le {d z A B : Int} {a L u v : Nat}
    (hA : d ∣ A * z ^ a - 1) (hB : d ∣ B * z ^ L - 1) (hle : a * u ≤ L * v) :
    d ∣ B ^ v * z ^ (L * v - a * u) - A ^ u := by
  have ht := dvd_pow_sub hA u
  have hh := dvd_pow_sub hB v
  rw [Int.mul_pow, ← Int.pow_mul, Int.one_pow] at ht hh
  have hi : d ∣ z ^ (a * u) * A ^ u - 1 := by
    rwa [Int.mul_comm]
  apply dvd_of_inverse hi
  have h := Int.dvd_sub hh ht
  rw [show L * v = a * u + (L * v - a * u) by omega, Int.pow_add] at h
  rw [show B ^ v * (z ^ (a * u) * z ^ (L * v - a * u)) - 1 -
      (A ^ u * z ^ (a * u) - 1) =
      z ^ (a * u) * (B ^ v * z ^ (L * v - a * u) - A ^ u) by grind] at h
  exact h

/-- Combining the two phase powers eliminates their common exponent. -/
theorem dvd_short_power_relation {d z : Int} {a L u v : Nat}
    (h₂ : d ∣ 2 * z ^ a - 1) (h₃ : d ∣ 3 * z ^ L - 1) (hle : a * u ≤ L * v) :
    d ∣ (3 : Int) ^ v * z ^ (L * v - a * u) - (2 : Int) ^ u :=
  dvd_power_relation_of_le h₂ h₃ hle

private theorem close_multiples {a L Q : Nat} (ha : a < L) (hQ : 0 < Q) :
    ∃ u v : Nat, 0 < u ∧ u ≤ Q ∧ v ≤ u ∧ Q * (a * u - L * v) < L ∧ Q * (L * v - a * u) < L := by
  have hL : 0 < L := by omega
  let r := fun t : Nat => a * t % L
  let q := fun t : Nat => a * t / L
  let f := fun t : Nat => Q * r t / L
  have hr (t : Nat) : r t < L := Nat.mod_lt _ hL
  have hf (t : Nat) : f t < Q :=
    (Nat.div_lt_iff_lt_mul hL).mpr (Nat.mul_lt_mul_of_pos_left (hr t) hQ)
  obtain ⟨i, j, hij, hj, hsame⟩ :=
    Pigeonhole.exists_repeat (f := f) (fun i _ => hf i) (Nat.le_refl Q)
  let u := j - i
  let v := q j - q i
  have hqi : q i ≤ q j := Nat.div_le_div_right (Nat.mul_le_mul_left a (by omega))
  have hsplit (t : Nat) : L * q t + r t = a * t := Nat.div_add_mod _ _
  have hu : a * u + r i = L * v + r j := by
    dsimp only [u, v]
    rw [Nat.mul_sub, Nat.mul_sub]
    have hi := hsplit i
    have hJ := hsplit j
    have hai := Nat.mul_le_mul_left a (Nat.le_of_lt hij)
    have hqij := Nat.mul_le_mul_left L hqi
    omega
  have hv : v ≤ u := by
    by_cases h : v ≤ u
    · exact h
    · have hl := Nat.mul_le_mul_left L (show u + 1 ≤ v by omega)
      rw [Nat.mul_succ] at hl
      have hmul := Nat.mul_le_mul_right u (Nat.le_of_lt ha)
      have hri := hr i
      omega
  have hsmall (t : Nat) : L * f t + Q * r t % L = Q * r t := Nat.div_add_mod _ _
  have hm := hsmall i
  have hn := hsmall j
  rw [hsame] at hm
  have hmodi := Nat.mod_lt (Q * r i) hL
  have hmodj := Nat.mod_lt (Q * r j) hL
  have hd := congrArg (fun n : Nat => Q * n) hu
  simp only [Nat.mul_add] at hd
  refine ⟨u, v, by dsimp [u]; omega, by dsimp [u]; omega, hv, ?_, ?_⟩ <;>
    rw [Nat.mul_sub] <;> omega

/-- A bounded search over multiples of the two phase exponents gives a
binomial of degree less than `L / Q` in the strict scaled sense. -/
theorem exists_short_binomial_of_bases {d z A B : Int} {a L Q : Nat} (ha : a < L) (hQ : 0 < Q)
    (hA : d ∣ A * z ^ a - 1) (hB : d ∣ B * z ^ L - 1) :
    ∃ u v δ : Nat, 0 < u ∧ u ≤ Q ∧ v ≤ u ∧ Q * δ < L ∧
      ((d ∣ B ^ v * z ^ δ - A ^ u) ∨ (d ∣ A ^ u * z ^ δ - B ^ v)) := by
  obtain ⟨u, v, hu, huQ, hv, hd₁, hd₂⟩ := close_multiples ha hQ
  rcases Nat.le_total (a * u) (L * v) with hle | hle
  · exact ⟨u, v, L * v - a * u, hu, huQ, hv, hd₂, Or.inl (dvd_power_relation_of_le hA hB hle)⟩
  · exact ⟨u, v, a * u - L * v, hu, huQ, hv, hd₁, Or.inr (dvd_power_relation_of_le hB hA hle)⟩

/-- Specialization to the unsigned phase powers. -/
theorem exists_short_binomial {d z : Int} {a L Q : Nat} (ha : a < L) (hQ : 0 < Q)
    (h₂ : d ∣ 2 * z ^ a - 1) (h₃ : d ∣ 3 * z ^ L - 1) :
    ∃ u v δ : Nat, 0 < u ∧ u ≤ Q ∧ v ≤ u ∧ Q * δ < L ∧
      ((d ∣ (3 : Int) ^ v * z ^ δ - (2 : Int) ^ u) ∨
        (d ∣ (2 : Int) ^ u * z ^ δ - (3 : Int) ^ v)) :=
  exists_short_binomial_of_bases ha hQ h₂ h₃

private theorem reciprocal {d z : Int} (hf : d ∣ 1 - z ^ 2 + z ^ 3)
    {a : Nat} (hp : d ∣ 2 * z ^ a - 1) :
    let w := z - z ^ 2
    (d ∣ w ^ 3 - w + 1) ∧ (d ∣ w ^ a - 2) := by
  let w := z - z ^ 2
  have hi : d ∣ z * w - 1 := by
    rw [show z * w - 1 = -(1 - z ^ 2 + z ^ 3) by dsimp [w]; grind]
    exact Int.dvd_neg.mpr hf
  have hiPow (k : Nat) : d ∣ z ^ k * w ^ k - 1 := by
    simpa only [Int.mul_pow, Int.one_pow] using dvd_pow_sub hi k
  constructor
  · apply dvd_of_inverse (hiPow 3)
    have h := Int.dvd_add (Int.dvd_sub hf (Int.dvd_trans hi (Int.dvd_mul_left (z ^ 2) _))) (hiPow 3)
    rw [show (1 - z ^ 2 + z ^ 3 - z ^ 2 * (z * w - 1)) + (z ^ 3 * w ^ 3 - 1) =
      z ^ 3 * (w ^ 3 - w + 1) by grind] at h
    exact h
  · have h := Int.dvd_sub (Int.dvd_trans (hiPow a) (Int.dvd_mul_left 2 _))
      (Int.dvd_trans hp (Int.dvd_mul_left (w ^ a) _))
    rw [show 2 * (z ^ a * w ^ a - 1) - w ^ a * (2 * z ^ a - 1) = w ^ a - 2 by grind] at h
    exact h

private theorem cubic_dvd_norms {d z : Int} {a : Nat} (hp : d ∣ 2 * z ^ a - 1)
    (hf : (d ∣ 1 - z ^ 2 + z ^ 3) ∨ (d ∣ 1 - z + z ^ 3)) :
    (d ∣ (coeff a).twiceMinusOne.norm) ∨ (d ∣ (coeff a).minusTwo.norm) := by
  rcases hf with h | h
  · right
    obtain ⟨hw, hpow⟩ := reciprocal h hp
    apply dvd_norm _ hw
    have hh := Int.dvd_add (eval_power hw a) hpow
    rw [show ((coeff a).eval (z - z ^ 2) - (z - z ^ 2) ^ a) + ((z - z ^ 2) ^ a - 2) =
        (coeff a).minusTwo.eval (z - z ^ 2) by
      simp only [Triple.eval, Triple.minusTwo]
      omega] at hh
    exact hh
  · left
    have hz : d ∣ z ^ 3 - z + 1 := by
      rwa [show z ^ 3 - z + 1 = 1 - z + z ^ 3 by omega]
    apply dvd_norm _ hz
    have hh := Int.dvd_add (Int.dvd_trans (eval_power hz a) (Int.dvd_mul_left 2 _)) hp
    rw [show 2 * ((coeff a).eval z - z ^ a) + (2 * z ^ a - 1) =
        (coeff a).twiceMinusOne.eval z by
      simp only [Triple.eval, Triple.twiceMinusOne]
      grind] at hh
    exact hh

private theorem norm_shift (c : Triple) : c.shift.norm = -c.norm := by
  simp only [Triple.norm, Triple.q₀, Triple.q₁, Triple.q₂, Triple.shift]
  grind

private theorem coeff_norm_odd (a : Nat) : (coeff a).norm % 2 = 1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [coeff, norm_shift, Int.neg_emod_two, ih]

private theorem twice_minus_one_norm_odd (c : Triple) : c.twiceMinusOne.norm % 2 = 1 := by
  have h : c.twiceMinusOne.norm =
      2 * (4 * c.norm - 6 * c.u ^ 2 + 3 * c.u - 8 * c.u * c.w + 2 * c.w -
        2 * c.w ^ 2 + 2 * c.v ^ 2 - 6 * c.v * c.w) - 1 := by
    simp only [Triple.norm, Triple.q₀, Triple.q₁, Triple.q₂, Triple.twiceMinusOne]
    grind
  omega

private theorem minus_two_norm_odd (a : Nat) : (coeff a).minusTwo.norm % 2 = 1 := by
  let c := coeff a
  have h : c.minusTwo.norm = c.norm +
      2 * (-3 * c.u ^ 2 + 6 * c.u - 4 - 4 * c.u * c.w + 4 * c.w -
        c.w ^ 2 + c.v ^ 2 - 3 * c.v * c.w) := by
    simp only [Triple.norm, Triple.q₀, Triple.q₁, Triple.q₂, Triple.minusTwo]
    grind
  have hodd : c.norm % 2 = 1 := coeff_norm_odd a
  change c.minusTwo.norm % 2 = 1
  omega

private theorem coeff_rec (a : Nat) :
    coeff (a + 3) = ⟨(coeff (a + 1)).u - (coeff a).u,
      (coeff (a + 1)).v - (coeff a).v, (coeff (a + 1)).w - (coeff a).w⟩ := by
  have h (c : Triple) :
      c.shift.shift.shift = ⟨c.shift.u - c.u, c.shift.v - c.v, c.shift.w - c.w⟩ := by
    simp only [Triple.shift]
    congr 1 <;> omega
  exact h (coeff a)

private def Bounded (c : Triple) (scale bound : Nat) : Prop :=
  scale * c.u.natAbs ≤ bound ∧ scale * c.v.natAbs ≤ bound ∧ scale * c.w.natAbs ≤ bound

private theorem recurrence_bound {a : Nat} {x y : Int}
    (hx : 3 ^ (a + 1) * x.natAbs ≤ 4 ^ (a + 1)) (hy : 3 ^ a * y.natAbs ≤ 4 ^ a) :
    3 ^ (a + 3) * (x - y).natAbs ≤ 4 ^ (a + 3) := by
  calc
    _ ≤ 3 ^ (a + 3) * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Int.natAbs_sub_le ..)
    _ = 9 * (3 ^ (a + 1) * x.natAbs) + 27 * (3 ^ a * y.natAbs) := by
      rw [Nat.mul_add, Nat.pow_add 3 a 3, Nat.pow_add 3 a 1]
      change 3 ^ a * 27 * x.natAbs + 3 ^ a * 27 * y.natAbs =
        9 * (3 ^ a * 3 * x.natAbs) + 27 * (3 ^ a * y.natAbs)
      grind
    _ ≤ 9 * 4 ^ (a + 1) + 27 * 4 ^ a :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hx) (Nat.mul_le_mul_left _ hy)
    _ ≤ _ := by rw [Nat.pow_add 4 a 1, Nat.pow_add 4 a 3]; grind

private theorem coeff_bound (a : Nat) : Bounded (coeff a) (3 ^ a) (4 ^ a) := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    match a with
    | 0 => unfold Bounded; decide
    | 1 => unfold Bounded; decide
    | 2 => unfold Bounded; decide
    | a + 3 =>
      obtain ⟨h₀, h₁, h₂⟩ := ih a (by omega)
      obtain ⟨g₀, g₁, g₂⟩ := ih (a + 1) (by omega)
      rw [coeff_rec]
      exact ⟨recurrence_bound g₀ h₀, recurrence_bound g₁ h₁, recurrence_bound g₂ h₂⟩

private theorem abs_mul_le {x y : Int} {U V : Nat} (hx : x.natAbs ≤ U) (hy : y.natAbs ≤ V) :
    (x * y).natAbs ≤ U * V := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul hx hy

private theorem abs_sub_le {x y : Int} {U V : Nat} (hx : x.natAbs ≤ U) (hy : y.natAbs ≤ V) :
    (x - y).natAbs ≤ U + V :=
  Nat.le_trans (Int.natAbs_sub_le ..) (Nat.add_le_add hx hy)

private theorem abs_norm_bound (c : Triple) (K : Nat) (h : Bounded c 1 K) :
    c.norm.natAbs ≤ 48 * K ^ 3 := by
  obtain ⟨hu, hv, hw⟩ : c.u.natAbs ≤ K ∧ c.v.natAbs ≤ K ∧ c.w.natAbs ≤ K := by
    simpa [Bounded] using h
  have hsum : (c.u + c.w).natAbs ≤ K + K :=
    Nat.le_trans (Int.natAbs_add_le ..) (Nat.add_le_add hu hw)
  have hsub : (c.v - c.w).natAbs ≤ K + K := abs_sub_le hv hw
  have h₀ : c.q₀.natAbs ≤ (K + K) * (K + K) + K * (K + K) := by
    rw [Triple.q₀, Int.pow_succ, Int.pow_one]
    exact abs_sub_le (abs_mul_le hsum hsum) (abs_mul_le hv hsub)
  have h₁ : c.q₁.natAbs ≤ K * (K + K) + K * (K + K) :=
    abs_sub_le (abs_mul_le hw hsub) (abs_mul_le hv hsum)
  have h₂ : c.q₂.natAbs ≤ K * K + K * (K + K) := by
    rw [Triple.q₂, Int.pow_succ, Int.pow_one]
    exact abs_sub_le (abs_mul_le hv hv) (abs_mul_le hw hsum)
  have hN := abs_sub_le (abs_sub_le (abs_mul_le hu h₀) (abs_mul_le hw h₁)) (abs_mul_le hv h₂)
  apply Nat.le_trans hN
  grind

private def Triple.scale (c : Triple) (s : Int) : Triple := ⟨s * c.u, s * c.v, s * c.w⟩

private theorem norm_scale (c : Triple) (s : Int) : (c.scale s).norm = s ^ 3 * c.norm := by
  simp only [Triple.norm, Triple.q₀, Triple.q₁, Triple.q₂, Triple.scale]
  grind

private theorem scaled_norm_bound (c : Triple) (a : Nat) (h : Bounded c (3 ^ a) (3 * 4 ^ a)) :
    27 ^ a * c.norm.natAbs ≤ 1296 * 64 ^ a := by
  have hs : Bounded (c.scale ((3 : Nat) ^ a : Nat)) 1 (3 * 4 ^ a) := by
    simpa [Bounded, Triple.scale, Int.natAbs_mul] using h
  have hN := abs_norm_bound _ _ hs
  rw [norm_scale, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hN
  have hp (k : Nat) : (k ^ a) ^ 3 = (k ^ 3) ^ a := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  rw [Nat.mul_pow, hp 3, hp 4, ← Nat.mul_assoc] at hN
  exact hN

private theorem adjusted_bounds (a : Nat) :
    Bounded (coeff a).twiceMinusOne (3 ^ a) (3 * 4 ^ a) ∧
      Bounded (coeff a).minusTwo (3 ^ a) (3 * 4 ^ a) := by
  let c := coeff a
  obtain ⟨hu, hv, hw⟩ := coeff_bound a
  have hp : 3 ^ a ≤ 4 ^ a := Nat.pow_le_pow_left (by decide) _
  have htwice (x : Int) (hx : 3 ^ a * x.natAbs ≤ 4 ^ a) :
      3 ^ a * (2 * x).natAbs ≤ 2 * 4 ^ a := by
    rw [Int.natAbs_mul, show (2 : Int).natAbs = 2 from rfl, Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ hx
  have hfirst : 3 ^ a * (2 * c.u - 1).natAbs ≤ 3 * 4 ^ a := by
    have h := Nat.mul_le_mul_left (3 ^ a) (Int.natAbs_sub_le (2 * c.u) 1)
    have h' := htwice c.u hu
    rw [Nat.mul_add, show (1 : Int).natAbs = 1 from rfl, Nat.mul_one] at h
    omega
  have hsecond : 3 ^ a * (c.u - 2).natAbs ≤ 3 * 4 ^ a := by
    have h := Nat.mul_le_mul_left (3 ^ a) (Int.natAbs_sub_le c.u 2)
    rw [Nat.mul_add, show (2 : Int).natAbs = 2 from rfl, Nat.mul_comm (3 ^ a) 2] at h
    change 3 ^ a * c.u.natAbs ≤ 4 ^ a at hu
    omega
  exact ⟨⟨hfirst, Nat.le_trans (htwice c.v hv) (by omega),
    Nat.le_trans (htwice c.w hw) (by omega)⟩,
    ⟨hsecond, Nat.le_trans hv (by omega), Nat.le_trans hw (by omega)⟩⟩

/-- Either cubic and the phase power equation force an upper bound on the
modulus using a nonzero integer norm. -/
theorem gap_le_of_cubic {d a : Nat} {z : Int} (hp : (d : Int) ∣ 2 * z ^ a - 1)
    (hf : ((d : Int) ∣ 1 - z ^ 2 + z ^ 3) ∨ ((d : Int) ∣ 1 - z + z ^ 3)) :
    27 ^ a * d ≤ 1296 * 64 ^ a := by
  obtain ⟨hb₁, hb₂⟩ := adjusted_bounds a
  rcases cubic_dvd_norms hp hf with hd | hd
  · have hodd := twice_minus_one_norm_odd (coeff a)
    have hpos : 0 < (coeff a).twiceMinusOne.norm.natAbs := Int.natAbs_pos.mpr (by omega)
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_dvd hpos (Int.ofNat_dvd_left.mp hd)))
      (scaled_norm_bound _ _ hb₁)
  · have hodd := minus_two_norm_odd a
    have hpos : 0 < (coeff a).minusTwo.norm.natAbs := Int.natAbs_pos.mpr (by omega)
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_of_dvd hpos (Int.ofNat_dvd_left.mp hd)))
      (scaled_norm_bound _ _ hb₂)

private theorem density_bound {a L : Nat} (hlt : 3 ^ a < 2 ^ L) : 3 * a < 2 * L := by
  have hlow : ((2 : Nat) ^ 3) ^ a ≤ ((3 : Nat) ^ 2) ^ a :=
    Nat.pow_le_pow_left (by decide) _
  have hhigh : ((3 : Nat) ^ a) ^ 2 < ((2 : Nat) ^ L) ^ 2 :=
    Nat.pow_lt_pow_left hlt (by decide)
  rw [← Nat.pow_mul, ← Nat.pow_mul] at hlow hhigh
  rw [Nat.mul_comm a 2, Nat.mul_comm L 2] at hhigh
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt hlow hhigh)

set_option exponentiation.threshold 1024 in
private theorem base_exponential_dominates : 2592 ^ 3 * 1024 ^ 42 * 512 ^ 1024 < 729 ^ 1024 := by
  decide

private theorem exponential_growth {C q p R s L : Nat} (hs : 0 < s) (hp : 0 < p)
    (hL : s ≤ L) (hbase : C * s ^ R * q ^ s < p ^ s)
    (hratio : q * (s + 1) ^ R ≤ p * s ^ R) :
    C * L ^ R * q ^ L < p ^ L := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  clear hL
  induction k with
  | zero => exact hbase
  | succ k ih =>
    let j := s + k
    change C * (j + 1) ^ R * q ^ (j + 1) < p ^ (j + 1)
    change C * j ^ R * q ^ j < p ^ j at ih
    have hscale : s * (j + 1) ≤ (s + 1) * j := by
      rw [Nat.mul_succ, Nat.succ_mul]
      dsimp [j]
      omega
    have hpow := Nat.pow_le_pow_left hscale R
    rw [Nat.mul_pow, Nat.mul_pow] at hpow
    have hstep : (j + 1) ^ R * q ≤ j ^ R * p := by
      apply Nat.le_of_mul_le_mul_left _ (Nat.pow_pos (n := R) hs)
      calc
        s ^ R * ((j + 1) ^ R * q) = (s ^ R * (j + 1) ^ R) * q := by ac_rfl
        _ ≤ ((s + 1) ^ R * j ^ R) * q := Nat.mul_le_mul_right _ hpow
        _ = (q * (s + 1) ^ R) * j ^ R := by ac_rfl
        _ ≤ (p * s ^ R) * j ^ R := Nat.mul_le_mul_right _ hratio
        _ = _ := by ac_rfl
    rw [Nat.pow_succ q j, Nat.pow_succ p j]
    calc
      C * (j + 1) ^ R * (q ^ j * q) = (C * q ^ j) * ((j + 1) ^ R * q) := by ac_rfl
      _ ≤ (C * q ^ j) * (j ^ R * p) := Nat.mul_le_mul_left _ hstep
      _ = (C * j ^ R * q ^ j) * p := by ac_rfl
      _ < _ := Nat.mul_lt_mul_of_pos_right ih hp

private theorem exponential_dominates {L : Nat} (hL : 1024 ≤ L) :
    2592 ^ 3 * L ^ 42 * 512 ^ L < 729 ^ L :=
  exponential_growth (by decide) (by decide) hL base_exponential_dominates (by decide)

private theorem no_cubic_gap_of_separation (hsep : PowerSeparation) {a L : Nat}
    (hlt : 3 ^ a < 2 ^ L) (hL : 1024 ≤ L)
    (hupper : 27 ^ a * (2 ^ L - 3 ^ a) ≤ 1296 * 64 ^ a) : False := by
  let d := 2 ^ L - 3 ^ a
  have hscaled : 27 ^ a * 2 ^ L ≤ 2592 * L ^ 14 * 64 ^ a := by
    calc
      _ ≤ 27 ^ a * (2 * L ^ 14 * d) := Nat.mul_le_mul_left _ (hsep a L hlt)
      _ = (2 * L ^ 14) * (27 ^ a * d) := by ac_rfl
      _ ≤ (2 * L ^ 14) * (1296 * 64 ^ a) := Nat.mul_le_mul_left _ hupper
      _ = _ := by
        rw [show (2592 : Nat) = 2 * 1296 by decide]
        ac_rfl
  have hcube : 27 ^ (a * 3) * 8 ^ L ≤ 2592 ^ 3 * L ^ 42 * 64 ^ (a * 3) := by
    have hh := Nat.pow_le_pow_left hscaled 3
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul 27 a 3,
      ← Nat.pow_mul 64 a 3, ← Nat.pow_mul L 14 3, ← Nat.pow_mul 2 L 3,
      Nat.mul_comm L 3, Nat.pow_mul 2 3 L] at hh
    exact hh
  have hcount := density_bound hlt
  let k := 2 * L - a * 3
  have hk : a * 3 + k = 2 * L := by dsimp [k]; omega
  have hcombined : 27 ^ (2 * L) * 8 ^ L ≤ 2592 ^ 3 * L ^ 42 * 64 ^ (2 * L) := by
    calc
      _ = (27 ^ (a * 3) * 8 ^ L) * 27 ^ k := by rw [← hk, Nat.pow_add]; ac_rfl
      _ ≤ (2592 ^ 3 * L ^ 42 * 64 ^ (a * 3)) * 27 ^ k := Nat.mul_le_mul_right _ hcube
      _ ≤ (2592 ^ 3 * L ^ 42 * 64 ^ (a * 3)) * 64 ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
      _ = _ := by rw [← hk, Nat.pow_add, Nat.mul_assoc]
  have h₂₇ : 27 ^ (2 * L) = 729 ^ L := by rw [Nat.pow_mul]
  have h₆₄ : 64 ^ (2 * L) = 512 ^ L * 8 ^ L := by rw [Nat.pow_mul, ← Nat.mul_pow]
  rw [h₂₇, h₆₄, ← Nat.mul_assoc] at hcombined
  have hfinal := Nat.le_of_mul_le_mul_right hcombined (Nat.pow_pos (by decide))
  exact Nat.not_lt_of_ge hfinal (exponential_dominates hL)

/-- Given the integer power separation bound, every coprime least cycle of
discrepancy width at most `L+2` reaches one. The finite short-period range
is covered by the existing verified cycle-length bound. -/
theorem reachesOne_of_coprime_width_two (hsep : PowerSeparation) {n L : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hcop : (oddCount n L).Coprime L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + 2) : Reach.ReachesOne n := by
  by_cases hr : Reach.ReachesOne n
  · exact hr
  exfalso
  have hnon : 2 < n := by
    by_cases hlt : 2 < n
    · exact hlt
    · rcases (show n = 1 ∨ n = 2 by omega) with h₁ | h₂
      · exact (hr (h₁ ▸ Reach.reachesOne_one)).elim
      · exact (hr (h₂ ▸ Reach.reachesOne_two)).elim
  have hL := CycleLength1539.length_ge_1539 hn h hr
  have hgap := (accCycle_bounds hn h).2.2
  obtain ⟨z, hp, _, hf⟩ := PhasePolynomial.cycle_width_two_cubic hn h hleast hnon hcop hw
  exact no_cubic_gap_of_separation hsep hgap (by omega) (gap_le_of_cubic hp hf)

/-- The walk is a multiple of the common divisor of the odd count and
period. An excess width smaller than that divisor contributes no new heights. -/
theorem reachesOne_of_width_excess_lt_gcd {n L r : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hg : r < (oddCount n L).gcd L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) : Reach.ReachesOne n := by
  let a := oddCount n L
  let g := a.gcd L
  have hga : (g : Int) ∣ (a : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left a L)
  have hgL : (g : Int) ∣ (L : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right a L)
  have hd (t : Nat) : (g : Int) ∣ walk n L t := by
    unfold walk
    exact Int.dvd_sub (Int.dvd_trans hgL (Int.dvd_mul_right _ _))
      (Int.dvd_trans hga (Int.dvd_mul_right _ _))
  have hwidth (i j : Nat) : walk n L i ≤ walk n L j + L := by
    apply Int.le_of_not_gt
    intro hlt
    have hpos : 0 < walk n L i - walk n L j - (L : Int) := by omega
    have hbound := Int.le_of_dvd hpos (Int.dvd_sub (Int.dvd_sub (hd i) (hd j)) hgL)
    have hle := hw i j
    change r < g at hg
    omega
  rcases (BoundaryWidthCycle.width_at_most_period_forces_trivial hn h hleast hwidth).2 with he | he
  · exact he ▸ Reach.reachesOne_one
  · exact he ▸ Reach.reachesOne_two

/-- Given power separation, a nonconvergent least cycle of width at most
`L+2` would have exactly two copies of each discrepancy residue. -/
theorem gcd_eq_two_of_narrow_nonconvergent_cycle (hsep : PowerSeparation) {n L : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hnr : ¬ Reach.ReachesOne n)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + 2) : (oddCount n L).gcd L = 2 := by
  have hpos := Nat.gcd_pos_of_pos_right (oddCount n L) h.1
  by_cases hcop : (oddCount n L).Coprime L
  · exact (hnr (reachesOne_of_coprime_width_two hsep hn h hleast hcop hw)).elim
  · change (oddCount n L).gcd L ≠ 1 at hcop
    by_cases hlarge : 3 ≤ (oddCount n L).gcd L
    · exact (hnr (reachesOne_of_width_excess_lt_gcd hn h hleast (by omega : 2 < (oddCount n L).gcd L)
        hw)).elim
    · omega

end Collatz.CubicPhaseNorm
