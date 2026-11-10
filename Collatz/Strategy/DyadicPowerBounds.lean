import Std

/-!
# Exact comparisons of large powers with bounded dyadic intervals

A bound consists of a small integer significand and a symbolic
binary shift. Squaring rounds the lower significand down and the
upper one up. The certified comparator cancels the common shift,
so near-equal powers can be compared without expanding either one.
-/

namespace Collatz.DyadicPowerBounds

structure Scaled where
  significand : Nat
  shift : Nat

def Scaled.value (x : Scaled) : Nat :=
  x.significand * 2 ^ x.shift

def Scaled.mul (x y : Scaled) : Scaled :=
  ⟨x.significand * y.significand, x.shift + y.shift⟩

theorem Scaled.mul_value (x y : Scaled) :
    (x.mul y).value = x.value * y.value := by
  simp only [Scaled.value, Scaled.mul, Nat.pow_add]
  ac_rfl

private def Scaled.cut (x : Scaled) (precision : Nat) : Nat :=
  x.significand.log2 + 1 - precision

def Scaled.roundDown (x : Scaled) (precision : Nat) : Scaled :=
  let cut := x.cut precision
  ⟨x.significand / 2 ^ cut, cut + x.shift⟩

def Scaled.roundUp (x : Scaled) (precision : Nat) : Scaled :=
  let cut := x.cut precision
  let unit := 2 ^ cut
  ⟨(x.significand + (unit - 1)) / unit, cut + x.shift⟩

theorem Scaled.roundDown_le (x : Scaled) (precision : Nat) :
    (x.roundDown precision).value ≤ x.value := by
  simp only [Scaled.roundDown, Scaled.value, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)

private theorem le_ceil_mul (n unit : Nat) (hunit : 0 < unit) :
    n ≤ ((n + (unit - 1)) / unit) * unit := by
  have h := Nat.mod_add_div (n + (unit - 1)) unit
  have hm := Nat.mod_lt (n + (unit - 1)) hunit
  rw [Nat.mul_comm unit] at h
  omega

theorem Scaled.le_roundUp (x : Scaled) (precision : Nat) :
    x.value ≤ (x.roundUp precision).value := by
  simp only [Scaled.roundUp, Scaled.value, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (le_ceil_mul _ _ (Nat.two_pow_pos _))

/-- Cancel the smaller of the two shifts before comparing values. -/
def Scaled.less (x y : Scaled) : Bool :=
  if x.shift ≤ y.shift then decide (x.significand < y.significand * 2 ^ (y.shift - x.shift))
  else decide (x.significand * 2 ^ (x.shift - y.shift) < y.significand)

theorem Scaled.less_sound {x y : Scaled} (h : x.less y = true) :
    x.value < y.value := by
  unfold Scaled.less at h
  unfold Scaled.value
  by_cases hxy : x.shift ≤ y.shift
  · simp only [if_pos hxy, decide_eq_true_eq] at h
    have he : (y.shift - x.shift) + x.shift = y.shift := Nat.sub_add_cancel hxy
    have hm := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos x.shift)
    rwa [Nat.mul_assoc, ← Nat.pow_add, he] at hm
  · simp only [if_neg hxy, decide_eq_true_eq] at h
    have he : (x.shift - y.shift) + y.shift = x.shift :=
      Nat.sub_add_cancel (Nat.le_of_not_ge hxy)
    have hm := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos y.shift)
    rwa [Nat.mul_assoc, ← Nat.pow_add, he] at hm

structure Bounds where
  lower : Scaled
  upper : Scaled

def Bounds.Contains (x : Bounds) (n : Nat) : Prop :=
  x.lower.value ≤ n ∧ n ≤ x.upper.value

def Bounds.exact (n : Nat) : Bounds :=
  ⟨⟨n, 0⟩, ⟨n, 0⟩⟩

theorem Bounds.exact_contains (n : Nat) : (Bounds.exact n).Contains n := by
  simp [Bounds.exact, Bounds.Contains, Scaled.value]

def Bounds.mul (x y : Bounds) (precision : Nat) : Bounds :=
  ⟨(x.lower.mul y.lower).roundDown precision, (x.upper.mul y.upper).roundUp precision⟩

theorem Bounds.mul_contains {x y : Bounds} {m n : Nat} (hx : x.Contains m) (hy : y.Contains n)
    (precision : Nat) : (x.mul y precision).Contains (m * n) := by
  constructor
  · exact Nat.le_trans (Scaled.roundDown_le ..)
      (by rw [Scaled.mul_value]; exact Nat.mul_le_mul hx.1 hy.1)
  · exact Nat.le_trans (by rw [Scaled.mul_value]; exact Nat.mul_le_mul hx.2 hy.2)
      (Scaled.le_roundUp ..)

private def powerLoop (base precision : Nat) : Nat → Nat → Bounds
  | 0, _ => Bounds.exact 1
  | fuel + 1, exponent =>
    let half := powerLoop base precision fuel (exponent / 2)
    let square := half.mul half precision
    if exponent % 2 = 0 then square else square.mul (Bounds.exact base) precision

private theorem powerLoop_contains (base precision fuel exponent : Nat)
    (h : exponent < 2 ^ fuel) : (powerLoop base precision fuel exponent).Contains (base ^ exponent) := by
  induction fuel generalizing exponent with
  | zero =>
    have he : exponent = 0 := by simpa using h
    subst exponent
    exact Bounds.exact_contains 1
  | succ fuel ih =>
    have hhalf : exponent / 2 < 2 ^ fuel := by
      rw [Nat.pow_succ] at h
      omega
    have hrec := ih _ hhalf
    have hsquare := Bounds.mul_contains hrec hrec precision
    have hsplit := Nat.div_add_mod exponent 2
    rw [powerLoop]
    by_cases heven : exponent % 2 = 0
    · rw [if_pos heven]
      have he : exponent = exponent / 2 + exponent / 2 := by omega
      have hpow : base ^ exponent = base ^ (exponent / 2) * base ^ (exponent / 2) :=
        (congrArg (base ^ ·) he).trans (Nat.pow_add ..)
      rw [hpow]
      exact hsquare
    · rw [if_neg heven]
      have he : exponent = (exponent / 2 + exponent / 2) + 1 := by omega
      have hpow : base ^ exponent = (base ^ (exponent / 2) * base ^ (exponent / 2)) * base := by
        calc
          _ = base ^ ((exponent / 2 + exponent / 2) + 1) := congrArg (base ^ ·) he
          _ = _ := by rw [Nat.pow_succ, Nat.pow_add]
      rw [hpow]
      exact Bounds.mul_contains hsquare (Bounds.exact_contains _) precision

/-- A logarithmic number of interval squarings bounds the power. -/
def power (base exponent precision : Nat) : Bounds :=
  powerLoop base precision (exponent.log2 + 1) exponent

theorem power_contains (base exponent precision : Nat) :
    (power base exponent precision).Contains (base ^ exponent) := by
  apply powerLoop_contains
  by_cases h : exponent = 0
  · simp [h]
  · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)

/-- An interval comparison against a dyadic value certifies a strict
lower bound without evaluating either represented power. -/
theorem lower_comparison (base exponent precision shift : Nat)
    (h : (⟨1, shift⟩ : Scaled).less (power base exponent precision).lower = true) :
    2 ^ shift < base ^ exponent := by
  have hlt := Scaled.less_sound h
  change 1 * 2 ^ shift < (power base exponent precision).lower.value at hlt
  rw [Nat.one_mul] at hlt
  exact Nat.lt_of_lt_of_le hlt (power_contains base exponent precision).1

/-- An interval comparison also certifies a scaled upper bound. -/
theorem upper_comparison (base exponent precision left right shift : Nat)
    (h : ((power base exponent precision).upper.mul ⟨left, 0⟩).less ⟨right, shift⟩ = true) :
    left * base ^ exponent ≤ right * 2 ^ shift := by
  have hlt := Scaled.less_sound h
  rw [Scaled.mul_value] at hlt
  change (power base exponent precision).upper.value * (left * 2 ^ 0) < right * 2 ^ shift at hlt
  rw [Nat.pow_zero, Nat.mul_one, Nat.mul_comm _ left] at hlt
  exact Nat.le_trans
    (Nat.mul_le_mul_left _ (power_contains base exponent precision).2) (Nat.le_of_lt hlt)

/-- Compare two power intervals while retaining an extra symbolic
shift on the right-hand side. -/
theorem shifted_power_comparison (a i b j shift precision : Nat)
    (h : (power a i precision).upper.less
      ((power b j precision).lower.mul ⟨1, shift⟩) = true) :
    a ^ i < b ^ j * 2 ^ shift := by
  have hlt := Scaled.less_sound h
  rw [Scaled.mul_value] at hlt
  change (power a i precision).upper.value <
    (power b j precision).lower.value * (1 * 2 ^ shift) at hlt
  rw [Nat.one_mul] at hlt
  exact Nat.lt_of_le_of_lt (power_contains a i precision).2
    (Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ (power_contains b j precision).1))

end Collatz.DyadicPowerBounds
