import Collatz.Strategy.SyracuseData

/-!
# Exact real-size and ternary shadows of a Syracuse word

All formulas use chronological exponent words and cleared denominators.
There are no randomness, independence, or convergence assumptions.
-/
namespace Collatz.SyracuseShadows

open ValuationTransition

/-- The numerator of the additive cocycle: `sum_i 3^(k-i) * 2^S_(i-1)`. -/
def cocycle : List Nat → Nat
  | [] => 0
  | v :: vs => 3 ^ vs.length + 2 ^ v * cocycle vs

/-- The exact affine identity, with the source term retained. -/
theorem affine {n e : Nat} {vs : List Nat} (h : SyrPath n vs e) :
    2 ^ valSum vs * e = 3 ^ vs.length * n + cocycle vs := by
  induction h with
  | nil n => simp [valSum, cocycle]
  | @cons n v m e vs hs ht ih =>
    simp only [valSum, cocycle, List.length_cons, Nat.pow_add]
    calc
      _ = 2 ^ v * (2 ^ valSum vs * e) := by ac_rfl
      _ = 2 ^ v * (3 ^ vs.length * m + cocycle vs) := by rw [ih]
      _ = 3 ^ vs.length * (2 ^ v * m) + 2 ^ v * cocycle vs := by
        rw [Nat.mul_add]
        ac_rfl
      _ = 3 ^ vs.length * (3 * n + 1) + 2 ^ v * cocycle vs := by rw [← hs.2.2]
      _ = _ := by simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_one]; ac_rfl

/-- The binary shadow of the same cocycle, including the bit fixing terminal oddness. -/
theorem seed_binary_residue {n e : Nat} {vs : List Nat} (h : SyrPath n vs e)
    (ho : e % 2 = 1) :
    (3 ^ vs.length * n + cocycle vs) % 2 ^ (valSum vs + 1) = 2 ^ valSum vs := by
  rw [← affine h]
  have he : e = 2 * (e / 2) + 1 := by omega
  have hh : 2 ^ valSum vs * e =
      2 ^ (valSum vs + 1) * (e / 2) + 2 ^ valSum vs := by
    calc
      _ = 2 ^ valSum vs * (2 * (e / 2) + 1) := congrArg (fun x => 2 ^ valSum vs * x) he
      _ = _ := by rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ]; ac_rfl
  rw [hh, Nat.mul_add_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hp : 0 < (2 : Nat) ^ valSum vs := Nat.pow_pos (by decide)
  rw [Nat.pow_succ]
  omega

/-- Exact periodic words satisfy the cycle equation; this is not a cycle exclusion. -/
theorem cycle_equation {n : Nat} {vs : List Nat} (h : SyrPath n vs n) :
    n * (2 ^ valSum vs - 3 ^ vs.length) = cocycle vs := by
  have ha := affine h
  rw [Nat.mul_sub]
  have hm : n * 2 ^ valSum vs = n * 3 ^ vs.length + cocycle vs := by
    simpa only [Nat.mul_comm] using ha
  omega

/-- One exact Syracuse step satisfies the shifted real-size bound. -/
theorem step_growth {n v e : Nat} (h : SyrStep n v e) :
    2 * (e + 1) ≤ 3 * (n + 1) := by
  have hv := h.one_le
  have hp : 2 ≤ (2 : Nat) ^ v := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hv
  have hm := Nat.mul_le_mul_right e hp
  rw [← h.2.2] at hm
  omega

/-- The size estimate depends on the number of Syracuse steps, not total halvings. -/
theorem growth {n e : Nat} {vs : List Nat} (h : SyrPath n vs e) :
    2 ^ vs.length * (e + 1) ≤ 3 ^ vs.length * (n + 1) := by
  induction h with
  | nil n => simp
  | @cons n v m e vs hs ht ih =>
    have h1 := Nat.mul_le_mul_left 2 ih
    have h2 := Nat.mul_le_mul_left (3 ^ vs.length) (step_growth hs)
    simp only [List.length_cons, Nat.pow_succ]
    calc
      _ = 2 * (2 ^ vs.length * (e + 1)) := by ac_rfl
      _ ≤ 2 * (3 ^ vs.length * (m + 1)) := h1
      _ = 3 ^ vs.length * (2 * (m + 1)) := by ac_rfl
      _ ≤ 3 ^ vs.length * (3 * (n + 1)) := h2
      _ = _ := by ac_rfl

/-- Non-strict `2^k ≥ n+1` already suffices for the claimed forgetting bound. -/
theorem endpoint_lt_three_pow {n e : Nat} {vs : List Nat}
    (h : SyrPath n vs e) (hn : n + 1 ≤ 2 ^ vs.length) : e < 3 ^ vs.length := by
  have hg := growth h
  have hm := Nat.mul_le_mul_left (3 ^ vs.length) hn
  have he : 2 ^ vs.length * (e + 1) ≤ 2 ^ vs.length * 3 ^ vs.length := by
    have hc : 3 ^ vs.length * 2 ^ vs.length = 2 ^ vs.length * 3 ^ vs.length := by ac_rfl
    omega
  have hc := Nat.le_of_mul_le_mul_left he (Nat.pow_pos (by decide))
  omega

/-- Every positive-time Syracuse state is a unit modulo three.
Consequently raw equidistribution over all ternary residues is impossible. -/
theorem target_not_three {n v e : Nat} (h : SyrStep n v e) : e % 3 ≠ 0 := by
  intro he
  have hm : (2 ^ v * e) % 3 = 0 := by rw [Nat.mul_mod, he]; simp
  rw [← h.2.2] at hm
  omega

/-- The source term vanishes modulo the ternary horizon. -/
theorem scaled_residue {n e : Nat} {vs : List Nat} (h : SyrPath n vs e) :
    (2 ^ valSum vs * e) % 3 ^ vs.length = cocycle vs % 3 ^ vs.length := by
  rw [affine h, Nat.mul_add_mod_self_left]

/-- A canonical inverse of two modulo `3^k`. -/
def invTwo (k : Nat) : Nat := (3 ^ k + 1) / 2

theorem three_pow_odd (k : Nat) : (3 : Nat) ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem invTwo_exact (k : Nat) : 2 * invTwo k = 3 ^ k + 1 := by
  have ho := three_pow_odd k
  unfold invTwo
  omega

/-- Inversion is exact at every exponent, including modulus one. -/
theorem inverse_power (k s : Nat) :
    (2 ^ s * invTwo k ^ s) % 3 ^ k = 1 % 3 ^ k := by
  rw [← Nat.mul_pow, invTwo_exact]
  rw [Nat.pow_mod, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  rw [← Nat.pow_mod, Nat.one_pow]

/-- Cancel a power of two modulo any ternary horizon. -/
theorem cancel_two_power {k s x y : Nat}
    (h : (2 ^ s * x) % 3 ^ k = (2 ^ s * y) % 3 ^ k) :
    x % 3 ^ k = y % 3 ^ k := by
  have hi := inverse_power k s
  have hx : (invTwo k ^ s * (2 ^ s * x)) % 3 ^ k = x % 3 ^ k := by
    rw [Nat.mul_left_comm, ← Nat.mul_assoc, Nat.mul_mod, hi, ← Nat.mul_mod, Nat.one_mul]
  have hy : (invTwo k ^ s * (2 ^ s * y)) % 3 ^ k = y % 3 ^ k := by
    rw [Nat.mul_left_comm, ← Nat.mul_assoc, Nat.mul_mod, hi, ← Nat.mul_mod, Nat.one_mul]
  rw [← hx, ← hy, Nat.mul_mod, h, ← Nat.mul_mod]

/-- The user's tail-denominator sum, represented by modular inverses. -/
def tailSum (k : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => 3 ^ vs.length * invTwo k ^ valSum (v :: vs) + tailSum k vs

/-- Cleared-denominator equivalence of the prefix and tail cocycles. -/
theorem tailSum_scaled (k : Nat) (vs : List Nat) :
    (2 ^ valSum vs * tailSum k vs) % 3 ^ k = cocycle vs % 3 ^ k := by
  induction vs with
  | nil => simp [valSum, tailSum, cocycle]
  | cons v vs ih =>
    have he : 2 ^ valSum (v :: vs) * tailSum k (v :: vs) =
        3 ^ vs.length * (2 ^ valSum (v :: vs) * invTwo k ^ valSum (v :: vs)) +
        2 ^ v * (2 ^ valSum vs * tailSum k vs) := by
      simp only [tailSum, valSum, Nat.pow_add, Nat.mul_add]
      ac_rfl
    rw [he, Nat.add_mod, Nat.mul_mod, inverse_power, ← Nat.mul_mod, Nat.mul_one]
    rw [Nat.mul_mod (2 ^ v), ih, ← Nat.mul_mod, ← Nat.add_mod]
    rfl

/-- The exact ternary shadow; no size bound is required for the congruence. -/
theorem endpoint_residue {n e : Nat} {vs : List Nat} (h : SyrPath n vs e) :
    e % 3 ^ vs.length = tailSum vs.length vs % 3 ^ vs.length := by
  apply cancel_two_power (s := valSum vs)
  rw [scaled_residue h, tailSum_scaled]

/-- Once the size threshold is reached, the residue is the actual integer endpoint. -/
theorem seed_forgetting {n e : Nat} {vs : List Nat}
    (h : SyrPath n vs e) (hn : n + 1 ≤ 2 ^ vs.length) :
    e = tailSum vs.length vs % 3 ^ vs.length := by
  have hr := endpoint_residue h
  rw [Nat.mod_eq_of_lt (endpoint_lt_three_pow h hn)] at hr
  exact hr

/-- An explicit logarithmic forgetting horizon, with no asymptotic notation. -/
theorem seed_forgetting_log {n e : Nat} {vs : List Nat}
    (h : SyrPath n vs e) (hk : Nat.log2 (n + 1) + 1 ≤ vs.length) :
    e = tailSum vs.length vs % 3 ^ vs.length := by
  have hp := Nat.lt_log2_self (n := n + 1)
  have hm := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  exact seed_forgetting h (by omega)

/-- Equal words with small enough sources have equal endpoints. -/
theorem same_word_endpoint {n n' e e' : Nat} {vs : List Nat}
    (h : SyrPath n vs e) (h' : SyrPath n' vs e')
    (hn : n + 1 ≤ 2 ^ vs.length) (hn' : n' + 1 ≤ 2 ^ vs.length) : e = e' := by
  rw [seed_forgetting h hn, seed_forgetting h' hn']

/-- Forgetting is not independence: that same word uniquely encodes the small source. -/
theorem same_word_source {n n' e e' : Nat} {vs : List Nat}
    (h : SyrPath n vs e) (h' : SyrPath n' vs e')
    (hn : n + 1 ≤ 2 ^ vs.length) (hn' : n' + 1 ≤ 2 ^ vs.length) : n = n' := by
  have he := same_word_endpoint h h' hn hn'
  have ha := affine h
  have hb := affine h'
  rw [he] at ha
  have hm : 3 ^ vs.length * n = 3 ^ vs.length * n' := by omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hm

end Collatz.SyracuseShadows
