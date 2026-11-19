import Collatz.Strategy.CoefficientStopping

/-!
# One Syracuse orbit, three arithmetic shadows

The Syracuse map on an odd positive integer is `T(n) = (3n+1) / 2^v`, where
`v = v₂(3n+1)`. Write `n_k` for the `k`-th iterate and `S_k` for the sum of
the first `k` exponents.

The real shadow is `2^k (n_k + 1) ≤ 3^k (n_0 + 1)`. Once `n_0 + 1 < 2^k`,
this forces `n_k < 3^k`.

The 3-adic shadow is the cocycle `2^{S_k} n_k = 3^k n_0 + b_k` from
`CoefficientStopping.orbit_identity`. The accumulator satisfies `b_0 = 0` and
`b_{j+1} = 3 b_j + 2^{S_j}`, so modulo `3^k` the seed term disappears. Below
`3^k`, the resulting residue has one representative.

A finite 2-adic shadow is checked by `certifies`: a residue class modulo a
positive integer can force an exponent prefix and a drop below the class.
`certified_drop` turns a successful check into a statement about every
positive cofactor.

No inverse theorem, entropy dimension, or universal convergence statement is
proved here.
-/

namespace Collatz.SyracuseShadow

open Collatz.Arith Collatz.CoefficientStopping

def v2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 ∧ 0 < n then v2Aux fuel (n / 2) + 1 else 0

def oddAux : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 ∧ 0 < n then oddAux fuel (n / 2) else n

def v2 (n : Nat) : Nat := v2Aux n n

def oddPart (n : Nat) : Nat := oddAux n n

theorem aux_succ_v2 (fuel n : Nat) :
    v2Aux (fuel + 1) n = if n % 2 = 0 ∧ 0 < n then v2Aux fuel (n / 2) + 1 else 0 := by
  simp [v2Aux]

theorem aux_succ_odd (fuel n : Nat) :
    oddAux (fuel + 1) n = if n % 2 = 0 ∧ 0 < n then oddAux fuel (n / 2) else n := by
  simp [oddAux]

theorem aux_spec : ∀ fuel n, 0 < n → n ≤ fuel →
    n = 2 ^ v2Aux fuel n * oddAux fuel n ∧ oddAux fuel n % 2 = 1 := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    rw [aux_succ_v2, aux_succ_odd]
    by_cases he : n % 2 = 0 ∧ 0 < n
    · rw [if_pos he, if_pos he]
      obtain ⟨heq, hodd⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨?_, hodd⟩
      have hn2 : n = 2 * (n / 2) := by omega
      have hmul := congrArg (fun z => 2 * z) heq
      calc
        n = 2 * (n / 2) := hn2
        _ = 2 * (2 ^ v2Aux fuel (n / 2) * oddAux fuel (n / 2)) := hmul
        _ = 2 ^ (v2Aux fuel (n / 2) + 1) * oddAux fuel (n / 2) := by
          rw [← Nat.mul_assoc]
          have hpow : 2 * 2 ^ v2Aux fuel (n / 2) = 2 ^ (v2Aux fuel (n / 2) + 1) := by
            rw [Nat.mul_comm, ← Nat.pow_succ]
          rw [hpow]
    · rw [if_neg he, if_neg he]
      exact ⟨by simp, by omega⟩

theorem v2_factor {n : Nat} (hn : 0 < n) :
    n = 2 ^ v2 n * oddPart n ∧ oddPart n % 2 = 1 ∧ 0 < oddPart n := by
  obtain ⟨heq, hodd⟩ := aux_spec n n hn (Nat.le_refl n)
  have hpos : 0 < oddPart n := by
    have : oddPart n ≠ 0 := by
      intro h0
      have haux : oddAux n n = 0 := by simpa [oddPart] using h0
      rw [haux] at heq
      simp at heq
      omega
    omega
  exact ⟨heq, hodd, hpos⟩

theorem two_pow_mul_odd_inj {a b p q : Nat} (hp : p % 2 = 1) (hq : q % 2 = 1)
    (h : 2 ^ a * p = 2 ^ b * q) : a = b ∧ p = q := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero =>
      simp at h
      exact ⟨rfl, h⟩
    | succ b =>
      exfalso
      have hp' : p = 2 * (2 ^ b * q) := by
        rw [Nat.pow_zero, Nat.one_mul] at h
        calc
          p = 2 ^ (b + 1) * q := h
          _ = 2 ^ b * 2 * q := by rw [Nat.pow_succ]
          _ = 2 * 2 ^ b * q := by rw [Nat.mul_comm (2 ^ b) 2]
          _ = 2 * (2 ^ b * q) := by rw [Nat.mul_assoc]
      have hmod : p % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨2 ^ b * q, hp'⟩
      have hcontra : (1 : Nat) = 0 := by rw [← hp, hmod]
      cases hcontra
  | succ a ih =>
    cases b with
    | zero =>
      exfalso
      have hq' : q = 2 * (2 ^ a * p) := by
        rw [Nat.pow_zero, Nat.one_mul] at h
        calc
          q = 2 ^ (a + 1) * p := h.symm
          _ = 2 ^ a * 2 * p := by rw [Nat.pow_succ]
          _ = 2 * 2 ^ a * p := by rw [Nat.mul_comm (2 ^ a) 2]
          _ = 2 * (2 ^ a * p) := by rw [Nat.mul_assoc]
      have hmod : q % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨2 ^ a * p, hq'⟩
      have hcontra : (1 : Nat) = 0 := by rw [← hq, hmod]
      cases hcontra
    | succ b =>
      have hleft : 2 * (2 ^ a * p) = 2 ^ (a + 1) * p := by
        calc
          2 * (2 ^ a * p) = 2 * 2 ^ a * p := by rw [← Nat.mul_assoc]
          _ = 2 ^ a * 2 * p := by rw [Nat.mul_comm 2]
          _ = 2 ^ (a + 1) * p := by rw [Nat.pow_succ]
      have hright : 2 * (2 ^ b * q) = 2 ^ (b + 1) * q := by
        calc
          2 * (2 ^ b * q) = 2 * 2 ^ b * q := by rw [← Nat.mul_assoc]
          _ = 2 ^ b * 2 * q := by rw [Nat.mul_comm 2]
          _ = 2 ^ (b + 1) * q := by rw [Nat.pow_succ]
      have h2 : 2 * (2 ^ a * p) = 2 * (2 ^ b * q) := by rw [hleft, h, hright]
      obtain ⟨ha, hpq⟩ := ih (Nat.mul_left_cancel (by decide) h2)
      exact ⟨by omega, hpq⟩

theorem v2_two_pow_mul_odd {v q : Nat} (hq : q % 2 = 1) (hpos : 0 < q) :
    v2 (2 ^ v * q) = v ∧ (2 ^ v * q) / 2 ^ v = q := by
  have hn : 0 < 2 ^ v * q := Nat.mul_pos (two_pow_pos v) hpos
  obtain ⟨heq, hodd, _⟩ := v2_factor hn
  obtain ⟨hv, _⟩ := two_pow_mul_odd_inj hodd hq heq.symm
  exact ⟨hv, Nat.mul_div_cancel_left q (two_pow_pos v)⟩

/-! ## The Syracuse step -/

def exponent (n : Nat) : Nat := v2 (3 * n + 1)

def syracuse (n : Nat) : Nat := oddPart (3 * n + 1)

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => syracuse (orbit k n)

theorem syracuse_step {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    syracuse n * 2 ^ exponent n = 3 * n + 1 ∧ syracuse n % 2 = 1 ∧
      0 < exponent n ∧ 0 < syracuse n := by
  have hpos : 0 < 3 * n + 1 := by omega
  have heven : (3 * n + 1) % 2 = 0 := by omega
  obtain ⟨heq, hodd', hpos'⟩ := v2_factor hpos
  have hv : 0 < exponent n := by
    suffices v2 (3 * n + 1) ≠ 0 by
      unfold exponent
      omega
    intro hzero
    obtain ⟨heq0, hodd0, _⟩ := v2_factor hpos
    rw [hzero, Nat.pow_zero, Nat.one_mul] at heq0
    have hmod : (3 * n + 1) % 2 = 1 := by
      rw [heq0]
      exact hodd0
    omega
  refine ⟨?_, hodd', hv, hpos'⟩
  rw [Nat.mul_comm]
  simpa [syracuse, exponent] using heq.symm

theorem orbit_odd {n k : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    0 < orbit k n ∧ orbit k n % 2 = 1 := by
  induction k with
  | zero => exact ⟨hn, hodd⟩
  | succ k ih =>
    obtain ⟨hp, ho⟩ := ih
    obtain ⟨_, hs, _, hp'⟩ := syracuse_step hp ho
    exact ⟨hp', hs⟩

/-! ## Real contraction -/

theorem one_step_shadow {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    2 * (syracuse n + 1) ≤ 3 * (n + 1) := by
  obtain ⟨heq, _, hv, _⟩ := syracuse_step hn hodd
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hv)
  have hpow : 2 ≤ 2 ^ exponent n := by
    rw [he, Nat.pow_succ]
    have hone : 1 ≤ 2 ^ e := Nat.succ_le_of_lt (two_pow_pos e)
    omega
  have hle : syracuse n * 2 ≤ syracuse n * 2 ^ exponent n :=
    Nat.mul_le_mul_left _ hpow
  have hre : 2 * syracuse n ≤ 3 * n + 1 := by
    have hcomm : syracuse n * 2 ≤ 3 * n + 1 := by simpa [heq] using hle
    rwa [Nat.mul_comm] at hcomm
  omega

theorem shadow_bound {n k : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    2 ^ k * (orbit k n + 1) ≤ 3 ^ k * (n + 1) := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    obtain ⟨hp, ho⟩ := orbit_odd hn hodd (k := k)
    have hstep := one_step_shadow hp ho
    have hL : 2 ^ (k + 1) * (orbit (k + 1) n + 1) =
        2 ^ k * (2 * (syracuse (orbit k n) + 1)) := by
      rw [orbit, Nat.pow_succ]
      exact Nat.mul_assoc (2 ^ k) 2 _
    have hmid := Nat.mul_le_mul_left (2 ^ k) hstep
    have hcomm : 2 ^ k * (3 * (orbit k n + 1)) = 3 * (2 ^ k * (orbit k n + 1)) := by
      calc
        2 ^ k * (3 * (orbit k n + 1)) = (2 ^ k * 3) * (orbit k n + 1) :=
          (Nat.mul_assoc _ _ _).symm
        _ = (3 * 2 ^ k) * (orbit k n + 1) := by rw [Nat.mul_comm (2 ^ k) 3]
        _ = 3 * (2 ^ k * (orbit k n + 1)) := Nat.mul_assoc _ _ _
    calc
      2 ^ (k + 1) * (orbit (k + 1) n + 1)
          = 2 ^ k * (2 * (syracuse (orbit k n) + 1)) := hL
      _ ≤ 2 ^ k * (3 * (orbit k n + 1)) := hmid
      _ = 3 * (2 ^ k * (orbit k n + 1)) := hcomm
      _ ≤ 3 * (3 ^ k * (n + 1)) := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (k + 1) * (n + 1) := by
        calc
          3 * (3 ^ k * (n + 1)) = 3 * 3 ^ k * (n + 1) := by rw [← Nat.mul_assoc]
          _ = 3 ^ k * 3 * (n + 1) := by rw [Nat.mul_comm 3]
          _ = 3 ^ (k + 1) * (n + 1) := by rw [← Nat.pow_succ]

/-- After more than `log₂(n₀ + 1)` steps, the iterate lies in `{0, …, 3^k − 1}`. -/
theorem seed_forgetting {n k : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (hlog : n + 1 < 2 ^ k) : orbit k n < 3 ^ k := by
  have h := shadow_bound (k := k) hn hodd
  have hlt : 2 ^ k * (orbit k n + 1) < 2 ^ k * 3 ^ k := by
    calc
      _ ≤ 3 ^ k * (n + 1) := h
      _ < 3 ^ k * 2 ^ k := Nat.mul_lt_mul_of_pos_left hlog (three_pow_pos k)
      _ = _ := Nat.mul_comm _ _
  have hone := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-! ## The cocycle -/

def partialS (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => partialS n m + exponent (orbit m n)

def partialB (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => 3 * partialB n m + 2 ^ partialS n m

theorem cocycle {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) (m : Nat) :
    orbit m n * 2 ^ partialS n m = 3 ^ m * n + partialB n m := by
  refine orbit_identity (fun i => orbit i n) (fun i => exponent (orbit i n))
      (partialS n) (partialB n) rfl ?_ rfl ?_ ?_ m
  · intro _; rfl
  · intro _; rfl
  · intro i
    obtain ⟨hp, ho⟩ := orbit_odd hn hodd (k := i)
    obtain ⟨heq, _, _, _⟩ := syracuse_step hp ho
    simpa [orbit] using heq

theorem history_residue {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) (m : Nat) :
    (2 ^ partialS n m * orbit m n) % 3 ^ m = partialB n m % 3 ^ m := by
  have h := cocycle hn hodd m
  rw [Nat.mul_comm] at h
  rw [h, Nat.add_comm, Nat.add_mul_mod_self_left]

theorem three_dvd_of_dvd_two_mul {m : Nat} (h : 3 ∣ 2 * m) : 3 ∣ m := by
  obtain ⟨t, ht⟩ := h
  have hle : t ≤ m := by omega
  have hsub := Nat.mul_sub_left_distrib 3 m t
  refine ⟨m - t, ?_⟩
  omega

theorem three_dvd_of_dvd_mul_two_pow {s q : Nat} (h : 3 ∣ 2 ^ s * q) : 3 ∣ q := by
  induction s generalizing q with
  | zero => simpa using h
  | succ s ih =>
    have hcomm : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hcomm] at h
    exact ih (three_dvd_of_dvd_two_mul h)

theorem three_pow_dvd_of_dvd_mul_two_pow {k s q : Nat} (h : 3 ^ k ∣ 2 ^ s * q) :
    3 ^ k ∣ q := by
  induction k generalizing q with
  | zero => exact Nat.one_dvd q
  | succ k ih =>
    have h3 : 3 ∣ 2 ^ s * q := by
      refine Nat.dvd_trans ?_ h
      exact ⟨3 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨q', rfl⟩ := three_dvd_of_dvd_mul_two_pow h3
    have hmul : 2 ^ s * (3 * q') = 3 * (2 ^ s * q') := by rw [Nat.mul_left_comm]
    have h' : 3 ^ k ∣ 2 ^ s * q' := by
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ k) 3, hmul] at h
      exact (Nat.mul_dvd_mul_iff_left (by decide)).mp h
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_dvd_mul_left 3 (ih h')

private theorem unique_le {k s x y : Nat} (_hx : x < 3 ^ k) (hy : y < 3 ^ k)
    (hle : x ≤ y) (h : (2 ^ s * x) % 3 ^ k = (2 ^ s * y) % 3 ^ k) : x = y := by
  let m := 3 ^ k
  have hmul : 2 ^ s * x ≤ 2 ^ s * y := Nat.mul_le_mul_left _ hle
  have hxdiv := (Nat.mod_add_div (2 ^ s * x) m).symm
  have hydiv := (Nat.mod_add_div (2 ^ s * y) m).symm
  have hmod : (2 ^ s * x) % m = (2 ^ s * y) % m := by simpa [m] using h
  have hxeq : 2 ^ s * x = (2 ^ s * x) % m + m * ((2 ^ s * x) / m) := hxdiv
  have hyeq : 2 ^ s * y = (2 ^ s * y) % m + m * ((2 ^ s * y) / m) := hydiv
  have hdivle : (2 ^ s * x) / m ≤ (2 ^ s * y) / m := Nat.div_le_div_right hmul
  let rx := (2 ^ s * x) % m
  let dx := (2 ^ s * x) / m
  let dy := (2 ^ s * y) / m
  have hxeq' : 2 ^ s * x = rx + m * dx := by simpa [rx, dx] using hxeq
  have hyeq' : 2 ^ s * y = rx + m * dy := by
    have hrx : (2 ^ s * y) % m = rx := by simpa [rx] using hmod.symm
    simpa [rx, dy, hrx] using hyeq
  have hsum : 2 ^ s * y = 2 ^ s * x + m * (dy - dx) := by
    have hsplit := Nat.mul_sub_left_distrib m dy dx
    rw [hyeq', hxeq']
    omega
  have hfactor : 2 ^ s * (y - x) = 2 ^ s * y - 2 ^ s * x := Nat.mul_sub_left_distrib (2 ^ s) y x
  have hdvd : m ∣ 2 ^ s * (y - x) := ⟨dy - dx, by
    rw [hfactor, hsum]
    omega⟩
  have hq := three_pow_dvd_of_dvd_mul_two_pow (by simpa [m] using hdvd)
  have hzero := Nat.eq_zero_of_dvd_of_lt hq (by
    change y - x < 3 ^ k
    omega)
  omega

theorem unique_below_pow {k s x y : Nat} (hx : x < 3 ^ k) (hy : y < 3 ^ k)
    (h : (2 ^ s * x) % 3 ^ k = (2 ^ s * y) % 3 ^ k) : x = y := by
  rcases Nat.le_total x y with hle | hle
  · exact unique_le hx hy hle h
  · exact (unique_le hy hx hle h.symm).symm

theorem determined_by_history {n k : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (hlog : n + 1 < 2 ^ k) :
    orbit k n < 3 ^ k ∧ ∀ x, x < 3 ^ k →
      (2 ^ partialS n k * x) % 3 ^ k = (2 ^ partialS n k * orbit k n) % 3 ^ k →
      x = orbit k n := by
  have hlt := seed_forgetting hn hodd hlog
  refine ⟨hlt, ?_⟩
  intro x hx hcong
  exact unique_below_pow hx hlt hcong

/-! ## A residue-class certificate -/

def stepOk (c d : Nat) : Bool :=
  d % 2 == 1 && c != 0 && decide (v2 (3 * d + 1) < v2 (3 * c))

def stepData (c d : Nat) : Nat × Nat :=
  let v := v2 (3 * d + 1)
  (3 * c / 2 ^ v, (3 * d + 1) / 2 ^ v)

def runData (c d : Nat) : Nat → Nat × Nat
  | 0 => (c, d)
  | k + 1 =>
      let p := runData c d k
      stepData p.1 p.2

def runOk (c d : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
      let p := runData c d k
      runOk c d k && stepOk p.1 p.2

def certifies (modulus residue k : Nat) : Bool :=
  let p := runData modulus residue k
  runOk modulus residue k && p.1 < modulus && p.2 ≤ residue

theorem stepOk_spec {c d : Nat} (h : stepOk c d = true) :
    d % 2 = 1 ∧ 0 < c ∧ v2 (3 * d + 1) < v2 (3 * c) := by
  unfold stepOk at h
  simp [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at h
  obtain ⟨⟨hd, hc⟩, hv⟩ := h
  exact ⟨hd, by omega, hv⟩

theorem oddPart_eq_div {n : Nat} (hn : 0 < n) : oddPart n = n / 2 ^ v2 n := by
  obtain ⟨heq, hodd, hpos⟩ := v2_factor hn
  have hdiv := v2_two_pow_mul_odd (v := v2 n) (q := oddPart n) hodd hpos
  rw [← heq] at hdiv
  exact hdiv.2.symm

theorem two_dvd_of_dvd_three_mul {m : Nat} (h : 2 ∣ 3 * m) : 2 ∣ m := by
  obtain ⟨t, ht⟩ := h
  have hle : m ≤ t := by omega
  have hsub := Nat.mul_sub_left_distrib 2 t m
  refine ⟨t - m, ?_⟩
  omega

theorem step_image {c d t : Nat} (h : stepOk c d = true) :
    0 < c * t + d ∧ (c * t + d) % 2 = 1 ∧
      syracuse (c * t + d) = (stepData c d).1 * t + (stepData c d).2 := by
  obtain ⟨hd, hc, hv⟩ := stepOk_spec h
  have hposD : 0 < 3 * d + 1 := by omega
  have hvpos : 0 < v2 (3 * d + 1) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    obtain ⟨heq0, hodd0, _⟩ := v2_factor hposD
    rw [hzero, Nat.pow_zero, Nat.one_mul] at heq0
    have hmod : (3 * d + 1) % 2 = 1 := by rw [heq0]; exact hodd0
    have heven : (3 * d + 1) % 2 = 0 := by omega
    omega
  let v := v2 (3 * d + 1)
  obtain ⟨hdEq, hdOdd, hdPos⟩ := v2_factor hposD
  have hcpos : 0 < 3 * c := by omega
  obtain ⟨hcEq, _, _⟩ := v2_factor hcpos
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hv)
  let oddC := 2 ^ (q + 1) * oddPart (3 * c)
  have hCeq : 3 * c = 2 ^ v * oddC := by
    have hexp : v2 (3 * c) = v + (q + 1) := by
      dsimp [v]
      rw [hq]
      omega
    rw [hexp] at hcEq
    rw [Nat.pow_add, Nat.mul_assoc] at hcEq
    simpa [oddC] using hcEq
  have hCeven : 2 ∣ oddC := by
    dsimp [oddC]
    refine ⟨2 ^ q * oddPart (3 * c), ?_⟩
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
  have hdivC : 3 * c / 2 ^ v = oddC :=
    Nat.div_eq_of_eq_mul_left (two_pow_pos v) (by rw [hCeq, Nat.mul_comm])
  let podd := oddPart (3 * d + 1)
  have hDeq : 3 * d + 1 = 2 ^ v * podd := by
    dsimp [v, podd]
    exact hdEq
  have hfac : 3 * (c * t + d) + 1 = 2 ^ v * (oddC * t + podd) := by
    have hsum : 3 * c * t + (3 * d + 1) = 2 ^ v * oddC * t + 2 ^ v * podd := by
      rw [hCeq, hDeq]
    have hassoc : 2 ^ v * oddC * t + 2 ^ v * podd = 2 ^ v * (oddC * t + podd) := by
      rw [Nat.mul_assoc, Nat.mul_add]
    calc
      3 * (c * t + d) + 1 = 3 * (c * t) + 3 * d + 1 := by rw [Nat.mul_add]
      _ = 3 * (c * t) + (3 * d + 1) := by rw [Nat.add_assoc]
      _ = 3 * c * t + (3 * d + 1) := by rw [Nat.mul_assoc]
      _ = 2 ^ v * oddC * t + 2 ^ v * podd := hsum
      _ = 2 ^ v * (oddC * t + podd) := hassoc
  have hsumOdd : (oddC * t + podd) % 2 = 1 := by
    obtain ⟨z, hz⟩ := hCeven
    have hzero : (2 * (z * t)) % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨z * t, rfl⟩
    have hmul : oddC * t = 2 * (z * t) := by rw [hz, Nat.mul_assoc]
    rw [hmul, Nat.add_mod, hzero, Nat.zero_add, Nat.mod_mod]
    dsimp [podd]
    exact hdOdd
  have hsumPos : 0 < oddC * t + podd := by
    dsimp [podd]
    omega
  obtain ⟨hv2, hdiv⟩ := v2_two_pow_mul_odd hsumOdd hsumPos
  have hval : v2 (3 * (c * t + d) + 1) = v := by rw [hfac, hv2]
  have hpart : oddPart (3 * (c * t + d) + 1) = oddC * t + podd := by
    rw [oddPart_eq_div (by omega : 0 < 3 * (c * t + d) + 1), hval, hfac, hdiv]
  have htwoC : 2 ∣ 3 * c := by
    generalize hk : v - 1 = k
    have hv1 : v = k + 1 := by omega
    refine ⟨2 ^ k * oddC, ?_⟩
    calc
      3 * c = 2 ^ v * oddC := hCeq
      _ = 2 ^ (k + 1) * oddC := by rw [hv1]
      _ = 2 ^ k * 2 * oddC := by rw [Nat.pow_succ]
      _ = 2 * (2 ^ k * oddC) := by rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
  have hcEven : c % 2 = 0 := Nat.mod_eq_zero_of_dvd (two_dvd_of_dvd_three_mul htwoC)
  have hoddN : (c * t + d) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, hcEven, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, hd]
  have hposN : 0 < c * t + d := by omega
  refine ⟨hposN, hoddN, ?_⟩
  have hsy : syracuse (c * t + d) = oddC * t + podd := by
    unfold syracuse
    exact hpart
  have hdDiv : podd = (3 * d + 1) / 2 ^ v := by
    dsimp [podd, v]
    exact oddPart_eq_div hposD
  have hdata : stepData c d = (oddC, podd) := by
    unfold stepData
    dsimp [v]
    rw [hdivC, hdDiv]
  rw [hsy, hdata]

theorem run_image {c d k t : Nat} (hok : runOk c d k = true) :
    let p := runData c d k
    orbit k (c * t + d) = p.1 * t + p.2 := by
  induction k with
  | zero => simp [orbit, runData]
  | succ k ih =>
    rw [runOk] at hok
    simp [Bool.and_eq_true] at hok
    have hprev := ih hok.1
    have hstep := step_image (c := (runData c d k).1) (d := (runData c d k).2)
      (t := t) hok.2
    rw [orbit, hprev]
    simpa [runData] using hstep.2.2

theorem affine_lt {M r c d t : Nat} (ht : 0 < t) (hc : c < M) (hd : d ≤ r) :
    c * t + d < M * t + r := by
  generalize hm : M - 1 = m
  have hM : M = m + 1 := by omega
  have hc' : c ≤ m := by omega
  have hle : c * t + d ≤ m * t + r := Nat.add_le_add (Nat.mul_le_mul_right t hc') hd
  have hsplit : M * t = m * t + t := by rw [hM, Nat.add_mul, Nat.one_mul]
  have hstrict : m * t + r < M * t + r := by omega
  exact Nat.lt_of_le_of_lt hle hstrict

theorem certified_drop {M r k t : Nat} (h : certifies M r k = true) (ht : 0 < t) :
    orbit k (M * t + r) < M * t + r := by
  unfold certifies at h
  simp [Bool.and_eq_true] at h
  obtain ⟨⟨hok, hc⟩, hd⟩ := h
  have himg := run_image (c := M) (d := r) (k := k) (t := t) hok
  rw [himg]
  exact affine_lt ht (by simpa using hc) hd

theorem certifies_one_mod_eight : certifies 8 1 1 = true := by
  decide

theorem certifies_nineteen_mod_thirtytwo : certifies 32 19 2 = true := by
  decide

theorem certifies_fortythree_mod_sixtyfour : certifies 64 43 3 = true := by
  decide

theorem drop_one_mod_eight {t : Nat} (ht : 0 < t) : orbit 1 (8 * t + 1) < 8 * t + 1 :=
  certified_drop certifies_one_mod_eight ht

theorem drop_nineteen_mod_thirtytwo {t : Nat} (ht : 0 < t) :
    orbit 2 (32 * t + 19) < 32 * t + 19 :=
  certified_drop certifies_nineteen_mod_thirtytwo ht

theorem drop_fortythree_mod_sixtyfour {t : Nat} (ht : 0 < t) :
    orbit 3 (64 * t + 43) < 64 * t + 43 :=
  certified_drop certifies_fortythree_mod_sixtyfour ht

end Collatz.SyracuseShadow
