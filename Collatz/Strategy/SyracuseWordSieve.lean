import Collatz.Strategy.SyracuseShadows

/-!
# Kernel-checkable stopping certificates for Syracuse residue classes

A checked finite valuation word transfers to an entire infinite binary
residue class. This checker does not assert that these classes cover all inputs.
-/
namespace Collatz.SyracuseWordSieve

open ValuationTransition SyracuseShadows

/-- Adding the correct even lift preserves the exact valuation, not just divisibility. -/
theorem step_lift {n v m : Nat} (h : SyrStep n v m) (q : Nat) :
    SyrStep (n + 2 ^ (v + 1) * q) v (m + 2 * (3 * q)) := by
  have he : 2 ^ (v + 1) * q = 2 * (2 ^ v * q) := by
    rw [Nat.pow_succ]
    ac_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    have := h.1
    omega
  · have := h.2.1
    omega
  · calc
      _ = (3 * n + 1) + 3 * (2 ^ (v + 1) * q) := by omega
      _ = 2 ^ v * m + 3 * (2 ^ (v + 1) * q) := by rw [h.2.2]
      _ = _ := by rw [Nat.mul_add, Nat.pow_succ]; ac_rfl

/-- An exact word class has modulus `2^(S+1)`; the extra bit fixes final oddness. -/
theorem path_lift {n e : Nat} {vs : List Nat} (h : SyrPath n vs e) (q : Nat) :
    SyrPath (n + 2 ^ (valSum vs + 1) * q) vs (e + 2 * 3 ^ vs.length * q) := by
  induction h generalizing q with
  | nil n => simpa [valSum] using SyrPath.nil (n + 2 * q)
  | @cons n v m e vs hs ht ih =>
    have hstep : SyrStep (n + 2 ^ (valSum (v :: vs) + 1) * q) v
        (m + 2 ^ (valSum vs + 1) * (3 * q)) := by
      simpa only [valSum, Nat.pow_add, Nat.pow_succ, Nat.pow_one,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        step_lift hs (2 ^ valSum vs * q)
    have hall := SyrPath.cons hstep (ih (3 * q))
    simpa only [List.length_cons, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hall

def wordEval : Nat → List Nat → Nat
  | n, [] => n
  | n, v :: vs => wordEval ((3 * n + 1) / 2 ^ v) vs

/-- The step equations, including odd target, are checked rather than assumed. -/
def pathCheck : Nat → List Nat → Bool
  | _, [] => true
  | n, v :: vs =>
      let m := (3 * n + 1) / 2 ^ v
      decide (n % 2 = 1 ∧ m % 2 = 1 ∧ 3 * n + 1 = 2 ^ v * m) && pathCheck m vs

theorem pathCheck_sound {n : Nat} {vs : List Nat} (h : pathCheck n vs = true) :
    SyrPath n vs (wordEval n vs) := by
  induction vs generalizing n with
  | nil => exact SyrPath.nil n
  | cons v vs ih =>
    have hh : SyrStep n v ((3 * n + 1) / 2 ^ v) ∧
        pathCheck ((3 * n + 1) / 2 ^ v) vs = true := by
      simpa only [pathCheck, SyrStep, Bool.and_eq_true, decide_eq_true_eq] using h
    exact SyrPath.cons hh.1 (ih hh.2)

/-- A representative, actual word, contracting coefficient, and actual drop. -/
def classCheck (r : Nat) (vs : List Nat) : Bool :=
  pathCheck r vs && decide (r < 2 ^ (valSum vs + 1) ∧
    3 ^ vs.length < 2 ^ valSum vs ∧ wordEval r vs < r)

/-- Each accepted certificate proves descent for every nonnegative class lift. -/
theorem classCheck_sound {r : Nat} {vs : List Nat} (h : classCheck r vs = true) (q : Nat) :
    ∃ e, SyrPath (r + 2 ^ (valSum vs + 1) * q) vs e ∧
      e < r + 2 ^ (valSum vs + 1) * q := by
  have hh : pathCheck r vs = true ∧ r < 2 ^ (valSum vs + 1) ∧
      3 ^ vs.length < 2 ^ valSum vs ∧ wordEval r vs < r := by
    simpa only [classCheck, Bool.and_eq_true, decide_eq_true_eq] using h
  refine ⟨wordEval r vs + 2 * 3 ^ vs.length * q, path_lift (pathCheck_sound hh.1) q, ?_⟩
  have hm := Nat.mul_le_mul_right q (Nat.mul_le_mul_left 2 (Nat.le_of_lt hh.2.2.1))
  have hl := Nat.add_lt_add_of_lt_of_le hh.2.2.2 hm
  simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hl

/-- A residue-class certificate applies directly to every input with that residue. -/
theorem descent_of_residue {r n : Nat} {vs : List Nat} (h : classCheck r vs = true)
    (hr : n % 2 ^ (valSum vs + 1) = r) : ∃ e, SyrPath n vs e ∧ e < n := by
  have hn : r + 2 ^ (valSum vs + 1) * (n / 2 ^ (valSum vs + 1)) = n := by
    simpa only [hr] using Nat.mod_add_div n (2 ^ (valSum vs + 1))
  simpa only [hn] using classCheck_sound h (n / 2 ^ (valSum vs + 1))

/-- `3 → 5 → 1`: all positive inputs `3 mod 64` drop after this exact word. -/
theorem certificate_three : classCheck 3 [1, 4] = true := by decide

/-- `5 → 1`: all positive inputs `5 mod 32` have this exact one-step valuation. -/
theorem certificate_five : classCheck 5 [4] = true := by decide

/-- `7 → 11 → 17 → 13 → 5`: a longer genuine word-class certificate. -/
theorem certificate_seven : classCheck 7 [1, 1, 2, 3] = true := by decide

end Collatz.SyracuseWordSieve
