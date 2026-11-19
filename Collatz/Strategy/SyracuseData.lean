import Collatz.Basic

/-! Exact Syracuse steps and words, without finite-search dependencies. -/
namespace Collatz.ValuationTransition

/-- An exact odd-to-odd step; oddness of the target makes the exponent exact. -/
def SyrStep (n r m : Nat) : Prop :=
  n % 2 = 1 ∧ m % 2 = 1 ∧ 3 * n + 1 = 2 ^ r * m

theorem SyrStep.pos {n r m : Nat} (h : SyrStep n r m) : 0 < n := by
  obtain ⟨hn, _, _⟩ := h
  omega

theorem SyrStep.one_le {n r m : Nat} (h : SyrStep n r m) : 1 ≤ r := by
  obtain ⟨hn, hm, he⟩ := h
  cases r with
  | zero => simp at he; omega
  | succ r => omega

theorem SyrStep.target_pos {n r m : Nat} (h : SyrStep n r m) : 0 < m := by
  obtain ⟨_, hm, _⟩ := h
  omega

/-- Exponents are recorded in chronological order. -/
inductive SyrPath : Nat → List Nat → Nat → Prop where
  | nil (n : Nat) : SyrPath n [] n
  | cons {n r m e : Nat} {rs : List Nat} :
      SyrStep n r m → SyrPath m rs e → SyrPath n (r :: rs) e

def valSum : List Nat → Nat
  | [] => 0
  | r :: rs => r + valSum rs

@[simp] theorem valSum_nil : valSum [] = 0 := rfl

@[simp] theorem valSum_cons (r : Nat) (rs : List Nat) :
    valSum (r :: rs) = r + valSum rs := rfl

end Collatz.ValuationTransition
