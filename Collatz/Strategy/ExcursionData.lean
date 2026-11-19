import Collatz.Accelerated

/-!
# Lightweight excursion data

The excursion equations and their actual-orbit interpretation do not require
any finite search certificates or assumptions about nonconvergent orbits.
-/

namespace Collatz.ExcursionMap

/-- A maximal positive odd run followed by all of its extra halvings. -/
def IsExcursion (n v u W e : Nat) : Prop :=
  n % 2 = 1 ∧ u % 2 = 1 ∧ e % 2 = 1 ∧
  0 < v ∧ 0 < W ∧
  n + 1 = 2 ^ v * u ∧
  3 ^ v * u = 2 ^ W * e + 1

private theorem odd_run_value (v u : Nat) (hu : 0 < u) :
    acceleratedOrbit v (2 ^ v * u - 1) = 3 ^ v * u - 1 := by
  induction v generalizing u with
  | zero => simp [acceleratedOrbit]
  | succ v ih =>
    have hp : 0 < 2 ^ v * u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
    have he : 2 ^ (v + 1) * u = 2 * (2 ^ v * u) := by
      rw [Nat.pow_succ]
      ac_rfl
    have hs : acceleratedStep (2 ^ (v + 1) * u - 1) = 2 ^ v * (3 * u) - 1 := by
      rw [he, acceleratedStep, if_neg (by omega)]
      have hm : 2 ^ v * (3 * u) = 3 * (2 ^ v * u) := by ac_rfl
      rw [hm]
      omega
    rw [acceleratedOrbit, hs, ih (3 * u) (by omega)]
    simp only [Nat.pow_succ, Nat.mul_assoc]

private theorem halve_power (W e : Nat) :
    acceleratedOrbit W (2 ^ W * e) = e := by
  induction W with
  | zero => simp [acceleratedOrbit]
  | succ W ih =>
    have he : 2 ^ (W + 1) * e = 2 * (2 ^ W * e) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [he, acceleratedOrbit, acceleratedStep, if_pos (by omega),
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact ih

/-- Every genuine excursion lands on its stated accelerated-orbit endpoint. -/
theorem landing_eq {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit (v + W) n = e := by
  have hn : n = 2 ^ v * u - 1 := by have := h.2.2.2.2.2.1; omega
  have hu : 0 < u := by have := h.2.1; omega
  have hp : acceleratedOrbit v n = 2 ^ W * e := by
    rw [hn, odd_run_value v u hu, h.2.2.2.2.2.2, Nat.add_sub_cancel]
  rw [Nat.add_comm v W, ← acceleratedOrbit_add, hp]
  exact halve_power W e

end Collatz.ExcursionMap
