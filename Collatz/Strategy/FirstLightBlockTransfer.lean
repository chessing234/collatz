import Collatz.Search.Sieved
import Collatz.Strategy.FirstLightConsequences

/-!
# Keep the descent time in finite block certificates

The block certificates already bound their descent search by a fixed
fuel. Retaining this bound lets a verified range serve as the finite
input component of a first-coefficient-crossing theorem.
-/

namespace Collatz.Search

private theorem bounded_drop_of_aux {n fuel j : Nat}
    (h : dropsAux n fuel (acceleratedOrbit j n) = true) :
    ∃ k, k ≤ j + fuel ∧ acceleratedOrbit k n < n := by
  induction fuel generalizing j with
  | zero => simp at h
  | succ fuel ih =>
    rw [dropsAux_succ, ← acceleratedOrbit_succ_step] at h
    by_cases hd : acceleratedOrbit (j + 1) n < n
    · exact ⟨j + 1, by omega, hd⟩
    · rw [if_neg hd] at h
      obtain ⟨k, hk, hdrop⟩ := ih h
      exact ⟨k, by omega, hdrop⟩

theorem bounded_drop_of_dropsWithin {n fuel : Nat} (h : dropsWithin fuel n = true) :
    ∃ k, k ≤ fuel ∧ acceleratedOrbit k n < n := by
  have h0 : dropsAux n fuel (acceleratedOrbit 0 n) = true := h
  simpa only [Nat.zero_add] using bounded_drop_of_aux h0

/-- Both branches of the block sieve supply a short descent witness. -/
theorem bounded_drop_of_blocks {M fuel : Nat}
    (h : ∀ m r, m < M → r ∈ survivorsMod1024 →
      dropsWithin fuel (2 ^ 10 * m + r) = true)
    {n : Nat} (hn : 1 < n) (hbound : n < 2 ^ 10 * M) :
    ∃ k, k ≤ max 100 fuel ∧ acceleratedOrbit k n < n := by
  by_cases hsmall : n ≤ 1024
  · obtain ⟨k, hk, hd⟩ := bounded_drop_of_dropsWithin
      (dropsWithin_of_allDrop check_drop_10000 hn (by omega))
    exact ⟨k, Nat.le_trans hk (Nat.le_max_left ..), hd⟩
  by_cases hs : Congruence.survives 10 (n % 2 ^ 10) = true
  · have hm : n / 2 ^ 10 < M := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      (by simpa only [Nat.mul_comm] using hbound)
    have hc := h (n / 2 ^ 10) (n % 2 ^ 10) hm (mem_survivors_of_survives hs)
    rw [Nat.div_add_mod] at hc
    obtain ⟨k, hk, hd⟩ := bounded_drop_of_dropsWithin hc
    exact ⟨k, Nat.le_trans hk (Nat.le_max_right ..), hd⟩
  · obtain ⟨i, hi, hd⟩ := Congruence.exists_descends_of_not_survives hs
    rw [Minimal.mod_pow_two_mod hi] at hd
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hi
    have hdrop := Congruence.accOrbit_lt_of_descends_of_mod hd (by omega : 2 ^ i ≤ n)
    exact ⟨i, Nat.le_trans (by omega : i ≤ 100) (Nat.le_max_left ..), hdrop⟩

end Collatz.Search

namespace Collatz.FirstLightDescent

open FirstLightConsequences

/-- A known drop by a certified horizon forces the first coefficient
crossing to be within that horizon, where it also descends. -/
theorem first_light_drop_of_bounded_drop {H n j k : Nat} (hexact : ExactThrough H)
    (hn : 1 < n) (hj : j ≤ H) (hd : acceleratedOrbit j n < n) (hf : FirstLight n k) :
    acceleratedOrbit k n < n := by
  have hk : k ≤ j := Nat.le_of_not_gt fun h =>
    Nat.not_le_of_gt hd (no_descent_before_first_light hf j h)
  exact hexact n k hn (Nat.le_trans hk hj) hf

end Collatz.FirstLightDescent
