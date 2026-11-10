import Collatz.Strategy.LongRunPeakRigidity

/-!
# A bound on chains of certified peak drops

At any common suffix horizon, a certified drop preserves the sum of
the peak exponent and the suffix odd count. Thus a chain can spend
only the even steps of the original suffix, even if its certificates
use different horizons.
-/

namespace Collatz.PeakDropChains

open Collatz.LongRunPeakRigidity

/-- A certificate preserves the sum of the exponent and the odd count
at every suffix horizon at least as long as the certificate. -/
theorem later_invariant {k K v w u : Nat} (hk : 0 < k) (hK : k ≤ K)
    (hw : w ≤ v) (hu : u % 2 = 1) (hc : scaledPeakCertificate k v u (v - w) = true) :
    w + oddCount (3 ^ w * u - 1) K = v + oddCount (3 ^ v * u - 1) K := by
  have ⟨hmeet, hcount⟩ := scaledPeakCertificate_spec (Nat.sub_le v w) hk hu hc
  rw [show v - (v - w) = w by omega] at hmeet hcount
  have hl := AccumulatorArith.oddCount_add (3 ^ w * u - 1) k (K - k)
  have hr := AccumulatorArith.oddCount_add (3 ^ v * u - 1) k (K - k)
  rw [Nat.add_sub_of_le hK, hmeet, hcount] at hl
  rw [Nat.add_sub_of_le hK] at hr
  omega

/-- The endpoint of a descending chain has the same invariant as the
start, using a single upper bound on the individual suffix horizons. -/
theorem chain_invariant {u K N : Nat} (v : Nat → Nat) (hu : u % 2 = 1)
    (hsteps : ∀ i < N, ∃ k, 0 < k ∧ k ≤ K ∧ v (i + 1) ≤ v i ∧
      scaledPeakCertificate k (v i) u (v i - v (i + 1)) = true) :
    v N + oddCount (3 ^ v N * u - 1) K = v 0 + oddCount (3 ^ v 0 * u - 1) K := by
  induction N with
  | zero => rfl
  | succ N ih =>
    obtain ⟨k, hk, hK, hv, hc⟩ := hsteps N (Nat.lt_succ_self _)
    exact (later_invariant hk hK hv hu hc).trans
      (ih (fun i hi => hsteps i (Nat.lt_succ_of_lt hi)))

/-- Every exponent removed by the chain uses one even step of the
original suffix at the common horizon. -/
theorem chain_loss_le_even_count {u K N : Nat} (v : Nat → Nat) (hu : u % 2 = 1)
    (hsteps : ∀ i < N, ∃ k, 0 < k ∧ k ≤ K ∧ v (i + 1) ≤ v i ∧
      scaledPeakCertificate k (v i) u (v i - v (i + 1)) = true) :
    v 0 - v N ≤ K - oddCount (3 ^ v 0 * u - 1) K := by
  have h := chain_invariant v hu hsteps
  have hc := AffineExact.oddCount_le_self (3 ^ v N * u - 1) K
  omega

private theorem cap_of_chain {u c N : Nat} (v : Nat → Nat) (hu : u % 2 = 1)
    (hsteps : ∀ i < N, ∃ k, 0 < k ∧ c * k ≤ v i ∧ v (i + 1) ≤ v i ∧
      scaledPeakCertificate k (v i) u (v i - v (i + 1)) = true) (hc : 0 < c) :
    v 0 - v N ≤ v 0 / c - oddCount (3 ^ v 0 * u - 1) (v 0 / c) := by
  have hmono (i : Nat) (hi : i ≤ N) : v i ≤ v 0 := by
    induction i with
    | zero => exact Nat.le_refl _
    | succ i ih =>
      obtain ⟨_, _, _, hle, _⟩ := hsteps i (by omega)
      exact Nat.le_trans hle (ih (by omega))
  apply chain_loss_le_even_count v hu
  intro i hi
  obtain ⟨k, hk, hbound, hv, hcheck⟩ := hsteps i hi
  exact ⟨k, hk, (Nat.le_div_iff_mul_le hc).mpr
    (by rw [Nat.mul_comm]; exact Nat.le_trans hbound (hmono i (by omega))), hv, hcheck⟩

/-- A chain using the adaptive rigidity regime cannot remove more
than half of its initial exponent. The original suffix's odd steps
reduce this budget further. -/
theorem adaptive_chain_cap {u N : Nat} (v : Nat → Nat) (hu : u % 2 = 1)
    (hsteps : ∀ i < N, ∃ k, 0 < k ∧ requiredRunLength k (v i) u ≤ v i ∧ v (i + 1) ≤ v i ∧
      scaledPeakCertificate k (v i) u (v i - v (i + 1)) = true) :
    v 0 - v N ≤ v 0 / 2 - oddCount (3 ^ v 0 * u - 1) (v 0 / 2) := by
  apply cap_of_chain v hu _ (by decide : 0 < 2)
  intro i hi
  obtain ⟨k, hk, hbound, hv, hcheck⟩ := hsteps i hi
  rw [requiredRunLength_eq k (v i) u (by omega), adaptiveRigidityCutoff] at hbound
  exact ⟨k, hk, by omega, hv, hcheck⟩

/-- Using the fixed linear cutoff limits the total loss to one sixth
of the initial exponent, before subtracting the original odd steps. -/
theorem fixed_chain_cap {u N : Nat} (v : Nat → Nat) (hu : u % 2 = 1)
    (hsteps : ∀ i < N, ∃ k, 0 < k ∧ rigidityCutoff k ≤ v i ∧ v (i + 1) ≤ v i ∧
      scaledPeakCertificate k (v i) u (v i - v (i + 1)) = true) :
    v 0 - v N ≤ v 0 / 6 - oddCount (3 ^ v 0 * u - 1) (v 0 / 6) := by
  apply cap_of_chain v hu _ (by decide : 0 < 6)
  intro i hi
  obtain ⟨k, hk, hbound, hv, hcheck⟩ := hsteps i hi
  exact ⟨k, hk, Nat.le_trans (Nat.le_add_right _ _) hbound, hv, hcheck⟩

end Collatz.PeakDropChains
