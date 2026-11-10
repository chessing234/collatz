import Collatz.Strategy.PeakContraction
import Collatz.Strategy.CouplingDead

/-!
# Separation of shifted peaks at unequal depths

The images of a common dyadic lift are contained in affine intervals
whose widths equal their slopes. For unequal depths the two slopes
have different dyadic valuations. After removing their shared power
of three, the smaller slope is bounded by the dyadic depth gap.
-/

namespace Collatz.UnequalPeakDepth

private theorem peak_band {k l e q r : Nat} (hk : k ≤ l) (hr : r < 2 ^ l) :
    ∃ a x, x < 2 ^ (l - k) * 3 ^ (a + e) ∧
      acceleratedOrbit k (3 ^ e * (2 ^ l * q + (r + 1)) - 1) =
        (2 ^ (l - k) * 3 ^ (a + e)) * q + x := by
  let low := 3 ^ e * (r + 1) - 1
  have hpos : 1 ≤ 3 ^ e * (r + 1) := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.succ_pos _)
  have hpow : 2 ^ k * 2 ^ (l - k) = 2 ^ l := by rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hsplit : 3 ^ e * (2 ^ l * q + (r + 1)) - 1 =
      2 ^ k * (2 ^ (l - k) * (3 ^ e * q)) + low := by
    rw [Nat.mul_add, Nat.add_sub_assoc hpos, ← Nat.mul_assoc (2 ^ k), hpow]
    dsimp only [low]
    ac_rfl
  have hlow : low < (2 ^ (l - k) * 3 ^ e) * 2 ^ k := by
    rw [Nat.mul_right_comm, Nat.mul_comm (2 ^ (l - k)) (2 ^ k), hpow, Nat.mul_comm]
    have hle := Nat.mul_le_mul_left (3 ^ e) (Nat.succ_le_of_lt hr)
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos (by decide)) hle
  refine ⟨oddCount low k, acceleratedOrbit k low, ?_, ?_⟩
  · have h := OrbitCapacity.image_lt hlow
    rwa [Nat.mul_assoc, Nat.mul_comm (3 ^ e), ← Nat.pow_add] at h
  · rw [hsplit, Congruence.accOrbit_pow_two_mul_add, Nat.pow_add]
    ac_rfl

private theorem ordered_bands {g a b q x y : Nat} (hab : a < b) (hq : a ≤ q)
    (hx : x < g * a) : (g * a) * q + x < (g * b) * q + y := by
  calc
    _ < (g * a) * q + g * a := Nat.add_lt_add_left hx _
    _ ≤ (g * a) * q + g * q := Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _
    _ = (g * (a + 1)) * q := by rw [Nat.mul_succ, Nat.add_mul]
    _ ≤ (g * b) * q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hab))
    _ ≤ _ := Nat.le_add_right _ _

private theorem slopes_separate {s a b q x y : Nat} (hs : 0 < s) (hq : 2 ^ s ≤ q)
    (hx : x < 2 ^ s * 3 ^ a) (hy : y < 3 ^ b) :
    (2 ^ s * 3 ^ a) * q + x ≠ 3 ^ b * q + y := by
  by_cases hab : a ≤ b
  · have hpow : 3 ^ b = 3 ^ a * 3 ^ (b - a) := by rw [← Nat.pow_add, Nat.add_sub_of_le hab]
    rw [Nat.mul_comm (2 ^ s)] at hx ⊢
    rw [hpow] at hy ⊢
    have hne : 2 ^ s ≠ 3 ^ (b - a) := by
      intro he
      have hd : 2 ^ s ∣ 3 ^ (b - a) := he ▸ Nat.dvd_refl (2 ^ s)
      exact (Nat.ne_of_gt hs) ((CouplingDead.two_pow_dvd_three_pow_iff _ _).mp hd)
    rcases Nat.lt_or_gt_of_ne hne with hl | hr
    · exact Nat.ne_of_lt (ordered_bands hl hq hx)
    · exact (Nat.ne_of_lt (ordered_bands hr (Nat.le_trans (Nat.le_of_lt hr) hq) hy)).symm
  · have hba : b ≤ a := by omega
    have hpow : 2 ^ s * 3 ^ a = 3 ^ b * (2 ^ s * 3 ^ (a - b)) := by
      rw [Nat.mul_left_comm, ← Nat.pow_add, Nat.add_sub_of_le hba]
    have htwo : 1 < 2 ^ s := Nat.one_lt_pow (by omega) (by decide)
    have hg : 1 < 2 ^ s * 3 ^ (a - b) :=
      Nat.lt_of_lt_of_le htwo (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))
    rw [hpow]
    have hl := ordered_bands (g := 3 ^ b) (q := q) (y := x) hg (by omega)
      (by simpa only [Nat.mul_one] using hy)
    simpa only [Nat.mul_one] using (Nat.ne_of_lt hl).symm

/-- At unequal depths, the two peak images cannot coincide once the
common shifted cofactor exceeds the stated dyadic threshold. The
bound is independent of the two peak exponents. -/
theorem unequal_depths_disjoint {k l e f B : Nat} (hk : k < l)
    (hB : 2 ^ (l + (l - k)) < B) :
    acceleratedOrbit k (3 ^ e * B - 1) ≠ acceleratedOrbit l (3 ^ f * B - 1) := by
  let q := (B - 1) / 2 ^ l
  let r := (B - 1) % 2 ^ l
  have hBpos : 0 < B := Nat.lt_trans (Nat.two_pow_pos _) hB
  have hr : r < 2 ^ l := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit : 2 ^ l * q + (r + 1) = B := by
    have hs : 2 ^ l * q + r = B - 1 := Nat.div_add_mod _ _
    omega
  have hq : 2 ^ (l - k) ≤ q := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos l)).mpr
    rw [← Nat.pow_add, Nat.add_comm]
    omega
  obtain ⟨a, x, hx, hleft⟩ := peak_band (e := e) (q := q) (Nat.le_of_lt hk) hr
  obtain ⟨b, y, hy, hright⟩ := peak_band (e := f) (q := q) (Nat.le_refl l) hr
  rw [hsplit] at hleft hright
  simp only [Nat.sub_self, Nat.pow_zero, Nat.one_mul] at hy hright
  rw [hleft, hright]
  exact slopes_separate (by omega) hq hx hy

/-- Across two suffix windows of length at most K, a meeting can
occur only at the same depth when the common cofactor is large. -/
theorem depth_eq_of_large_meeting {k l K e f B : Nat} (hk : k ≤ K) (hl : l ≤ K)
    (hB : 2 ^ (2 * K) < B)
    (hmeet : acceleratedOrbit k (3 ^ e * B - 1) = acceleratedOrbit l (3 ^ f * B - 1)) :
    k = l := by
  have hsize (i j : Nat) (hj : j ≤ K) : 2 ^ (j + (j - i)) < B :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hB
  rcases Nat.lt_trichotomy k l with h | h | h
  · exact (unequal_depths_disjoint h (hsize k l hl) hmeet).elim
  · exact h
  · exact (unequal_depths_disjoint h (hsize l k hk) hmeet.symm).elim

end Collatz.UnequalPeakDepth
