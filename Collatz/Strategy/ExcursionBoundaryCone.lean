import Collatz.Strategy.ExcursionBeattyCrossing

/-!
# A two-generator cone for failed first excursion crossings

The phase charge places the exponent ratio in a narrow rational cone.
Determinant-one coordinates express its integer points in two generators.
A further exact power comparison removes the part of that cone whose
coefficient is expanding. Only eight exponent pairs remain below the
stated odd-step horizon.
-/

namespace Collatz.ExcursionPowerGap

open DyadicPowerBounds

private def floorScale : Nat := 4 * 2 ^ 71

private theorem cone_lower : (2 : Nat) ^ 103768467013 < 3 ^ 65470613321 :=
  lower_comparison 3 65470613321 128 103768467013 (by decide +kernel)

private theorem cone_upper_power :
    (3 * (floorScale + 1)) ^ (72057431991 * 325000000000) <
      floorScale ^ (72057431991 * 325000000000) * 2 ^ (114208327604 * 325000000000 + 1) :=
  shifted_power_comparison (3 * (floorScale + 1)) (72057431991 * 325000000000)
    floorScale (72057431991 * 325000000000) (114208327604 * 325000000000 + 1)
    192 (by decide +kernel)

private theorem bad_lower_mix : (2 : Nat) ^ 975675645481 < 3 ^ 615582794569 :=
  lower_comparison 3 615582794569 192 975675645481 (by decide +kernel)

/-- Integer points compatible with the small-gap bound are generated
by the exceptional pair and the next upper convergent. -/
theorem boundary_cone_of_scaled_gap {a b : Nat} (ha : 0 < a) (hbound : a < 325000000000)
    (hcross : 3 ^ a < 2 ^ b) (hgap : (4 * 2 ^ 71) * (2 ^ b - 3 ^ a) ≤ a * 3 ^ a) :
    ∃ u v : Nat, 0 < u + v ∧
      a = 72057431991 * u + 137528045312 * v ∧
      b = 114208327604 * u + 217976794617 * v := by
  have hleft := lower_cross_product ha hcross cone_lower
  have hright : b * 72057431991 ≤ 114208327604 * a :=
    exponent_cross_le_of_gap (F := floorScale) (N := 325000000000)
      (by decide) (Nat.le_of_lt hbound) hcross hgap cone_upper_power
  let i := 114208327604 * a - 72057431991 * b
  let j := 65470613321 * b - 103768467013 * a
  have hi : i + 72057431991 * b = 114208327604 * a :=
    Nat.sub_add_cancel (by omega)
  have hj : j + 103768467013 * a = 65470613321 * b :=
    Nat.sub_add_cancel (by omega)
  have hjpos : 0 < j := Nat.sub_pos_iff_lt.mpr (by omega)
  have hA : a = 65470613321 * i + 72057431991 * j := by omega
  have hB : b = 103768467013 * i + 114208327604 * j := by omega
  have hj4 : j ≤ 4 := by omega
  have hij : i ≤ j := by
    apply Nat.le_of_not_gt
    intro hlarge
    let d := 4 * i - 5 * j
    have hd : d + 5 * j = 4 * i := Nat.sub_add_cancel (by omega)
    have hA4 : a * 4 = 615582794569 * j + 65470613321 * d := by omega
    have hB4 : b * 4 = 975675645481 * j + 103768467013 * d := by omega
    have hweak : (2 ^ b) ^ 4 ≤ (3 ^ a) ^ 4 := by
      calc
        _ = (2 ^ 975675645481) ^ j * (2 ^ 103768467013) ^ d := by
          rw [← Nat.pow_mul, hB4, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
        _ ≤ (3 ^ 615582794569) ^ j * (3 ^ 65470613321) ^ d :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_of_lt bad_lower_mix) _)
            (Nat.pow_le_pow_left (Nat.le_of_lt cone_lower) _)
        _ = _ := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← hA4, Nat.pow_mul]
    exact Nat.not_lt_of_ge hweak (Nat.pow_lt_pow_left hcross (by decide : 4 ≠ 0))
  exact ⟨j - i, i, by omega, by omega, by omega⟩

def boundaryPairs : List (Nat × Nat) :=
  [(72057431991, 114208327604), (137528045312, 217976794617),
      (144114863982, 228416655208), (209585477303, 332185122221),
      (216172295973, 342624982812), (275056090624, 435953589234),
      (281642909294, 446393449825), (288229727964, 456833310416)]

/-- The cone has eight integer points in the covered range. -/
theorem eight_pairs_of_boundary_cone {a b u v : Nat} (hbound : a < 325000000000)
    (hpos : 0 < u + v) (ha : a = 72057431991 * u + 137528045312 * v)
    (hb : b = 114208327604 * u + 217976794617 * v) : (a, b) ∈ boundaryPairs := by
  simp only [boundaryPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases hv with rfl | rfl | rfl
  · have hu : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
    rcases hu with rfl | rfl | rfl | rfl <;> omega
  · have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hu with rfl | rfl | rfl <;> omega
  · have hu : u = 0 := by omega
    omega

theorem boundary_eight_pairs_of_scaled_gap {a b : Nat} (ha : 0 < a) (hbound : a < 325000000000)
    (hcross : 3 ^ a < 2 ^ b) (hgap : (4 * 2 ^ 71) * (2 ^ b - 3 ^ a) ≤ a * 3 ^ a) :
    (a, b) ∈ boundaryPairs := by
  obtain ⟨u, v, hpos, ha, hb⟩ := boundary_cone_of_scaled_gap ha hbound hcross hgap
  exact eight_pairs_of_boundary_cone hbound hpos ha hb

end Collatz.ExcursionPowerGap

namespace Collatz.ExcursionBudget

set_option maxRecDepth 4096 in
/-- Every failed first excursion crossing above the verified floor
lies in the two-generator cone through 325 billion odd steps. -/
theorem Trace.first_crossing_failure_boundary_cone {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 325000000000)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) :
    ∃ u v : Nat, 0 < u + v ∧
      oddCount rs = 72057431991 * u + 137528045312 * v ∧
      time rs = 114208327604 * u + 217976794617 * v := by
  let a := oddCount rs
  let A := 3 ^ a
  let B := 2 ^ time rs
  let D := B - A
  have ha : 22 ≤ a := by
    apply Nat.le_of_not_gt
    intro hsmall
    have hsource := h.first_crossing_failure_source_lt hproper hcross (by omega) hkeep
    omega
  have hsum : A + D = B := Nat.add_sub_of_le (Nat.le_of_lt hcross)
  have hbudget : D * n ≤ offset rs := by
    apply Nat.le_of_add_le_add_left (a := A * n)
    rw [← Nat.add_mul, hsum, h.affine]
    exact Nat.mul_le_mul_left _ hkeep
  have hcharge := h.offset_le_phase_charge hproper hcross
  have hgap : (4 * 2 ^ 71) * D ≤ a * A := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 10000)
    calc
      _ = 4 * (10000 * (D * 2 ^ 71)) := by ac_rfl
      _ ≤ 4 * (10000 * (D * n)) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlarge))
      _ ≤ 4 * (10000 * offset rs) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hbudget)
      _ ≤ 4 * ((2431 * a + 1500) * A) := Nat.mul_le_mul_left _ hcharge
      _ = (4 * (2431 * a + 1500)) * A := by ac_rfl
      _ ≤ (10000 * a) * A := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ac_rfl
  exact ExcursionPowerGap.boundary_cone_of_scaled_gap (by omega) hbound hcross hgap

/-- The first-crossing consequence in explicit finite-list form. -/
theorem Trace.first_crossing_failure_eight_pairs {n e : Nat} {rs : List Run}
    (h : Trace n e rs) (hproper : ProperPrefixBound 1 1 rs)
    (hcross : 3 ^ oddCount rs < 2 ^ time rs) (hbound : oddCount rs < 325000000000)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e) :
    (oddCount rs, time rs) ∈ ExcursionPowerGap.boundaryPairs := by
  obtain ⟨_, _, hpos, ha, hb⟩ := h.first_crossing_failure_boundary_cone
    hproper hcross hbound hlarge hkeep
  exact ExcursionPowerGap.eight_pairs_of_boundary_cone hbound hpos ha hb

end Collatz.ExcursionBudget
