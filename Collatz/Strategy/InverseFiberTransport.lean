import Collatz.Strategy.SynchronousDynamics

/-!
# Ternary translations of inverse fibers

At fixed depth, translating the target by a full ternary period
keeps every admissible parity profile. The corresponding source
translation depends on its odd count. The least source then has a
stable parity profile on all positive translates.
-/

namespace Collatz.InverseFiberTransport

open Collatz.SynchronousClasses Collatz.SynchronousDynamics

/-- A source translation preserving its parity word at depth k. -/
def translate (k q x : Nat) : Nat :=
  x + 2 ^ k * (3 ^ (k - oddCount x k) * q)

theorem translate_residue (k q x : Nat) : translate k q x % 2 ^ k = x % 2 ^ k := by
  rw [translate, Nat.mul_comm (2 ^ k), Nat.add_mul_mod_self_right]

theorem translate_parity (k q x : Nat) : parityVector (translate k q x) k = parityVector x k := by
  rw [parityVector_mod_pow_two (translate k q x), translate_residue,
    ← parityVector_mod_pow_two]

theorem translate_oddCount (k q x : Nat) : oddCount (translate k q x) k = oddCount x k := by
  rw [Density.oddCount_mod (translate k q x), translate_residue, ← Density.oddCount_mod]

theorem translate_injective (k q : Nat) {x y : Nat}
    (h : translate k q x = translate k q y) : x = y := by
  have hcount : oddCount x k = oddCount y k := by
    rw [← translate_oddCount k q x, h, translate_oddCount]
  unfold translate at h
  rw [hcount] at h
  exact Nat.add_right_cancel h

private theorem target_translate {k a : Nat} (ha : a ≤ k) (z q : Nat) :
    (z + 3 ^ k * q) % 3 ^ a = z % 3 ^ a ∧
      (z + 3 ^ k * q) / 3 ^ a = z / 3 ^ a + 3 ^ (k - a) * q := by
  have hs : 3 ^ k * q = (3 ^ (k - a) * q) * 3 ^ a := by
    rw [← Nat.mul_right_comm, ← Nat.pow_add, Nat.sub_add_cancel ha]
  rw [hs, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
  exact ⟨rfl, rfl⟩

/-- Translating a source gives exactly one full ternary-period
translation at the target for each unit of q. -/
theorem orbit_translate (k q x : Nat) :
    acceleratedOrbit k (translate k q x) = acceleratedOrbit k x + 3 ^ k * q := by
  let D := 2 ^ k
  let r := x % D
  let u := x / D
  have hr : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit : D * u + r = x := Nat.div_add_mod x D
  have hc : oddCount x k = oddCount r k := Density.oddCount_mod x k
  have hleft : translate k q x = D * (u + 3 ^ (k - oddCount r k) * q) + r := by
    rw [translate, hc, ← hsplit, Nat.mul_add]
    ac_rfl
  have hold := (orbit_target_iff hr).mp
    (congrArg (acceleratedOrbit k) hsplit)
  have hnew := target_translate (AffineExact.oddCount_le_self r k) (acceleratedOrbit k x) q
  rw [hleft]
  exact (orbit_target_iff hr).mpr ⟨hnew.1.trans hold.1, hnew.2.trans
    (congrArg (· + 3 ^ (k - oddCount r k) * q) hold.2)⟩

/-- Every source of the translated target comes from exactly one source
of the original target by the same profile-dependent translation. -/
theorem mem_fiber_translate {k z q x : Nat} :
    x ∈ fiber k (z + 3 ^ k * q) ↔ ∃ w ∈ fiber k z, x = translate k q w := by
  constructor
  · intro hx
    let D := 2 ^ k
    let r := x % D
    let a := oddCount r k
    let w := D * (z / 3 ^ a) + r
    have hr : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : D * (x / D) + r = x := Nat.div_add_mod x D
    have hx' := (orbit_target_iff hr).mp
      ((congrArg (acceleratedOrbit k) hsplit).trans (mem_fiber.mp hx))
    have htr := target_translate (AffineExact.oddCount_le_self r k) z q
    have hw : acceleratedOrbit k w = z :=
      (orbit_target_iff hr).mpr ⟨htr.1.symm.trans hx'.1, rfl⟩
    refine ⟨w, mem_fiber.mpr hw, ?_⟩
    have hres : w % D = r := by
      dsimp [w]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hwcount : oddCount w k = a := by rw [Density.oddCount_mod w, hres]
    rw [← hsplit, translate, hwcount]
    have hquot := hx'.2.symm.trans htr.2
    change x / D = z / 3 ^ a + 3 ^ (k - a) * q at hquot
    rw [hquot, Nat.mul_add]
    dsimp only [w]
    ac_rfl
  · rintro ⟨w, hw, rfl⟩
    exact mem_fiber.mpr ((orbit_translate k q w).trans
      (congrArg (· + 3 ^ k * q) (mem_fiber.mp hw)))

private theorem translate_ge_period (k q x : Nat) (hq : 0 < q) :
    2 ^ k ≤ translate k q x := by
  have hpos := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3) (n := k - oddCount x k)) hq
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ hpos) (Nat.le_add_left _ _)

/-- The relative order of two preimages after a positive translation is
independent of the size of that translation. -/
theorem translate_order {k p q u v : Nat} (hp : 0 < p) (hq : 0 < q)
    (h : acceleratedOrbit k u = acceleratedOrbit k v) :
    translate k p u < translate k p v ↔ translate k q u < translate k q v := by
  have hmeet (s : Nat) : acceleratedOrbit k (translate k s v) = acceleratedOrbit k (translate k s u) := by
    rw [orbit_translate, orbit_translate, h]
  rw [smaller_mate_iff (translate_ge_period k p v hp) (hmeet p),
    smaller_mate_iff (translate_ge_period k q v hq) (hmeet q)]
  simp only [translate_residue, translate_oddCount]

/-- A single source profile determines the minimum of every positively
translated fiber. -/
theorem stable_minimum (k z : Nat) (hne : ∃ x, acceleratedOrbit k x = z) :
    ∃ w, acceleratedOrbit k w = z ∧ ∀ q, 0 < q → ∀ n,
      acceleratedOrbit k n = z + 3 ^ k * q → leastAt k n = translate k q w := by
  obtain ⟨x, hx⟩ := hne
  let b := translate k 1 x
  have hb : acceleratedOrbit k b = z + 3 ^ k * 1 := by rw [orbit_translate, hx]
  have hmin : leastAt k b ∈ fiber k (z + 3 ^ k * 1) :=
    mem_fiber.mpr ((leastAt_meets k b).trans hb)
  obtain ⟨w, hw, hwmin⟩ := mem_fiber_translate.mp hmin
  have hwz := mem_fiber.mp hw
  refine ⟨w, hwz, ?_⟩
  intro q hq n hn
  have hmeet : acceleratedOrbit k n = acceleratedOrbit k (translate k q w) := by
    rw [orbit_translate, hwz, hn]
  apply Nat.le_antisymm (leastAt_le hmeet)
  apply Nat.le_of_not_gt
  intro hbad
  have hc : leastAt k n ∈ fiber k (z + 3 ^ k * q) :=
    mem_fiber.mpr ((leastAt_meets k n).trans hn)
  obtain ⟨v, hv, hvmin⟩ := mem_fiber_translate.mp hc
  have hvz := mem_fiber.mp hv
  have hbefore : translate k 1 v < translate k 1 w :=
    (translate_order (by decide) hq (hvz.trans hwz.symm)).mpr (hvmin ▸ hbad)
  have hm : leastAt k b ≤ translate k 1 v := by
    apply leastAt_le
    rw [hb, orbit_translate, hvz]
  rw [hwmin] at hm
  exact Nat.not_le_of_gt hbefore hm

/-- The parity profile of the least source is periodic in the target
once the target is at least one full ternary period. -/
theorem least_profile_periodic {k x y : Nat}
    (hx : 3 ^ k ≤ acceleratedOrbit k x) (hy : 3 ^ k ≤ acceleratedOrbit k y)
    (hmod : acceleratedOrbit k x % 3 ^ k = acceleratedOrbit k y % 3 ^ k) :
    parityVector (leastAt k x) k = parityVector (leastAt k y) k := by
  let M := 3 ^ k
  let z := acceleratedOrbit k x % M
  let p := acceleratedOrbit k x / M
  let q := acceleratedOrbit k y / M
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hp : 0 < p := Nat.div_pos hx hM
  have hq : 0 < q := Nat.div_pos hy hM
  have hx' : acceleratedOrbit k x = z + M * p := (Nat.mod_add_div _ _).symm
  have hy' : acceleratedOrbit k y = z + M * q := by
    change z = acceleratedOrbit k y % M at hmod
    rw [hmod]
    exact (Nat.mod_add_div _ _).symm
  have hmem : x ∈ fiber k (z + 3 ^ k * p) := mem_fiber.mpr hx'
  obtain ⟨u, hu, _⟩ := mem_fiber_translate.mp hmem
  obtain ⟨w, _, hw⟩ := stable_minimum k z ⟨u, mem_fiber.mp hu⟩
  rw [hw p hp x hx', hw q hq y hy', translate_parity, translate_parity]

end Collatz.InverseFiberTransport
