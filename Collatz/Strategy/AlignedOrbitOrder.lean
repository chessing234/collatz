import Collatz.Strategy.AccumulatorArith

/-! Order comparisons for two prefixes with nearby odd counts. -/

namespace Collatz.AlignedOrbitOrder

open Collatz.Arith

/-- The second prefix's odd count minus the first prefix's odd count. -/
def countDifference (x y k : Nat) : Int := (oddCount y k : Int) - (oddCount x k : Int)

private def ordered (d : Int) (x y : Nat) : Prop :=
  if d = -2 then x < 9 * y
  else if d = -1 then x < 3 * y
  else if d = 1 then 3 * x < y
  else if d = 2 then 9 * x < y
  else x ≤ y

private theorem ordered_step {x y : Nat} {d : Int}
    (hlo : -1 ≤ d) (hhi : d ≤ 1) (h : ordered d x y) :
    ordered (d + (y % 2 : Nat) - (x % 2 : Nat)) (acceleratedStep x) (acceleratedStep y) := by
  rcases (show d = -1 ∨ d = 0 ∨ d = 1 by omega) with rfl | rfl | rfl <;>
    rcases mod_two_eq_zero_or_one x with hx | hx <;>
    rcases mod_two_eq_zero_or_one y with hy | hy <;>
    simp [ordered, acceleratedStep, hx, hy] at h ⊢ <;> omega

private theorem twice_step_even {x : Nat} (hx : x % 2 = 0) : 2 * acceleratedStep x = x := by
  rw [acceleratedStep, if_pos hx]
  omega

private theorem twice_step_odd {x : Nat} (hx : x % 2 = 1) : 2 * acceleratedStep x = 3 * x + 1 := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

private theorem twice_step (x : Nat) :
    2 * acceleratedStep x = 3 ^ (x % 2) * x + x % 2 := by
  rcases mod_two_eq_zero_or_one x with hx | hx
  · simpa [hx] using twice_step_even hx
  · simpa [hx] using twice_step_odd hx

private theorem weighted_step_le {x y c : Nat} (hc : 0 < c) (hxy : x ≤ c * y) :
    3 ^ (y % 2) * acceleratedStep x ≤ c * (3 ^ (x % 2) * acceleratedStep y) := by
  let u := x % 2
  let v := y % 2
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
  change 2 * (3 ^ v * acceleratedStep x) ≤ 2 * (c * (3 ^ u * acceleratedStep y))
  have hX : 2 * (3 ^ v * acceleratedStep x) = 3 ^ (u + v) * x + 3 ^ v * u := by
    rw [Nat.mul_left_comm 2, twice_step, Nat.mul_add, Nat.pow_add]
    change 3 ^ v * (3 ^ u * x) + 3 ^ v * u = _
    rw [Nat.mul_left_comm (3 ^ v), Nat.mul_assoc]
  have hY : 2 * (c * (3 ^ u * acceleratedStep y)) =
      3 ^ (u + v) * (c * y) + c * (3 ^ u * v) := by
    rw [Nat.mul_left_comm 2 c, Nat.mul_left_comm 2 (3 ^ u), twice_step]
    change c * (3 ^ u * (3 ^ v * y + v)) = _
    rw [Nat.mul_add, Nat.mul_add, Nat.pow_add]
    congr 1
    ac_rfl
  rw [hX, hY]
  by_cases hu : u = 0
  · rw [hu, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    exact Nat.le_trans (Nat.mul_le_mul_left _ hxy) (Nat.le_add_right _ _)
  have hu' : u = 1 := by have := Nat.mod_lt x (by decide : 0 < 2); dsimp [u] at *; omega
  rcases mod_two_eq_zero_or_one y with hv | hv
  · change v = 0 at hv
    simp [hu', hv]
    have hy := twice_step_even (show y % 2 = 0 from hv)
    have hcy : c * y = 2 * (c * acceleratedStep y) := calc
      _ = c * (2 * acceleratedStep y) := congrArg (c * ·) hy.symm
      _ = _ := Nat.mul_left_comm c 2 _
    change x % 2 = 1 at hu'
    omega
  · change v = 1 at hv
    rw [hu', hv]
    apply Nat.add_le_add (Nat.mul_le_mul_left _ hxy)
    simp only [Nat.mul_one]
    omega

private theorem triple_step_le {x y : Nat} (hxy : 3 * x < y) :
    3 * (3 ^ (y % 2) * acceleratedStep x) ≤ 3 ^ (x % 2) * acceleratedStep y := by
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
  rw [Nat.mul_left_comm 2 3, Nat.mul_left_comm 2 (3 ^ (y % 2)), twice_step x,
    Nat.mul_left_comm 2 (3 ^ (x % 2)), twice_step y]
  rcases mod_two_eq_zero_or_one x with hx | hx <;>
    rcases mod_two_eq_zero_or_one y with hy | hy <;>
    simp [hx, hy] <;> omega

private theorem scaled_step_le_of_count_upper {x y k : Nat}
    (hu : oddCount y k ≤ oddCount x k + 1)
    (hle : 3 ^ oddCount y k * acceleratedOrbit k x ≤ 3 ^ oddCount x k * acceleratedOrbit k y) :
    3 ^ oddCount y (k + 1) * acceleratedOrbit (k + 1) x ≤
      3 ^ oddCount x (k + 1) * acceleratedOrbit (k + 1) y := by
  let a := oddCount x k
  let b := oddCount y k
  let X := acceleratedOrbit k x
  let Y := acceleratedOrbit k y
  rw [Density.oddCount_succ_last, Density.oddCount_succ_last, acceleratedOrbit_succ_step,
    acceleratedOrbit_succ_step, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc]
  change 3 ^ b * (3 ^ (Y % 2) * acceleratedStep X) ≤ 3 ^ a * (3 ^ (X % 2) * acceleratedStep Y)
  change 3 ^ b * X ≤ 3 ^ a * Y at hle
  by_cases hba : b ≤ a
  · let c := 3 ^ (a - b)
    have hp : 3 ^ a = 3 ^ b * c := by
      dsimp only [c]
      rw [← Nat.pow_add, Nat.add_sub_of_le hba]
    rw [hp, Nat.mul_assoc] at hle ⊢
    have h := Nat.le_of_mul_le_mul_left hle (Nat.pow_pos (by decide))
    exact Nat.mul_le_mul_left _ (weighted_step_le (Nat.pow_pos (by decide)) h)
  · have hb : b = a + 1 := by dsimp [b, a] at *; omega
    rw [hb, Nat.pow_succ, Nat.mul_assoc] at hle ⊢
    have h := Nat.le_of_mul_le_mul_left hle (Nat.pow_pos (by decide))
    have hpos : 0 < oddCount y k := by change 0 < b; omega
    have hne : 3 * X ≠ Y := fun he =>
      AccumulatorArith.three_not_dvd_orbit_of_odd_step hpos ⟨X, he.symm⟩
    exact Nat.mul_le_mul_left _ (triple_step_le (Nat.lt_of_le_of_ne h hne))

/-- Normalized order propagates from any prefix if the right orbit has
at most one excess odd step. The left orbit's excess is unrestricted. -/
theorem scaled_orbit_le_from {x y s t : Nat} (hst : s ≤ t)
    (hs : 3 ^ oddCount y s * acceleratedOrbit s x ≤ 3 ^ oddCount x s * acceleratedOrbit s y)
    (hu : ∀ k, s ≤ k → k < t → oddCount y k ≤ oddCount x k + 1) :
    3 ^ oddCount y t * acceleratedOrbit t x ≤ 3 ^ oddCount x t * acceleratedOrbit t y := by
  induction t with
  | zero => simpa [show s = 0 by omega] using hs
  | succ t ih =>
    by_cases he : s = t + 1
    · simpa [he] using hs
    exact scaled_step_le_of_count_upper (hu t (by omega) (by omega))
      (ih (by omega) (fun k hk hkt => hu k hk (by omega)))

private theorem ordered_after_isolated_double {x y : Nat} {d e f : Int}
    (hd : -1 ≤ d ∧ d ≤ 1) (he : e = -2 ∨ e = 2) (hf : -1 ≤ f ∧ f ≤ 1)
    (h₁ : e = d + (y % 2 : Nat) - (x % 2 : Nat))
    (h₂ : f = e + (acceleratedStep y % 2 : Nat) - (acceleratedStep x % 2 : Nat))
    (h : ordered d x y) :
    ordered f (acceleratedStep (acceleratedStep x)) (acceleratedStep (acceleratedStep y)) := by
  have hx := Nat.mod_lt x (by decide : 0 < 2)
  have hy := Nat.mod_lt y (by decide : 0 < 2)
  have hX := Nat.mod_lt (acceleratedStep x) (by decide : 0 < 2)
  have hY := Nat.mod_lt (acceleratedStep y) (by decide : 0 < 2)
  rcases he with he | he
  · have hd' : d = -1 := by omega
    have hf' : f = -1 := by omega
    have hX₀ := twice_step_odd (show x % 2 = 1 by omega)
    have hY₀ := twice_step_even (show y % 2 = 0 by omega)
    have hX₁ := twice_step_even (show acceleratedStep x % 2 = 0 by omega)
    have hY₁ := twice_step_odd (show acceleratedStep y % 2 = 1 by omega)
    simp [ordered, hd'] at h
    simp [ordered, hf']
    omega
  · have hd' : d = 1 := by omega
    have hf' : f = 1 := by omega
    have hX₀ := twice_step_even (show x % 2 = 0 by omega)
    have hY₀ := twice_step_odd (show y % 2 = 1 by omega)
    have hX₁ := twice_step_odd (show acceleratedStep x % 2 = 1 by omega)
    have hY₁ := twice_step_even (show acceleratedStep y % 2 = 0 by omega)
    simp [ordered, hd'] at h
    simp [ordered, hf']
    omega

/-- The difference changes by the difference of the two current parities. -/
theorem countDifference_succ (x y k : Nat) :
    countDifference x y (k + 1) = countDifference x y k +
      (acceleratedOrbit k y % 2 : Nat) - (acceleratedOrbit k x % 2 : Nat) := by
  unfold countDifference
  rw [Density.oddCount_succ_last, Density.oddCount_succ_last]
  omega

private theorem ordered_of_isolated_double {x y k : Nat} (hxy : x ≤ y)
    (hnear : ∀ j, j ≤ k → -2 ≤ countDifference x y j ∧ countDifference x y j ≤ 2)
    (hsep : ∀ j, j < k → (countDifference x y j = -2 ∨ countDifference x y j = 2) →
      -1 ≤ countDifference x y (j + 1) ∧ countDifference x y (j + 1) ≤ 1) :
    ordered (countDifference x y k) (acceleratedOrbit k x) (acceleratedOrbit k y) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    cases k with
    | zero => simpa [ordered, countDifference] using hxy
    | succ k =>
      by_cases hmid : -1 ≤ countDifference x y k ∧ countDifference x y k ≤ 1
      · have hprev := ih k (by omega) (fun j hj => hnear j (by omega))
          (fun j hj => hsep j (by omega))
        rw [countDifference_succ, acceleratedOrbit_succ_step, acceleratedOrbit_succ_step]
        exact ordered_step hmid.1 hmid.2 hprev
      have hnear' := hnear k (by omega)
      have he : countDifference x y k = -2 ∨ countDifference x y k = 2 := by omega
      cases k with
      | zero => simp [countDifference] at he
      | succ k =>
        have hbase := hnear k (by omega)
        have hbase' : -1 ≤ countDifference x y k ∧ countDifference x y k ≤ 1 := by
          by_cases hd : countDifference x y k = -2 ∨ countDifference x y k = 2
          · have hh := hsep k (by omega) hd
            exact False.elim (hmid hh)
          · omega
        have hprev := ih k (by omega) (fun j hj => hnear j (by omega))
          (fun j hj => hsep j (by omega))
        have hlast := hsep (k + 1) (by omega) he
        have h₁ := countDifference_succ x y k
        have h₂ := countDifference_succ x y (k + 1)
        rw [acceleratedOrbit_succ_step k x, acceleratedOrbit_succ_step k y] at h₂
        rw [acceleratedOrbit_succ_step (k + 1) x, acceleratedOrbit_succ_step (k + 1) y,
          acceleratedOrbit_succ_step k x, acceleratedOrbit_succ_step k y]
        exact ordered_after_isolated_double hbase' he hlast h₁ h₂ hprev

/-- The scaled order also holds when a difference of two odd steps is
allowed, provided each such occurrence is isolated. -/
theorem scaled_orbit_le_of_isolated_double {x y k : Nat} (hxy : x ≤ y)
    (hnear : ∀ j, j ≤ k → -2 ≤ countDifference x y j ∧ countDifference x y j ≤ 2)
    (hsep : ∀ j, j < k → (countDifference x y j = -2 ∨ countDifference x y j = 2) →
      -1 ≤ countDifference x y (j + 1) ∧ countDifference x y (j + 1) ≤ 1) :
    3 ^ oddCount y k * acceleratedOrbit k x ≤ 3 ^ oddCount x k * acceleratedOrbit k y := by
  have horder := ordered_of_isolated_double hxy hnear hsep
  have hb := hnear k (Nat.le_refl _)
  let d := countDifference x y k
  change -2 ≤ d ∧ d ≤ 2 at hb
  change ordered d _ _ at horder
  rcases (show d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 by omega) with h | h | h | h | h
  · have hc : oddCount x k = oddCount y k + 2 := by dsimp [d, countDifference] at h; omega
    simp [ordered, h] at horder
    rw [hc, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt horder)
  · have hc : oddCount x k = oddCount y k + 1 := by dsimp [d, countDifference] at h; omega
    simp [ordered, h] at horder
    rw [hc, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt horder)
  · have hc : oddCount x k = oddCount y k := by dsimp [d, countDifference] at h; omega
    simp [ordered, h] at horder
    rw [hc]
    exact Nat.mul_le_mul_left _ horder
  · have hc : oddCount y k = oddCount x k + 1 := by dsimp [d, countDifference] at h; omega
    simp [ordered, h] at horder
    rw [hc, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt horder)
  · have hc : oddCount y k = oddCount x k + 2 := by dsimp [d, countDifference] at h; omega
    simp [ordered, h] at horder
    rw [hc, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_of_lt horder)

/-- When two prefix odd counts stay within one of each other, dividing each
endpoint by its own power of three preserves the initial order. -/
theorem scaled_orbit_le {x y k : Nat} (hxy : x ≤ y)
    (hnear : ∀ j, j ≤ k → oddCount x j ≤ oddCount y j + 1 ∧ oddCount y j ≤ oddCount x j + 1) :
    3 ^ oddCount y k * acceleratedOrbit k x ≤ 3 ^ oddCount x k * acceleratedOrbit k y := by
  have hclose (j : Nat) (hj : j ≤ k) : -1 ≤ countDifference x y j ∧ countDifference x y j ≤ 1 := by
    have := hnear j hj
    unfold countDifference
    omega
  apply scaled_orbit_le_of_isolated_double hxy
  · intro j hj
    have := hclose j hj
    omega
  · intro j hj _
    exact hclose (j + 1) (by omega)

/-- Normalized order between an orbit and an increasing shift telescopes
over successive copies of the shift. The first strict inequality suffices. -/
theorem iterated_offset_order {x p q : Nat} (hxy : x < acceleratedOrbit p x) (hq : 0 < q)
    (hle : ∀ j, j < q → 3 ^ oddCount (acceleratedOrbit p x) (p * j) * acceleratedOrbit (p * j) x ≤
      3 ^ oddCount x (p * j) * acceleratedOrbit (p * j) (acceleratedOrbit p x)) :
    3 ^ oddCount x (p * q) * x < 3 ^ (oddCount x p * q) * acceleratedOrbit (p * q) x := by
  let b := oddCount x p
  let F := fun j => acceleratedOrbit (p * j) x
  let A := fun j => oddCount x (p * j)
  change 3 ^ A q * x < 3 ^ (b * q) * F q
  have hstep (j : Nat) (hj : j < q) : 3 ^ A (j + 1) * F j ≤ 3 ^ (b + A j) * F (j + 1) := by
    have ht := hle j hj
    have ho : acceleratedOrbit (p * j) (acceleratedOrbit p x) = F (j + 1) := by
      dsimp only [F]
      rw [acceleratedOrbit_add, Nat.mul_succ]
    have hc : b + oddCount (acceleratedOrbit p x) (p * j) = A (j + 1) := by
      unfold A
      rw [Nat.mul_succ, Nat.add_comm (p * j) p, AccumulatorArith.oddCount_add]
    change 3 ^ oddCount (acceleratedOrbit p x) (p * j) * F j ≤
      3 ^ A j * acceleratedOrbit (p * j) (acceleratedOrbit p x) at ht
    rw [ho] at ht
    have hh := Nat.mul_le_mul_left (3 ^ b) ht
    rwa [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hc] at hh
  have hloop (j : Nat) (hj : 0 < j) (hj' : j ≤ q) : 3 ^ A j * x < 3 ^ (b * j) * F j := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hz : j = 0
      · subst j
        have h : A 1 = b := by simp [A, b]
        rw [h, Nat.mul_one]
        exact Nat.mul_lt_mul_of_pos_left (by simpa [F] using hxy) (Nat.pow_pos (by decide))
      have hprev := ih (by omega) (by omega)
      have hlo := Nat.mul_lt_mul_of_pos_left hprev (Nat.pow_pos (n := A (j + 1)) (by decide : 0 < 3))
      have hhi := Nat.mul_le_mul_left (3 ^ (b * j)) (hstep j (by omega))
      have hjoin : 3 ^ A (j + 1) * (3 ^ (b * j) * F j) =
          3 ^ (b * j) * (3 ^ A (j + 1) * F j) := by ac_rfl
      rw [hjoin] at hlo
      have hboth := Nat.lt_of_lt_of_le hlo hhi
      have hright : 3 ^ (b * j) * (3 ^ (b + A j) * F (j + 1)) =
          3 ^ A j * (3 ^ (b * (j + 1)) * F (j + 1)) := by
        rw [Nat.mul_succ b j, Nat.pow_add (m := b) (n := A j), Nat.pow_add (m := b * j) (n := b)]
        ac_rfl
      rw [hright, Nat.mul_left_comm] at hboth
      exact Nat.lt_of_mul_lt_mul_left hboth
  exact hloop q hq (Nat.le_refl _)

end Collatz.AlignedOrbitOrder
