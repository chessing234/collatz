import Collatz.Strategy.OrbitWindowBootstrap
import Collatz.Strategy.ExcursionCoefficientCoverage

/-!
# Quantitative gaps at future minima of injective orbits

If every future minimum in a short interval had a small gap
to some later state, taking the next future minimum would
pack many distinct orbit values into that interval. The
translated-window count rules out such packing. In particular,
arbitrarily late future minima are separated from all later
states by a constant times the twentieth root of their size.
-/

namespace Collatz.OrbitMinimumSpacing

open Collatz.OrbitCapacity Collatz.OrbitWindowBootstrap

/-- The state at this index is least among all subsequent states. -/
def FutureMinimum (states : Nat → Nat) (i : Nat) : Prop :=
  ∀ j, i ≤ j → states i ≤ states j

theorem minimum_after (states : Nat → Nat) (H : Nat) :
    ∃ i, H ≤ i ∧ ∀ j, H ≤ j → states i ≤ states j := by
  have hmin (x : Nat) (hx : ∃ i, H ≤ i ∧ states i = x) :
      ∃ i, H ≤ i ∧ ∀ j, H ≤ j → states i ≤ states j := by
    induction x using Nat.strongRecOn with
    | _ x ih =>
      by_cases hsmaller : ∃ j, H ≤ j ∧ states j < x
      · obtain ⟨j, hj, hsmall⟩ := hsmaller
        exact ih (states j) hsmall ⟨j, hj, rfl⟩
      · obtain ⟨i, hi, heq⟩ := hx
        refine ⟨i, hi, ?_⟩
        intro j hj
        rw [heq]
        exact Nat.le_of_not_gt (fun h => hsmaller ⟨j, hj, h⟩)
  exact hmin (states H) ⟨H, Nat.le_refl _, rfl⟩

/-- If every eligible minimum has a small future gap, take a chain
of such minima within the available value window. The indices are
distinct even when the coordinates at those indices coincide. -/
theorem minima_indices_of_small_gaps {states : Nat → Nat} {H upper D : Nat}
    (hsmall : ∀ i, H ≤ i → FutureMinimum states i → states i ≤ upper →
      ∃ j, i < j ∧ states j < states i + D)
    (count : Nat) {i : Nat} (hi : H ≤ i) (hmin : FutureMinimum states i)
    (hroom : states i + count * D ≤ upper) :
    ∃ indices : List Nat, indices.Nodup ∧ indices.length = count ∧
      ∀ j ∈ indices, i ≤ j ∧ states i ≤ states j ∧ states j ≤ upper := by
  induction count generalizing i with
  | zero => exact ⟨[], List.nodup_nil, rfl, by simp⟩
  | succ count ih =>
    have hlo : states i ≤ upper := Nat.le_trans (Nat.le_add_right _ _) hroom
    obtain ⟨j, hij, hj⟩ := hsmall i hi hmin hlo
    obtain ⟨k, hik, hk⟩ := minimum_after states (i + 1)
    have hkmin : FutureMinimum states k := fun l hl => hk l (by omega)
    have hnext : states k + count * D ≤ upper := by
      have hkj := hk j (by omega)
      rw [Nat.succ_mul] at hroom
      omega
    obtain ⟨indices, hnd, hlen, hmembers⟩ := ih (by omega : H ≤ k) hkmin hnext
    refine ⟨i :: indices, List.nodup_cons.mpr ⟨?_, hnd⟩, by simp [hlen], ?_⟩
    · intro hm
      have := (hmembers i hm).1
      omega
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨Nat.le_refl _, Nat.le_refl _, hlo⟩
      · obtain ⟨hkl, hklo, hhi⟩ := hmembers l hl
        have hik' : i ≤ k := by omega
        exact ⟨Nat.le_trans hik' hkl, Nat.le_trans (hmin k hik') hklo, hhi⟩

/-- From any future minimum, a value window of order `D^20`
contains another future minimum separated by `D` from every
later state. The constant is independent of the orbit. -/
theorem isolated_minimum_in_window :
    ∃ C, ∀ {n start D : Nat},
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      FutureMinimum (fun i => acceleratedOrbit i n) start →
      ∃ i, start ≤ i ∧ FutureMinimum (fun j => acceleratedOrbit j n) i ∧
        acceleratedOrbit i n ≤ acceleratedOrbit start n + (C * (D + 1) ^ 19 + 1) * D ∧
        ∀ j, i < j → acceleratedOrbit i n + D ≤ acceleratedOrbit j n := by
  obtain ⟨C, hC⟩ := orbit_window_power
  refine ⟨C, ?_⟩
  intro n start D hinj hmin
  let states := fun i => acceleratedOrbit i n
  let count := C * (D + 1) ^ 19 + 1
  let upper := states start + count * D
  apply Classical.byContradiction
  intro hnone
  have hsmall (i : Nat) (hi : start ≤ i) (hlocal : FutureMinimum states i)
      (hupper : states i ≤ upper) : ∃ j, i < j ∧ states j < states i + D := by
    apply Classical.byContradiction
    intro h
    apply hnone
    refine ⟨i, hi, hlocal, hupper, ?_⟩
    intro j hj
    exact Nat.le_of_not_gt (fun hlt => h ⟨j, hj, hlt⟩)
  obtain ⟨indices, hnd, hlen, hmembers⟩ :=
    minima_indices_of_small_gaps hsmall count (Nat.le_refl start) hmin (Nat.le_refl upper)
  let xs := indices.map states
  have hxs : xs.Nodup := List.pairwise_map.mpr
    (hnd.imp (fun hne heq => hne (hinj _ _ heq)))
  let width := count * D + 1
  have hcount : count ^ 20 ≤ C * width ^ 19 := by
    have hlen' : xs.length = count := by simp [xs, hlen]
    rw [← hlen']
    apply hC (a := states start) (X := width) (Nat.succ_pos _)
      (no_merging_of_injective hinj) xs hxs
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, hlo, hhi⟩ := hmembers j hj
    exact ⟨hlo, by dsimp [upper, width] at *; omega, j, rfl⟩
  have hcount_pos : 0 < count := Nat.succ_pos _
  have hwidth : width ≤ count * (D + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_left hcount_pos _
  have hscaled : count * count ^ 19 ≤ (C * (D + 1) ^ 19) * count ^ 19 := by
    calc
      _ = count ^ 20 := (Nat.pow_succ' (m := count) (n := 19)).symm
      _ ≤ C * width ^ 19 := hcount
      _ ≤ C * (count * (D + 1)) ^ 19 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth _)
      _ = C * (count ^ 19 * (D + 1) ^ 19) := by rw [Nat.mul_pow]
      _ = C * ((D + 1) ^ 19 * count ^ 19) :=
        congrArg (C * ·) (Nat.mul_comm _ _)
      _ = _ := (Nat.mul_assoc ..).symm
  have hfail := Nat.le_of_mul_le_mul_right hscaled (Nat.pow_pos hcount_pos)
  dsimp [count] at hfail
  omega

/-- Every injective shortcut orbit has arbitrarily late minima
with a future gap at least a fixed positive multiple of the
twentieth root of their value. The statement uses integer powers. -/
theorem isolated_minimum_power :
    ∃ L, 0 < L ∧ ∀ {n : Nat},
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      ∀ H, ∃ i D, H ≤ i ∧ 0 < D ∧ acceleratedOrbit i n ≤ L * D ^ 20 ∧
        ∀ j, i < j → acceleratedOrbit i n + D ≤ acceleratedOrbit j n := by
  obtain ⟨C, hC⟩ := isolated_minimum_in_window
  let L := 2 ^ 20 + C * 2 ^ 19 + 1
  refine ⟨L, Nat.succ_pos _, ?_⟩
  intro n hinj H
  let states := fun i => acceleratedOrbit i n
  obtain ⟨start, hs, hmin⟩ := minimum_after states H
  let x := states start
  let m := x.log2 / 20
  let D := 2 ^ m
  have hD : 0 < D := Nat.two_pow_pos _
  have hlog : x.log2 + 1 ≤ 20 * (m + 1) := by
    have hdiv := Nat.mod_add_div x.log2 20
    have hmod := Nat.mod_lt x.log2 (by decide : 0 < 20)
    dsimp [m]
    omega
  have hx : x ≤ 2 ^ 20 * D ^ 20 := by
    change x ≤ 2 ^ 20 * (2 ^ m) ^ 20
    rw [← Nat.pow_mul, ← Nat.pow_add, show 20 + m * 20 = 20 * (m + 1) by omega]
    exact Nat.le_trans (Nat.le_of_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨i, hstart, _, hi, hgap⟩ :=
    hC (D := D) hinj (fun j hj => hmin j (Nat.le_trans hs hj))
  have hplus : D + 1 ≤ 2 * D := by omega
  have hd20 : D ≤ D ^ 20 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right hD (by decide : 1 ≤ 20)
  have hwidth : (C * (D + 1) ^ 19 + 1) * D ≤ (C * 2 ^ 19 + 1) * D ^ 20 := by
    calc
      _ ≤ (C * (2 * D) ^ 19 + 1) * D := Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hplus _)) _)
      _ = (C * 2 ^ 19) * D ^ 20 + D := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_pow, ← Nat.mul_assoc, Nat.mul_assoc (C * 2 ^ 19),
          ← Nat.pow_succ]
      _ ≤ _ := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left hd20 _
  refine ⟨i, D, Nat.le_trans hs hstart, hD, ?_, hgap⟩
  calc
    _ ≤ x + (C * (D + 1) ^ 19 + 1) * D := hi
    _ ≤ 2 ^ 20 * D ^ 20 + (C * 2 ^ 19 + 1) * D ^ 20 := Nat.add_le_add hx hwidth
    _ = _ := by rw [← Nat.add_mul]; simp [L, Nat.add_assoc]

open Collatz.ExcursionBudget Collatz.ExcursionMap

/-- A future gap of size `D` prevents any coefficient crossing
within the first `D` complete excursions. -/
theorem heavy_of_future_gap {n e D : Nat} {rs : List Run}
    (h : Trace n e rs)
    (hgap : ∀ k, 0 < k → k ≤ time rs → n + D ≤ acceleratedOrbit k n)
    (hlen : rs.length ≤ D) :
    2 ^ time rs ≤ 3 ^ ExcursionBudget.oddCount rs ∧ ProperPrefixBound 1 1 rs := by
  induction h with
  | nil => exact ⟨by decide, trivial⟩
  | @step x y v u W rs hprev hrun ih =>
    have hlen' : rs.length + 1 ≤ D := hlen
    have hsub : time rs ≤ time (⟨v, W⟩ :: rs) := by simp [time]
    obtain ⟨hprevFull, hprevProper⟩ :=
      ih (fun k hk hle => hgap k hk (Nat.le_trans hle hsub)) (by omega)
    let word : List Run := ⟨v, W⟩ :: rs
    have hp : ProperPrefixBound 1 1 word :=
      ⟨by simpa only [Nat.one_mul] using hprevFull, hprevProper⟩
    refine ⟨?_, hp⟩
    apply Nat.le_of_not_gt
    intro hc
    let A := 3 ^ ExcursionBudget.oddCount word
    let B := 2 ^ time word
    have ht : Trace n y word := .step hprev hrun
    have htime : 0 < time word := by
      have hv := hrun.2.2.2.1
      change 0 < v + W + time rs
      omega
    have hy : n + D ≤ y := ht.landing ▸ hgap _ htime (Nat.le_refl _)
    have hC : offset word ≤ A * D :=
      Nat.le_trans (offset_le_length_mul_coefficient hp) (Nat.mul_le_mul_left _ hlen)
    have hlt : A * (n + D) < A * (n + D) := by
      calc
        _ < B * (n + D) := Nat.mul_lt_mul_of_pos_right hc (by omega)
        _ ≤ B * y := Nat.mul_le_mul_left _ hy
        _ = A * n + offset word := ht.affine.symm
        _ ≤ _ := by rw [Nat.mul_add]; exact Nat.add_le_add_left hC _
    exact Nat.lt_irrefl _ hlt

/-- In every positive injective shortcut orbit there are arbitrarily
late starts in the remaining excursion residue classes whose
multiplier stays at least one through a constant multiple of
the twentieth root of their size. -/
theorem isolated_heavy_prefix :
    ∃ L, 0 < L ∧ ∀ {n : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      ∀ H, ∃ i D, H ≤ i ∧ 0 < D ∧ acceleratedOrbit i n ≤ L * D ^ 20 ∧
        (acceleratedOrbit i n % 16 = 7 ∨ acceleratedOrbit i n % 16 = 15 ∨
          acceleratedOrbit i n % 32 = 27) ∧
        ∀ k, k ≤ 2 * D → 2 ^ k ≤ 3 ^ Collatz.oddCount (acceleratedOrbit i n) k := by
  obtain ⟨L, hL, hmin⟩ := isolated_minimum_power
  refine ⟨L, hL, ?_⟩
  intro n hn hinj H
  obtain ⟨i, D, hi, hD, hsize, hgap⟩ := hmin hinj H
  let x := acceleratedOrbit i n
  have hx : 0 < x := acceleratedOrbit_positive hn i
  have hshift (k : Nat) (hk : 0 < k) : x + D ≤ acceleratedOrbit k x := by
    change x + D ≤ acceleratedOrbit k (acceleratedOrbit i n)
    rw [acceleratedOrbit_add, Nat.add_comm k i]
    exact hgap (i + k) (by omega)
  have hx1 : 1 < x := by
    apply Nat.lt_of_not_ge
    intro hle
    have he : x = 1 := by omega
    have h := hshift 2 (by decide)
    rw [he, show acceleratedOrbit 2 1 = 1 by decide] at h
    omega
  have hno (k : Nat) : x ≤ acceleratedOrbit k x := by
    cases k with
    | zero => exact Nat.le_refl _
    | succ k => exact Nat.le_trans (Nat.le_add_right _ _) (hshift _ (Nat.succ_pos _))
  have hodd : x % 2 = 1 := by
    apply Classical.byContradiction
    intro hnodd
    have hlt := even_branch_contracts hx1 (by omega : x % 2 = 0)
    exact Nat.not_le_of_gt hlt (hno 1)
  have h1 : x % 4 ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := return_of_one_mod_four hx1 h
    exact Nat.not_le_of_gt hk (hno k)
  have h3 : x % 16 ≠ 3 := by
    intro h
    obtain ⟨k, hk⟩ := return_of_three_mod_sixteen hx1 h
    exact Nat.not_le_of_gt hk (hno k)
  have h11 : x % 32 ≠ 11 := by
    intro h
    obtain ⟨k, hk⟩ := return_of_eleven_mod_thirtytwo hx1 h
    exact Nat.not_le_of_gt hk (hno k)
  have hmod : x % 16 = 7 ∨ x % 16 = 15 ∨ x % 32 = 27 := by omega
  obtain ⟨y, rs, ht, hlen, htime, _⟩ := trace_of_length x hodd D
  obtain ⟨hfull, hproper⟩ :=
    heavy_of_future_gap ht (fun k hk _ => hshift k hk) (Nat.le_of_eq hlen)
  refine ⟨i, D, hi, hD, hsize, hmod, ?_⟩
  intro k hk
  exact ht.shortcut_heavy_of_boundary_heavy hfull hproper k (Nat.le_trans hk htime)

end Collatz.OrbitMinimumSpacing
