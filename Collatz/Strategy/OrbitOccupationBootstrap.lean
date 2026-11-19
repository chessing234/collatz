import Collatz.Strategy.OrbitCapacity
import Collatz.Structure.ParityMoments

/-!
# Bootstrapping occupation with orbit images

Low-odd-count sources compress into a smaller interval. Their images
are still in the same orbit, so the smaller interval admits the same
occupation estimate. This lets the exceptional parity count, rather
than the raw size of the compressed interval, set the final rate.
-/

namespace Collatz.OrbitOccupationBootstrap

open Collatz.OrbitCapacity Collatz.Sum

structure Tilt where
  odd : Nat
  even : Nat
  cover : Nat
  even_pos : 0 < even
  even_le : even ≤ odd
  cover_ge_two : 2 ≤ cover
  compression : 3 ^ odd < 2 ^ (odd + even)
  moment_gap : (odd + even) ^ (odd + even) ≤ cover * (odd ^ odd * even ^ even)

def Tilt.steps (t : Tilt) : Nat := t.odd + t.even

/-- More odd steps than the chosen threshold at this block scale. -/
def exceptional (t : Tilt) (h x : Nat) : Bool :=
  decide (t.odd * h < oddCount x (t.steps * h))

/-- Uniform bound for the exceptional residues in two complete periods. -/
theorem heavy_count (t : Tilt) (h : Nat) :
    ((List.range (2 ^ (t.steps * h) * 2)).filter (exceptional t h)).length ≤
      2 * t.cover ^ h := by
  let k := t.steps * h
  let weight := ParityMoments.weight t.odd t.even k
  have hmoment : sumRange (2 ^ k * 2) (fun x => weight (oddCount x k)) =
      2 * t.steps ^ k := by
    rw [Nat.mul_comm (2 ^ k) 2, sumRange_two_mul]
    have hshift : sumRange (2 ^ k) (fun x => weight (oddCount (2 ^ k + x) k)) =
        ParityMoments.moment t.odd t.even k :=
      sumRange_congr (fun _ hi => by rw [Density.oddCount_two_pow_add hi])
    change ParityMoments.moment t.odd t.even k + _ = _
    rw [hshift, ParityMoments.moment_eq]
    exact (Nat.two_mul _).symm
  have he : k - t.odd * h = t.even * h := by
    simp [k, Tilt.steps, Nat.add_mul]
  let W := t.odd ^ t.odd * t.even ^ t.even
  have hwt : weight (t.odd * h) = W ^ h := by
    dsimp [weight, ParityMoments.weight, W]
    rw [he, Nat.pow_mul, Nat.pow_mul, Nat.mul_pow]
  have hcount : W ^ h * countRange (2 ^ k * 2) (exceptional t h) ≤ 2 * t.steps ^ k := by
    rw [← hwt, ← hmoment]
    apply mul_countRange_le
    intro x _ hx
    have hgt : t.odd * h < oddCount x k := of_decide_eq_true hx
    exact ParityMoments.weight_mono t.even_le (Nat.le_of_lt hgt)
      (AffineExact.oddCount_le_self x k)
  have hW : 0 < W := Nat.mul_pos (Nat.pow_pos (Nat.lt_of_lt_of_le t.even_pos t.even_le))
    (Nat.pow_pos t.even_pos)
  rw [length_filter_range]
  apply Nat.le_of_mul_le_mul_left _ (show 0 < W ^ h from Nat.pow_pos hW)
  calc
    _ ≤ 2 * t.steps ^ k := hcount
    _ = 2 * (t.steps ^ t.steps) ^ h := by rw [show k = t.steps * h from rfl, Nat.pow_mul]
    _ ≤ 2 * (t.cover * W) ^ h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left t.moment_gap h)
    _ = W ^ h * (2 * t.cover ^ h) := by rw [Nat.mul_pow]; ac_rfl

/-- Above this threshold, low-count images lose at least one block of scale. -/
theorem power_threshold (t : Tilt) :
    ∃ H, ∀ h, H ≤ h → (2 ^ t.steps) * (3 ^ t.odd) ^ h ≤ (2 ^ t.steps) ^ h := by
  obtain ⟨H, hH⟩ := ExcursionAlphabetMass.exists_weight_power t.compression (2 ^ t.steps)
  refine ⟨H, ?_⟩
  intro h hh
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hH (Nat.pow_le_pow_left (Nat.le_of_lt t.compression) _)

private theorem light_image {t : Tilt} {h x : Nat}
    (hx : x < 2 ^ (t.steps * (h + 1)) * 2)
    (hlight : exceptional t (h + 1) x = false)
    (hscale : 2 ^ t.steps * (3 ^ t.odd) ^ (h + 1) ≤ (2 ^ t.steps) ^ (h + 1)) :
    acceleratedOrbit (t.steps * (h + 1)) x < 2 ^ (t.steps * h) * 2 := by
  have ho : oddCount x (t.steps * (h + 1)) ≤ t.odd * (h + 1) := by
    simpa [exceptional, Nat.not_lt] using hlight
  have hpow : (3 ^ t.odd) ^ (h + 1) ≤ (2 ^ t.steps) ^ h := by
    rw [show (2 ^ t.steps : Nat) ^ (h + 1) = 2 ^ t.steps * (2 ^ t.steps) ^ h
      from Nat.pow_succ'] at hscale
    exact Nat.le_of_mul_le_mul_left hscale (Nat.two_pow_pos _)
  have hval := image_lt (k := t.steps * (h + 1)) (c := 2)
    (by simpa only [Nat.mul_comm 2] using hx)
  have hsmall : 3 ^ oddCount x (t.steps * (h + 1)) ≤ 2 ^ (t.steps * h) := by
    rw [Nat.pow_mul]
    exact Nat.le_trans (by simpa only [Nat.pow_mul] using Nat.pow_le_pow_right (by decide : 0 < 3) ho)
      hpow
  simpa only [Nat.mul_comm 2] using Nat.lt_of_lt_of_le hval (Nat.mul_le_mul_left 2 hsmall)

/-- The recursive occupation proof also works when an image is
replaced by a smaller member of the same collection, provided the
replacement map stays injective. -/
theorem bound_of_compression (t : Tilt) :
    ∃ C, ∀ (keep : Nat → Prop) (compress : Nat → Nat → Nat),
      (∀ k x, keep x → keep (compress k x) ∧ compress k x ≤ acceleratedOrbit k x) →
      (∀ k x y, keep x → keep y → compress k x = compress k y → x = y) →
      ∀ h (xs : List Nat), xs.Nodup →
        (∀ x ∈ xs, x < 2 ^ (t.steps * h) * 2 ∧ keep x) →
        xs.length ≤ C * t.cover ^ h := by
  obtain ⟨H, hscale⟩ := power_threshold t
  let C := 2 ^ (t.steps * H) * 2 + 4
  have hC : 4 ≤ C := Nat.le_add_left _ _
  refine ⟨C, ?_⟩
  intro keep compress hcompress hinjective h
  have hbase (h : Nat) (hh : h ≤ H) (xs : List Nat) (hnd : xs.Nodup)
      (hsmall : ∀ x ∈ xs, x < 2 ^ (t.steps * h) * 2 ∧ keep x) :
      xs.length ≤ C * t.cover ^ h := by
    have hs : xs ⊆ List.range (2 ^ (t.steps * h) * 2) :=
      fun x hx => List.mem_range.mpr (hsmall x hx).1
    have hl : xs.length ≤ 2 ^ (t.steps * h) * 2 := by
      simpa using hnd.length_le_of_subset hs
    have hp : 2 ^ (t.steps * h) ≤ 2 ^ (t.steps * H) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hh)
    exact Nat.le_trans hl (Nat.le_trans (Nat.mul_le_mul_right _ hp)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _
        (Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) t.cover_ge_two)))))
  induction h with
  | zero => exact hbase 0 (Nat.zero_le _)
  | succ h ih =>
    intro xs hnd hsmall
    by_cases hthreshold : H ≤ h + 1
    · let high := xs.filter (exceptional t (h + 1))
      let low := xs.filter (fun x => !(exceptional t (h + 1) x))
      have hhigh : high.length ≤ 2 * t.cover ^ (h + 1) := by
        have hs : high ⊆ (List.range (2 ^ (t.steps * (h + 1)) * 2)).filter
            (exceptional t (h + 1)) := by
          intro x hx
          obtain ⟨hx, hv⟩ := List.mem_filter.mp hx
          exact List.mem_filter.mpr ⟨List.mem_range.mpr (hsmall x hx).1, hv⟩
        exact Nat.le_trans ((List.filter_sublist.nodup hnd).length_le_of_subset hs)
          (heavy_count t (h + 1))
      let k := t.steps * (h + 1)
      let images := low.map (compress k)
      have hi : images.Nodup := by
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp_of_mem _ (List.filter_sublist.nodup hnd)
        intro x y hx hy hne heq
        exact hne (hinjective k x y (hsmall x (List.mem_filter.mp hx).1).2
          (hsmall y (List.mem_filter.mp hy).1).2 heq)
      have hs : ∀ y ∈ images, y < 2 ^ (t.steps * h) * 2 ∧ keep y := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        obtain ⟨hx, hl⟩ := List.mem_filter.mp hx
        obtain ⟨hlt, hkeep⟩ := hsmall x hx
        have hl' : exceptional t (h + 1) x = false := by simpa using hl
        obtain ⟨hkeep', hle⟩ := hcompress k x hkeep
        exact ⟨Nat.lt_of_le_of_lt hle (light_image hlt hl' (hscale _ hthreshold)), hkeep'⟩
      have hlow : low.length ≤ C * t.cover ^ h := by
        simpa only [images, List.length_map] using ih images hi hs
      have hsplit : high.length + low.length = xs.length := by
        simpa only [high, low, List.length_append] using
          (List.filter_append_perm (exceptional t (h + 1)) xs).length_eq
      have hbudget : C ≤ (C - 2) * t.cover :=
        Nat.le_trans (by omega : C ≤ (C - 2) * 2)
          (Nat.mul_le_mul_left _ t.cover_ge_two)
      have hlow' : low.length ≤ (C - 2) * t.cover ^ (h + 1) := by
        rw [Nat.pow_succ', ← Nat.mul_assoc]
        exact Nat.le_trans hlow (Nat.mul_le_mul_right _ hbudget)
      rw [← hsplit]
      calc
        _ ≤ 2 * t.cover ^ (h + 1) + (C - 2) * t.cover ^ (h + 1) :=
          Nat.add_le_add hhigh hlow'
        _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : 2 ≤ C)]
    · exact hbase _ (by omega) xs hnd hsmall

/-- A forward-closed, nonmerging collection inherits the exceptional rate. -/
theorem bound (t : Tilt) :
    ∃ C, ∀ (states : Nat → Nat), NoMerging states →
      (∀ k i, ∃ j, states j = acceleratedOrbit k (states i)) →
      ∀ h (xs : List Nat), xs.Nodup →
        (∀ x ∈ xs, x < 2 ^ (t.steps * h) * 2 ∧ ∃ i, states i = x) →
        xs.length ≤ C * t.cover ^ h := by
  obtain ⟨C, hC⟩ := bound_of_compression t
  refine ⟨C, ?_⟩
  intro states hmerge hclosed
  apply hC (fun x => ∃ i, states i = x) acceleratedOrbit
  · intro k x hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨hclosed k i, Nat.le_refl _⟩
  · intro k x y hx hy heq
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hmerge k i j heq

set_option exponentiation.threshold 4000 in
/-- The chosen threshold is `94/149`, immediately below `log₃ 2`
at this scale. All constants are checked as natural integers. -/
def tilt149 : Tilt where
  odd := 94
  even := 55
  cover := 4081199576119298850484664607591547430685275
  even_pos := by decide
  even_le := by decide
  cover_ge_two := by decide
  compression := by decide
  moment_gap := by decide

set_option exponentiation.threshold 4000 in
theorem tilt149_rate : tilt149.cover ^ 20 ≤ (2 : Nat) ^ 2831 := by decide

/-- For every nonmerging orbit, the number of distinct orbit values
below `2^(2980*j+1)` is at most a uniform constant times `2^(2831*j)`.
The exponent ratio is exactly `19/20`. -/
theorem orbit_count_nineteen_twentieths :
    ∃ C, ∀ {n : Nat}, NoMerging (fun i => acceleratedOrbit i n) →
      ∀ j (xs : List Nat), xs.Nodup →
        (∀ x ∈ xs, x < 2 ^ (2980 * j) * 2 ∧ ∃ i, acceleratedOrbit i n = x) →
        xs.length ≤ C * 2 ^ (2831 * j) := by
  obtain ⟨C, hC⟩ := bound tilt149
  refine ⟨C, ?_⟩
  intro n hmerge j xs hnd hx
  have hsteps : tilt149.steps * (20 * j) = 2980 * j := by
    rw [← Nat.mul_assoc]
    rfl
  have hclosed (k i : Nat) :
      ∃ t, acceleratedOrbit t n = acceleratedOrbit k (acceleratedOrbit i n) :=
    ⟨k + i, (acceleratedOrbit_add k i n).symm⟩
  have hb := hC _ hmerge hclosed (20 * j) xs hnd (by simpa only [hsteps] using hx)
  refine Nat.le_trans hb (Nat.mul_le_mul_left _ ?_)
  rw [Nat.pow_mul, Nat.pow_mul]
  exact Nat.pow_le_pow_left tilt149_rate j

set_option exponentiation.threshold 4000 in
/-- Interpolate a count between the aligned dyadic scales. -/
theorem power_of_aligned {C X count : Nat} (hX : 0 < X)
    (hcount : ∀ j, X ≤ 2 ^ (2980 * j) → count ≤ C * 2 ^ (2831 * j)) :
    count ^ 20 ≤ (C ^ 20 * ((2 : Nat) ^ 2980) ^ 19) * X ^ 19 := by
  let j := X.log2 / 2980 + 1
  have hlow : X.log2 + 1 ≤ 2980 * j := by
    have hsplit := Nat.mod_add_div X.log2 2980
    have hrem := Nat.mod_lt X.log2 (by decide : 0 < 2980)
    dsimp [j]
    omega
  have hhigh : 2980 * j ≤ X.log2 + 2980 := by
    have hdiv := Nat.div_mul_le_self X.log2 2980
    dsimp [j]
    omega
  have hXj : X < 2 ^ (2980 * j) := Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by decide) hlow)
  have hscale : 2 ^ (2980 * j) ≤ 2 ^ 2980 * X := by
    calc
      _ ≤ 2 ^ (X.log2 + 2980) := Nat.pow_le_pow_right (by decide) hhigh
      _ = 2 ^ 2980 * 2 ^ X.log2 := by rw [Nat.add_comm, Nat.pow_add]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.log2_self_le (Nat.ne_of_gt hX))
  calc
    _ ≤ (C * 2 ^ (2831 * j)) ^ 20 := Nat.pow_le_pow_left (hcount j (Nat.le_of_lt hXj)) 20
    _ = C ^ 20 * (2 ^ (2980 * j)) ^ 19 := by
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        show 2831 * j * 20 = 2980 * j * 19 by omega]
    _ ≤ C ^ 20 * (2 ^ 2980 * X) ^ 19 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale _)
    _ = _ := by rw [Nat.mul_pow, Nat.mul_assoc]

/-- A uniform power bound at every positive cutoff, expressed without
real powers. -/
theorem orbit_count_power :
    ∃ C, ∀ {n X : Nat}, 0 < X → NoMerging (fun i => acceleratedOrbit i n) →
      ∀ xs : List Nat, xs.Nodup →
        (∀ x ∈ xs, x < X ∧ ∃ i, acceleratedOrbit i n = x) →
        xs.length ^ 20 ≤ C * X ^ 19 := by
  obtain ⟨C, hC⟩ := orbit_count_nineteen_twentieths
  refine ⟨C ^ 20 * ((2 : Nat) ^ 2980) ^ 19, ?_⟩
  intro n X hX hmerge xs hnd hx
  apply power_of_aligned hX
  intro j hj
  apply hC hmerge j xs hnd
  intro x hxm
  obtain ⟨hlt, him⟩ := hx x hxm
  exact ⟨Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt hj)
    (Nat.le_mul_of_pos_right _ (by decide)), him⟩

end Collatz.OrbitOccupationBootstrap
