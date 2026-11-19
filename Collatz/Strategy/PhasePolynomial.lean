import Collatz.Strategy.OneExtraCycle
import Collatz.Strategy.PhaseResidueBox
import Collatz.Strategy.LocalBlindness
import Collatz.Strategy.CycleArcSplit
import Collatz.Structure.CycleSum

/-! A polynomial with coefficients indexed by discrepancy residues detects
divisibility of the affine accumulator by the full power gap. -/

namespace Collatz.PhasePolynomial

open Collatz.Arith Collatz.AccCycle Collatz.AffineExact Collatz.CyclicOrder
open Collatz.OneExtraCycle Collatz.Sum

private def Cong (d : Nat) (x y : Int) : Prop := (d : Int) ∣ x - y

private theorem Cong.refl (d : Nat) (x : Int) : Cong d x x := by
  simp [Cong]

private theorem Cong.symm {d x y} (h : Cong d x y) : Cong d y x := by
  unfold Cong at *
  simpa only [Int.neg_sub] using Int.dvd_neg.mpr h

private theorem Cong.trans {d x y z} (h : Cong d x y) (g : Cong d y z) : Cong d x z := by
  unfold Cong at *
  rw [show x - z = (x - y) + (y - z) by omega]
  exact Int.dvd_add h g

private theorem Cong.add {d x y u v} (h : Cong d x y) (g : Cong d u v) :
    Cong d (x + u) (y + v) := by
  change (d : Int) ∣ (x + u) - (y + v)
  rw [show (x + u) - (y + v) = (x - y) + (u - v) by omega]
  exact Int.dvd_add h g

private theorem Cong.mul {d x y u v} (h : Cong d x y) (g : Cong d u v) :
    Cong d (x * u) (y * v) := by
  change (d : Int) ∣ x * u - y * v
  rw [show x * u - y * v = (x - y) * u + y * (u - v) by grind]
  exact Int.dvd_add (Int.dvd_trans h (Int.dvd_mul_right _ _))
    (Int.dvd_trans g (Int.dvd_mul_left _ _))

private theorem Cong.pow {d x y} (h : Cong d x y) (s : Nat) : Cong d (x ^ s) (y ^ s) :=
  dvd_pow_sub h s

private theorem Cong.cancel {d a : Nat} {x y : Int} (hc : d.Coprime a)
    (h : Cong d ((a : Int) * x) ((a : Int) * y)) : Cong d x y := by
  unfold Cong at *
  rw [← Int.mul_sub] at h
  exact cancel_coprime_factor hc h

private theorem Cong.dvd_iff {d x y} (h : Cong d x y) : ((d : Int) ∣ x) ↔ ((d : Int) ∣ y) := by
  unfold Cong at h
  constructor
  · intro hx
    simpa only [Int.sub_sub_self] using Int.dvd_sub hx h
  · intro hy
    simpa only [Int.sub_add_cancel] using Int.dvd_add h hy

private theorem Cong.reduce {d D x y} (hd : d ∣ D) (h : Cong D x y) : Cong d x y :=
  Int.dvd_trans (Int.ofNat_dvd.mpr hd) h

private theorem gap_cong {a L : Nat} (hgap : 3 ^ a ≤ 2 ^ L) :
    Cong (2 ^ L - 3 ^ a) ((2 : Int) ^ L) ((3 : Int) ^ a) := by
  unfold Cong
  rw [Int.ofNat_sub hgap, Int.natCast_pow, Int.natCast_pow]
  exact Int.dvd_refl _

private theorem exists_three_inverse {d : Nat} (hd : d % 3 ≠ 0) :
    ∃ u : Int, Cong d (3 * u) 1 := by
  have h := Nat.div_add_mod d 3
  rcases (show d % 3 = 1 ∨ d % 3 = 2 by omega) with hr | hr
  · exact ⟨-((d / 3 : Nat) : Int), -1, by omega⟩
  · exact ⟨((d / 3 : Nat) : Int) + 1, 1, by omega⟩

private theorem exists_phase_unit {a L k b : Nat} (ha : 0 < a) (hL : 0 < L)
    (hgap : 3 ^ a < 2 ^ L) (he : a * k + 1 = L * b) :
    let d := 2 ^ L - 3 ^ a
    ∃ z : Int, Cong d ((3 : Int) ^ b * z) ((2 : Int) ^ k) ∧
      Cong d (2 * z ^ a) 1 ∧ Cong d (3 * z ^ L) 1 := by
  let d := 2 ^ L - 3 ^ a
  let X := (2 : Int) ^ k
  let Y := (3 : Int) ^ b
  let A := (3 : Int) ^ a
  let B := (2 : Int) ^ L
  have hBA : Cong d B A := gap_cong (Nat.le_of_lt hgap)
  obtain ⟨u, hu⟩ := exists_three_inverse (GapPrimes.gap_not_three ha hgap)
  let z := X * u ^ b
  have hz : Cong d (Y * z) X := by
    have h := (hu.pow b).mul (Cong.refl d X)
    rw [Int.mul_pow, Int.one_pow, Int.one_mul] at h
    simpa only [z, Y, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h
  have hc (s : Nat) : d.Coprime ((3 ^ b) ^ s) :=
    ((gap_coprime_two_three ha hL hgap).2.pow_right b).pow_right s
  refine ⟨z, hz, ?_, ?_⟩
  · have h₂ : Cong d (2 * X ^ a) (Y ^ a) := by
      have hl : 2 * X ^ a = B ^ b := by
        dsimp [X, B]
        rw [← Int.pow_mul, ← Int.pow_mul, ← he, Nat.mul_comm k a, Int.pow_succ, Int.mul_comm]
      have hr : Y ^ a = A ^ b := by
        dsimp [Y, A]
        rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm b a]
      rw [hl, hr]
      exact hBA.pow b
    have h := ((Cong.refl d 2).mul (hz.pow a)).trans h₂
    rw [Int.mul_pow, Int.mul_left_comm 2] at h
    have hc' := hc a
    apply Cong.cancel hc'
    simpa [Int.natCast_pow, Y] using h
  · have h₃ : Cong d (3 * X ^ L) (Y ^ L) := by
      have hl : X ^ L = B ^ k := by
        dsimp [X, B]
        rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm k L]
      have hr : Y ^ L = 3 * A ^ k := by
        dsimp [Y, A]
        rw [← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm b L, ← he, Int.pow_succ, Int.mul_comm]
      rw [hl, hr]
      exact (Cong.refl d 3).mul (hBA.pow k)
    have h := ((Cong.refl d 3).mul (hz.pow L)).trans h₃
    rw [Int.mul_pow, Int.mul_left_comm 3] at h
    apply Cong.cancel (hc L)
    simpa [Int.natCast_pow, Y] using h

private theorem phase_bijection {a L k b : Nat} (hL : 1 < L) (ha : a < L)
    (he : a * k + 1 = L * b) :
    List.Perm ((List.range L).map (fun s => k * s % L)) (List.range L) := by
  let f := fun s => k * s % L
  let g := fun t => (L - a) * t % L
  have hmul : (L - a) * k + L * b = L * k + 1 := by
    rw [Nat.sub_mul, ← he, ← Nat.add_assoc, Nat.sub_add_cancel
      (Nat.mul_le_mul_right k (Nat.le_of_lt ha))]
  have hmod := congrArg (fun u : Nat => u % L) hmul
  rw [Nat.add_mul_mod_self_left, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt hL] at hmod
  have hgf (s : Nat) : g (f s) = s % L := by
    dsimp [f, g]
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod, hmod, Nat.one_mul, Nat.mod_mod]
  have hfg (t : Nat) : f (g t) = t % L := by
    dsimp [f, g]
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_comm k (L - a), Nat.mul_mod, hmod,
      Nat.one_mul, Nat.mod_mod]
  have hnd : ((List.range L).map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro s t hs ht hne h
    apply hne
    have h' := congrArg g h
    rw [hgf, hgf, Nat.mod_eq_of_lt (List.mem_range.mp hs), Nat.mod_eq_of_lt (List.mem_range.mp ht)] at h'
    exact h'
  have hm (t : Nat) : t ∈ (List.range L).map f ↔ t ∈ List.range L := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨s, _, rfl⟩
      exact Nat.mod_lt _ (by omega)
    · intro ht
      exact ⟨g t, Nat.mod_lt _ (by omega), (hfg t).trans (Nat.mod_eq_of_lt ht)⟩
  apply List.perm_iff_count.mpr
  intro t
  rw [hnd.count, List.nodup_range.count]
  simp only [hm]

private def sumZ (L : Nat) (f : Nat → Int) : Int := ((List.range L).map f).sum

private theorem sumZ_succ (L : Nat) (f : Nat → Int) : sumZ (L + 1) f = sumZ L f + f L := by
  simp [sumZ, List.range_succ, List.sum_append]

private theorem sumZ_perm {xs ys : List Int} (h : List.Perm xs ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Int.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sumZ_cong {d L : Nat} {f g : Nat → Int} (h : ∀ s, s < L → Cong d (f s) (g s)) :
    Cong d (sumZ L f) (sumZ L g) := by
  induction L with
  | zero => exact Cong.refl _ _
  | succ L ih =>
    rw [sumZ_succ, sumZ_succ]
    exact (ih fun s hs => h s (by omega)).add (h L (by omega))

private theorem sumZ_ofNat (L : Nat) (f : Nat → Nat) :
    ((sumRange L f : Nat) : Int) = sumZ L (fun t => (f t : Int)) := by
  induction L with
  | zero => rfl
  | succ L ih => rw [sumRange_succ, Int.natCast_add, sumZ_succ, ih]

private theorem sumZ_mul (L : Nat) (c : Int) (f : Nat → Int) :
    c * sumZ L f = sumZ L (fun t => c * f t) := by
  induction L with
  | zero => simp [sumZ]
  | succ L ih => rw [sumZ_succ, Int.mul_add, ih, sumZ_succ]

private theorem phase_coordinate {a L k b s : Nat} (hL : 0 < L) (he : a * k + 1 = L * b) :
    let t := k * s % L
    let q := k * s / L
    ∃ c, a * t + s = L * c ∧ a * q + c = b * s := by
  let t := k * s % L
  let q := k * s / L
  have hqt : L * q + t = k * s := Nat.div_add_mod _ _
  have h : L * (a * q) + (a * t + s) = L * (b * s) := by
    calc
      _ = a * (L * q + t) + s := by rw [Nat.mul_add, ← Nat.add_assoc]; ac_rfl
      _ = (a * k + 1) * s := by rw [hqt, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      _ = _ := by rw [he, Nat.mul_assoc]
  have hle : a * q ≤ b * s := Nat.le_of_mul_le_mul_left (by omega) hL
  change ∃ c, a * t + s = L * c ∧ a * q + c = b * s
  refine ⟨b * s - a * q, ?_, by omega⟩
  rw [Nat.mul_sub]
  omega

/-- The number of full periods of height above the phase's least residue. -/
def lift (n L k s : Nat) : Nat := (walk n L (k * s % L)).toNat / L

private theorem phase_lift_at {a L t s c u : Nat} (hL : 0 < L) (hs : s < L)
    (hcoord : a * t + s = L * c) (hw : 0 ≤ (L : Int) * u - (a : Int) * t) :
    let w := (L : Int) * u - (a : Int) * t
    let e := w.toNat / L
    u = c + e ∧ w = ((L * e + s : Nat) : Int) := by
  let w := (L : Int) * u - (a : Int) * t
  have hcoordZ : (a : Int) * (t : Int) + (s : Int) = (L : Int) * (c : Int) := by
    exact_mod_cast hcoord
  have hw' : w = (L : Int) * ((u : Int) - (c : Int)) + (s : Int) := by
    unfold w
    rw [Int.mul_sub]
    omega
  have hcu : c ≤ u := by
    by_cases hle : c ≤ u
    · exact hle
    have hm := Int.mul_le_mul_of_nonneg_left (b := -1)
      (show (u : Int) - (c : Int) ≤ -1 by omega) (show 0 ≤ (L : Int) by omega)
    rw [Int.mul_neg, Int.mul_one] at hm
    omega
  have hnat : w = ((L * (u - c) + s : Nat) : Int) := by
    rw [hw', Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hcu]
  have hlift : w.toNat / L = u - c := by
    rw [hnat, Int.toNat_natCast]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (u - c)]; omega
  change u = c + w.toNat / L ∧ w = _
  rw [hlift, hnat]
  omega

private theorem phase_lift {n L k s c : Nat} (hL : 0 < L) (hs : s < L)
    (hcoord : oddCount n L * (k * s % L) + s = L * c)
    (hw : 0 ≤ walk n L (k * s % L)) :
    oddCount n (k * s % L) = c + lift n L k s ∧
      walk n L (k * s % L) = ((L * lift n L k s + s : Nat) : Int) :=
  phase_lift_at hL hs hcoord hw

private theorem phase_power {a L k b s c : Nat} {z : Int}
    (ha : 0 < a) (hL : 0 < L) (hgap : 3 ^ a < 2 ^ L)
    (hz : Cong (2 ^ L - 3 ^ a) ((3 : Int) ^ b * z) ((2 : Int) ^ k))
    (hc : a * (k * s / L) + c = b * s) :
    Cong (2 ^ L - 3 ^ a) ((3 : Int) ^ c * z ^ s) ((2 : Int) ^ (k * s % L)) := by
  let d := 2 ^ L - 3 ^ a
  let t := k * s % L
  let q := k * s / L
  have hqt : L * q + t = k * s := Nat.div_add_mod _ _
  have hleft : ((3 : Int) ^ b * z) ^ s = (3 : Int) ^ (a * q) * ((3 : Int) ^ c * z ^ s) := by
    rw [Int.mul_pow, ← Int.pow_mul, ← Int.mul_assoc, ← Int.pow_add, hc]
  have htwo : ((2 : Int) ^ k) ^ s = (2 : Int) ^ t * ((2 : Int) ^ L) ^ q := by
    rw [← Int.pow_mul, ← Int.pow_mul, ← Int.pow_add, Nat.add_comm, hqt]
  have hright : (2 : Int) ^ t * ((3 : Int) ^ a) ^ q = (3 : Int) ^ (a * q) * (2 : Int) ^ t := by
    rw [← Int.pow_mul, Int.mul_comm]
  have hBA : Cong d ((2 : Int) ^ L) ((3 : Int) ^ a) := gap_cong (Nat.le_of_lt hgap)
  have h := hz.pow s
  rw [hleft, htwo] at h
  have hh := h.trans ((Cong.refl d ((2 : Int) ^ t)).mul (hBA.pow q))
  rw [hright] at hh
  apply Cong.cancel ((gap_coprime_two_three ha hL hgap).2.pow_right (a * q))
  simpa [Int.natCast_pow] using hh

private def weight (n L t : Nat) : Nat := 2 ^ t * 3 ^ (oddCount n L - oddCount n t)

private theorem phase_weight {n L k b E s : Nat} {z : Int}
    (ha : 0 < oddCount n L) (hL : 0 < L) (hgap : 3 ^ oddCount n L < 2 ^ L)
    (he : oddCount n L * k + 1 = L * b)
    (hz : Cong (2 ^ L - 3 ^ oddCount n L) ((3 : Int) ^ b * z) ((2 : Int) ^ k))
    (hs : s < L) (hw : 0 ≤ walk n L (k * s % L)) (hE : lift n L k s ≤ E) :
    Cong (2 ^ L - 3 ^ oddCount n L) ((3 : Int) ^ E * (weight n L (k * s % L) : Int))
      ((3 : Int) ^ oddCount n L * ((3 : Int) ^ (E - lift n L k s) * z ^ s)) := by
  let a := oddCount n L
  let t := k * s % L
  let u := oddCount n t
  let d := 2 ^ L - 3 ^ a
  let e := lift n L k s
  obtain ⟨c, hc, hq⟩ := phase_coordinate (s := s) hL he
  have ht : t ≤ L := Nat.le_of_lt (Nat.mod_lt _ hL)
  have hu : u ≤ a := by
    have := Discrepancy.oddCount_split (n := n) ht
    omega
  have hcount : u = c + e := (phase_lift hL hs hc hw).1
  have hexp : E + (a - u) + c = a + (E - e) := by omega
  have h := (Cong.refl d ((3 : Int) ^ E * (3 : Int) ^ (a - u))).mul
    (phase_power ha hL hgap hz hq).symm
  rw [← Int.mul_assoc, ← Int.pow_add, ← Int.pow_add, hexp] at h
  change Cong d ((3 : Int) ^ E * (weight n L t : Int)) _
  simpa [weight, Int.pow_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h

private theorem affine_weight_cong {n L : Nat} (hgap : 3 ^ oddCount n L ≤ 2 ^ L) :
    Cong (2 ^ L - 3 ^ oddCount n L) (4 * (affineC L n : Int))
      (sumZ L (fun t => (weight n L t : Int))) := by
  let f := weight n L
  have hstep (t : Nat) : f (t + 1) = 2 * (2 ^ t * 3 ^ (oddCount n L - oddCount n (t + 1))) := by
    unfold f weight
    rw [Nat.pow_succ]
    ac_rfl
  have hshift := CycleSum.sumRange_shift L f
  have hzero : f 0 = 3 ^ oddCount n L := by simp [f, weight, Congruence.oddCount_zero]
  have hlast : f L = 2 ^ L := by simp [f, weight]
  rw [hzero, hlast, sumRange_congr (fun i _ => hstep i), sumRange_const_mul] at hshift
  have hn : 4 * affineC L n + 2 ^ L = 3 ^ oddCount n L + sumRange L f := by
    have := affine_area n L
    omega
  have hZ : 4 * (affineC L n : Int) + (2 : Int) ^ L =
      (3 : Int) ^ oddCount n L + sumZ L (fun t => (f t : Int)) := by
    have h := congrArg (fun x : Nat => (x : Int)) hn
    simpa [sumZ_ofNat] using h
  unfold Cong
  rw [show 4 * (affineC L n : Int) - sumZ L (fun t => (f t : Int)) =
    (3 : Int) ^ oddCount n L - (2 : Int) ^ L by omega]
  exact (gap_cong hgap).symm

/-- The coefficient at a phase is a power of three, with exponent given by the
difference between the chosen height bound and the phase lift. -/
def evaluate (n L k E : Nat) (z : Int) : Int :=
  sumZ L (fun s => (3 : Int) ^ (E - lift n L k s) * z ^ s)

/-- A single residue determines the divisibility test for all lift bounds.
The test applies to any prefix with nonnegative walk and positive power gap. -/
theorem exists_phase_polynomial {n L k b : Nat} (ha : 0 < oddCount n L)
    (hal : oddCount n L < L) (hgap : 3 ^ oddCount n L < 2 ^ L)
    (he : oddCount n L * k + 1 = L * b) (hw : ∀ t, t < L → 0 ≤ walk n L t) :
    let d : Nat := 2 ^ L - 3 ^ oddCount n L
    ∃ z : Int, ((d : Int) ∣ 2 * z ^ oddCount n L - 1) ∧ ((d : Int) ∣ 3 * z ^ L - 1) ∧
      ∀ E, (∀ s, s < L → lift n L k s ≤ E) →
        (d ∣ affineC L n ↔ (d : Int) ∣ evaluate n L k E z) := by
  let a := oddCount n L
  let d := 2 ^ L - 3 ^ a
  have hL : 0 < L := by omega
  obtain ⟨z, hz, hz₂, hz₃⟩ := exists_phase_unit ha hL hgap he
  refine ⟨z, hz₂, hz₃, ?_⟩
  intro E hE
  let f := fun t => (weight n L t : Int)
  let g := fun s => (3 : Int) ^ (E - lift n L k s) * z ^ s
  have hp := (phase_bijection (by omega) hal he).map f
  have hreindex : sumZ L (fun s => f (k * s % L)) = sumZ L f := by
    simpa [sumZ, List.map_map, Function.comp_def] using sumZ_perm hp
  have hsum := sumZ_cong (fun s hs =>
    phase_weight ha hL hgap he hz hs (hw _ (Nat.mod_lt _ hL)) (hE s hs))
  change Cong d (sumZ L (fun s => (3 : Int) ^ E * f (k * s % L)))
    (sumZ L (fun s => (3 : Int) ^ a * g s)) at hsum
  rw [← sumZ_mul, ← sumZ_mul, hreindex] at hsum
  have h₀ : Cong d (4 * (affineC L n : Int)) (sumZ L f) := affine_weight_cong (Nat.le_of_lt hgap)
  have h := ((Cong.refl d ((3 : Int) ^ E)).mul h₀).trans hsum
  have hcop := gap_coprime_two_three ha hL hgap
  have hleft : d.Coprime (3 ^ E * 4) := (hcop.2.pow_right E).mul_right (hcop.1.pow_right 2)
  have hright : d.Coprime (3 ^ a) := hcop.2.pow_right a
  have hc := h.dvd_iff
  change d ∣ affineC L n ↔ (d : Int) ∣ sumZ L g
  rw [← Int.mul_assoc] at hc
  constructor
  · intro hd
    exact cancel_coprime_factor hright (by
      rw [Int.natCast_pow]
      exact hc.mp (Int.dvd_trans (Int.ofNat_dvd.mpr hd) (Int.dvd_mul_left _ _)))
  · intro hd
    apply Int.ofNat_dvd.mp
    apply cancel_coprime_factor hleft
    rw [Int.natCast_mul, Int.natCast_pow]
    exact hc.mpr (Int.dvd_trans hd (Int.dvd_mul_left _ _))

/-- A coprime odd count and period admit an index with discrepancy residue one. -/
theorem exists_adjacent_phase {a L : Nat} (ha : 0 < a) (hL : 1 < L) (hcop : a.Coprime L) :
    ∃ k b, k < L ∧ a * k + 1 = L * b := by
  obtain ⟨e, he, hpow⟩ := LocalBlindness.exists_pow_one_mod (by omega) ha hcop
  let u := a ^ (e - 1)
  let k := (L - 1) * u % L
  have hau : a * u % L = 1 := by
    change a * a ^ (e - 1) % L = 1
    rw [Nat.mul_comm, ← Nat.pow_succ, show (e - 1).succ = e by omega, hpow, Nat.mod_eq_of_lt hL]
  have hk : k < L := Nat.mod_lt _ (by omega)
  have hm : a * k % L = L - 1 := by
    dsimp [k]
    rw [Nat.mul_mod_mod, show a * ((L - 1) * u) = (L - 1) * (a * u) by ac_rfl,
      Nat.mul_mod, hau, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : L - 1 < L)]
  have hd : L ∣ a * k + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hm, Nat.mod_eq_of_lt hL, show L - 1 + 1 = L by omega, Nat.mod_self]
  exact ⟨k, hd.choose, hk, hd.choose_spec⟩

private theorem sumZ_sub (L : Nat) (f g : Nat → Int) :
    sumZ L (fun s => f s - g s) = sumZ L f - sumZ L g := by
  induction L with
  | zero => rfl
  | succ L ih => rw [sumZ_succ, ih, sumZ_succ, sumZ_succ]; omega

private theorem sumZ_eq {L : Nat} {f g : Nat → Int} (h : ∀ s, s < L → f s = g s) :
    sumZ L f = sumZ L g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [sumZ_succ, sumZ_succ, h L (by omega), ih (fun s hs => h s (by omega))]

private theorem sumZ_trim {r L : Nat} (hr : r ≤ L) (f : Nat → Int)
    (hz : ∀ s, r ≤ s → s < L → f s = 0) : sumZ L f = sumZ r f := by
  induction L with
  | zero => rw [show r = 0 by omega]
  | succ L ih =>
    by_cases he : r = L + 1
    · rw [he]
    · rw [sumZ_succ, hz L (by omega) (by omega), Int.add_zero]
      exact ih (by omega) (fun s hs hsL => hz s hs (by omega))

private theorem geom (L : Nat) (z : Int) : (1 - z) * sumZ L (fun s => z ^ s) = 1 - z ^ L := by
  induction L with
  | zero => simp [sumZ]
  | succ L ih =>
    rw [sumZ_succ, Int.mul_add, ih, Int.pow_succ]
    grind

private theorem unit_mul_dvd_iff {d : Nat} {u v x : Int} (hu : Cong d (u * v) 1) :
    (d : Int) ∣ u * x ↔ (d : Int) ∣ x := by
  have h := (hu.mul (Cong.refl d x)).dvd_iff
  rw [Int.one_mul, Int.mul_comm u v, Int.mul_assoc] at h
  exact ⟨fun hd => h.mp (Int.dvd_trans hd (Int.dvd_mul_left _ _)),
    fun hd => Int.dvd_trans hd (Int.dvd_mul_left _ _)⟩

private def liftedSum (n L k r : Nat) (z : Int) : Int :=
  sumZ r (fun s => if lift n L k s = 1 then z ^ s else 0)

/-- With lift at most one, the geometric part of the full phase polynomial
reduces to a constant and only the lifted phases need to be retained. -/
def sparseEvaluate (n L k r : Nat) (z : Int) : Int := 1 - (1 - z) * liftedSum n L k (r + 1) z

private theorem sumZ_zero (n : Nat) : sumZ n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumZ_succ, ih, Int.add_zero]

private theorem sumZ_head (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = f 0 + sumZ n (fun j => f (j + 1)) := by
  induction n with
  | zero => rw [sumZ_succ]; simp [sumZ]
  | succ n ih => rw [sumZ_succ, ih, sumZ_succ, Int.add_assoc]

private def marker (n L k r s : Nat) : Int :=
  if s ≤ r ∧ lift n L k s = 1 then 1 else 0

private def coefficient (n L k r : Nat) : Nat → Int
  | 0 => 1
  | s + 1 => marker n L k r s - marker n L k r (s + 1)

/-- Sum of the absolute coefficients of the sparse phase polynomial. -/
def coefficientMass (n L k r : Nat) : Nat :=
  sumRange (r + 2) (fun i => (coefficient n L k r i).natAbs)

private theorem coefficient_abs_le_one (n L k r i : Nat) : (coefficient n L k r i).natAbs ≤ 1 := by
  cases i with
  | zero => exact Nat.le_refl 1
  | succ i =>
    change (marker n L k r i - marker n L k r (i + 1)).natAbs ≤ 1
    unfold marker
    split <;> split <;> decide

/-- The absolute coefficient sum is at most the available number of degrees. -/
theorem coefficientMass_le (n L k r : Nat) : coefficientMass n L k r ≤ r + 2 := by
  unfold coefficientMass
  have h := sumRange_le (n := r + 2) (g := fun _ => 1)
    (fun i _ => coefficient_abs_le_one n L k r i)
  simpa only [sumRange_const, Nat.mul_one] using h

private theorem coefficient_evaluation (n L k r : Nat) (z : Int) :
    PhaseResidueBox.evaluate (r + 2) (coefficient n L k r) z = sparseEvaluate n L k r z := by
  let m := marker n L k r
  let f := fun j => m j * z ^ j
  have hzero : f 0 = 0 := by simp [f, m, marker, lift]
  have hlast : f (r + 1) = 0 := by simp [f, m, marker, show ¬ r + 1 ≤ r by omega]
  have hshift : sumZ (r + 1) (fun s => f (s + 1)) = sumZ (r + 1) f := by
    have h := sumZ_head (r + 1) f
    rw [sumZ_succ, hzero, hlast, Int.zero_add, Int.add_zero] at h
    exact h.symm
  have hsum : sumZ (r + 1) f = liftedSum n L k (r + 1) z := by
    apply sumZ_eq
    intro s hs
    change marker n L k r s * z ^ s = _
    unfold marker
    by_cases h : lift n L k s = 1 <;> simp [h, show s ≤ r by omega]
  change sumZ (r + 2) (fun j => coefficient n L k r j * z ^ j) = _
  rw [sumZ_head (r + 1)]
  simp only [coefficient, Int.pow_zero, Int.mul_one]
  rw [show (fun s => (marker n L k r s - marker n L k r (s + 1)) * z ^ (s + 1)) =
      (fun s => z * f s - f (s + 1)) by
    funext s
    simp only [f, m, Int.sub_mul, Int.pow_succ]
    grind, sumZ_sub, ← sumZ_mul, hshift, hsum]
  unfold sparseEvaluate
  grind

private theorem exists_last {P : Nat → Prop} (r : Nat) (h : ∃ i, i ≤ r ∧ P i) :
    ∃ i, i ≤ r ∧ P i ∧ ∀ j, i < j → j ≤ r → ¬ P j := by
  classical
  induction r with
  | zero =>
    obtain ⟨i, hi, hP⟩ := h
    exact ⟨i, hi, hP, fun j hj hle => by omega⟩
  | succ r ih =>
    by_cases hp : P (r + 1)
    · exact ⟨r + 1, Nat.le_refl _, hp, fun j hj hle => by omega⟩
    · obtain ⟨i, hi, hP, hmax⟩ := ih (by
        obtain ⟨i, hi, hpi⟩ := h
        have hne : i ≠ r + 1 := fun he => hp (he ▸ hpi)
        exact ⟨i, by omega, hpi⟩)
      refine ⟨i, by omega, hP, fun j hj hle hq => ?_⟩
      by_cases he : j = r + 1
      · exact hp (he ▸ hq)
      · exact hmax j hj (by omega) hq

/-- A sparse phase root modulo a nonunit gap comes from a monic polynomial
with constant coefficient one and all coefficients between minus one and one. -/
theorem sparse_polynomial_coefficients {n L k r D : Nat} {z : Int}
    (hD : 1 < D) (hroot : (D : Int) ∣ sparseEvaluate n L k r z) :
    ∃ (d : Nat) (P : Nat → Int), 0 < d ∧ d ≤ r + 1 ∧ P 0 = 1 ∧ P d = 1 ∧
      sumRange (d + 1) (fun i => (P i).natAbs) = coefficientMass n L k r ∧
      ∀ y : Int, PhaseResidueBox.evaluate (d + 1) P y = sparseEvaluate n L k r y := by
  classical
  have hsome : ∃ s, s ≤ r ∧ lift n L k s = 1 := by
    by_cases h : ∃ s, s ≤ r ∧ lift n L k s = 1
    · exact h
    · have hsum : liftedSum n L k (r + 1) z = 0 := by
        unfold liftedSum
        calc
          _ = sumZ (r + 1) (fun _ => 0) :=
            sumZ_eq (fun s hs => if_neg (fun he => h ⟨s, by omega, he⟩))
          _ = 0 := sumZ_zero _
      rw [sparseEvaluate, hsum, Int.mul_zero, Int.sub_zero] at hroot
      have hd : D ∣ 1 := Int.ofNat_dvd.mp hroot
      have := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
  obtain ⟨s, hs, htop, hlast⟩ := exists_last r hsome
  refine ⟨s + 1, coefficient n L k s, by omega, by omega, rfl, ?_, ?_, ?_⟩
  · simp [coefficient, marker, htop, show ¬ s + 1 ≤ s by omega]
  · have hmarker (j : Nat) : marker n L k r j = marker n L k s j := by
      unfold marker
      by_cases hj : j ≤ s
      · simp [hj, show j ≤ r by omega]
      · by_cases hr : j ≤ r
        · simp [hj, hlast j (by omega) hr]
        · simp [hj, hr]
    have hc : coefficient n L k r = coefficient n L k s := by
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [coefficient, hmarker]
    unfold coefficientMass
    rw [hc, show r + 2 = (s + 2) + (r - s) by omega, sumRange_split (s + 2) (r - s)]
    have hz : sumRange (r - s) (fun i => (coefficient n L k s (s + 2 + i)).natAbs) = 0 := by
      rw [sumRange_congr (g := fun _ => 0), sumRange_const, Nat.mul_zero]
      intro i _
      rw [show s + 2 + i = (s + 1 + i) + 1 by omega]
      simp [coefficient, marker, show ¬ s + 1 + i ≤ s by omega,
        show ¬ s + 1 + i + 1 ≤ s by omega]
    simp only [hz, Nat.add_zero]
  · intro y
    rw [coefficient_evaluation]
    have ht : liftedSum n L k (r + 1) y = liftedSum n L k (s + 1) y := by
      apply sumZ_trim (by omega)
      intro j hj hrl
      exact if_neg (hlast j (by omega) (by omega))
    unfold sparseEvaluate
    rw [ht]

private theorem evaluate_one (n L k : Nat) (z : Int) (hE : ∀ s, s < L → lift n L k s ≤ 1) :
    evaluate n L k 1 z = 3 * sumZ L (fun s => z ^ s) - 2 * liftedSum n L k L z := by
  rw [evaluate, liftedSum, sumZ_mul, sumZ_mul, ← sumZ_sub]
  apply sumZ_eq
  intro s hs
  have he := hE s hs
  rcases (show lift n L k s = 0 ∨ lift n L k s = 1 by omega) with h | h
  · simp [h]
  · simp [h, Int.two_mul]; omega

private theorem width_lift {n L k b r s : Nat} (hL : 0 < L) (hr : r < L) (hs : s < L)
    (he : oddCount n L * k + 1 = L * b)
    (hw : 0 ≤ walk n L (k * s % L) ∧ walk n L (k * s % L) ≤ (L : Int) + r) :
    lift n L k s ≤ 1 ∧ (r < s → lift n L k s = 0) := by
  obtain ⟨c, hc, _⟩ := phase_coordinate (s := s) hL he
  have h := (phase_lift hL hs hc hw.1).2
  have hle : L * lift n L k s + s ≤ L + r := by
    have h' := hw.2
    rw [h, ← Int.natCast_add] at h'
    exact Int.ofNat_le.mp h'
  constructor
  · by_cases h' : lift n L k s ≤ 1
    · exact h'
    · have hm := Nat.mul_le_mul_left L (show 2 ≤ lift n L k s by omega)
      rw [Nat.mul_comm L 2, Nat.two_mul] at hm
      omega
  · intro hsr
    by_cases hz : lift n L k s = 0
    · exact hz
    · have hm := Nat.mul_le_mul_left L (show 1 ≤ lift n L k s by omega)
      rw [Nat.mul_one] at hm
      omega

private theorem sparse_dvd_iff {n L k r d a : Nat} {z : Int}
    (h₂ : Cong d (2 * z ^ a) 1) (h₃ : Cong d (3 * z ^ L) 1) (hcop : d.Coprime 2)
    (hr : r < L) (hE : ∀ s, s < L → lift n L k s ≤ 1)
    (hz : ∀ s, r < s → s < L → lift n L k s = 0) :
    ((d : Int) ∣ evaluate n L k 1 z) ↔ (d : Int) ∣ sparseEvaluate n L k r z := by
  let S := liftedSum n L k (r + 1) z
  have htrim : liftedSum n L k L z = S := by
    apply sumZ_trim (by omega)
    intro s hrs hs
    simp [hz s (by omega) hs]
  have hunit : Cong d ((1 - z) * (2 * sumZ a (fun s => z ^ s))) 1 := by
    rw [← Int.mul_left_comm 2, geom]
    change (d : Int) ∣ 2 * (1 - z ^ a) - 1
    rw [show 2 * (1 - z ^ a) - 1 = -(2 * z ^ a - 1) by omega]
    exact Int.dvd_neg.mpr h₂
  have hgeom : Cong d (3 * (1 - z ^ L)) 2 := by
    change (d : Int) ∣ 3 * (1 - z ^ L) - 2
    rw [show 3 * (1 - z ^ L) - 2 = -(3 * z ^ L - 1) by omega]
    exact Int.dvd_neg.mpr h₃
  have heval : (1 - z) * evaluate n L k 1 z = 3 * (1 - z ^ L) - 2 * ((1 - z) * S) := by
    rw [evaluate_one n L k z hE, htrim, Int.mul_sub, ← Int.mul_left_comm 3, geom,
      Int.mul_left_comm (1 - z) 2]
  have hc := hgeom.add (Cong.refl d (-(2 * ((1 - z) * S))))
  rw [Int.add_neg_eq_sub, Int.add_neg_eq_sub, ← heval,
    show 2 - 2 * ((1 - z) * S) = 2 * sparseEvaluate n L k r z by
      change _ = 2 * (1 - (1 - z) * S)
      rw [Int.mul_sub, Int.mul_one]] at hc
  constructor
  · intro hd
    apply cancel_coprime_factor hcop
    exact hc.dvd_iff.mp ((unit_mul_dvd_iff hunit).mpr hd)
  · intro hd
    exact (unit_mul_dvd_iff hunit).mp (hc.dvd_iff.mpr (Int.dvd_trans hd (Int.dvd_mul_left _ _)))

/-- Within a strip of width `L+r<2L`, the accumulator test uses only phases
`1,...,r` that reach the upper lift. -/
theorem exists_sparse_phase_polynomial {n L k b r : Nat} (ha : 0 < oddCount n L)
    (hal : oddCount n L < L) (hgap : 3 ^ oddCount n L < 2 ^ L)
    (he : oddCount n L * k + 1 = L * b) (hr : r < L)
    (hw : ∀ t, t < L → 0 ≤ walk n L t ∧ walk n L t ≤ (L : Int) + r) :
    let d : Nat := 2 ^ L - 3 ^ oddCount n L
    ∃ z : Int, ((d : Int) ∣ 2 * z ^ oddCount n L - 1) ∧ ((d : Int) ∣ 3 * z ^ L - 1) ∧
      (d ∣ affineC L n ↔ (d : Int) ∣ sparseEvaluate n L k r z) := by
  have hL : 0 < L := by omega
  obtain ⟨z, h₂, h₃, hp⟩ := exists_phase_polynomial ha hal hgap he (fun t ht => (hw t ht).1)
  have hl (s : Nat) (hs : s < L) :=
    width_lift hL hr hs he (hw _ (Nat.mod_lt _ hL))
  have hE (s : Nat) (hs : s < L) := (hl s hs).1
  exact ⟨z, h₂, h₃, (hp 1 hE).trans (sparse_dvd_iff h₂ h₃
    (gap_coprime_two_three ha hL hgap).1 hr hE (fun s hrs hs => (hl s hs).2 hrs))⟩

private theorem exists_argmin (f : Nat → Int) (m : Nat) :
    ∃ j, j < m + 1 ∧ ∀ i, i < m + 1 → f j ≤ f i := by
  induction m with
  | zero =>
    refine ⟨0, by omega, fun i hi => ?_⟩
    have he : i = 0 := by omega
    exact he ▸ Int.le_refl _
  | succ m ih =>
    obtain ⟨j, hj, hmin⟩ := ih
    by_cases h : f j ≤ f (m + 1)
    · refine ⟨j, by omega, fun i hi => ?_⟩
      by_cases he : i = m + 1
      · exact he ▸ h
      · exact hmin i (by omega)
    · refine ⟨m + 1, by omega, fun i hi => ?_⟩
      by_cases he : i = m + 1
      · exact he ▸ Int.le_refl _
      · exact Int.le_trans (by omega) (hmin i (by omega))

/-- Rotating at the minimum discrepancy puts the walk in the nonnegative strip. -/
theorem exists_min_rotation {n L r : Nat} (h : AccIsCycleOf n L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    ∃ j, j < L ∧ (∀ t, walk n L j ≤ walk n L t) ∧ ∀ t, 0 ≤ walk (acceleratedOrbit j n) L t ∧
      walk (acceleratedOrbit j n) L t ≤ (L : Int) + r := by
  obtain ⟨j, hj, hmin⟩ := exists_argmin (walk n L) (L - 1)
  have hL : L - 1 + 1 = L := by have := h.1; omega
  rw [hL] at hj hmin
  have hlo (t : Nat) : walk n L j ≤ walk n L t := by
    rw [walk_mod h.1 h.2 t]
    exact hmin (t % L) (Nat.mod_lt _ h.1)
  refine ⟨j, hj, hlo, fun t => ?_⟩
  rw [walk_shift h.2]
  have hlow := hlo (j + t)
  have hhi := hw (j + t) j
  omega

/-- A coprime cycle in a strip of width `L+r<2L` supplies a root of the
sparse phase polynomial modulo its power gap. -/
theorem cycle_sparse_root {n L r : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hcop : (oddCount n L).Coprime L) (hr : r < L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    let d : Nat := 2 ^ L - 3 ^ oddCount n L
    ∃ j k : Nat, j < L ∧ k < L ∧ ∃ z : Int,
      ((d : Int) ∣ 2 * z ^ oddCount n L - 1) ∧ ((d : Int) ∣ 3 * z ^ L - 1) ∧
      (d : Int) ∣ sparseEvaluate (acceleratedOrbit j n) L k r z := by
  obtain ⟨j, hj, _, hjmin⟩ := exists_min_rotation h hw
  let x := acceleratedOrbit j n
  have hx : 0 < x := acceleratedOrbit_positive hn j
  have hc := accIsCycleOf_orbit h j
  have hshift : oddCount x L = oddCount n L := AccumulatorCap.oddCount_shift h.2 j
  obtain ⟨ha, hal, hgap⟩ := accCycle_bounds hx hc
  obtain ⟨k, b, hk, he⟩ := exists_adjacent_phase ha (by omega) (hshift.symm ▸ hcop)
  obtain ⟨z, h₂, h₃, hp⟩ := exists_sparse_phase_polynomial ha hal hgap he hr
    (fun t _ => hjmin t)
  have hd := hp.mp (CycleAccumulator.cycle_gap_dvd hx hc)
  refine ⟨j, k, hj, hk, z, ?_⟩
  rw [hshift] at h₂ hd
  exact ⟨h₂, by simpa only [hshift] using h₃, hd⟩

private theorem width_two_lift {n L k b t : Nat} (hL : 2 < L) (hal : oddCount n L < L)
    (he : oddCount n L * k + 1 = L * b) (ht : t < L)
    (hmax : walk n L t = (L : Int) + 2) : lift n L k 2 = 1 := by
  have hp := phase_bijection (by omega) hal he
  have hm := hp.mem_iff.mpr (List.mem_range.mpr ht)
  obtain ⟨s, hs, hst⟩ := List.mem_map.mp hm
  have hsL : s < L := List.mem_range.mp hs
  obtain ⟨c, hc, _⟩ := phase_coordinate (s := s) (by omega) he
  have hw : 0 ≤ walk n L (k * s % L) := by rw [hst, hmax]; omega
  have hl := (phase_lift (by omega) hsL hc hw).2
  rw [hst, hmax, Int.natCast_add, Int.natCast_mul] at hl
  have hbound := (width_lift (by omega) hL hsL he ⟨hw, by rw [hst, hmax]; exact Int.le_refl _⟩).1
  rcases (show lift n L k s = 0 ∨ lift n L k s = 1 by omega) with hz | ho
  · rw [hz] at hl
    simp at hl
    omega
  · rw [ho] at hl
    simp at hl
    have hs2 : s = 2 := by omega
    exact hs2 ▸ ho

private theorem sparse_two_forms {n L k : Nat} (z : Int) (h₂ : lift n L k 2 = 1) :
    sparseEvaluate n L k 2 z = 1 - z ^ 2 + z ^ 3 ∨
      sparseEvaluate n L k 2 z = 1 - z + z ^ 3 := by
  have hzero : lift n L k 0 = 0 := by simp [lift]
  unfold sparseEvaluate liftedSum
  rw [show (2 : Nat) + 1 = 2 + 1 from rfl, sumZ_succ,
    show (2 : Nat) = 1 + 1 from rfl, sumZ_succ,
    show (1 : Nat) = 0 + 1 from rfl, sumZ_succ]
  by_cases h₁ : lift n L k 1 = 1
  · right
    simp only [hzero, h₁, h₂, if_true]
    change 1 - (1 - z) * (0 + 0 + z ^ 1 + z ^ 2) = _
    grind
  · left
    simp only [hzero, h₁, h₂, if_false, if_true]
    change 1 - (1 - z) * (0 + 0 + 0 + z ^ 2) = _
    grind

/-- At the next possible width, a nontrivial coprime cycle must supply a
common modular root for the two power equations and one of two cubics. -/
theorem cycle_width_two_cubic {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n) (hnon : 2 < n)
    (hcop : (oddCount n L).Coprime L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + 2) :
    let d : Nat := 2 ^ L - 3 ^ oddCount n L
    ∃ z : Int, ((d : Int) ∣ 2 * z ^ oddCount n L - 1) ∧ ((d : Int) ∣ 3 * z ^ L - 1) ∧
      (((d : Int) ∣ 1 - z ^ 2 + z ^ 3) ∨ ((d : Int) ∣ 1 - z + z ^ 3)) := by
  have hL : 2 < L := by
    have hle := two_le_length_of_accCycle hn h
    by_cases ht : L = 2
    · rcases accIsCycleOf_two_length hn (ht ▸ h) with hz | hz <;> omega
    · omega
  obtain ⟨i, j, _, _, hij⟩ := nontrivial_cycle_needs_extra_width hn h hleast hnon
  obtain ⟨m, hm, hmlo, hstrip⟩ := exists_min_rotation h hw
  let x := acceleratedOrbit m n
  have hx : 0 < x := acceleratedOrbit_positive hn m
  have hc := accIsCycleOf_orbit h m
  have hshift : oddCount x L = oddCount n L := AccumulatorCap.oddCount_shift h.2 m
  obtain ⟨t, ht, hval⟩ := walk_range' h.1 h.2 hm i
  have hmax : walk x L t = (L : Int) + 2 := by
    have hlo := hmlo j
    have hhi := hw i m
    change walk x L t = walk n L i - walk n L m at hval
    omega
  obtain ⟨ha, hal, hgap⟩ := accCycle_bounds hx hc
  obtain ⟨k, b, _, he⟩ := exists_adjacent_phase ha (by omega) (hshift.symm ▸ hcop)
  obtain ⟨z, h₂, h₃, hp⟩ := exists_sparse_phase_polynomial ha hal hgap he hL
    (fun t _ => hstrip t)
  have hd := hp.mp (CycleAccumulator.cycle_gap_dvd hx hc)
  have hl := width_two_lift hL hal he ht hmax
  rw [hshift] at hd h₂
  refine ⟨z, h₂, by simpa only [hshift] using h₃, ?_⟩
  rcases sparse_two_forms z hl with hf | hf
  · exact Or.inl (hf ▸ hd)
  · exact Or.inr (hf ▸ hd)

private theorem sumZ_split (n m : Nat) (f : Nat → Int) :
    sumZ (n + m) f = sumZ n f + sumZ m (fun i => f (n + i)) := by
  induction m with
  | zero => exact (Int.add_zero _).symm
  | succ m ih => rw [← Nat.add_assoc, sumZ_succ, ih, sumZ_succ, Int.add_assoc]

private theorem sumZ_add (n : Nat) (f g : Nat → Int) :
    sumZ n (fun i => f i + g i) = sumZ n f + sumZ n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumZ_succ, sumZ_succ, sumZ_succ, ih]; omega

private theorem sign_square (i : Nat) : (-1 : Int) ^ i * (-1 : Int) ^ i = 1 := by
  induction i with
  | zero => decide
  | succ i ih => rw [Int.pow_succ, show ((-1 : Int) ^ i * -1) * ((-1 : Int) ^ i * -1) =
      (-1 : Int) ^ i * (-1 : Int) ^ i by grind, ih]

private theorem plus_gap_cong (p b : Nat) :
    Cong (2 ^ p + 3 ^ b) ((2 : Int) ^ p) (-(3 : Int) ^ b) := by
  change ((2 ^ p + 3 ^ b : Nat) : Int) ∣ (2 : Int) ^ p - (-(3 : Int) ^ b)
  simp

private theorem plus_gap_divides {p b : Nat} (hgap : 3 ^ (2 * b) ≤ 2 ^ (2 * p)) :
    2 ^ p + 3 ^ b ∣ 2 ^ (2 * p) - 3 ^ (2 * b) := by
  have h := (plus_gap_cong p b).pow 2
  change ((2 ^ p + 3 ^ b : Nat) : Int) ∣ ((2 : Int) ^ p) ^ 2 - (-(3 : Int) ^ b) ^ 2 at h
  rw [show (-(3 : Int) ^ b) ^ 2 = ((3 : Int) ^ b) ^ 2 by grind,
    ← Int.pow_mul, ← Int.pow_mul, Nat.mul_comm p 2, Nat.mul_comm b 2] at h
  exact Int.ofNat_dvd.mp (by simpa [Int.ofNat_sub hgap] using h)

private theorem plus_gap_pow (p b i : Nat) :
    Cong (2 ^ p + 3 ^ b) (((2 : Int) ^ p) ^ i) ((-1 : Int) ^ i * (3 : Int) ^ (b * i)) := by
  have h := (plus_gap_cong p b).pow i
  rw [show -(3 : Int) ^ b = (-1) * (3 : Int) ^ b by simp, Int.mul_pow,
    ← Int.pow_mul (a := (3 : Int))] at h
  exact h

private theorem exists_signed_unit {p b k c : Nat}
    (hc : (2 ^ p + 3 ^ b).Coprime 3) (he : b * k + 1 = p * c) :
    let D := 2 ^ p + 3 ^ b
    ∃ z : Int, Cong D ((3 : Int) ^ c * z) ((2 : Int) ^ k) ∧
      Cong D ((2 * (-1 : Int) ^ c) * z ^ b) 1 ∧
      Cong D ((3 * (-1 : Int) ^ k) * z ^ p) 1 := by
  let D := 2 ^ p + 3 ^ b
  have hn3 : D % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ D := Nat.dvd_of_mod_eq_zero h
    have h' := Nat.dvd_gcd hd (Nat.dvd_refl 3)
    change D.gcd 3 = 1 at hc
    rw [hc] at h'
    omega
  obtain ⟨u, hu⟩ := exists_three_inverse hn3
  let z := (2 : Int) ^ k * u ^ c
  have hz : Cong D ((3 : Int) ^ c * z) ((2 : Int) ^ k) := by
    have h := (hu.pow c).mul (Cong.refl D ((2 : Int) ^ k))
    rw [Int.mul_pow, Int.one_pow, Int.one_mul] at h
    simpa only [z, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h
  have h₂ : Cong D (2 * z ^ b) ((-1 : Int) ^ c) := by
    have h := (Cong.refl D 2).mul (hz.pow b)
    have hpow : 2 * ((2 : Int) ^ k) ^ b = ((2 : Int) ^ p) ^ c := by
      rw [← Int.pow_mul, ← Int.pow_mul, ← he, Nat.mul_comm k b, Int.pow_succ, Int.mul_comm]
    rw [hpow, Int.mul_pow, ← Int.pow_mul] at h
    have h' := h.trans (plus_gap_pow p b c)
    rw [Int.mul_left_comm 2, Nat.mul_comm b c, Int.mul_comm ((-1 : Int) ^ c)] at h'
    exact Cong.cancel (hc.pow_right (c * b)) (by simpa using h')
  have h₃ : Cong D (3 * z ^ p) ((-1 : Int) ^ k) := by
    have h := (Cong.refl D 3).mul (hz.pow p)
    rw [← Int.pow_mul (a := (2 : Int)), Nat.mul_comm k p, Int.pow_mul (a := (2 : Int))] at h
    have h' := h.trans ((Cong.refl D 3).mul (plus_gap_pow p b k))
    have hr : 3 * ((-1 : Int) ^ k * (3 : Int) ^ (b * k)) = (3 : Int) ^ (c * p) * (-1 : Int) ^ k := by
      rw [Int.mul_left_comm, ← Int.pow_succ', he, Nat.mul_comm p c, Int.mul_comm]
    rw [Int.mul_pow, ← Int.pow_mul (a := (3 : Int)), Int.mul_left_comm 3, hr] at h'
    exact Cong.cancel (hc.pow_right (c * p)) (by simpa using h')
  refine ⟨z, hz, ?_, ?_⟩
  · have h := (Cong.refl D ((-1 : Int) ^ c)).mul h₂
    rw [sign_square, ← Int.mul_assoc, Int.mul_comm ((-1 : Int) ^ c) 2] at h
    exact h
  · have h := (Cong.refl D ((-1 : Int) ^ k)).mul h₃
    rw [sign_square, ← Int.mul_assoc, Int.mul_comm ((-1 : Int) ^ k) 3] at h
    exact h

private theorem signed_phase_power {p b k c s v : Nat} {z : Int}
    (hc : (2 ^ p + 3 ^ b).Coprime 3)
    (hz : Cong (2 ^ p + 3 ^ b) ((3 : Int) ^ c * z) ((2 : Int) ^ k))
    (hv : b * (k * s / p) + v = c * s) :
    Cong (2 ^ p + 3 ^ b) ((2 : Int) ^ (k * s % p))
      ((-1 : Int) ^ (k * s / p) * ((3 : Int) ^ v * z ^ s)) := by
  let D := 2 ^ p + 3 ^ b
  let t := k * s % p
  let q := k * s / p
  have hqt : p * q + t = k * s := Nat.div_add_mod _ _
  have hl : ((3 : Int) ^ c * z) ^ s = (3 : Int) ^ (b * q) * ((3 : Int) ^ v * z ^ s) := by
    rw [Int.mul_pow, ← Int.pow_mul, ← Int.mul_assoc, ← Int.pow_add, hv]
  have hr : ((2 : Int) ^ k) ^ s = (2 : Int) ^ t * ((2 : Int) ^ p) ^ q := by
    rw [← Int.pow_mul, ← Int.pow_mul, ← Int.pow_add, Nat.add_comm, hqt]
  have h := hz.pow s
  rw [hl, hr] at h
  have hh := h.trans ((Cong.refl D ((2 : Int) ^ t)).mul (plus_gap_pow p b q))
  have hh' : Cong D ((3 : Int) ^ (b * q) * ((3 : Int) ^ v * z ^ s))
      ((3 : Int) ^ (b * q) * ((-1 : Int) ^ q * (2 : Int) ^ t)) := by
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hh
  have hc' := Cong.cancel (hc.pow_right (b * q)) (by simpa using hh')
  have hsign := (Cong.refl D ((-1 : Int) ^ q)).mul hc'
  rw [← Int.mul_assoc ((-1 : Int) ^ q) ((-1 : Int) ^ q), sign_square, Int.one_mul] at hsign
  exact hsign.symm

private def reducedWalk (n p b t : Nat) : Int := (p : Int) * oddCount n t - (b : Int) * t

private theorem walk_eq_twice_reduced {n p b : Nat} (hb : oddCount n (2 * p) = 2 * b) (t : Nat) :
    walk n (2 * p) t = 2 * reducedWalk n p b t := by
  unfold walk reducedWalk
  rw [hb, Int.natCast_mul, Int.natCast_mul]
  grind

private theorem reduced_lift_at {n p b t s v r : Nat} (hp : 0 < p) (hr : r < p) (hs : s < p)
    (hc : b * t + s = p * v) (hw : 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r) :
    let e := (reducedWalk n p b t).toNat / p
    oddCount n t = v + e ∧ reducedWalk n p b t = ((p * e + s : Nat) : Int) ∧
      e ≤ 1 ∧ (r < s → e = 0) := by
  let e := (reducedWalk n p b t).toNat / p
  have ⟨hcount, hw'⟩ := phase_lift_at hp hs hc hw.1
  change oddCount n t = v + e at hcount
  change reducedWalk n p b t = ((p * e + s : Nat) : Int) at hw'
  have hbound : p * e + s ≤ p + r := by
    have ht := hw.2
    rw [hw', ← Int.natCast_add] at ht
    exact Int.ofNat_le.mp ht
  refine ⟨hcount, hw', ?_, ?_⟩
  · change e ≤ 1
    apply Classical.byContradiction
    intro h
    have hh := Nat.mul_le_mul_left p (show 2 ≤ e by omega)
    rw [Nat.mul_comm p 2, Nat.two_mul] at hh
    omega
  · intro hsr
    change e = 0
    apply Classical.byContradiction
    intro h
    have hh := Nat.mul_le_mul_left p (Nat.pos_of_ne_zero h)
    rw [Nat.mul_one] at hh
    omega

private theorem scaled_phase_weight {n L t v e s D : Nat} {z sign : Int}
    (ht : t ≤ L) (hcount : oddCount n t = v + e) (he : e ≤ 1)
    (hpower : Cong D ((2 : Int) ^ t) (sign * ((3 : Int) ^ v * z ^ s))) :
    Cong D (3 * (weight n L t : Int))
      ((3 : Int) ^ oddCount n L * (sign * ((3 : Int) ^ (1 - e) * z ^ s))) := by
  have hu : oddCount n t ≤ oddCount n L := by
    have := Discrepancy.oddCount_split (n := n) ht
    omega
  have hexp : 1 + (oddCount n L - oddCount n t) + v = oddCount n L + (1 - e) := by omega
  have h := (Cong.refl D ((3 : Int) ^ (1 + (oddCount n L - oddCount n t)))).mul hpower
  have hr : (3 : Int) ^ (1 + (oddCount n L - oddCount n t)) * (sign * ((3 : Int) ^ v * z ^ s)) =
      (3 : Int) ^ oddCount n L * (sign * ((3 : Int) ^ (1 - e) * z ^ s)) := by
    calc
      _ = (3 : Int) ^ (1 + (oddCount n L - oddCount n t) + v) * (sign * z ^ s) := by
        rw [Int.pow_add (m := 1 + (oddCount n L - oddCount n t)) (n := v)]; ac_rfl
      _ = _ := by rw [hexp, Int.pow_add]; ac_rfl
  rw [hr] at h
  simpa [weight, Int.pow_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using h

private def pairedCoefficient (n p b k s : Nat) : Int :=
  let t := k * s % p
  let first := (reducedWalk n p b t).toNat / p
  let second := (reducedWalk n p b (t + p)).toNat / p
  (-1 : Int) ^ (k * s / p) * ((second : Int) - (first : Int))

private theorem paired_lifts {n p b k c s r : Nat} (hp : 0 < p) (hr : r < p) (hs : s < p)
    (he : b * k + 1 = p * c)
    (hstrip : ∀ t, 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r) :
    let t := k * s % p
    let e₀ := (reducedWalk n p b t).toNat / p
    let e₁ := (reducedWalk n p b (t + p)).toNat / p
    ∃ v, b * (k * s / p) + v = c * s ∧
      oddCount n t = v + e₀ ∧ oddCount n (t + p) = v + b + e₁ ∧
      reducedWalk n p b t = ((p * e₀ + s : Nat) : Int) ∧
      reducedWalk n p b (t + p) = ((p * e₁ + s : Nat) : Int) ∧
      e₀ ≤ 1 ∧ e₁ ≤ 1 ∧ (r < s → e₀ = 0 ∧ e₁ = 0) := by
  let t := k * s % p
  obtain ⟨v, hv, hq⟩ := phase_coordinate (s := s) hp he
  have hv' : b * (t + p) + s = p * (v + b) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm b p]
    change b * t + s = p * v at hv
    omega
  obtain ⟨hc₀, hw₀, he₀, hz₀⟩ := reduced_lift_at hp hr hs hv (hstrip t)
  obtain ⟨hc₁, hw₁, he₁, hz₁⟩ := reduced_lift_at hp hr hs hv' (hstrip (t + p))
  exact ⟨v, hq, hc₀, hc₁, hw₀, hw₁, he₀, he₁, fun h => ⟨hz₀ h, hz₁ h⟩⟩

private theorem paired_weight {n p b k c r s : Nat} {z : Int}
    (hp : 0 < p) (hr : r < p) (hs : s < p) (hb : oddCount n (2 * p) = 2 * b)
    (he : b * k + 1 = p * c) (hc : (2 ^ p + 3 ^ b).Coprime 3)
    (hstrip : ∀ t, 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r)
    (hz : Cong (2 ^ p + 3 ^ b) ((3 : Int) ^ c * z) ((2 : Int) ^ k)) :
    let t := k * s % p
    Cong (2 ^ p + 3 ^ b) (3 * ((weight n (2 * p) t : Int) + (weight n (2 * p) (t + p) : Int)))
      (2 * (3 : Int) ^ (2 * b) * (pairedCoefficient n p b k s * z ^ s)) := by
  let t := k * s % p
  let sign := (-1 : Int) ^ (k * s / p)
  let e₀ := (reducedWalk n p b t).toNat / p
  let e₁ := (reducedWalk n p b (t + p)).toNat / p
  obtain ⟨v, hv, hc₀, hc₁, _, _, he₀, he₁, _⟩ := paired_lifts hp hr hs he hstrip
  have ht : t < p := Nat.mod_lt _ hp
  have hpow₀ := signed_phase_power hc hz hv
  have hpow₁ : Cong (2 ^ p + 3 ^ b) ((2 : Int) ^ (t + p)) (-sign * ((3 : Int) ^ (v + b) * z ^ s)) := by
    have h := hpow₀.mul (plus_gap_cong p b)
    change Cong (2 ^ p + 3 ^ b) ((2 : Int) ^ t * (2 : Int) ^ p)
      ((sign * ((3 : Int) ^ v * z ^ s)) * -(3 : Int) ^ b) at h
    rw [Int.pow_add, Int.pow_add]
    rw [show (sign * ((3 : Int) ^ v * z ^ s)) * -(3 : Int) ^ b =
      -sign * ((3 : Int) ^ v * (3 : Int) ^ b * z ^ s) by grind] at h
    exact h
  have h₀ := scaled_phase_weight (by omega : t ≤ 2 * p) hc₀ he₀ hpow₀
  have h₁ := scaled_phase_weight (by omega : t + p ≤ 2 * p) hc₁ he₁ hpow₁
  have hsum := h₀.add h₁
  rw [← Int.mul_add, hb] at hsum
  change Cong _ _ (2 * (3 : Int) ^ (2 * b) * ((sign * ((e₁ : Int) - (e₀ : Int))) * z ^ s))
  have hsmall (e : Nat) (he : e ≤ 1) : (3 : Int) ^ (1 - e) = 3 - 2 * (e : Int) := by
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;> decide
  rw [hsmall _ he₀, hsmall _ he₁] at hsum
  have hpoly :
      (3 : Int) ^ (2 * b) * (sign * ((3 - 2 * (e₀ : Int)) * z ^ s)) +
      (3 : Int) ^ (2 * b) * (-sign * ((3 - 2 * (e₁ : Int)) * z ^ s)) =
      2 * (3 : Int) ^ (2 * b) * ((sign * ((e₁ : Int) - (e₀ : Int))) * z ^ s) := by grind
  rw [← hpoly]
  exact hsum

private theorem paired_root {n p b k c r : Nat} {z : Int} (hp : 1 < p) (hbp : b < p)
    (hr : r < p) (hb : oddCount n (2 * p) = 2 * b)
    (he : b * k + 1 = p * c) (hgap : 3 ^ (2 * b) < 2 ^ (2 * p))
    (hcop : (2 ^ p + 3 ^ b).Coprime (2 * 3 ^ (2 * b)))
    (hthree : (2 ^ p + 3 ^ b).Coprime 3)
    (hstrip : ∀ t, 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r)
    (hz : Cong (2 ^ p + 3 ^ b) ((3 : Int) ^ c * z) ((2 : Int) ^ k))
    (hdvd : 2 ^ (2 * p) - 3 ^ (2 * b) ∣ affineC (2 * p) n) :
    ((2 ^ p + 3 ^ b : Nat) : Int) ∣ sumZ (r + 1) (fun s => pairedCoefficient n p b k s * z ^ s) := by
  let D := 2 ^ p + 3 ^ b
  let w := fun t => (weight n (2 * p) t : Int)
  let f := fun t => w t + w (t + p)
  let g := fun s => pairedCoefficient n p b k s * z ^ s
  have hsplit : sumZ (2 * p) w = sumZ p f := by
    rw [show 2 * p = p + p from Nat.two_mul p, sumZ_split]
    simpa only [f, Nat.add_comm] using (sumZ_add p w (fun t => w (t + p))).symm
  have hreindex : sumZ p (fun s => f (k * s % p)) = sumZ p f := by
    simpa [sumZ, List.map_map, Function.comp_def] using sumZ_perm ((phase_bijection hp hbp he).map f)
  have hsum := sumZ_cong (L := p) (fun s hs => paired_weight (by omega : 0 < p) hr hs hb he hthree hstrip hz)
  change Cong D (sumZ p (fun s => 3 * f (k * s % p)))
    (sumZ p (fun s => (2 * (3 : Int) ^ (2 * b)) * g s)) at hsum
  rw [← sumZ_mul, ← sumZ_mul, hreindex, ← hsplit] at hsum
  have hd := plus_gap_divides (Nat.le_of_lt hgap)
  have ha : 3 ^ oddCount n (2 * p) ≤ 2 ^ (2 * p) := by rw [hb]; exact Nat.le_of_lt hgap
  have harea := affine_weight_cong ha
  rw [hb] at harea
  have h := ((Cong.refl D 3).mul (harea.reduce hd)).trans hsum
  have hC := Int.ofNat_dvd.mpr (Nat.dvd_trans hd hdvd)
  have hscaled := h.dvd_iff.mp (Int.dvd_trans (Int.dvd_trans hC (Int.dvd_mul_left _ _)) (Int.dvd_mul_left _ _))
  have hroot : (D : Int) ∣ sumZ p g := cancel_coprime_factor hcop (by simpa using hscaled)
  have htrim : sumZ p g = sumZ (r + 1) g := by
    apply sumZ_trim (by omega)
    intro s hs hsp
    obtain ⟨_, _, _, _, _, _, _, _, hz₀⟩ := paired_lifts (by omega : 0 < p) hr hsp he hstrip
    obtain ⟨hf, hl⟩ := hz₀ (by omega)
    dsimp only [g, pairedCoefficient]
    rw [hf, hl]
    simp
  rwa [htrim] at hroot

private theorem paired_coefficient_range {n p b k c r s : Nat} (hp : 0 < p) (hr : r < p)
    (hs : s < p) (he : b * k + 1 = p * c)
    (hstrip : ∀ t, 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r) :
    (pairedCoefficient n p b k s).natAbs ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, hf, hl, _⟩ := paired_lifts hp hr hs he hstrip
  dsimp only [pairedCoefficient]
  rw [Int.natAbs_mul, Int.natAbs_pow]
  simp only [Int.natAbs_neg, Int.natAbs_one, Nat.one_pow, Nat.one_mul]
  generalize (reducedWalk n p b (k * s % p)).toNat / p = e₀ at hf ⊢
  generalize (reducedWalk n p b (k * s % p + p)).toNat / p = e₁ at hl ⊢
  omega

private theorem paired_coefficient_nonzero {n p b k c r : Nat} (hp : 1 < p) (hbp : b < p)
    (hr : r < p) (hb : oddCount n (2 * p) = 2 * b) (he : b * k + 1 = p * c)
    (h : AccIsCycleOf n (2 * p))
    (hleast : ∀ j, 0 < j → j < 2 * p → acceleratedOrbit j n ≠ n)
    (hstrip : ∀ t, 0 ≤ reducedWalk n p b t ∧ reducedWalk n p b t ≤ (p : Int) + r) :
    ∃ s, s ≤ r ∧ pairedCoefficient n p b k s ≠ 0 := by
  apply Classical.byContradiction
  intro hzero
  have hfold (t : Nat) (ht : t < p) : walk n (2 * p) (t + p) = walk n (2 * p) t := by
    have hmem := (phase_bijection hp hbp he).mem_iff.mpr (List.mem_range.mpr ht)
    obtain ⟨s, hsp, rfl⟩ := List.mem_map.mp hmem
    have hs := List.mem_range.mp hsp
    obtain ⟨_, _, _, _, hw₀, hw₁, _, _, hz⟩ := paired_lifts (by omega : 0 < p) hr hs he hstrip
    have heq :
        (reducedWalk n p b (k * s % p + p)).toNat / p = (reducedWalk n p b (k * s % p)).toNat / p := by
      by_cases hsr : r < s
      · exact (hz hsr).2.trans (hz hsr).1.symm
      have hz' : pairedCoefficient n p b k s = 0 := by
        apply Classical.byContradiction
        exact fun hn => hzero ⟨s, by omega, hn⟩
      have hsign : (-1 : Int) ^ (k * s / p) ≠ 0 := by
        intro ht
        have h₁ := sign_square (k * s / p)
        rw [ht] at h₁
        simp at h₁
      dsimp only [pairedCoefficient] at hz'
      have hd := (Int.mul_eq_zero.mp hz').resolve_left hsign
      omega
    rw [walk_eq_twice_reduced hb, walk_eq_twice_reduced hb, hw₀, hw₁, heq]
  obtain ⟨t, ht, hne⟩ := CycleArcSplit.exists_window_count_ne_of_least_period
    (b := b) h hleast (by omega : 0 < p) (by omega : p < 2 * p)
  have hwindow : walk n (2 * p) (t + p) = walk n (2 * p) t := by
    by_cases htp : t < p
    · exact hfold t htp
    have hh := hfold (t - p) (by omega)
    rw [show t - p + p = t by omega] at hh
    rw [show t + p = t - p + 2 * p by omega, walk_period h.2, hh]
  have hshift := walk_shift h.2 t p
  rw [hwindow, Int.sub_self] at hshift
  unfold walk at hshift
  rw [AccumulatorCap.oddCount_shift h.2 t, hb] at hshift
  apply hne
  have heq : 2 * p * oddCount (acceleratedOrbit t n) p = 2 * p * b := by
    have hZ : (2 * (p : Int)) * (oddCount (acceleratedOrbit t n) p : Int) =
        (2 * (p : Int)) * (b : Int) := by
      simp [Int.natCast_mul] at hshift
      grind
    exact_mod_cast hZ
  exact Nat.eq_of_mul_eq_mul_left (by omega) heq

private theorem trim_unit_root {r D : Nat} {P : Nat → Int} {z u : Int}
    (hD : 1 < D) (hu : Cong D (z * u) 1)
    (hP : ∀ i, i ≤ r → (P i).natAbs ≤ 1) (hnz : ∃ i, i ≤ r ∧ P i ≠ 0)
    (hroot : (D : Int) ∣ sumZ (r + 1) (fun i => P i * z ^ i)) :
    ∃ (d : Nat) (Q : Nat → Int), 0 < d ∧ d ≤ r ∧ Q 0 % 2 = 1 ∧ Q d % 2 = 1 ∧
      sumRange (d + 1) (fun i => (Q i).natAbs) ≤ r + 1 ∧
      (D : Int) ∣ PhaseResidueBox.evaluate (d + 1) Q z := by
  obtain ⟨l, ⟨hl, hPl⟩, hmin⟩ := Minimum.exists_min_lt hnz
  obtain ⟨h, hh, hPh, hmax⟩ := exists_last r hnz
  have hlh := hmin h ⟨hh, hPh⟩
  let d := h - l
  let Q := fun i => P (l + i)
  have hzero (i : Nat) (hi : i < l) : P i = 0 := by
    apply Classical.byContradiction
    intro hn
    have := hmin i ⟨by omega, hn⟩
    omega
  have hlow : sumZ l (fun i => P i * z ^ i) = 0 := by
    rw [sumZ_eq (g := fun _ => 0) (fun i hi => by simp [hzero i hi]), sumZ_zero]
  have htrim : sumZ (r + 1) (fun i => P i * z ^ i) =
      z ^ l * PhaseResidueBox.evaluate (d + 1) Q z := by
    rw [sumZ_trim (r := h + 1) (by omega) _ (fun i hi hir => by
      have hz : P i = 0 := Classical.byContradiction (hmax i (by omega) (by omega))
      rw [hz, Int.zero_mul]),
      show h + 1 = l + (d + 1) by dsimp [d]; omega, sumZ_split, hlow, Int.zero_add]
    change _ = z ^ l * sumZ (d + 1) (fun i => Q i * z ^ i)
    rw [sumZ_mul]
    apply sumZ_eq
    intro i _
    rw [Int.pow_add]
    unfold Q
    ac_rfl
  have hu' := hu.pow l
  rw [Int.mul_pow, Int.one_pow] at hu'
  have hQ := (unit_mul_dvd_iff hu').mp (htrim ▸ hroot)
  have hd : 0 < d := by
    apply Classical.byContradiction
    intro hn
    have he : d = 0 := by omega
    rw [he] at hQ
    change (D : Int) ∣ sumZ 1 (fun i => Q i * z ^ i) at hQ
    have hs : sumZ 1 (fun i => Q i * z ^ i) = Q 0 := by simp [sumZ]
    rw [hs] at hQ
    have hle := Int.natAbs_dvd_natAbs.mpr hQ
    have h₁ := hP l hl
    have h₂ : (Q 0).natAbs = 1 := by simpa [Q] using (show (P l).natAbs = 1 by omega)
    rw [h₂, Int.natAbs_natCast] at hle
    have := Nat.le_of_dvd (by decide : 0 < 1) hle
    omega
  refine ⟨d, Q, hd, by dsimp [d]; omega, ?_, ?_, ?_, hQ⟩
  · have := hP l hl
    simp only [Q, Nat.add_zero]
    omega
  · have := hP h hh
    have he : l + d = h := by dsimp [d]; omega
    simp only [Q, he]
    omega
  · have hm : sumRange (d + 1) (fun i => (Q i).natAbs) ≤ sumRange (d + 1) (fun _ => 1) := by
      apply sumRange_le
      intro i hi
      apply hP
      dsimp [d] at hi
      omega
    rw [sumRange_const, Nat.mul_one] at hm
    exact Nat.le_trans hm (by dsimp [d]; omega)

/-- A least cycle with two copies of each phase gives a signed polynomial
root modulo the sum of the two half-period powers. -/
theorem cycle_paired_phase_root {n p b r : Nat} (hn : 0 < n) (h : AccIsCycleOf n (2 * p))
    (hleast : ∀ i, 0 < i → i < 2 * p → acceleratedOrbit i n ≠ n)
    (hb : oddCount n (2 * p) = 2 * b) (hbp : b.Coprime p) (hr : r < p)
    (hw : ∀ i j, walk n (2 * p) i ≤ walk n (2 * p) j + (2 * p : Nat) + (2 * r : Nat)) :
    let D := 2 ^ p + 3 ^ b
    ∃ k c : Nat, ∃ z : Int, ∃ d : Nat, ∃ P : Nat → Int,
      (D : Int) ∣ (2 * (-1 : Int) ^ c) * z ^ b - 1 ∧
      (D : Int) ∣ (3 * (-1 : Int) ^ k) * z ^ p - 1 ∧
      0 < d ∧ d ≤ r ∧ P 0 % 2 = 1 ∧ P d % 2 = 1 ∧
      sumRange (d + 1) (fun i => (P i).natAbs) ≤ r + 1 ∧
      (D : Int) ∣ PhaseResidueBox.evaluate (d + 1) P z := by
  have ⟨hpos, hcount, hgap⟩ := accCycle_bounds hn h
  rw [hb] at hpos hcount hgap
  have hb₀ : 0 < b := by omega
  have hb₁ : b < p := by omega
  have hp : 1 < p := by omega
  let D := 2 ^ p + 3 ^ b
  have hd := plus_gap_divides (Nat.le_of_lt hgap)
  have hcop := gap_coprime_two_three hpos h.1 hgap
  have htwo : D.Coprime 2 := Nat.Coprime.coprime_dvd_left hd hcop.1
  have hthree : D.Coprime 3 := Nat.Coprime.coprime_dvd_left hd hcop.2
  obtain ⟨j, hj, _, hmin⟩ := exists_min_rotation h hw
  let x := acceleratedOrbit j n
  have hx : 0 < x := acceleratedOrbit_positive hn j
  have hcycle : AccIsCycleOf x (2 * p) := accIsCycleOf_orbit h j
  have hleast' (i : Nat) (hi : 0 < i) (hi' : i < 2 * p) : acceleratedOrbit i x ≠ x := by
    intro he
    have hback := congrArg (acceleratedOrbit (2 * p - j)) he
    change acceleratedOrbit (2 * p - j) (acceleratedOrbit i (acceleratedOrbit j n)) =
      acceleratedOrbit (2 * p - j) (acceleratedOrbit j n) at hback
    rw [acceleratedOrbit_add i, acceleratedOrbit_add, acceleratedOrbit_add,
      show 2 * p - j + (i + j) = i + 2 * p by omega, show 2 * p - j + j = 2 * p by omega,
      ← acceleratedOrbit_add, h.2] at hback
    exact hleast i hi hi' hback
  have hbx : oddCount x (2 * p) = 2 * b := (AccumulatorCap.oddCount_shift h.2 j).trans hb
  have hstrip (t : Nat) : 0 ≤ reducedWalk x p b t ∧ reducedWalk x p b t ≤ (p : Int) + r := by
    have ht := hmin t
    change 0 ≤ walk x (2 * p) t ∧ walk x (2 * p) t ≤ _ at ht
    rw [walk_eq_twice_reduced hbx] at ht
    simp only [Int.natCast_mul] at ht
    omega
  obtain ⟨k, c, _, he⟩ := exists_adjacent_phase hb₀ hp hbp
  obtain ⟨z, hz, h₂, h₃⟩ := exists_signed_unit hthree he
  let u := (2 * (-1 : Int) ^ c) * z ^ (b - 1)
  have hu : Cong D (z * u) 1 := by
    have hh : z * u = (2 * (-1 : Int) ^ c) * z ^ b := by
      have hpow : z ^ b = z ^ (b - 1) * z := by
        rw [← Int.pow_succ, show (b - 1).succ = b by omega]
      dsimp [u]
      rw [hpow]
      ac_rfl
    rw [hh]
    exact h₂
  have hD : 1 < D := by
    have h := Nat.one_lt_two_pow (n := p) (by omega)
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  have hdvd := CycleAccumulator.cycle_gap_dvd hx hcycle
  rw [hbx] at hdvd
  have hroot := paired_root hp hb₁ hr hbx he hgap (htwo.mul_right (hthree.pow_right (2 * b)))
    hthree hstrip hz hdvd
  obtain ⟨d, P, hd, hdr, hP₀, hPd, hmass, hP⟩ := trim_unit_root hD hu
    (fun s hs => paired_coefficient_range (by omega) hr (by omega : s < p) he hstrip)
    (paired_coefficient_nonzero hp hb₁ hr hbx he hcycle hleast' hstrip) hroot
  exact ⟨k, c, z, d, P, h₂, h₃, hd, hdr, hP₀, hPd, hmass, hP⟩

end Collatz.PhasePolynomial
