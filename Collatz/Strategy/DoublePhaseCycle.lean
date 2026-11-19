import Collatz.Strategy.CubicPhaseNorm

/-! With two copies of each discrepancy phase, two half-period return
equations force the same orbit point when the strip is sufficiently narrow. -/

namespace Collatz.DoublePhaseCycle

open Collatz.Arith Collatz.AccCycle Collatz.AffineExact Collatz.CyclicOrder Collatz.Sum
open Collatz.OneExtraCycle

private theorem weight_le_two_pow {p b t c : Nat} (hp : 0 < p) (ht : t ≤ p)
    (hgap : 3 ^ b ≤ 2 ^ p) (hcount : b * t ≤ p * c) :
    2 ^ t * 3 ^ (b - c) ≤ 2 ^ p := by
  have hexp : (b - c) * p ≤ b * (p - t) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm c p, Nat.mul_comm b p]
    omega
  have hpower : (3 : Nat) ^ ((b - c) * p) ≤ (3 ^ b) ^ (p - t) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) hexp
  apply (Nat.pow_le_pow_iff_left (by omega : p ≠ 0)).mp
  calc
    (2 ^ t * 3 ^ (b - c)) ^ p = (2 ^ p) ^ t * 3 ^ ((b - c) * p) := by
      rw [Nat.mul_pow, ← Nat.pow_mul 2 t p, ← Nat.pow_mul 2 p t, Nat.mul_comm t p,
        ← Nat.pow_mul 3 (b - c) p]
    _ ≤ (2 ^ p) ^ t * (3 ^ b) ^ (p - t) := Nat.mul_le_mul_left _ hpower
    _ ≤ (2 ^ p) ^ t * (2 ^ p) ^ (p - t) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgap _)
    _ = (2 ^ p) ^ p := by rw [← Nat.pow_add, Nat.add_sub_of_le ht]

private theorem indicator_le_one {f : Nat → Int} {p : Nat} (c : Int)
    (hinj : ∀ i j, i < p → j < p → f i = f j → i = j) :
    sumRange p (fun i => if f i = c then 1 else 0) ≤ 1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sumRange_succ]
    by_cases h : f p = c
    · rw [if_pos h, sumRange_congr (g := fun _ => 0) (fun i hi => if_neg (fun he => by
        have := hinj i p (by omega) (by omega) (he.trans h.symm)
        omega)), sumRange_const, Nat.mul_zero]
      decide
    · rw [if_neg h, Nat.add_zero]
      exact ih (fun i j hi hj he => hinj i j (by omega) (by omega) he)

private def areaWeight (x b i : Nat) : Nat := 2 ^ i * 3 ^ (b - oddCount x (i + 1))

private def exceptional (r : Nat → Int) (i : Nat) : Nat :=
  (if r i = 0 then 1 else 0) + (if r i = 1 then 1 else 0)

private theorem correction_close {x y p b : Nat} {r : Nat → Int} (hp : 0 < p)
    (hx : oddCount x p = b) (hy : oddCount y p = b) (hgap : 3 ^ b ≤ 2 ^ p)
    (hinj : ∀ i j, i < p → j < p → r i = r j → i = j)
    (hcounts : ∀ i, i < p →
      oddCount x (i + 1) = oddCount y (i + 1) ∨
        ((r i = 0 ∨ r i = 1) ∧
          (oddCount x (i + 1) + 1 = oddCount y (i + 1) ∨
            oddCount y (i + 1) + 1 = oddCount x (i + 1)) ∧
          b * (i + 1) ≤ p * max (oddCount x (i + 1)) (oddCount y (i + 1)))) :
    affineC p x ≤ affineC p y + 2 ^ p := by
  let B := (2 : Nat) ^ p
  have hE : sumRange p (exceptional r) ≤ 2 := by
    unfold exceptional
    rw [sumRange_add]
    have h₀ := indicator_le_one 0 hinj
    have h₁ := indicator_le_one 1 hinj
    omega
  have hterm (i : Nat) (hi : i < p) : areaWeight x b i ≤ areaWeight y b i + B * exceptional r i := by
    let u := oddCount x (i + 1)
    let v := oddCount y (i + 1)
    change 2 ^ i * 3 ^ (b - u) ≤ 2 ^ i * 3 ^ (b - v) + B * exceptional r i
    rcases Nat.le_total v u with hle | hge
    · have hmono := Nat.pow_le_pow_right (by decide : 0 < 3)
        (show b - u ≤ b - v by omega)
      exact Nat.le_trans (Nat.mul_le_mul_left _ hmono) (Nat.le_add_right _ _)
    · by_cases he : u = v
      · rw [he]
        exact Nat.le_add_right _ _
      · obtain ⟨hr, hd, hc⟩ := (hcounts i hi).resolve_left he
        have huv : u + 1 = v := by change u + 1 = v ∨ v + 1 = u at hd; omega
        have hvb : v ≤ b := by
          have hs := Discrepancy.oddCount_split (n := y) (j := i + 1) (L := p) (by omega)
          rw [hy] at hs
          change v ≤ b
          omega
        change b * (i + 1) ≤ p * max u v at hc
        rw [Nat.max_eq_right hge] at hc
        have hw := weight_le_two_pow hp (by omega : i + 1 ≤ p) hgap hc
        have hexp : b - u = b - v + 1 := by omega
        have hcount : 1 ≤ exceptional r i := by
          unfold exceptional
          rcases hr with hr | hr
          · simp [hr]
          · simp [hr]
        have hB := Nat.mul_le_mul_left B hcount
        rw [Nat.mul_one] at hB
        rw [Nat.pow_succ 2 i] at hw
        rw [hexp, Nat.pow_succ 3 (b - v)]
        calc
          _ = 2 ^ i * 3 ^ (b - v) + (2 ^ i * 2) * 3 ^ (b - v) := by grind
          _ ≤ _ := Nat.add_le_add_left (Nat.le_trans hw hB) _
  have hs := sumRange_le hterm
  rw [sumRange_add, sumRange_const_mul] at hs
  have hsum := Nat.mul_le_mul_left B hE
  have hareaX := affine_area x p
  have hareaY := affine_area y p
  rw [hx] at hareaX
  rw [hy] at hareaY
  change 2 * affineC p x + B = 3 ^ b + sumRange p (areaWeight x b) at hareaX
  change 2 * affineC p y + B = 3 ^ b + sumRange p (areaWeight y b) at hareaY
  rw [Nat.mul_comm B 2] at hsum
  change affineC p x ≤ affineC p y + B
  omega

private def reducedWalk (n p b t : Nat) : Int :=
  (p : Int) * (oddCount n t : Int) - (b : Int) * (t : Int)

private theorem reducedWalk_add (n p b s t : Nat) :
    reducedWalk n p b (s + t) = reducedWalk n p b s +
      ((p : Int) * (oddCount (acceleratedOrbit s n) t : Int) - (b : Int) * (t : Int)) := by
  unfold reducedWalk
  rw [AccumulatorArith.oddCount_add, Int.natCast_add, Int.natCast_add, Int.mul_add, Int.mul_add]
  omega

private theorem phase_same (n p b s t : Nat) :
    ((p : Int) ∣ reducedWalk n p b t - reducedWalk n p b s) ↔
      (p : Int) ∣ (b : Int) * ((t : Int) - (s : Int)) := by
  let X := (p : Int) * ((oddCount n t : Int) - (oddCount n s : Int))
  let Y := (b : Int) * ((t : Int) - (s : Int))
  have he : reducedWalk n p b t - reducedWalk n p b s = X - Y := by
    dsimp [reducedWalk, X, Y]
    rw [Int.mul_sub, Int.mul_sub]
    omega
  rw [he]
  have hX : (p : Int) ∣ X := Int.dvd_mul_right _ _
  constructor
  · intro hd
    have h := Int.dvd_sub hX hd
    rwa [show X - (X - Y) = Y by omega] at h
  · exact Int.dvd_sub hX

private theorem strip_step {p v w : Int} (hp : 2 < p) (hlo : 0 ≤ w) (hhi : v ≤ p + 1)
    (hlt : w < v) (hd : p ∣ v - w) : v = w + p ∧ w ≤ 1 := by
  have hle := Int.le_of_dvd (show 0 < v - w by omega) hd
  by_cases he : v - w = p
  · omega
  · have hpos : 0 < v - w - p := by omega
    have hbad := Int.le_of_dvd hpos (Int.dvd_sub hd (Int.dvd_refl p))
    omega

private theorem unique_height_two {p v : Int} (hp : 2 < p) (hlo : 0 ≤ v) (hhi : v ≤ p + 1)
    (hd : p ∣ v - 2) : v = 2 := by
  rcases Int.lt_trichotomy v 2 with hlt | he | hgt
  · have h' := Int.dvd_neg.mpr hd
    rw [show -(v - 2) = 2 - v by omega] at h'
    have := Int.le_of_dvd (show 0 < 2 - v by omega) h'
    omega
  · exact he
  · have := Int.le_of_dvd (show 0 < v - 2 by omega) hd
    omega

private theorem high_prefix {p b t u v : Nat} {X Y : Int} (hp : 2 < p)
    (hx : 0 ≤ X) (hy : Y ≤ (p : Int) + 1) (hlt : X < Y)
    (hd : (p : Int) ∣ Y - X)
    (hX : X = 2 + ((p : Int) * (u : Int) - (b : Int) * (t : Int)))
    (hY : Y = 2 + ((p : Int) * (v : Int) - (b : Int) * (t : Int))) :
    (X % (p : Int) = 0 ∨ X % (p : Int) = 1) ∧ u + 1 = v ∧ b * t ≤ p * v := by
  have hp' : 2 < (p : Int) := by omega
  obtain ⟨he, hlow⟩ := strip_step hp' hx hy hlt hd
  have hprod : (p : Int) * ((v : Int) - (u : Int)) = (p : Int) * 1 := by
    rw [Int.mul_sub, Int.mul_one]
    omega
  have hdiff := Int.eq_of_mul_eq_mul_left (show (p : Int) ≠ 0 by omega) hprod
  have hm : (b : Int) * (t : Int) ≤ (p : Int) * (v : Int) := by omega
  rw [Int.emod_eq_of_lt hx (by omega)]
  exact ⟨by omega, by omega, by exact_mod_cast hm⟩

private theorem prefix_comparison {p b t u v : Nat} {X Y : Int} (hp : 2 < p)
    (hx : 0 ≤ X ∧ X ≤ (p : Int) + 1) (hy : 0 ≤ Y ∧ Y ≤ (p : Int) + 1)
    (hd : (p : Int) ∣ Y - X)
    (hX : X = 2 + ((p : Int) * (u : Int) - (b : Int) * (t : Int)))
    (hY : Y = 2 + ((p : Int) * (v : Int) - (b : Int) * (t : Int))) :
    u = v ∨ ((X % (p : Int) = 0 ∨ X % (p : Int) = 1) ∧
      (u + 1 = v ∨ v + 1 = u) ∧ b * t ≤ p * max u v) := by
  rcases Int.lt_trichotomy X Y with hlt | he | hgt
  · obtain ⟨hr, hd, hb⟩ := high_prefix hp hx.1 hy.2 hlt hd hX hY
    exact Or.inr ⟨hr, Or.inl hd, by rw [Nat.max_eq_right (by omega : u ≤ v)]; exact hb⟩
  · left
    have hprod : (p : Int) * (u : Int) = (p : Int) * (v : Int) := by omega
    have h := Int.eq_of_mul_eq_mul_left (show (p : Int) ≠ 0 by omega) hprod
    exact Int.ofNat_inj.mp h
  · have hd' : (p : Int) ∣ X - Y := by simpa only [Int.neg_sub] using Int.dvd_neg.mpr hd
    have hr' : X % (p : Int) = Y % (p : Int) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hd')
    obtain ⟨hr, hd, hb⟩ := high_prefix hp hy.1 hx.2 hgt hd' hY hX
    rw [hr']
    exact Or.inr ⟨hr, Or.inr hd, by rw [Nat.max_eq_left (by omega : v ≤ u)]; exact hb⟩

private theorem period_fold {n p b : Nat} (hb : oddCount n (2 * p) = 2 * b) (t : Nat) :
    walk n (2 * p) t = 2 * reducedWalk n p b t := by
  unfold walk reducedWalk
  rw [hb, Int.natCast_mul, Int.natCast_mul]
  grind

private theorem reduced_start {x p b k c : Nat} (hp : 2 < p)
    (he : b * k + 1 = p * c)
    (hstrip : ∀ t, 0 ≤ reducedWalk x p b t ∧ reducedWalk x p b t ≤ (p : Int) + 1)
    (i : Nat) : reducedWalk x p b (2 * k + i * p) = 2 := by
  have heq : b * (2 * k + i * p) + 2 = p * (2 * c + b * i) := by
    calc
      _ = 2 * (b * k + 1) + p * (b * i) := by grind
      _ = _ := by rw [he, Nat.mul_add]; ac_rfl
  let t := 2 * k + i * p
  have htZ : (b : Int) * (t : Int) + 2 = (p : Int) * ((2 * c + b * i : Nat) : Int) := by
    exact_mod_cast heq
  apply unique_height_two (by omega : (2 : Int) < p) (hstrip t).1 (hstrip t).2
  refine ⟨(oddCount x t : Int) - ((2 * c + b * i : Nat) : Int), ?_⟩
  unfold reducedWalk
  rw [Int.mul_sub]
  omega

private theorem count_of_equal_height {x p b s : Nat} (hp : 0 < p)
    (h : reducedWalk x p b (s + p) = reducedWalk x p b s) :
    oddCount (acceleratedOrbit s x) p = b := by
  rw [reducedWalk_add, Int.mul_comm (b : Int) (p : Int)] at h
  have he : (p : Int) * (oddCount (acceleratedOrbit s x) p : Int) = (p : Int) * (b : Int) := by omega
  exact Int.ofNat_inj.mp (Int.eq_of_mul_eq_mul_left (show (p : Int) ≠ 0 by omega) he)

private theorem residue_inj {x p b s i j : Nat} (hcop : b.Coprime p) (hi : i < p) (hj : j < p)
    (he : reducedWalk x p b (s + (i + 1)) % (p : Int) =
      reducedWalk x p b (s + (j + 1)) % (p : Int)) : i = j := by
  have hd := Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)
  have h := (phase_same x p b (s + (j + 1)) (s + (i + 1))).mp hd
  rw [show ((s + (i + 1) : Nat) : Int) - ((s + (j + 1) : Nat) : Int) =
    (i : Int) - (j : Int) by omega] at h
  have h' := cancel_coprime_factor hcop.symm h
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have hh := Int.dvd_neg.mpr h'
    rw [show -((i : Int) - (j : Int)) = (j : Int) - (i : Int) by omega] at hh
    have := Int.le_of_dvd (show (0 : Int) < (j : Int) - (i : Int) by omega) hh
    omega
  · exact heq
  · have := Int.le_of_dvd (show (0 : Int) < (i : Int) - (j : Int) by omega) h'
    omega

/-- The case of two copies of each discrepancy phase is excluded by the
two half-period corrections alone. -/
theorem reachesOne_of_gcd_two_width_two {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hg : (oddCount n L).gcd L = 2)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + 2) : Reach.ReachesOne n := by
  by_cases hnr : Reach.ReachesOne n
  · exact hnr
  exfalso
  have hlong := CycleLength1539.length_ge_1539 hn h hnr
  have hdL : 2 ∣ L := by simpa only [hg] using Nat.gcd_dvd_right (oddCount n L) L
  obtain ⟨p, rfl⟩ := hdL
  have hda : 2 ∣ oddCount n (2 * p) := by
    simpa only [hg] using Nat.gcd_dvd_left (oddCount n (2 * p)) (2 * p)
  obtain ⟨b, hb⟩ := hda
  have hp : 2 < p := by omega
  have hbp : b.Coprime p := by
    rw [hb, Nat.gcd_mul_left] at hg
    change b.gcd p = 1
    omega
  have hcount := accCycle_bounds hn h
  have hgap : 3 ^ b < 2 ^ p := by
    apply (Nat.pow_lt_pow_iff_left (n := 2) (by decide)).mp
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm b 2, Nat.mul_comm p 2, ← hb]
    exact hcount.2.2
  obtain ⟨m, _, _, hm⟩ := PhasePolynomial.exists_min_rotation h hw
  let x := acceleratedOrbit m n
  have hx : AccIsCycleOf x (2 * p) := accIsCycleOf_orbit h m
  have hcountX : oddCount x (2 * p) = 2 * b :=
    (AccumulatorCap.oddCount_shift h.2 m).trans hb
  have hstrip (t : Nat) : 0 ≤ reducedWalk x p b t ∧ reducedWalk x p b t ≤ (p : Int) + 1 := by
    have ht := hm t
    change 0 ≤ walk x (2 * p) t ∧ walk x (2 * p) t ≤ _ at ht
    rw [period_fold hcountX, Int.natCast_mul, show ((2 : Nat) : Int) = 2 from rfl] at ht
    omega
  obtain ⟨k, c, _, he⟩ := PhasePolynomial.exists_adjacent_phase (by omega : 0 < b) (by omega : 1 < p) hbp
  let s := 2 * k
  let x₀ := acceleratedOrbit s x
  let x₁ := acceleratedOrbit (s + p) x
  have hstart (i : Nat) : reducedWalk x p b (s + i * p) = 2 := reduced_start hp he hstrip i
  have h₀ : reducedWalk x p b s = 2 := by simpa only [Nat.zero_mul, Nat.add_zero] using hstart 0
  have h₁ : reducedWalk x p b (s + p) = 2 := by simpa only [Nat.one_mul] using hstart 1
  have h₂ : reducedWalk x p b (s + p + p) = 2 := by
    rw [show s + p + p = s + 2 * p by omega]
    exact hstart 2
  have hx₀ : oddCount x₀ p = b := count_of_equal_height (by omega) (h₁.trans h₀.symm)
  have hx₁ : oddCount x₁ p = b := count_of_equal_height (by omega) (h₂.trans h₁.symm)
  let r := fun i : Nat => reducedWalk x p b (s + (i + 1)) % (p : Int)
  have hinj (i j : Nat) (hi : i < p) (hj : j < p) (hr : r i = r j) : i = j :=
    residue_inj hbp hi hj hr
  have hcomp (i : Nat) :
      oddCount x₀ (i + 1) = oddCount x₁ (i + 1) ∨
        ((r i = 0 ∨ r i = 1) ∧
          (oddCount x₀ (i + 1) + 1 = oddCount x₁ (i + 1) ∨
            oddCount x₁ (i + 1) + 1 = oddCount x₀ (i + 1)) ∧
          b * (i + 1) ≤ p * max (oddCount x₀ (i + 1)) (oddCount x₁ (i + 1))) := by
    let u := s + (i + 1)
    let v := s + p + (i + 1)
    have hd : (p : Int) ∣ reducedWalk x p b v - reducedWalk x p b u := by
      apply (phase_same x p b u v).mpr
      refine ⟨(b : Int), ?_⟩
      rw [show (v : Int) - (u : Int) = (p : Int) by dsimp [u, v]; omega, Int.mul_comm]
    have hu := reducedWalk_add x p b s (i + 1)
    have hv := reducedWalk_add x p b (s + p) (i + 1)
    rw [h₀] at hu
    rw [h₁] at hv
    exact prefix_comparison hp (hstrip u) (hstrip v) hd hu hv
  have hcomp' (i : Nat) :
      oddCount x₁ (i + 1) = oddCount x₀ (i + 1) ∨
        ((r i = 0 ∨ r i = 1) ∧
          (oddCount x₁ (i + 1) + 1 = oddCount x₀ (i + 1) ∨
            oddCount x₀ (i + 1) + 1 = oddCount x₁ (i + 1)) ∧
          b * (i + 1) ≤ p * max (oddCount x₁ (i + 1)) (oddCount x₀ (i + 1))) := by
    rcases hcomp i with hEq | ⟨hr, hd, hc⟩
    · exact Or.inl hEq.symm
    · exact Or.inr ⟨hr, hd.symm, by rw [Nat.max_comm]; exact hc⟩
  have hC₀ := correction_close (by omega) hx₀ hx₁ (Nat.le_of_lt hgap) hinj (fun i _ => hcomp i)
  have hC₁ := correction_close (by omega) hx₁ hx₀ (Nat.le_of_lt hgap) hinj (fun i _ => hcomp' i)
  have h01 : acceleratedOrbit p x₀ = x₁ := by
    dsimp [x₀, x₁]
    rw [acceleratedOrbit_add, Nat.add_comm p s]
  have h10 : acceleratedOrbit p x₁ = x₀ := by
    rw [← h01, acceleratedOrbit_add, show p + p = 2 * p by omega]
    exact (accIsCycleOf_orbit hx s).2
  have hA₀ := affine_exact x₀ p
  have hA₁ := affine_exact x₁ p
  rw [hx₀, h01] at hA₀
  rw [hx₁, h10] at hA₁
  have hfix : x₀ = x₁ := by
    have hclose {u v : Nat} (hlt : u < v) :
        2 ^ p * u + 2 ^ p ≤ 2 ^ p * v ∧ 3 ^ b * u + 3 ^ b ≤ 3 ^ b * v := by
      simpa only [Nat.mul_add, Nat.mul_one] using
        And.intro (Nat.mul_le_mul_left (2 ^ p) (show u + 1 ≤ v by omega))
          (Nat.mul_le_mul_left (3 ^ b) (show u + 1 ≤ v by omega))
    have ha := three_pow_pos b
    rcases Nat.lt_trichotomy x₀ x₁ with hlt | heq | hgt
    · obtain ⟨hB, hA⟩ := hclose hlt
      omega
    · exact heq
    · obtain ⟨hB, hA⟩ := hclose hgt
      omega
  have hshift : acceleratedOrbit (s + m) n = x₀ := (acceleratedOrbit_add s m n).symm
  have hsync : acceleratedOrbit (s + m) (acceleratedOrbit p n) = acceleratedOrbit (s + m) n := by
    rw [acceleratedOrbit_add (s + m) p n, Nat.add_comm (s + m) p,
      ← acceleratedOrbit_add p (s + m) n, hshift, h01, hfix]
  exact hleast p (by omega) (by omega) (CycleCollisionBudget.periodic_eq_of_synchronized
    ⟨2 * p, accIsCycleOf_orbit h p⟩ ⟨2 * p, h⟩ hsync)

/-- Under the integer power separation bound, every least positive cycle of
width at most `L+2` reaches one. -/
theorem reachesOne_of_width_two (hsep : PowerSeparation) {n L : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + 2) : Reach.ReachesOne n := by
  by_cases hr : Reach.ReachesOne n
  · exact hr
  · exact reachesOne_of_gcd_two_width_two hn h hleast
      (CubicPhaseNorm.gcd_eq_two_of_narrow_nonconvergent_cycle hsep hn h hleast hr hw) hw

/-- Under power separation, a nonconvergent least cycle needs discrepancy
width at least `L+3` within one period. -/
theorem nonconvergent_cycle_needs_width_three (hsep : PowerSeparation) {n L : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hnr : ¬ Reach.ReachesOne n) :
    ∃ i j, i < L ∧ j < L ∧ walk n L j + L + 3 ≤ walk n L i := by
  apply Classical.byContradiction
  intro hno
  apply hnr
  apply reachesOne_of_width_two hsep hn h hleast
  intro i j
  rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
  have hlt : ¬ walk n L (j % L) + L + 3 ≤ walk n L (i % L) := fun hge =>
    hno ⟨i % L, j % L, Nat.mod_lt _ h.1, Nat.mod_lt _ h.1, hge⟩
  omega

end Collatz.DoublePhaseCycle
