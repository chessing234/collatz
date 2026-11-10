import Collatz.Strategy.ExcursionLattice

/-!
# Mixed residue floors for excursion products

An excursion source has a dyadic residue from its own odd-run length.
If it has a recorded predecessor, the predecessor's run supplies a
second residue modulo a power of three. Together these can raise the
lower bound on an individual source before the product is estimated.
-/

namespace Collatz.ExcursionMixedGrid

open Collatz.ExcursionMap Collatz.LiftExponent Collatz.ExcursionLattice Collatz.ExcursionBudget

private theorem dyadic_dvd_difference {x b v : Nat}
    (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v) (hxb : x ≤ b) :
    2 ^ (v + 1) ∣ b - x := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨w, hw, hbw⟩ := hb
  have huw : u ≤ w := Nat.le_of_mul_le_mul_left (by omega) (Nat.two_pow_pos v)
  have htwo : 2 ∣ w - u := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨k, hk⟩ := htwo
  have hdiff : 2 ^ v * (w - u) = b - x := by
    rw [Nat.mul_sub_left_distrib, ← hxu, ← hbw]
    omega
  rw [← hdiff, hk, ← Nat.mul_assoc, ← Nat.pow_succ]
  exact Nat.dvd_mul_right _ _

/-- A ternary divisor is unaffected by a dyadic factor. -/
theorem cancel_dyadic {v W z : Nat} (h : 3 ^ v ∣ 2 ^ W * z) :
    3 ^ v ∣ z := by
  have hgcd : Nat.gcd (3 ^ v) (2 ^ W) = 1 := Nat.pow_gcd_pow_of_gcd_eq_one (by decide)
  have hcancel := (Nat.dvd_gcd_mul_iff_dvd_mul).mpr h
  simpa only [hgcd, Nat.one_mul] using hcancel

/-- The common dyadic residue and scaled ternary residue give a joint period. -/
theorem mixed_period_dvd_difference {x b v p W : Nat}
    (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v) (hxb : x ≤ b)
    (ht : 3 ^ p ∣ 2 ^ W * (b - x)) : 2 ^ (v + 1) * 3 ^ p ∣ b - x := by
  obtain ⟨k, hk⟩ := dyadic_dvd_difference hx hb hxb
  have h3 := cancel_dyadic ht
  rw [hk] at h3
  obtain ⟨l, hl⟩ := cancel_dyadic h3
  refine ⟨l, ?_⟩
  rw [hk, hl, Nat.mul_assoc]

/-- Given a candidate point in both residue classes and less than one mixed
period above the floor, every admissible actual source is at least that point. -/
theorem mixed_floor {m x b v p W : Nat} (hfloor : m ≤ x)
    (hx : Val2 (x + 1) v) (hb : Val2 (b + 1) v)
    (hxin : 3 ^ p ∣ 2 ^ W * x + 1) (hbin : 3 ^ p ∣ 2 ^ W * b + 1)
    (hwindow : b < m + 2 ^ (v + 1) * 3 ^ p) : b ≤ x := by
  by_cases hxb : x < b
  · have ht := Nat.dvd_sub hbin hxin
    rw [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib] at ht
    have hperiod := mixed_period_dvd_difference hx hb (Nat.le_of_lt hxb) ht
    have hle := Nat.le_of_dvd (by omega : 0 < b - x) hperiod
    omega
  · exact Nat.le_of_not_gt hxb

/-- The incoming congruence is part of every exact excursion equation. -/
theorem landing_congruence {z p u W x : Nat} (h : IsExcursion z p u W x) :
    3 ^ p ∣ 2 ^ W * x + 1 :=
  ⟨u, h.2.2.2.2.2.2.symm⟩

/-- A list of candidate lower sources. The first source uses the dyadic
floor, and each later source comes with a certificate for both residues. -/
inductive Floors (m : Nat) : List Run → List Visit → Prop where
  | nil : Floors m [] []
  | first {v W : Nat} : Floors m [⟨v, W⟩] [⟨v, classBase m v⟩]
  | next {v W b : Nat} {prev : Run} {rs : List Run} {bs : List Visit} :
      Floors m (prev :: rs) bs →
      m ≤ b → Val2 (b + 1) v →
      3 ^ prev.oddSteps ∣ 2 ^ prev.halvings * b + 1 →
      b < m + 2 ^ (v + 1) * 3 ^ prev.oddSteps →
      Floors m (⟨v, W⟩ :: prev :: rs) (⟨v, b⟩ :: bs)

/-- Lower one source in the cross-multiplied comparison of visit products. -/
theorem compare_cons {v x b : Nat} {vs bs : List Visit} (hb : b ≤ x)
    (hprev : (vs.map Visit.numerator).prod * (bs.map Visit.source).prod ≤
      (vs.map Visit.source).prod * (bs.map Visit.numerator).prod) :
    ((⟨v, x⟩ :: vs).map Visit.numerator).prod * ((⟨v, b⟩ :: bs).map Visit.source).prod ≤
      ((⟨v, x⟩ :: vs).map Visit.source).prod * ((⟨v, b⟩ :: bs).map Visit.numerator).prod := by
  let a := 3 ^ v
  let c := a - 2 ^ v
  change (a * x + c) * (vs.map Visit.numerator).prod * (b * (bs.map Visit.source).prod) ≤
    x * (vs.map Visit.source).prod * ((a * b + c) * (bs.map Visit.numerator).prod)
  calc
    _ = ((a * x + c) * b) * ((vs.map Visit.numerator).prod * (bs.map Visit.source).prod) := by
      ac_rfl
    _ ≤ (x * (a * b + c)) * ((vs.map Visit.source).prod * (bs.map Visit.numerator).prod) :=
      Nat.mul_le_mul (cross_factor a c hb) hprev
    _ = x * (vs.map Visit.source).prod * ((a * b + c) * (bs.map Visit.numerator).prod) := by
      ac_rfl

/-- A previous excursion certifies the incoming residue of its endpoint. -/
theorem trace_incoming {n x : Nat} {r : Run} {rs : List Run} (h : Trace n x (r :: rs)) :
    3 ^ r.oddSteps ∣ 2 ^ r.halvings * x + 1 := by
  cases h with
  | step _ hrun => exact landing_congruence hrun

/-- The individually certified lower sources majorize the exact product. -/
theorem Floors.compare {m n e : Nat} {rs : List Run} {bs : List Visit} (hc : Floors m rs bs)
    (ht : Trace n e rs) (hm : ∀ r ∈ visits n rs, m ≤ r.source) :
    ((visits n rs).map Visit.numerator).prod * (bs.map Visit.source).prod ≤
      ((visits n rs).map Visit.source).prod * (bs.map Visit.numerator).prod := by
  induction hc generalizing e with
  | nil => simp [visits]
  | first =>
    cases ht with
    | step hp hrun =>
      rw [visits, hp.landing] at hm ⊢
      have hfloor := hm _ List.mem_cons_self
      exact compare_cons (classBase_le_source hrun hfloor) (by simp [visits])
  | next hc _ hval hin hwindow ih =>
    cases ht with
    | step hp hrun =>
      rw [visits, hp.landing] at hm ⊢
      have hx := mixed_floor (hm _ List.mem_cons_self) (val2_succ_of hrun) hval
        (trace_incoming hp) hin hwindow
      exact compare_cons hx (ih hp (fun r hr => hm r (List.mem_cons_of_mem _ hr)))

/-- A strict violation of the mixed residue product bound gives descent. -/
theorem drop_of_mixed_floors {m n e : Nat} {rs : List Run} {bs : List Visit}
    (h : Trace n e rs) (hc : Floors m rs bs) (hn : 0 < n) (hm : 0 < m)
    (hfloor : ∀ r ∈ visits n rs, m ≤ r.source)
    (hgap : (bs.map Visit.numerator).prod < 2 ^ time rs * (bs.map Visit.source).prod) :
    e < n := by
  apply Nat.lt_of_not_ge
  intro hkeep
  exact Nat.not_lt_of_ge (trace_denominator_le h hn hkeep
    (fun r hr => Nat.lt_of_lt_of_le hm (hfloor r hr)) (hc.compare h hfloor)) hgap

/-- The same certificate forces a descent for every source at least the
specified floor whose trace has the given run lengths and halving counts. -/
theorem descent_of_mixed_floors {m n e : Nat} {rs : List Run} {bs : List Visit}
    (h : Trace n e rs) (hc : Floors m rs bs) (hm : 0 < m) (hmn : m ≤ n)
    (hgap : (bs.map Visit.numerator).prod < 2 ^ time rs * (bs.map Visit.source).prod) :
    ∃ j ≤ time rs, Collatz.acceleratedOrbit j n < n := by
  apply Classical.byContradiction
  intro hno
  have hfloor : ∀ r ∈ visits n rs, m ≤ r.source := by
    intro r hr
    obtain ⟨j, hj, heq⟩ := visit_time hr
    rw [heq]
    exact Nat.le_trans hmn (Nat.le_of_not_gt (fun hd => hno ⟨j, hj, hd⟩))
  have hd := drop_of_mixed_floors h hc (Nat.lt_of_lt_of_le hm hmn) hm hfloor hgap
  exact hno ⟨time rs, Nat.le_refl _, h.landing.symm ▸ hd⟩

end Collatz.ExcursionMixedGrid
