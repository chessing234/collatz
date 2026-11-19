import Collatz.Strategy.CycleNumericalWidth
import Collatz.Strategy.PhaseOrderCycle
import Collatz.Structure.CycleMaxClass
import Collatz.Strategy.PhasePolynomial

/-! A cycle in a sufficiently thin discrepancy strip can be represented
inside one ternary annulus. Its normalized dynamics use integer rounding. -/

namespace Collatz.RoundedPhaseCycle

open Collatz.AccCycle Collatz.CyclicOrder Collatz.Arith

/-- Round up after halving, and multiply by three when the rounded result
falls below the bottom of the annulus. -/
def step (K v : Nat) : Nat :=
  let q := (v + 1) / 2
  if q < K then 3 * q else q

/-- Iterate the rounded map from its annulus floor. -/
def roundedOrbit (K : Nat) : Nat → Nat
  | 0 => K
  | t + 1 => step K (roundedOrbit K t)

/-- Divide normalized values in the unlifted layer by three. -/
def decode (v : Nat) : Nat := if v % 3 = 0 then v / 3 else v

private def coordinate (x L t : Nat) : Nat :=
  if walk x L t < (L : Int) then 3 * acceleratedOrbit t x else acceleratedOrbit t x

private theorem endpoint_band {x L t : Nat} (hx : 0 < x) (h : AccIsCycleOf x L)
    (hcop : (oddCount x L).Coprime L)
    (hw : ∀ i j, walk x L i < walk x L j + 2 * (L : Int))
    (hlo : 0 ≤ walk x L t) (hhi : walk x L t < 2 * (L : Int)) :
    (walk x L t < L → x ≤ acceleratedOrbit t x ∧ acceleratedOrbit t x < 3 * x) ∧
    ((L : Int) ≤ walk x L t → 3 * x < acceleratedOrbit t x ∧ acceleratedOrbit t x < 9 * x) := by
  have hL := h.1
  have hmin : x ≤ acceleratedOrbit t x := by
    apply Nat.le_of_not_gt
    intro ht
    have hh := (PhaseOrderCycle.orbit_lt_iff_walk_lt_of_width_lt_twice h hw t 0).mp (by simpa using ht)
    simp at hh
    omega
  by_cases ht : t % L = 0
  · have hX := CycleExtremes.accOrbit_mod_period h.2 t
    rw [ht, acceleratedOrbit_zero] at hX
    have hW : walk x L t = 0 := by rw [walk_mod hL h.2, ht, walk_zero]
    rw [hW, hX]
    omega
  let a := oddCount x L
  let b := t * a / L
  let c := oddCount x t
  let s := t * a % L
  have hs₀ : s ≠ 0 := by
    intro hs
    have hd : L ∣ t * a := Nat.dvd_iff_mod_eq_zero.mpr hs
    exact ht (Nat.dvd_iff_mod_eq_zero.mp (hcop.symm.dvd_of_dvd_mul_right hd))
  have hs := Nat.mod_lt (t * a) hL
  change s < L at hs
  have hsum : L * b + s = t * a := Nat.div_add_mod _ _
  have hsumZ : (L : Int) * (b : Int) + (s : Int) = (t : Int) * (a : Int) := by exact_mod_cast hsum
  have hwalk : walk x L t = (L : Int) * c - ((L : Int) * b + s) := by
    unfold walk
    change (L : Int) * (c : Int) - (a : Int) * (t : Int) = _
    rw [Int.mul_comm (a : Int), ← hsumZ]
  obtain ⟨h₁, h₂⟩ := PhaseOrderCycle.endpoint_ratio_between_phase_powers h hw (p := t) hs₀
  change 3 ^ b * acceleratedOrbit t x < 3 ^ c * x at h₁
  change 3 ^ c * x < 3 ^ (b + 1) * acceleratedOrbit t x at h₂
  have hupper {k : Nat} (hc : c ≤ b + k) : acceleratedOrbit t x < 3 ^ k * x := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) hc
    have hh := Nat.lt_of_lt_of_le h₁ (Nat.mul_le_mul_right x hpow)
    rw [Nat.pow_add, Nat.mul_assoc] at hh
    exact Nat.lt_of_mul_lt_mul_left hh
  constructor
  · intro ht
    have hc : c ≤ b + 1 := by
      have hh : (L : Int) * c < (L : Int) * ((b + 2 : Nat) : Int) := by
        rw [Int.natCast_add, Int.mul_add]
        change (L : Int) * c < (L : Int) * b + (L : Int) * 2
        rw [Int.mul_comm (L : Int) 2]
        omega
      have hh' : L * c < L * (b + 2) := by exact_mod_cast hh
      have := Nat.lt_of_mul_lt_mul_left hh'
      omega
    exact ⟨hmin, by simpa using hupper (k := 1) hc⟩
  · intro ht
    have hc₁ : b + 2 ≤ c := by
      have hh : (L : Int) * ((b + 1 : Nat) : Int) < (L : Int) * c := by
        simp only [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]
        omega
      have hh' : L * (b + 1) < L * c := by exact_mod_cast hh
      have := Nat.lt_of_mul_lt_mul_left hh'
      omega
    have hc₂ : c ≤ b + 2 := by
      have hh : (L : Int) * c < (L : Int) * ((b + 3 : Nat) : Int) := by
        rw [Int.natCast_add, Int.mul_add]
        change (L : Int) * c < (L : Int) * b + (L : Int) * 3
        rw [Int.mul_comm (L : Int) 3]
        omega
      have hh' : L * c < L * (b + 3) := by exact_mod_cast hh
      have := Nat.lt_of_mul_lt_mul_left hh'
      omega
    have he : c = b + 1 + 1 := by omega
    rw [he, Nat.pow_succ, Nat.mul_assoc] at h₂
    exact ⟨Nat.lt_of_mul_lt_mul_left h₂, by simpa using hupper (k := 2) hc₂⟩

private theorem next_coordinate_choice {x L t : Nat}
    (heven : acceleratedOrbit t x % 2 = 0 → walk x L (t + 1) < (L : Int))
    (hodd : acceleratedOrbit t x % 2 = 1 → walk x L t < (L : Int)) :
    let q := (coordinate x L t + 1) / 2
    coordinate x L (t + 1) = q ∨ coordinate x L (t + 1) = 3 * q := by
  let X := acceleratedOrbit t x
  rcases mod_two_eq_zero_or_one X with he | ho
  · have hn := heven he
    have hs' : acceleratedOrbit (t + 1) x = X / 2 := by
      rw [acceleratedOrbit_succ_step]
      change acceleratedStep X = _
      rw [acceleratedStep, if_pos he]
    by_cases ht : walk x L t < (L : Int)
    · left
      simp only [coordinate, if_pos ht, if_pos hn, hs']
      change 3 * (X / 2) = (3 * X + 1) / 2
      omega
    · right
      simp only [coordinate, if_neg ht, if_pos hn, hs']
      change 3 * (X / 2) = 3 * ((X + 1) / 2)
      omega
  · have ht := hodd ho
    have hs' : acceleratedOrbit (t + 1) x = (3 * X + 1) / 2 := by
      rw [acceleratedOrbit_succ_step]
      change acceleratedStep X = _
      rw [acceleratedStep, if_neg (by omega)]
    by_cases hn : walk x L (t + 1) < (L : Int)
    · right
      simp only [coordinate, if_pos ht, if_pos hn, hs']
      rfl
    · left
      simp only [coordinate, if_pos ht, if_neg hn, hs']
      rfl

private theorem roundedOrbit_from_choices {x L : Nat} (hx : 0 < x) (h : AccIsCycleOf x L)
    (hcop : (oddCount x L).Coprime L)
    (hwidth : ∀ i j, walk x L i < walk x L j + 2 * (L : Int))
    (hfloor : ∀ t, 0 ≤ walk x L t)
    (heven : ∀ t, acceleratedOrbit t x % 2 = 0 → walk x L (t + 1) < (L : Int))
    (hodd : ∀ t, acceleratedOrbit t x % 2 = 1 → walk x L t < (L : Int)) :
    let K := 3 * x
    roundedOrbit K L = K ∧
    ∀ t, K ≤ roundedOrbit K t ∧ roundedOrbit K t < 3 * K ∧
      decode (roundedOrbit K t) = acceleratedOrbit t x := by
  let v := coordinate x L
  let K := 3 * x
  have hL := h.1
  have hzero : v 0 = K := by simp [v, coordinate, K, hL]
  have hret : v L = K := by simp [v, coordinate, K, hL, h.2]
  have hv (t : Nat) : K ≤ v t ∧ v t < 3 * K := by
    have hhi := hwidth t 0
    rw [walk_zero, Int.zero_add] at hhi
    obtain ⟨hlo, htop⟩ := endpoint_band hx h hcop hwidth (hfloor t) hhi
    by_cases he : walk x L t < L
    · have hb := hlo he
      dsimp only [v, coordinate, K]
      rw [if_pos he]
      omega
    · have hb := htop (Int.le_of_not_gt he)
      dsimp only [v, coordinate, K]
      rw [if_neg he]
      omega
  have hstep (t : Nat) : v (t + 1) = step K (v t) := by
    have hchoice := next_coordinate_choice (heven t) (hodd t)
    let q := (v t + 1) / 2
    change v (t + 1) = q ∨ v (t + 1) = 3 * q at hchoice
    change v (t + 1) = if q < K then 3 * q else q
    have hnext := hv (t + 1)
    split
    · exact hchoice.resolve_left (by omega)
    · exact hchoice.resolve_right (by omega)
  have heq (t : Nat) : roundedOrbit K t = v t := by
    induction t with
    | zero => exact hzero.symm
    | succ t ih => change step K (roundedOrbit K t) = v (t + 1); rw [ih, hstep]
  refine ⟨(heq L).trans hret, fun t => ?_⟩
  change K ≤ roundedOrbit K t ∧ roundedOrbit K t < 3 * K ∧ decode (roundedOrbit K t) = acceleratedOrbit t x
  rw [heq]
  refine ⟨(hv t).1, (hv t).2, ?_⟩
  by_cases ht : walk x L t < L
  · simp [v, coordinate, decode, ht]
  · have hc : AccIsCycleOf (acceleratedOrbit t x) L := accIsCycleOf_orbit h t
    have hnd := CycleModThree.not_three_dvd_of_accCycle (acceleratedOrbit_positive hx t) hc
    have hmod : acceleratedOrbit t x % 3 ≠ 0 := fun he => hnd (Nat.dvd_iff_mod_eq_zero.mpr he)
    simp [v, coordinate, decode, ht, hmod]

/-- Thin coprime cycles give an integer orbit of the rounded map in a
single ternary annulus, and the original orbit is recovered by division. -/
theorem exists_rounded_cycle {n L r : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hcop : (oddCount n L).Coprime L)
    (hra : r < oddCount n L) (hrL : oddCount n L + r < L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    ∃ j < L, ∃ v : Nat → Nat,
      let x := acceleratedOrbit j n
      let K := 3 * x
      v 0 = K ∧ v L = K ∧
      ∀ t, K ≤ v t ∧ v t < 3 * K ∧ v (t + 1) = step K (v t) ∧ decode (v t) = acceleratedOrbit t x := by
  obtain ⟨j, hj, _, hstrip⟩ := PhasePolynomial.exists_min_rotation h hw
  let x := acceleratedOrbit j n
  have hx : 0 < x := acceleratedOrbit_positive hn j
  have hX : AccIsCycleOf x L := accIsCycleOf_orbit h j
  have ha : oddCount x L = oddCount n L := AccumulatorCap.oddCount_shift h.2 j
  have hL := h.1
  have hwidth (i t : Nat) : walk x L i < walk x L t + 2 * (L : Int) := by
    have h₁ := (hstrip i).2
    have h₂ := (hstrip t).1
    change walk x L i ≤ _ at h₁
    change 0 ≤ walk x L t at h₂
    omega
  have hfloor (t : Nat) : 0 ≤ walk x L t := (hstrip t).1
  have heven (t : Nat) (he : acceleratedOrbit t x % 2 = 0) : walk x L (t + 1) < (L : Int) := by
    have ht := (hstrip t).2
    change walk x L t ≤ _ at ht
    have hs := NarrowCycle.walk_step x L t
    rw [he, Int.natCast_zero, Int.mul_zero, Int.zero_sub, ha] at hs
    omega
  have hodd (t : Nat) (ho : acceleratedOrbit t x % 2 = 1) : walk x L t < (L : Int) := by
    have ht := (hstrip (t + 1)).2
    change walk x L (t + 1) ≤ _ at ht
    have hs := NarrowCycle.walk_step x L t
    rw [ho, Int.natCast_one, Int.mul_one, ha] at hs
    omega
  obtain ⟨hret, hv⟩ := roundedOrbit_from_choices hx hX (ha.symm ▸ hcop) hwidth hfloor heven hodd
  exact ⟨j, hj, roundedOrbit (3 * x), rfl, hret,
    fun t => ⟨(hv t).1, (hv t).2.1, rfl, (hv t).2.2⟩⟩

/-- The rounded trajectory from the annulus floor has the same least
period as the original thin cycle. -/
theorem roundedOrbit_of_least_cycle {n L r : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t n ≠ n)
    (hcop : (oddCount n L).Coprime L)
    (hra : r < oddCount n L) (hrL : oddCount n L + r < L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    ∃ j < L,
      let x := acceleratedOrbit j n
      let K := 3 * x
      roundedOrbit K L = K ∧
      (∀ t, 0 < t → t < L → roundedOrbit K t ≠ K) ∧
      ∀ t, K ≤ roundedOrbit K t ∧ roundedOrbit K t < 3 * K ∧
        decode (roundedOrbit K t) = acceleratedOrbit t x ∧ x ≤ acceleratedOrbit t x := by
  obtain ⟨j, hj, v, hzero, hret, hv⟩ := exists_rounded_cycle hn h hcop hra hrL hw
  let x := acceleratedOrbit j n
  let K := 3 * x
  have heq (t : Nat) : roundedOrbit K t = v t := by
    induction t with
    | zero => exact hzero.symm
    | succ t ih =>
      change step K (roundedOrbit K t) = v (t + 1)
      rw [ih]
      exact (hv t).2.2.1.symm
  refine ⟨j, hj, (heq L).trans hret, ?_, ?_⟩
  · intro t ht htL he
    have ht' : v t = v 0 := (heq t).symm.trans (he.trans hzero.symm)
    have hback := (hv t).2.2.2.symm.trans ((congrArg decode ht').trans (hv 0).2.2.2)
    change acceleratedOrbit t x = x at hback
    apply hleast t ht htL
    apply CycleCollisionBudget.periodic_eq_of_synchronized
      ⟨L, accIsCycleOf_orbit h t⟩ ⟨L, h⟩ (d := j)
    rw [acceleratedOrbit_add, Nat.add_comm j t, ← acceleratedOrbit_add]
    exact hback
  · intro t
    change K ≤ roundedOrbit K t ∧ roundedOrbit K t < 3 * K ∧
      decode (roundedOrbit K t) = acceleratedOrbit t x ∧ x ≤ acceleratedOrbit t x
    rw [heq]
    refine ⟨(hv t).1, (hv t).2.1, (hv t).2.2.2, ?_⟩
    have hfloor : 3 * x ≤ v t := (hv t).1
    have hdecode : decode (v t) = acceleratedOrbit t x := (hv t).2.2.2
    unfold decode at hdecode
    split at hdecode <;> omega

private theorem nonnegative_walk_of_minimum {m L : Nat} (h : AccIsCycleOf m L)
    (hfloor : ∀ t, m ≤ acceleratedOrbit t m)
    (hw : ∀ i j, walk m L i < walk m L j + 2 * (L : Int)) (t : Nat) :
    0 ≤ walk m L t := by
  apply Int.le_of_not_gt
  intro ht
  have hh := (PhaseOrderCycle.orbit_lt_iff_walk_lt_of_width_lt_twice h hw t 0).mpr (by simpa using ht)
  rw [acceleratedOrbit_zero] at hh
  exact Nat.not_lt_of_ge (hfloor t) hh

/-- A least cycle starting at its minimum and staying below nine halves
of that minimum has the exact rounded representation. -/
theorem roundedOrbit_of_numerical_band {m L : Nat} (hm : 4 ≤ m) (h : AccIsCycleOf m L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t m ≠ m)
    (hfloor : ∀ t, m ≤ acceleratedOrbit t m)
    (hceiling : ∀ t, 2 * acceleratedOrbit t m < 9 * m) :
    let K := 3 * m
    roundedOrbit K L = K ∧
    (∀ t, 0 < t → t < L → roundedOrbit K t ≠ K) ∧
    ∀ t, K ≤ roundedOrbit K t ∧ roundedOrbit K t < 3 * K ∧
      decode (roundedOrbit K t) = acceleratedOrbit t m := by
  let M := CycleExtremes.cycleMax m L
  obtain ⟨j, _, hj⟩ := CycleExtremes.cycleMax_attained h
  have hM : M ≤ 6 * m := by
    have hh := hceiling j
    change M = acceleratedOrbit j m at hj
    rw [← hj] at hh
    omega
  have hw := CycleNumericalWidth.walk_width_lt_twice_of_sixfold h hleast hm hfloor
    (CycleExtremes.le_cycleMax h) hM
  have hcop := PhaseOrderCycle.coprime_of_width_lt_twice h hleast hw
  have hnonneg := nonnegative_walk_of_minimum h hfloor hw
  have hlift (t : Nat) (ht : (L : Int) ≤ walk m L t) : 3 * m < acceleratedOrbit t m := by
    have hhi := hw t 0
    rw [walk_zero, Int.zero_add] at hhi
    exact ((endpoint_band (by omega) h hcop hw (hnonneg t) hhi).2 ht).1
  have heven (t : Nat) (he : acceleratedOrbit t m % 2 = 0) : walk m L (t + 1) < (L : Int) := by
    apply Int.lt_of_not_ge
    intro ht
    have hh := hlift (t + 1) ht
    have hstep : 2 * acceleratedOrbit (t + 1) m = acceleratedOrbit t m := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos he]
      omega
    have htop := hceiling t
    omega
  have hodd (t : Nat) (ho : acceleratedOrbit t m % 2 = 1) : walk m L t < (L : Int) := by
    apply Int.lt_of_not_ge
    intro ht
    have hh := hlift t ht
    have hstep : 2 * acceleratedOrbit (t + 1) m = 3 * acceleratedOrbit t m + 1 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by omega)]
      omega
    have htop := hceiling (t + 1)
    omega
  obtain ⟨hret, hv⟩ := roundedOrbit_from_choices (by omega) h hcop hw hnonneg heven hodd
  refine ⟨hret, ?_, hv⟩
  intro t ht htL he
  have hd := (hv t).2.2
  rw [he] at hd
  exact hleast t ht htL (by simpa [decode] using hd.symm)

/-- A nontrivial least accelerated cycle reaches at least five above
three times its minimum. -/
theorem cycleMax_ge_triple_min_add_five {m L : Nat} (hm : 2 < m) (h : AccIsCycleOf m L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t m ≠ m)
    (hfloor : ∀ t, m ≤ acceleratedOrbit t m) :
    3 * m + 5 ≤ CycleExtremes.cycleMax m L := by
  let M := CycleExtremes.cycleMax m L
  have hm₄ : 4 ≤ m := by
    by_cases hm₃ : m = 3
    · have ht : acceleratedOrbit 5 m = 1 := by rw [hm₃]; decide
      have hh := hfloor 5
      omega
    · omega
  have htop : 3 * m < M := by
    apply Nat.lt_of_not_ge
    intro hM
    have hw := CycleNumericalWidth.walk_width_lt_twice_of_sixfold h hleast hm₄ hfloor
      (CycleExtremes.le_cycleMax h) (by omega : M ≤ 6 * m)
    have hcop := PhaseOrderCycle.coprime_of_width_lt_twice h hleast hw
    have hlo := nonnegative_walk_of_minimum h hfloor hw
    obtain ⟨i, j, _, _, hwide⟩ := OneExtraCycle.nontrivial_cycle_needs_extra_width (by omega) h hleast hm
    have hlift : (L : Int) ≤ walk m L i := by have := hlo j; omega
    have hhi := hw i 0
    rw [walk_zero, Int.zero_add] at hhi
    have hh := ((endpoint_band (by omega) h hcop hw (hlo i) hhi).2 hlift).1
    have hMi : acceleratedOrbit i m ≤ M := CycleExtremes.le_cycleMax h i
    omega
  have hmod : M % 6 = 2 := CycleMaxClass.cycleMax_mod_six (by omega) h
  have hodd : m % 2 = 1 := accCycleMin_odd (by omega) ⟨0, rfl⟩ hfloor
  change 3 * m + 5 ≤ M
  omega

/-- A least cycle whose values stay within ratio `43/7` has coprime
period and odd count. -/
theorem coprime_of_numerical_ratio_43_7 {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t n ≠ n)
    (hm : 4 ≤ m) (hlo : ∀ t, m ≤ acceleratedOrbit t n) (hhi : ∀ t, acceleratedOrbit t n ≤ M)
    (hM : 7 * M ≤ 43 * m) : (oddCount n L).Coprime L := by
  have hw := CycleNumericalWidth.walk_width_lt_twice_of_ratio_43_7 h hleast hm hlo hhi hM
  exact PhaseOrderCycle.coprime_of_width_lt_twice h hleast hw

/-- A least cycle whose values stay within ratio `56/9` has coprime
period and odd count. -/
theorem coprime_of_numerical_ratio_56_9 {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t n ≠ n)
    (hm : 19 ≤ m) (hlo : ∀ t, m ≤ acceleratedOrbit t n) (hhi : ∀ t, acceleratedOrbit t n ≤ M)
    (hM : 9 * M ≤ 56 * m) : (oddCount n L).Coprime L := by
  have hw := CycleNumericalWidth.walk_width_lt_twice_of_ratio_56_9 h hleast hm hlo hhi hM
  exact PhaseOrderCycle.coprime_of_width_lt_twice h hleast hw

/-- A shared divisor of the period and the odd count forces the cycle to
leave every band of ratio `43/7`. -/
theorem repeated_phase_ratio_43_7 {m L : Nat} (hm : 4 ≤ m) (h : AccIsCycleOf m L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t m ≠ m)
    (hfloor : ∀ t, m ≤ acceleratedOrbit t m)
    (hg : 1 < (oddCount m L).gcd L) :
    43 * m + 1 ≤ 7 * CycleExtremes.cycleMax m L := by
  let M := CycleExtremes.cycleMax m L
  have hnot : ¬ 7 * M ≤ 43 * m := by
    intro hM
    have hw := CycleNumericalWidth.walk_width_lt_twice_of_ratio_43_7 h hleast hm hfloor
      (CycleExtremes.le_cycleMax h) hM
    obtain ⟨i, j, _, _, hwide⟩ := PhaseOrderCycle.repeated_phase_width_ge_twice h hleast hg
    exact Int.not_lt_of_ge hwide (hw i j)
  omega

/-- For a larger floor the same obstruction reaches ratio `56/9`. -/
theorem repeated_phase_ratio_56_9 {m L : Nat} (hm : 19 ≤ m) (h : AccIsCycleOf m L)
    (hleast : ∀ t, 0 < t → t < L → acceleratedOrbit t m ≠ m)
    (hfloor : ∀ t, m ≤ acceleratedOrbit t m)
    (hg : 1 < (oddCount m L).gcd L) :
    56 * m + 1 ≤ 9 * CycleExtremes.cycleMax m L := by
  let M := CycleExtremes.cycleMax m L
  have hnot : ¬ 9 * M ≤ 56 * m := by
    intro hM
    have hw := CycleNumericalWidth.walk_width_lt_twice_of_ratio_56_9 h hleast hm hfloor
      (CycleExtremes.le_cycleMax h) hM
    obtain ⟨i, j, _, _, hwide⟩ := PhaseOrderCycle.repeated_phase_width_ge_twice h hleast hg
    exact Int.not_lt_of_ge hwide (hw i j)
  omega

end Collatz.RoundedPhaseCycle
