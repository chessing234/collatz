import Collatz.Structure.CycleMinClass

/-!
# Congruence descent beyond the factor of four

A forward-orbit minimum cannot be `1` modulo `4`, because two accelerated
steps send it to `(3m+1)/4`. The same comparison does not stay uniform
modulo `8`: `T³(7) = 26`. On six thinner arithmetic progressions the parity
word is constant again, and the exact affine image lies strictly below the
start for every term.

| class | word | image |
| --- | --- | --- |
| `m ≡ 3 (mod 16)` | `OOEE` | `(9m+5)/16` |
| `m ≡ 11 (mod 32)` | `OOEOE` | `(27m+23)/32` |
| `m ≡ 23 (mod 32)` | `OOOEE` | `(27m+19)/32` |
| `m ≡ 7 (mod 128)` | `OOOEOEE` | `(81m+73)/128` |
| `m ≡ 15 (mod 128)` | `OOOOEEE` | `(81m+65)/128` |
| `m ≡ 59 (mod 128)` | `OOEOOEE` | `(81m+85)/128` |

The numerator coefficient is `3` to the number of odd steps and the
denominator is `2` to the length of the word. Each word contracts. Together
with the existing constraint that a nontrivial cycle minimum is `7` or `11`
modulo `12`, the least point lies in `8` classes modulo `96` and in `26`
classes modulo `384`. Nothing here asserts that every orbit reaches one.
-/

namespace Collatz.DescentSieve

open Collatz.AccCycle Collatz.CycleMinClass

private theorem odd_image {k x y : Nat}
    (hpar : acceleratedOrbit k x % 2 = 1)
    (hval : 3 * acceleratedOrbit k x + 1 = 2 * y) :
    acceleratedOrbit (k + 1) x = y := by
  have hstep : acceleratedStep (acceleratedOrbit k x) = y := by
    rw [acceleratedStep, if_neg (by omega : ¬ acceleratedOrbit k x % 2 = 0), hval]
    exact Nat.mul_div_cancel_left _ (by decide)
  rw [acceleratedOrbit_succ_step, hstep]

private theorem even_image {k x y : Nat}
    (hpar : acceleratedOrbit k x % 2 = 0)
    (hval : acceleratedOrbit k x = 2 * y) :
    acceleratedOrbit (k + 1) x = y := by
  have hstep : acceleratedStep (acceleratedOrbit k x) = y := by
    rw [acceleratedStep, if_pos hpar, hval]
    exact Nat.mul_div_cancel_left _ (by decide)
  rw [acceleratedOrbit_succ_step, hstep]

private theorem split_residue {m modulus residue : Nat}
    (h : m % modulus = residue) : m = modulus * (m / modulus) + residue := by
  have hsplit := Nat.mod_add_div m modulus
  omega

private theorem div_image {steps modulus residue coeff const add s : Nat}
    (hpos : 0 < modulus)
    (horb : acceleratedOrbit steps (modulus * s + residue) = coeff * s + add)
    (hmul : coeff * (modulus * s + residue) + const = modulus * (coeff * s + add)) :
    acceleratedOrbit steps (modulus * s + residue) =
      (coeff * (modulus * s + residue) + const) / modulus := by
  rw [horb, hmul]
  exact (Nat.mul_div_cancel_left _ hpos).symm

/-- Modulo `8` the third step is not a descent: `7` climbs to `26`. -/
theorem third_image_of_seven : acceleratedOrbit 3 7 = 26 := by
  decide

theorem not_uniform_three_step_descent :
    ¬ ∀ m : Nat, m % 8 = 7 → acceleratedOrbit 3 m < m := by
  intro h
  have hlt := h 7 (by decide)
  rw [third_image_of_seven] at hlt
  omega

/-! ## Exact images -/

/-- Four steps on `16s+3` are the word `OOEE`, with image `9s+2`. -/
theorem orbit_four_mod_sixteen (s : Nat) :
    acceleratedOrbit 4 (16 * s + 3) = 9 * s + 2 := by
  let x := 16 * s + 3
  have hx : x = 16 * s + 3 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 24 * s + 5 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 36 * s + 8 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 18 * s + 4 := by
    refine even_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  refine even_image (by rw [h3]; omega) ?_
  rw [h3]
  omega

/-- `T⁴(m) = (9m+5)/16` whenever `m ≡ 3 (mod 16)`. -/
theorem four_step_image {m : Nat} (h : m % 16 = 3) :
    acceleratedOrbit 4 m = (9 * m + 5) / 16 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide) (orbit_four_mod_sixteen (m / 16)) (by omega)

theorem four_step_descent {m : Nat} (h : m % 16 = 3) :
    acceleratedOrbit 4 m < m := by
  have hm := split_residue h
  rw [hm, orbit_four_mod_sixteen]
  omega

/-- Five steps on `32s+11` are the word `OOEOE`, with image `27s+10`. -/
theorem orbit_five_mod_thirtytwo_eleven (s : Nat) :
    acceleratedOrbit 5 (32 * s + 11) = 27 * s + 10 := by
  let x := 32 * s + 11
  have hx : x = 32 * s + 11 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 48 * s + 17 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 72 * s + 26 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 36 * s + 13 := by
    refine even_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  have h4 : acceleratedOrbit 4 x = 54 * s + 20 := by
    refine odd_image (by rw [h3]; omega) ?_
    rw [h3]
    omega
  refine even_image (by rw [h4]; omega) ?_
  rw [h4]
  omega

/-- `T⁵(m) = (27m+23)/32` whenever `m ≡ 11 (mod 32)`. -/
theorem five_step_image_of_eleven {m : Nat} (h : m % 32 = 11) :
    acceleratedOrbit 5 m = (27 * m + 23) / 32 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide) (orbit_five_mod_thirtytwo_eleven (m / 32)) (by omega)

theorem five_step_descent_of_eleven {m : Nat} (h : m % 32 = 11) :
    acceleratedOrbit 5 m < m := by
  have hm := split_residue h
  rw [hm, orbit_five_mod_thirtytwo_eleven]
  omega

/-- Five steps on `32s+23` are the word `OOOEE`, with image `27s+20`. -/
theorem orbit_five_mod_thirtytwo_twentythree (s : Nat) :
    acceleratedOrbit 5 (32 * s + 23) = 27 * s + 20 := by
  let x := 32 * s + 23
  have hx : x = 32 * s + 23 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 48 * s + 35 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 72 * s + 53 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 108 * s + 80 := by
    refine odd_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  have h4 : acceleratedOrbit 4 x = 54 * s + 40 := by
    refine even_image (by rw [h3]; omega) ?_
    rw [h3]
    omega
  refine even_image (by rw [h4]; omega) ?_
  rw [h4]
  omega

/-- `T⁵(m) = (27m+19)/32` whenever `m ≡ 23 (mod 32)`. -/
theorem five_step_image_of_twentythree {m : Nat} (h : m % 32 = 23) :
    acceleratedOrbit 5 m = (27 * m + 19) / 32 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide) (orbit_five_mod_thirtytwo_twentythree (m / 32)) (by omega)

theorem five_step_descent_of_twentythree {m : Nat} (h : m % 32 = 23) :
    acceleratedOrbit 5 m < m := by
  have hm := split_residue h
  rw [hm, orbit_five_mod_thirtytwo_twentythree]
  omega

/-- Seven steps on `128s+7` are the word `OOOEOEE`, with image `81s+5`. -/
theorem orbit_seven_mod_onehundredtwentyeight_seven (s : Nat) :
    acceleratedOrbit 7 (128 * s + 7) = 81 * s + 5 := by
  let x := 128 * s + 7
  have hx : x = 128 * s + 7 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 192 * s + 11 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 288 * s + 17 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 432 * s + 26 := by
    refine odd_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  have h4 : acceleratedOrbit 4 x = 216 * s + 13 := by
    refine even_image (by rw [h3]; omega) ?_
    rw [h3]
    omega
  have h5 : acceleratedOrbit 5 x = 324 * s + 20 := by
    refine odd_image (by rw [h4]; omega) ?_
    rw [h4]
    omega
  have h6 : acceleratedOrbit 6 x = 162 * s + 10 := by
    refine even_image (by rw [h5]; omega) ?_
    rw [h5]
    omega
  refine even_image (by rw [h6]; omega) ?_
  rw [h6]
  omega

/-- `T⁷(m) = (81m+73)/128` whenever `m ≡ 7 (mod 128)`. -/
theorem seven_step_image_of_seven {m : Nat} (h : m % 128 = 7) :
    acceleratedOrbit 7 m = (81 * m + 73) / 128 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide)
    (orbit_seven_mod_onehundredtwentyeight_seven (m / 128)) (by omega)

theorem seven_step_descent_of_seven {m : Nat} (h : m % 128 = 7) :
    acceleratedOrbit 7 m < m := by
  have hm := split_residue h
  rw [hm, orbit_seven_mod_onehundredtwentyeight_seven]
  omega

/-- Seven steps on `128s+15` are the word `OOOOEEE`, with image `81s+10`. -/
theorem orbit_seven_mod_onehundredtwentyeight_fifteen (s : Nat) :
    acceleratedOrbit 7 (128 * s + 15) = 81 * s + 10 := by
  let x := 128 * s + 15
  have hx : x = 128 * s + 15 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 192 * s + 23 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 288 * s + 35 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 432 * s + 53 := by
    refine odd_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  have h4 : acceleratedOrbit 4 x = 648 * s + 80 := by
    refine odd_image (by rw [h3]; omega) ?_
    rw [h3]
    omega
  have h5 : acceleratedOrbit 5 x = 324 * s + 40 := by
    refine even_image (by rw [h4]; omega) ?_
    rw [h4]
    omega
  have h6 : acceleratedOrbit 6 x = 162 * s + 20 := by
    refine even_image (by rw [h5]; omega) ?_
    rw [h5]
    omega
  refine even_image (by rw [h6]; omega) ?_
  rw [h6]
  omega

/-- `T⁷(m) = (81m+65)/128` whenever `m ≡ 15 (mod 128)`. -/
theorem seven_step_image_of_fifteen {m : Nat} (h : m % 128 = 15) :
    acceleratedOrbit 7 m = (81 * m + 65) / 128 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide)
    (orbit_seven_mod_onehundredtwentyeight_fifteen (m / 128)) (by omega)

theorem seven_step_descent_of_fifteen {m : Nat} (h : m % 128 = 15) :
    acceleratedOrbit 7 m < m := by
  have hm := split_residue h
  rw [hm, orbit_seven_mod_onehundredtwentyeight_fifteen]
  omega

/-- Seven steps on `128s+59` are the word `OOEOOEE`, with image `81s+38`. -/
theorem orbit_seven_mod_onehundredtwentyeight_fiftynine (s : Nat) :
    acceleratedOrbit 7 (128 * s + 59) = 81 * s + 38 := by
  let x := 128 * s + 59
  have hx : x = 128 * s + 59 := rfl
  have h0 : acceleratedOrbit 0 x = x := rfl
  have h1 : acceleratedOrbit 1 x = 192 * s + 89 := by
    refine odd_image (by rw [h0, hx]; omega) ?_
    rw [h0, hx]
    omega
  have h2 : acceleratedOrbit 2 x = 288 * s + 134 := by
    refine odd_image (by rw [h1]; omega) ?_
    rw [h1]
    omega
  have h3 : acceleratedOrbit 3 x = 144 * s + 67 := by
    refine even_image (by rw [h2]; omega) ?_
    rw [h2]
    omega
  have h4 : acceleratedOrbit 4 x = 216 * s + 101 := by
    refine odd_image (by rw [h3]; omega) ?_
    rw [h3]
    omega
  have h5 : acceleratedOrbit 5 x = 324 * s + 152 := by
    refine odd_image (by rw [h4]; omega) ?_
    rw [h4]
    omega
  have h6 : acceleratedOrbit 6 x = 162 * s + 76 := by
    refine even_image (by rw [h5]; omega) ?_
    rw [h5]
    omega
  refine even_image (by rw [h6]; omega) ?_
  rw [h6]
  omega

/-- `T⁷(m) = (81m+85)/128` whenever `m ≡ 59 (mod 128)`. -/
theorem seven_step_image_of_fiftynine {m : Nat} (h : m % 128 = 59) :
    acceleratedOrbit 7 m = (81 * m + 85) / 128 := by
  have hm := split_residue h
  rw [hm]
  exact div_image (by decide)
    (orbit_seven_mod_onehundredtwentyeight_fiftynine (m / 128)) (by omega)

theorem seven_step_descent_of_fiftynine {m : Nat} (h : m % 128 = 59) :
    acceleratedOrbit 7 m < m := by
  have hm := split_residue h
  rw [hm, orbit_seven_mod_onehundredtwentyeight_fiftynine]
  omega

/-! ## Orbit minima -/

theorem not_orbitMin_of_descent {n m k : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hlt : acceleratedOrbit k m < m) : False := by
  obtain ⟨i, hi⟩ := hm
  have heq : acceleratedOrbit (k + i) n = acceleratedOrbit k m := by
    rw [← acceleratedOrbit_add, hi]
  exact Nat.not_le_of_gt (heq.symm ▸ hlt) (hmin (k + i))

/-- The least value of a forward orbit avoids every class in the ladder. -/
theorem orbitMin_avoids_descent_classes {n m : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) :
    m % 16 ≠ 3 ∧ m % 32 ≠ 11 ∧ m % 32 ≠ 23 ∧
      m % 128 ≠ 7 ∧ m % 128 ≠ 15 ∧ m % 128 ≠ 59 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact not_orbitMin_of_descent hm hmin (four_step_descent h)
  · intro h
    exact not_orbitMin_of_descent hm hmin (five_step_descent_of_eleven h)
  · intro h
    exact not_orbitMin_of_descent hm hmin (five_step_descent_of_twentythree h)
  · intro h
    exact not_orbitMin_of_descent hm hmin (seven_step_descent_of_seven h)
  · intro h
    exact not_orbitMin_of_descent hm hmin (seven_step_descent_of_fifteen h)
  · intro h
    exact not_orbitMin_of_descent hm hmin (seven_step_descent_of_fiftynine h)

/-! ## Cycle minima -/

/-- Classes modulo `96` still open after the four- and five-step descents
and the condition of being `7` or `11` modulo `12`. -/
def survives96 (r : Nat) : Bool :=
  ((r % 12 == 7) || (r % 12 == 11)) &&
    (r % 16 != 3) && (r % 32 != 11) && (r % 32 != 23)

/-- The eight admissible residues modulo `96`. -/
def admissible96 : List Nat := [7, 31, 47, 59, 71, 79, 91, 95]

theorem admissible96_filter :
    (List.range 96).filter survives96 = admissible96 := by
  decide

theorem admissible96_length : admissible96.length = 8 := by
  decide

/-- Classes modulo `384` still open after every descent in this file. -/
def survives384 (r : Nat) : Bool :=
  ((r % 12 == 7) || (r % 12 == 11)) &&
    (r % 16 != 3) && (r % 32 != 11) && (r % 32 != 23) &&
    (r % 128 != 7) && (r % 128 != 15) && (r % 128 != 59)

/-- The twenty-six admissible residues modulo `384`. -/
def admissible384 : List Nat :=
  [31, 47, 71, 79, 91, 95, 103, 127, 155, 167, 175, 191, 199, 223, 239, 251,
   283, 287, 295, 319, 335, 347, 359, 367, 379, 383]

theorem admissible384_filter :
    (List.range 384).filter survives384 = admissible384 := by
  decide

theorem admissible384_length : admissible384.length = 26 := by
  decide

/-- The modulo-twelve condition alone leaves `64` residues modulo `384`. -/
theorem twelve_class_count_mod_384 :
    ((List.range 384).filter fun r => (r % 12 == 7) || (r % 12 == 11)).length = 64 := by
  decide

private theorem survives96_iff (r : Nat) :
    survives96 r = true ↔
      (r % 12 = 7 ∨ r % 12 = 11) ∧ r % 16 ≠ 3 ∧ r % 32 ≠ 11 ∧ r % 32 ≠ 23 := by
  unfold survives96
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  constructor <;> intro h <;> grind

private theorem survives384_iff (r : Nat) :
    survives384 r = true ↔
      (r % 12 = 7 ∨ r % 12 = 11) ∧ r % 16 ≠ 3 ∧ r % 32 ≠ 11 ∧ r % 32 ≠ 23 ∧
        r % 128 ≠ 7 ∧ r % 128 ≠ 15 ∧ r % 128 ≠ 59 := by
  unfold survives384
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  constructor <;> intro h <;> grind

/-- A nontrivial least cycle point is one of eight residues modulo `96`. -/
theorem cycleMin_mod_96 {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hcyc : AccIsCycleOf m L) :
    m % 96 = 7 ∨ m % 96 = 31 ∨ m % 96 = 47 ∨ m % 96 = 59 ∨
      m % 96 = 71 ∨ m % 96 = 79 ∨ m % 96 = 91 ∨ m % 96 = 95 := by
  have havoid := orbitMin_avoids_descent_classes hm hmin
  have h96 : survives96 (m % 96) = true := by
    rw [survives96_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd m (by decide : 12 ∣ 96)]
      exact cycleMin_mod_twelve hn hm hmin hgt hcyc
    · rw [Nat.mod_mod_of_dvd m (by decide : 16 ∣ 96)]
      exact havoid.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 32 ∣ 96)]
      exact havoid.2.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 32 ∣ 96)]
      exact havoid.2.2.1
  have hmem : m % 96 ∈ admissible96 := by
    have hrange : m % 96 ∈ (List.range 96).filter survives96 := by
      rw [List.mem_filter, List.mem_range]
      exact ⟨Nat.mod_lt _ (by decide), h96⟩
    rwa [admissible96_filter] at hrange
  simpa [admissible96, List.mem_cons, List.mem_nil_iff, or_false] using hmem

/-- A nontrivial least cycle point is one of the twenty-six residues
modulo `384` that survive the whole ladder. -/
theorem cycleMin_mem_admissible384 {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hcyc : AccIsCycleOf m L) :
    m % 384 ∈ admissible384 := by
  have h12 := cycleMin_mod_twelve hn hm hmin hgt hcyc
  have havoid := orbitMin_avoids_descent_classes hm hmin
  have h384 : survives384 (m % 384) = true := by
    rw [survives384_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd m (by decide : 12 ∣ 384)]
      exact h12
    · rw [Nat.mod_mod_of_dvd m (by decide : 16 ∣ 384)]
      exact havoid.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 32 ∣ 384)]
      exact havoid.2.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 32 ∣ 384)]
      exact havoid.2.2.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 128 ∣ 384)]
      exact havoid.2.2.2.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 128 ∣ 384)]
      exact havoid.2.2.2.2.1
    · rw [Nat.mod_mod_of_dvd m (by decide : 128 ∣ 384)]
      exact havoid.2.2.2.2.2
  have hrange : m % 384 ∈ (List.range 384).filter survives384 := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨Nat.mod_lt _ (by decide), h384⟩
  rwa [admissible384_filter] at hrange

end Collatz.DescentSieve
