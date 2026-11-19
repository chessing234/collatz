import Collatz.Core.Pigeonhole
import Collatz.Core.Sum
import Init.Data.List.Nat.Range
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Rat.Lemmas

/-! A box of bounded coefficient vectors has a finite capacity modulo
a power gap. The proof encodes its coordinates with varying radices. -/

namespace Collatz.PhaseResidueBox

/-- Number of integer vectors in a box with coordinate bounds `[-b i,b i]`. -/
def size : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | n + 1, b => (2 * b 0 + 1) * size n (fun i => b (i + 1))

private def digit (b : Nat) (x : Int) : Nat := (x + (b : Int)).toNat

private def code : Nat → (Nat → Nat) → (Nat → Int) → Nat
  | 0, _, _ => 0
  | n + 1, b, x => digit (b 0) (x 0) + (2 * b 0 + 1) *
      code n (fun i => b (i + 1)) (fun i => x (i + 1))

/-- Each coordinate is bounded in absolute value by the corresponding radius. -/
def InBox (n : Nat) (b : Nat → Nat) (x : Nat → Int) : Prop :=
  ∀ i, i < n → -(b i : Int) ≤ x i ∧ x i ≤ (b i : Int)

private theorem digit_lt {b : Nat} {x : Int} (h : -(b : Int) ≤ x ∧ x ≤ b) :
    digit b x < 2 * b + 1 := by
  unfold digit
  omega

private theorem digit_inj {b : Nat} {x y : Int} (hx : -(b : Int) ≤ x) (hy : -(b : Int) ≤ y)
    (he : digit b x = digit b y) : x = y := by
  unfold digit at he
  omega

private theorem tail_in_box {n : Nat} {b : Nat → Nat} {x : Nat → Int} (h : InBox (n + 1) b x) :
    InBox n (fun i => b (i + 1)) (fun i => x (i + 1)) :=
  fun i hi => h (i + 1) (by omega)

private theorem code_lt {n : Nat} {b : Nat → Nat} {x : Nat → Int} (hx : InBox n b x) :
    code n b x < size n b := by
  induction n generalizing b x with
  | zero => simp [code, size]
  | succ n ih =>
    rw [code, size]
    have hd := digit_lt (hx 0 (by omega))
    have ht := ih (tail_in_box hx)
    have hm := Nat.mul_le_mul_left (2 * b 0 + 1) (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at hm
    omega

private theorem code_inj {n : Nat} {b : Nat → Nat} {x y : Nat → Int}
    (hx : InBox n b x) (hy : InBox n b y) (he : code n b x = code n b y) :
    ∀ i, i < n → x i = y i := by
  induction n generalizing b x y with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [code, code] at he
    let B := 2 * b 0 + 1
    have hd₁ : digit (b 0) (x 0) < B := digit_lt (hx 0 (by omega))
    have hd₂ : digit (b 0) (y 0) < B := digit_lt (hy 0 (by omega))
    have hmod := congrArg (fun k : Nat => k % B) he
    change (digit (b 0) (x 0) + B * _) % B = (digit (b 0) (y 0) + B * _) % B at hmod
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd₁,
      Nat.mod_eq_of_lt hd₂] at hmod
    have hhead := digit_inj (hx 0 (by omega)).1 (hy 0 (by omega)).1 hmod
    have htail : code n (fun i => b (i + 1)) (fun i => x (i + 1)) =
        code n (fun i => b (i + 1)) (fun i => y (i + 1)) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < B by dsimp [B]; omega)
      rw [hmod] at he
      exact Nat.add_left_cancel he
    intro i hi
    cases i with
    | zero => exact hhead
    | succ i => exact ih (tail_in_box hx) (tail_in_box hy) htail i (by omega)

private def sumI (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).sum

/-- Evaluate an integer coefficient vector at `z`. -/
def evaluate (n : Nat) (x : Nat → Int) (z : Int) : Int := sumI n (fun i => x i * z ^ i)

private theorem eval_congr {n : Nat} {x y : Nat → Int} {z : Int}
    (h : ∀ i, i < n → x i = y i) : evaluate n x z = evaluate n y z := by
  unfold evaluate sumI
  rw [List.map_congr_left (g := fun i => y i * z ^ i)
    (fun i hi => by rw [h i (List.mem_range.mp hi)])]

/-- If every residue has a representative in the coefficient box, the
modulus is at most the box capacity. -/
theorem modulus_le_size {D n : Nat} {b : Nat → Nat} {z : Int}
    (hcover : ∀ k : Nat, k < D → ∃ x, InBox n b x ∧ evaluate n x z % (D : Int) = (k : Int)) :
    D ≤ size n b := by
  by_cases hle : D ≤ size n b
  · exact hle
  let rep := fun (k : Nat) (hk : k < D) => (hcover k hk).choose
  let f := fun k : Nat => if hk : k < D then code n b (rep k hk) else 0
  have hrep (k : Nat) (hk : k < D) : InBox n b (rep k hk) ∧
      evaluate n (rep k hk) z % (D : Int) = (k : Int) := (hcover k hk).choose_spec
  obtain ⟨i, j, hij, hj, he⟩ := Pigeonhole.exists_repeat (f := f) (B := size n b)
    (N := size n b) (fun k hk => by
      have ht : k < D := by omega
      change (if ht' : k < D then code n b (rep k ht') else 0) < size n b
      rw [dif_pos ht]
      exact code_lt (hrep k ht).1) (Nat.le_refl _)
  have hiD : i < D := by omega
  have hjD : j < D := by omega
  have hc : code n b (rep i hiD) = code n b (rep j hjD) := by
    simpa only [f, dif_pos hiD, dif_pos hjD] using he
  have hv : evaluate n (rep i hiD) z = evaluate n (rep j hjD) z :=
    eval_congr (code_inj (hrep i hiD).1 (hrep j hjD).1 hc)
  have hi := (hrep i hiD).2
  have hj := (hrep j hjD).2
  rw [hv, hj] at hi
  omega

open Collatz.Sum

private def sumQ (n : Nat) (f : Nat → Rat) : Rat := ((List.range n).map f).sum

private theorem sumI_succ (n : Nat) (f : Nat → Int) : sumI (n + 1) f = sumI n f + f n := by
  simp [sumI, List.range_succ, List.sum_append]

private theorem sumQ_succ (n : Nat) (f : Nat → Rat) : sumQ (n + 1) f = sumQ n f + f n := by
  simp [sumQ, List.range_succ, List.sum_append, Rat.add_zero]

private theorem sumI_sub (n : Nat) (f g : Nat → Int) :
    sumI n (fun i => f i - g i) = sumI n f - sumI n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumI_succ, sumI_succ, sumI_succ, ih]; omega

private theorem sumI_add (n : Nat) (f g : Nat → Int) :
    sumI n (fun i => f i + g i) = sumI n f + sumI n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumI_succ, sumI_succ, sumI_succ, ih]; omega

private theorem sumI_mul (n : Nat) (a : Int) (f : Nat → Int) :
    sumI n (fun i => a * f i) = a * sumI n f := by
  induction n with
  | zero => simp [sumI]
  | succ n ih => rw [sumI_succ, sumI_succ, ih, Int.mul_add]

private theorem sumI_swap (n m : Nat) (f : Nat → Nat → Int) :
    sumI n (fun i => sumI m (f i)) = sumI m (fun j => sumI n (fun i => f i j)) := by
  induction n with
  | zero =>
    change 0 = sumI m (fun _ => 0)
    induction m with
    | zero => rfl
    | succ m ih => rw [sumI_succ, Int.add_zero, ← ih]
  | succ n ih =>
    rw [sumI_succ, ih, show (fun j => sumI (n + 1) (fun i => f i j)) =
      (fun j => sumI n (fun i => f i j) + f n j) by funext j; rw [sumI_succ], sumI_add]

private theorem sumI_dvd {d : Int} {n : Nat} {f : Nat → Int} (h : ∀ i, i < n → d ∣ f i) :
    d ∣ sumI n f := by
  induction n with
  | zero => exact Int.dvd_zero _
  | succ n ih =>
    rw [sumI_succ]
    exact Int.dvd_add (ih (fun i hi => h i (by omega))) (h n (by omega))

private theorem sumI_single_zero (n : Nat) (k z : Int) :
    sumI (n + 1) (fun i => (if i = 0 then k else 0) * z ^ i) = k := by
  induction n with
  | zero => simp [sumI]
  | succ n ih => rw [sumI_succ, ih]; simp

private theorem sumQ_sub (n : Nat) (f g : Nat → Rat) :
    sumQ n (fun i => f i - g i) = sumQ n f - sumQ n g := by
  induction n with
  | zero => change (0 : Rat) = 0 - 0; grind
  | succ n ih => rw [sumQ_succ, sumQ_succ, sumQ_succ, ih]; grind

private theorem sumQ_neg (n : Nat) (f : Nat → Rat) :
    sumQ n (fun i => -f i) = -sumQ n f := by
  induction n with
  | zero => change (0 : Rat) = -0; decide
  | succ n ih => rw [sumQ_succ, sumQ_succ, ih]; grind

private theorem sumQ_le {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i ≤ g i) :
    sumQ n f ≤ sumQ n g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    rw [sumQ_succ, sumQ_succ]
    have h₀ := ih (fun i hi => h i (by omega))
    have h₁ := h n (by omega)
    grind

private theorem sumQ_intCast (n : Nat) (f : Nat → Int) :
    (sumI n f : Rat) = sumQ n (fun i => (f i : Rat)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumI_succ, sumQ_succ, Rat.intCast_add, ih]

private theorem sumI_ofNat (n : Nat) (f : Nat → Nat) :
    ((sumRange n f : Nat) : Int) = sumI n (fun i => (f i : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, sumI_succ, Int.natCast_add, ih]

private theorem floor_fraction_bound (a : Int) (q : Rat) :
    -((a.natAbs : Int) : Rat) ≤ (q - (q.floor : Rat)) * (a : Rat) ∧
      (q - (q.floor : Rat)) * (a : Rat) ≤ ((a.natAbs : Int) : Rat) := by
  let f := q - (q.floor : Rat)
  let B : Rat := ((a.natAbs : Int) : Rat)
  have hf₀ : 0 ≤ f := (Rat.le_iff_sub_nonneg _ _).mp (Rat.floor_le q)
  have hf₁ : f ≤ 1 := by
    have h := Rat.lt_floor_add_one q
    rw [Rat.intCast_add] at h
    change q - (q.floor : Rat) ≤ 1
    grind
  have hB : 0 ≤ B := by dsimp [B]; exact_mod_cast Nat.zero_le a.natAbs
  have hhi : (a : Rat) ≤ B := Rat.intCast_le_intCast.mpr Int.le_natAbs
  have hlo : -B ≤ (a : Rat) := by
    have h : ((-a : Int) : Rat) ≤ B := Rat.intCast_le_intCast.mpr
      (by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -a)))
    rw [Rat.intCast_neg] at h
    grind
  have hu := Rat.mul_le_mul_of_nonneg_right hhi hf₀
  have hl := Rat.mul_le_mul_of_nonneg_right hlo hf₀
  have hv := Rat.mul_le_mul_of_nonneg_left hf₁ hB
  change -B ≤ f * (a : Rat) ∧ f * (a : Rat) ≤ B
  grind

/-- Radius of the coordinate box obtained by reducing rational row
coefficients modulo one. -/
def columnRadius (n : Nat) (A : Nat → Nat → Int) (j : Nat) : Nat :=
  sumRange n (fun i => (A i j).natAbs)

/-- A rational span of the constant vectors bounds the modulus by the
integer coefficient box. Every matrix row must vanish at `z` modulo `D`. -/
theorem modulus_le_column_box {D n : Nat} {A : Nat → Nat → Int} {z : Int}
    (hn : 0 < n) (hrows : ∀ i, i < n → (D : Int) ∣ evaluate n (A i) z)
    (hspan : ∀ k : Nat, k < D → ∃ q : Nat → Rat, ∀ j, j < n →
      ((List.range n).map (fun i => q i * (A i j : Rat))).sum =
        ((if j = 0 then (k : Int) else 0 : Int) : Rat)) :
    D ≤ size n (columnRadius n A) := by
  apply modulus_le_size (z := z)
  intro k hk
  obtain ⟨q, hq⟩ := hspan k hk
  let c := fun j : Nat => if j = 0 then (k : Int) else 0
  let x := fun j : Nat => c j - sumI n (fun i => (q i).floor * A i j)
  have hcast (j : Nat) (hj : j < n) :
      (x j : Rat) = sumQ n (fun i => (q i - ((q i).floor : Rat)) * (A i j : Rat)) := by
    have h := hq j hj
    change sumQ n (fun i => q i * (A i j : Rat)) = (c j : Rat) at h
    dsimp only [x]
    rw [Rat.intCast_sub, sumQ_intCast, ← h]
    rw [show (fun i => (q i - ((q i).floor : Rat)) * (A i j : Rat)) =
        (fun i => q i * (A i j : Rat) - ((((q i).floor * A i j : Int) : Rat))) by
      funext i
      rw [Rat.intCast_mul]
      grind, sumQ_sub]
  refine ⟨x, ?_, ?_⟩
  · intro j hj
    have hlo := sumQ_le (n := n) (fun i _ => (floor_fraction_bound (A i j) (q i)).1)
    have hhi := sumQ_le (n := n) (fun i _ => (floor_fraction_bound (A i j) (q i)).2)
    have hR : ((columnRadius n A j : Int) : Rat) =
        sumQ n (fun i => (((A i j).natAbs : Int) : Rat)) := by
      unfold columnRadius
      rw [sumI_ofNat, sumQ_intCast]
    have hN : -((columnRadius n A j : Int) : Rat) =
        sumQ n (fun i => -(((A i j).natAbs : Int) : Rat)) := by
      rw [hR, sumQ_neg]
    rw [← hcast j hj, ← hN] at hlo
    rw [← hcast j hj, ← hR] at hhi
    exact ⟨Rat.intCast_le_intCast.mp (by simpa only [Rat.intCast_neg] using hlo),
      Rat.intCast_le_intCast.mp hhi⟩
  · have he : evaluate n x z = (k : Int) -
        sumI n (fun i => (q i).floor * evaluate n (A i) z) := by
      unfold evaluate
      dsimp only [x]
      rw [show (fun j => (c j - sumI n (fun i => (q i).floor * A i j)) * z ^ j) =
          (fun j => c j * z ^ j - sumI n (fun i => (q i).floor * (A i j * z ^ j))) by
        funext j
        rw [Int.sub_mul, Int.mul_comm (sumI n _), ← sumI_mul]
        congr 2
        funext i
        ac_rfl, sumI_sub, sumI_swap]
      simp only [sumI_mul]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact congrArg (fun a : Int => a - _) (sumI_single_zero m k z)
    have hd : (D : Int) ∣ evaluate n x z - (k : Int) := by
      rw [he]
      have hs := sumI_dvd (fun i hi => Int.dvd_trans (hrows i hi) (Int.dvd_mul_left (q i).floor _))
      rw [show (k : Int) - sumI n (fun i => (q i).floor * evaluate n (A i) z) - (k : Int) =
          -sumI n (fun i => (q i).floor * evaluate n (A i) z) by omega]
      exact Int.dvd_neg.mpr hs
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hd),
      Int.emod_eq_of_lt (by omega) (by omega)]

/-- An integer matrix is triangular modulo two if its diagonal is odd
and all entries on one side of that diagonal are even. -/
def OddTriangular (n : Nat) (A : Nat → Nat → Int) : Prop :=
  (∀ i, i < n → A i i % 2 = 1) ∧
    ((∀ i j, i < n → j < i → A i j % 2 = 0) ∨
     (∀ i j, j < n → i < j → A i j % 2 = 0))

private theorem sumQ_head (n : Nat) (f : Nat → Rat) :
    sumQ (n + 1) f = f 0 + sumQ n (fun i => f (i + 1)) := by
  induction n with
  | zero => rw [sumQ_succ]; simp [sumQ, Rat.add_zero, Rat.zero_add]
  | succ n ih => rw [sumQ_succ, ih, sumQ_succ, Rat.add_assoc]

private theorem sumQ_mul (n : Nat) (a : Rat) (f : Nat → Rat) :
    sumQ n (fun i => a * f i) = a * sumQ n f := by
  induction n with
  | zero => simp [sumQ, Rat.mul_zero]
  | succ n ih => rw [sumQ_succ, sumQ_succ, ih, Rat.mul_add]

private theorem schur_mod_two {p x y t : Int} (hp : p % 2 = 1)
    (hzero : y % 2 = 0 ∨ t % 2 = 0) : (p * x - y * t) % 2 = x % 2 := by
  rw [Int.sub_emod, Int.mul_emod p x 2, Int.mul_emod y t 2, hp]
  rcases hzero with h | h <;> simp [h]

private theorem solve_odd_triangular (n : Nat) (A : Nat → Nat → Int) (b : Nat → Rat)
    (hA : OddTriangular n A) :
    ∃ x : Nat → Rat, ∀ i, i < n → sumQ n (fun j => (A i j : Rat) * x j) = b i := by
  induction n generalizing A b with
  | zero => exact ⟨fun _ => 0, fun _ hi => by omega⟩
  | succ n ih =>
    let p := A 0 0
    let B := fun i j => p * A (i + 1) (j + 1) - A (i + 1) 0 * A 0 (j + 1)
    let c := fun i => (p : Rat) * b (i + 1) - (A (i + 1) 0 : Rat) * b 0
    have hp : p % 2 = 1 := hA.1 0 (by omega)
    have hinv : (p : Rat)⁻¹ * (p : Rat) = 1 :=
      Rat.inv_mul_cancel _ (fun hz => by
        have he := Rat.intCast_eq_zero_iff.mp hz
        omega)
    have hreduce (i j : Nat) (hi : i < n) (hj : j < n) :
        B i j % 2 = A (i + 1) (j + 1) % 2 := by
      apply schur_mod_two hp
      rcases hA.2 with hb | ha
      · exact Or.inl (hb (i + 1) 0 (by omega) (by omega))
      · exact Or.inr (ha 0 (j + 1) (by omega) (by omega))
    have hB : OddTriangular n B := by
      refine ⟨fun i hi => (hreduce i i hi hi).trans (hA.1 (i + 1) (by omega)), ?_⟩
      rcases hA.2 with hb | ha
      · exact Or.inl (fun i j hi hj =>
          (hreduce i j hi (by omega)).trans (hb (i + 1) (j + 1) (by omega) (by omega)))
      · exact Or.inr (fun i j hj hi =>
          (hreduce i j (by omega) hj).trans (ha (i + 1) (j + 1) (by omega) (by omega)))
    obtain ⟨y, hy⟩ := ih B c hB
    let s := fun i => sumQ n (fun j => (A i (j + 1) : Rat) * y j)
    let x₀ := (p : Rat)⁻¹ * (b 0 - s 0)
    have h₀ : (p : Rat) * x₀ + s 0 = b 0 := by
      dsimp only [x₀]
      rw [← Rat.mul_assoc, Rat.mul_comm (p : Rat) (p : Rat)⁻¹, hinv, Rat.one_mul]
      grind
    let x : Nat → Rat
      | 0 => x₀
      | i + 1 => y i
    refine ⟨x, fun i hi => ?_⟩
    rw [sumQ_head]
    change (A i 0 : Rat) * x₀ + s i = b i
    cases i with
    | zero => exact h₀
    | succ i =>
      have h := hy i (by omega)
      have hterm : (fun j => (B i j : Rat) * y j) =
          (fun j => (p : Rat) * ((A (i + 1) (j + 1) : Rat) * y j) -
            (A (i + 1) 0 : Rat) * ((A 0 (j + 1) : Rat) * y j)) := by
        funext j
        simp only [B, Rat.intCast_sub, Rat.intCast_mul]
        grind
      rw [hterm, sumQ_sub, sumQ_mul, sumQ_mul] at h
      change (p : Rat) * s (i + 1) - (A (i + 1) 0 : Rat) * s 0 =
        (p : Rat) * b (i + 1) - (A (i + 1) 0 : Rat) * b 0 at h
      have he : (p : Rat) * ((A (i + 1) 0 : Rat) * x₀ + s (i + 1)) = (p : Rat) * b (i + 1) := by
        calc
          _ = (A (i + 1) 0 : Rat) * ((p : Rat) * x₀ + s 0) +
              ((p : Rat) * s (i + 1) - (A (i + 1) 0 : Rat) * s 0) := by grind
          _ = _ := by rw [h₀, h]; grind
      have hm := congrArg (fun a : Rat => (p : Rat)⁻¹ * a) he
      simpa only [← Rat.mul_assoc, hinv, Rat.one_mul] using hm

/-- Triangularity modulo two supplies the rational span used in the
coefficient-box bound. -/
theorem modulus_le_column_box_of_odd_triangular {D n : Nat} {A : Nat → Nat → Int} {z : Int}
    (hn : 0 < n) (hrows : ∀ i, i < n → (D : Int) ∣ evaluate n (A i) z)
    (hA : OddTriangular n A) :
    D ≤ size n (columnRadius n A) := by
  apply modulus_le_column_box hn hrows
  let T := fun i j => A j i
  have hT : OddTriangular n T := by
    refine ⟨hA.1, ?_⟩
    rcases hA.2 with hb | ha
    · exact Or.inr (fun i j hj hi => hb j i hj hi)
    · exact Or.inl (fun i j hi hj => ha j i hi hj)
  intro k _
  obtain ⟨q, hq⟩ := solve_odd_triangular n T
    (fun j => ((if j = 0 then (k : Int) else 0 : Int) : Rat)) hT
  refine ⟨q, fun j hj => ?_⟩
  change sumQ n (fun i => q i * (A i j : Rat)) = _
  rw [show (fun i => q i * (A i j : Rat)) = (fun i => (T j i : Rat) * q i) by
    funext i
    exact Rat.mul_comm ..]
  exact hq j hj

private theorem size_mono {n : Nat} {b c : Nat → Nat} (h : ∀ j, j < n → b j ≤ c j) :
    size n b ≤ size n c := by
  induction n generalizing b c with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [size, size]
    exact Nat.mul_le_mul (by have := h 0 (by omega); omega)
      (ih (fun j hj => h (j + 1) (by omega)))

private theorem size_add_le (n : Nat) (b c : Nat → Nat) :
    size n (fun j => b j + c j) ≤ size n b * size n c := by
  induction n generalizing b c with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
    rw [size, size, size]
    have h : 2 * (b 0 + c 0) + 1 ≤ (2 * b 0 + 1) * (2 * c 0 + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.add_mul]
      omega
    apply Nat.le_trans (Nat.mul_le_mul h (ih (fun j => b (j + 1)) (fun j => c (j + 1))))
    exact Nat.le_of_eq (by ac_rfl)

private theorem size_const (n B : Nat) : size n (fun _ => B) = (2 * B + 1) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [size, ih, Nat.pow_succ, Nat.mul_comm]

private theorem size_interval_le (n lo w B : Nat) :
    size n (fun j => if lo ≤ j ∧ j < lo + w then B else 0) ≤ (2 * B + 1) ^ w := by
  induction n generalizing lo w with
  | zero => exact Nat.pow_pos (by omega)
  | succ n ih =>
    cases lo with
    | zero =>
      cases w with
      | zero =>
        have he : (fun j : Nat => if 0 ≤ j ∧ j < 0 + 0 then B else 0) = fun _ => 0 := by
          funext j
          simp
        rw [he, size_const]
        simp
      | succ w =>
        rw [size]
        simp only [Nat.zero_add, Nat.zero_le, true_and, Nat.zero_lt_succ, if_true,
          Nat.succ_lt_succ_iff]
        rw [Nat.pow_succ, Nat.mul_comm ((2 * B + 1) ^ w)]
        exact Nat.mul_le_mul_left _ (by simpa only [Nat.zero_add, Nat.zero_le, true_and] using ih 0 w)
    | succ lo =>
      rw [size]
      have he : (fun j : Nat => if lo + 1 ≤ j + 1 ∧ j + 1 < lo + 1 + w then B else 0) =
          (fun j => if lo ≤ j ∧ j < lo + w then B else 0) := by
        funext j
        have h : (lo + 1 ≤ j + 1 ∧ j + 1 < lo + 1 + w) ↔
            (lo ≤ j ∧ j < lo + w) := by omega
        simp only [h]
      have hz : ¬ (lo.succ ≤ 0 ∧ 0 < lo.succ + w) := by omega
      simp only [if_neg hz, Nat.mul_zero, Nat.zero_add, Nat.one_mul, he]
      exact ih lo w

private theorem sumRange_pick (n i B : Nat) :
    sumRange n (fun j => if j = i then B else 0) = if i < n then B else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumRange_succ, ih]
    by_cases h : n = i
    · subst i
      simp
    · rw [if_neg h, Nat.add_zero]
      have he : i < n + 1 ↔ i < n := by omega
      simp only [he]

private theorem sumRange_pick_offset (n i j : Nat) (f : Nat → Nat) :
    sumRange n (fun t => if i + t = j then f t else 0) =
      if i ≤ j ∧ j - i < n then f (j - i) else 0 := by
  by_cases hi : i ≤ j
  · have he : ∀ t : Nat, i + t = j ↔ t = j - i := fun _ => by omega
    rw [sumRange_congr (g := fun t => if t = j - i then f (j - i) else 0) (fun t _ => by
      simp only [he]
      split
      · rename_i ht
        rw [ht]
      · rfl), sumRange_pick]
    simp [hi]
  · rw [sumRange_congr (g := fun _ => 0) (fun t _ => if_neg (by omega)), sumRange_const]
    simp [hi]

private theorem sumRange_swap (n m : Nat) (f : Nat → Nat → Nat) :
    sumRange n (fun i => sumRange m (f i)) = sumRange m (fun j => sumRange n (fun i => f i j)) := by
  apply Int.ofNat_inj.mp
  simp only [sumI_ofNat]
  exact sumI_swap n m (fun i j => (f i j : Int))

private theorem sumI_eq {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumI n f = sumI n g := by
  unfold sumI
  rw [List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))]

private theorem sumI_zero (n : Nat) : sumI n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumI_succ, ih, Int.add_zero]

private theorem sumI_split (n m : Nat) (f : Nat → Int) :
    sumI (n + m) f = sumI n f + sumI m (fun i => f (n + i)) := by
  induction m with
  | zero => exact (Int.add_zero _).symm
  | succ m ih => rw [← Nat.add_assoc, sumI_succ, ih, sumI_succ, Int.add_assoc]

private theorem sumI_pick (n i : Nat) (x : Int) :
    sumI n (fun j => if j = i then x else 0) = if i < n then x else 0 := by
  induction n with
  | zero => simp [sumI]
  | succ n ih =>
    rw [sumI_succ, ih]
    by_cases h : n = i
    · subst i
      simp
    · rw [if_neg h, Int.add_zero]
      have he : i < n + 1 ↔ i < n := by omega
      simp only [he]

private def shifted (d : Nat) (P : Nat → Int) (i j : Nat) : Int :=
  if i ≤ j ∧ j - i ≤ d then P (j - i) else 0

private def binomialRow (e : Nat) (c b : Int) (i j : Nat) : Int :=
  (if j = i + e then c else 0) - (if j = i then b else 0)

private def stack (m : Nat) (A B : Nat → Nat → Int) (i j : Nat) : Int :=
  if i < m then A i j else B (i - m) j

private theorem columnRadius_stack (m n : Nat) (A B : Nat → Nat → Int) (j : Nat) :
    columnRadius (m + n) (stack m A B) j = columnRadius m A j + columnRadius n B j := by
  unfold columnRadius
  rw [sumRange_split]
  congr 1
  · apply sumRange_congr
    intro i hi
    simp [stack, hi]
  · apply sumRange_congr
    intro i _
    have h : ¬ m + i < m := by omega
    simp [stack, h]

private theorem eval_shifted {n d i : Nat} (P : Nat → Int) (z : Int) (hi : i + d < n) :
    evaluate n (shifted d P i) z = z ^ i * evaluate (d + 1) P z := by
  let F := fun j => shifted d P i j * z ^ j
  have hbefore : sumI i F = 0 := by
    rw [← sumI_zero i]
    apply sumI_eq
    intro j hj
    simp [F, shifted, show ¬ i ≤ j by omega]
  let m := n - (i + (d + 1))
  have hafter : sumI m (fun j => F (i + (d + 1) + j)) = 0 := by
    rw [← sumI_zero m]
    apply sumI_eq
    intro j _
    simp only [F, shifted, if_neg (show ¬ (i ≤ i + (d + 1) + j ∧ i + (d + 1) + j - i ≤ d)
      by omega), Int.zero_mul]
  have hmid : sumI (d + 1) (fun j => F (i + j)) = z ^ i * evaluate (d + 1) P z := by
    unfold evaluate
    rw [← sumI_mul]
    apply sumI_eq
    intro j hj
    simp only [F, shifted, Nat.add_sub_cancel_left, if_pos (show i ≤ i + j ∧ j ≤ d by omega),
      Int.pow_add]
    ac_rfl
  change sumI n F = _
  rw [show n = i + (d + 1) + m by dsimp [m]; omega, sumI_split (i + (d + 1)),
    sumI_split i (d + 1), hbefore, hmid, hafter, Int.zero_add, Int.add_zero]

private theorem eval_binomial {n e i : Nat} (c b z : Int) (hi : i + e < n) :
    evaluate n (binomialRow e c b i) z = z ^ i * (c * z ^ e - b) := by
  unfold evaluate
  rw [show (fun j => binomialRow e c b i j * z ^ j) =
      (fun j => (if j = i + e then c * z ^ (i + e) else 0) -
        (if j = i then b * z ^ i else 0)) by
    funext j
    unfold binomialRow
    rw [Int.sub_mul]
    have hh (t : Nat) (a : Int) : (if j = t then a else 0) * z ^ j =
        if j = t then a * z ^ t else 0 := by
      by_cases h : j = t
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h, Int.zero_mul]
    rw [hh, hh],
    sumI_sub, sumI_pick, sumI_pick, if_pos hi, if_pos (show i < n by omega), Int.pow_add]
  grind

private theorem shifted_columns (d e : Nat) (P : Nat → Int) (j : Nat) :
    columnRadius e (shifted d P) j ≤ sumRange (d + 1) (fun i => (P i).natAbs) := by
  unfold columnRadius
  have h (i : Nat) : (shifted d P i j).natAbs =
      sumRange (d + 1) (fun t => if i + t = j then (P t).natAbs else 0) := by
    rw [sumRange_pick_offset]
    unfold shifted
    have he : (i ≤ j ∧ j - i ≤ d) ↔ (i ≤ j ∧ j - i < d + 1) := by omega
    simp only [he]
    split <;> rfl
  rw [sumRange_congr (fun i _ => h i), sumRange_swap]
  apply sumRange_le
  intro t _
  have he : (fun i : Nat => if i + t = j then (P t).natAbs else 0) =
      (fun i => if t + i = j then (P t).natAbs else 0) := by
    funext i
    rw [Nat.add_comm i t]
  rw [he, sumRange_pick_offset]
  split <;> omega

private theorem binomial_columns (d e : Nat) (c b : Int) (j : Nat) :
    columnRadius d (binomialRow e c b) j ≤
      (if e ≤ j ∧ j < e + d then c.natAbs else 0) + (if 0 ≤ j ∧ j < 0 + d then b.natAbs else 0) := by
  unfold columnRadius
  have he : sumRange d (fun i => (if j = i + e then c else 0).natAbs) =
      if e ≤ j ∧ j < e + d then c.natAbs else 0 := by
    by_cases h : e ≤ j
    · have hf : (fun i : Nat => (if j = i + e then c else 0).natAbs) =
          (fun i => if i = j - e then c.natAbs else 0) := by
        funext i
        have ht : j = i + e ↔ i = j - e := by omega
        by_cases hi : i = j - e
        · rw [if_pos (ht.mpr hi), if_pos hi]
        · rw [if_neg (mt ht.mp hi), if_neg hi]; rfl
      rw [hf, sumRange_pick]
      have ht : (e ≤ j ∧ j < e + d) ↔ j - e < d := by omega
      simp only [ht]
    · rw [if_neg (by omega)]
      have hf : (fun i : Nat => (if j = i + e then c else 0).natAbs) = fun _ => 0 := by
        funext i
        simp [show j ≠ i + e by omega]
      rw [hf, sumRange_const, Nat.mul_zero]
  have hb : sumRange d (fun i => (if j = i then b else 0).natAbs) =
      if 0 ≤ j ∧ j < 0 + d then b.natAbs else 0 := by
    have hf : (fun i : Nat => (if j = i then b else 0).natAbs) =
        (fun i => if i = j then b.natAbs else 0) := by
      funext i
      by_cases hi : i = j
      · rw [if_pos hi.symm, if_pos hi]
      · rw [if_neg (Ne.symm hi), if_neg hi]; rfl
    rw [hf, sumRange_pick]
    simp
  calc
    _ ≤ sumRange d (fun i => (if j = i + e then c else 0).natAbs +
        (if j = i then b else 0).natAbs) := sumRange_le (fun i _ => Int.natAbs_sub_le ..)
    _ = _ := by rw [sumRange_add, he, hb]

private theorem binomial_parity_high {e : Nat} {c b : Int} (hc : c % 2 = 1) (hb : b % 2 = 0)
    (i j : Nat) : binomialRow e c b i j % 2 = if j = i + e then 1 else 0 := by
  have hmod (t : Nat) (x : Int) : (if j = t then x else 0) % 2 = if j = t then x % 2 else 0 := by
    by_cases h : j = t
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; decide
  unfold binomialRow
  rw [Int.sub_emod, hmod, hmod, hc, hb]
  simp only [ite_self, Int.sub_zero]
  split <;> decide

private theorem binomial_parity_low {e : Nat} {c b : Int} (hc : c % 2 = 0) (hb : b % 2 = 1)
    (i j : Nat) : binomialRow e c b i j % 2 = if j = i then 1 else 0 := by
  have hmod (t : Nat) (x : Int) : (if j = t then x else 0) % 2 = if j = t then x % 2 else 0 := by
    by_cases h : j = t
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; decide
  unfold binomialRow
  rw [Int.sub_emod, hmod, hmod, hc, hb]
  simp only [ite_self]
  split <;> decide

private theorem box_bound_of_columns {D d e M : Nat} {c b : Int} {A : Nat → Nat → Int}
    (h : D ≤ size (d + e) (columnRadius (d + e) A))
    (hcol : ∀ j, columnRadius (d + e) A j ≤ M +
      (if e ≤ j ∧ j < e + d then c.natAbs else 0) +
      (if 0 ≤ j ∧ j < 0 + d then b.natAbs else 0)) :
    D ≤ (2 * M + 1) ^ (d + e) * (2 * c.natAbs + 1) ^ d * (2 * b.natAbs + 1) ^ d := by
  let n := d + e
  let C := fun j => if e ≤ j ∧ j < e + d then c.natAbs else 0
  let B := fun j => if 0 ≤ j ∧ j < 0 + d then b.natAbs else 0
  calc
    _ ≤ size n (columnRadius n A) := h
    _ ≤ size n (fun j => (M + C j) + B j) := size_mono (fun j _ => hcol j)
    _ ≤ size n (fun j => M + C j) * size n B := size_add_le n _ B
    _ ≤ (size n (fun _ => M) * size n C) * size n B :=
      Nat.mul_le_mul_right _ (size_add_le n (fun _ => M) C)
    _ ≤ _ := by
      rw [size_const]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (size_interval_le n e d c.natAbs))
        (size_interval_le n 0 d b.natAbs)

/-- The absolute coefficient sum of a polynomial with odd endpoints
and a binomial with opposite coefficient parities bound their common
root modulus. -/
theorem modulus_le_of_binomial_of_odd_ends {D d e M : Nat} {z c b : Int} {P : Nat → Int}
    (hd : 0 < d) (hP₀ : P 0 % 2 = 1) (hPd : P d % 2 = 1)
    (hP : sumRange (d + 1) (fun i => (P i).natAbs) ≤ M)
    (hroot : (D : Int) ∣ evaluate (d + 1) P z)
    (hbin : (D : Int) ∣ c * z ^ e - b)
    (hpar : (c % 2 = 1 ∧ b % 2 = 0) ∨ (c % 2 = 0 ∧ b % 2 = 1)) :
    D ≤ (2 * M + 1) ^ (d + e) * (2 * c.natAbs + 1) ^ d * (2 * b.natAbs + 1) ^ d := by
  let F := shifted d P
  let G := binomialRow e c b
  have hF (i : Nat) (hi : i < e) : (D : Int) ∣ evaluate (d + e) (F i) z := by
    change (D : Int) ∣ evaluate (d + e) (shifted d P i) z
    rw [eval_shifted P z (by omega)]
    exact Int.dvd_trans hroot (Int.dvd_mul_left _ _)
  have hG (i : Nat) (hi : i < d) : (D : Int) ∣ evaluate (d + e) (G i) z := by
    change (D : Int) ∣ evaluate (d + e) (binomialRow e c b i) z
    rw [eval_binomial c b z (by omega)]
    exact Int.dvd_trans hbin (Int.dvd_mul_left _ _)
  rcases hpar with ⟨hc, hb⟩ | ⟨hc, hb⟩
  · let A := stack e F G
    have hrows (i : Nat) (hi : i < d + e) : (D : Int) ∣ evaluate (d + e) (A i) z := by
      by_cases h : i < e
      · have he : A i = F i := funext (fun j => by simp [A, stack, h])
        rw [he]
        exact hF i h
      · have he : A i = G (i - e) := funext (fun j => by simp [A, stack, h])
        rw [he]
        exact hG _ (by omega)
    have htri : OddTriangular (d + e) A := by
      refine ⟨fun i hi => ?_, Or.inl (fun i j hi hij => ?_)⟩
      · by_cases h : i < e
        · simp [A, stack, F, shifted, h, hP₀]
        · simp [A, stack, G, h, binomial_parity_high hc hb, show i - e + e = i by omega]
      · by_cases h : i < e
        · simp [A, stack, F, shifted, h, show ¬ i ≤ j by omega]
        · simp [A, stack, G, h, binomial_parity_high hc hb, show j ≠ i - e + e by omega]
    apply box_bound_of_columns (c := c) (b := b) (modulus_le_column_box_of_odd_triangular (by omega) hrows htri)
    intro j
    rw [Nat.add_comm d e, show columnRadius (e + d) A j = _ from columnRadius_stack e d F G j]
    have hf := Nat.le_trans (shifted_columns d e P j) hP
    have hg := binomial_columns d e c b j
    change columnRadius e F j ≤ M at hf
    change columnRadius d G j ≤ _ at hg
    omega
  · let A := stack d G F
    have hrows (i : Nat) (hi : i < d + e) : (D : Int) ∣ evaluate (d + e) (A i) z := by
      by_cases h : i < d
      · have he : A i = G i := funext (fun j => by simp [A, stack, h])
        rw [he]
        exact hG i h
      · have he : A i = F (i - d) := funext (fun j => by simp [A, stack, h])
        rw [he]
        exact hF _ (by omega)
    have htri : OddTriangular (d + e) A := by
      refine ⟨fun i hi => ?_, Or.inr (fun i j hj hij => ?_)⟩
      · by_cases h : i < d
        · simp [A, stack, G, h, binomial_parity_low hc hb]
        · have he : i - d ≤ i ∧ i - (i - d) ≤ d := by omega
          simp [A, stack, F, shifted, h, he, show i - (i - d) = d by omega, hPd]
      · by_cases h : i < d
        · simp [A, stack, G, h, binomial_parity_low hc hb, show j ≠ i by omega]
        · simp [A, stack, F, shifted, h, show ¬ j - (i - d) ≤ d by omega]
    apply box_bound_of_columns (c := c) (b := b) (modulus_le_column_box_of_odd_triangular (by omega) hrows htri)
    intro j
    rw [show columnRadius (d + e) A j = _ from columnRadius_stack d e G F j]
    have hf := Nat.le_trans (shifted_columns d e P j) hP
    have hg := binomial_columns d e c b j
    change columnRadius e F j ≤ M at hf
    change columnRadius d G j ≤ _ at hg
    omega

/-- The coefficient box bound for unit endpoint coefficients. -/
theorem modulus_le_of_binomial {D d e M : Nat} {z c b : Int} {P : Nat → Int}
    (hd : 0 < d) (hP₀ : P 0 = 1) (hPd : P d = 1)
    (hP : sumRange (d + 1) (fun i => (P i).natAbs) ≤ M)
    (hroot : (D : Int) ∣ evaluate (d + 1) P z)
    (hbin : (D : Int) ∣ c * z ^ e - b)
    (hpar : (c % 2 = 1 ∧ b % 2 = 0) ∨ (c % 2 = 0 ∧ b % 2 = 1)) :
    D ≤ (2 * M + 1) ^ (d + e) * (2 * c.natAbs + 1) ^ d * (2 * b.natAbs + 1) ^ d :=
  modulus_le_of_binomial_of_odd_ends hd (by rw [hP₀]; decide) (by rw [hPd]; decide) hP hroot hbin hpar

end Collatz.PhaseResidueBox
