import Collatz.Strategy.SortStair
import Collatz.Strategy.CyclicOrder
import Collatz.Strategy.CycleCollisionBudget
import Collatz.Strategy.Discrepancy

/-! Distinct odd cycle values give a telescoping upper bound on the
coefficient deficit in terms of the numerical spread. The resulting
fifth-power room `M^5 (M+2) < 9^5 m^6` forces discrepancy width below
two periods. Every rational band below the ceiling `9^{5/6}` has that
room once its floor clears an explicit slack threshold, including the
ratios `43/7` and `56/9`. -/

namespace Collatz.CycleNumericalWidth

open Collatz.AccCycle Collatz.Arith Collatz.CyclicOrder Collatz.OrbitProduct
open Collatz.SortStair Collatz.SortedStair

private def plusTwoProduct (l : List Nat) : Nat := (l.map (· + 2)).prod

private theorem fifth_power_factor {x : Nat} (hx : 4 ≤ x) :
    (3 * x + 1) ^ 5 ≤ 243 * x ^ 4 * (x + 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hx
  have he : (3 * (4 + k) + 1) ^ 5 +
      (1955 + 7041 * k + 4446 * k ^ 2 + 1026 * k ^ 3 + 81 * k ^ 4) =
      243 * (4 + k) ^ 4 * (4 + k + 2) := by grind
  exact he ▸ Nat.le_add_right _ _

private theorem shiftProd_fifth_le (l : List Nat) (hlo : ∀ x ∈ l, 4 ≤ x) :
    (shiftProd l) ^ 5 ≤ (3 ^ l.length) ^ 5 * (l.prod ^ 4 * plusTwoProduct l) := by
  induction l with
  | nil => simp [shiftProd, plusTwoProduct]
  | cons x xs ih =>
    have htail := ih (fun y hy => hlo y (List.mem_cons_of_mem _ hy))
    have hlen : (3 ^ (x :: xs).length) ^ 5 = (3 ^ xs.length) ^ 5 * 243 := by
      rw [List.length_cons, Nat.pow_succ 3 xs.length, Nat.mul_pow]
    have hprod : ((x :: xs).prod) ^ 4 = x ^ 4 * xs.prod ^ 4 := by
      rw [List.prod_cons, Nat.mul_pow]
    have hplus : plusTwoProduct (x :: xs) = (x + 2) * plusTwoProduct xs := rfl
    calc
      _ = (3 * x + 1) ^ 5 * (shiftProd xs) ^ 5 := by rw [shiftProd_cons, Nat.mul_pow]
      _ ≤ (243 * x ^ 4 * (x + 2)) * ((3 ^ xs.length) ^ 5 * (xs.prod ^ 4 * plusTwoProduct xs)) :=
        Nat.mul_le_mul (fifth_power_factor (hlo x List.mem_cons_self)) htail
      _ = _ := by rw [hlen, hprod, hplus]; ac_rfl

private theorem sorted_interval_product {l : List Nat} {m M : Nat} (hmM : m ≤ M + 2)
    (hs : StrictSorted l) (hlo : ∀ x ∈ l, m ≤ x) (hhi : ∀ x ∈ l, x ≤ M)
    (ho : ∀ x ∈ l, x % 2 = 1) :
    m * plusTwoProduct l ≤ (M + 2) * l.prod := by
  induction l generalizing m with
  | nil => simpa [plusTwoProduct] using hmM
  | cons x xs ih =>
    have hx := hhi x List.mem_cons_self
    have hox := ho x List.mem_cons_self
    have ht := ih (m := x + 2) (by omega) hs.2 (fun y hy => by
      have hlt := hs.1 y hy
      have hyodd := ho y (List.mem_cons_of_mem _ hy)
      omega) (fun y hy => hhi y (List.mem_cons_of_mem _ hy))
      (fun y hy => ho y (List.mem_cons_of_mem _ hy))
    change m * ((x + 2) * plusTwoProduct xs) ≤ (M + 2) * (x * xs.prod)
    calc
      _ ≤ x * ((x + 2) * plusTwoProduct xs) := Nat.mul_le_mul_right _ (hlo x List.mem_cons_self)
      _ ≤ x * ((M + 2) * xs.prod) := Nat.mul_le_mul_left _ ht
      _ = _ := by ac_rfl

/-- A least cycle in `[m,M]` above four has power ratio satisfying
`m * (2^L)^5 ≤ (M+2) * (3^a)^5`. -/
theorem power_ratio_fifth_le_of_interval {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hm : 4 ≤ m) (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M) :
    m * ((2 : Nat) ^ L) ^ 5 ≤ (M + 2) * (3 ^ oddCount n L) ^ 5 := by
  let l := oddElems n L
  let s := sortList l
  have hmin : m ≤ n := hlo 0
  have hmax : n ≤ M := hhi 0
  have hn : 0 < n := by omega
  have hinj (i j : Nat) (hi : i < L) (hj : j < L) (he : acceleratedOrbit i n = acceleratedOrbit j n) :
      i = j := by
    have hp := List.pairwise_iff_getElem.mp (CycleCollisionBudget.periodPoints_nodup h hleast)
    have hne (i j : Nat) (hi : i < L) (hj : j < L) (hlt : i < j) :
        acceleratedOrbit i n ≠ acceleratedOrbit j n := by
      have hi' : i < (CycleCollisionBudget.periodPoints n L).length := by
        simpa [CycleCollisionBudget.periodPoints] using hi
      have hj' : j < (CycleCollisionBudget.periodPoints n L).length := by
        simpa [CycleCollisionBudget.periodPoints] using hj
      simpa [CycleCollisionBudget.periodPoints] using hp i j hi' hj' hlt
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact False.elim (hne i j hi hj hij he)
    · exact hij
    · exact False.elim (hne j i hj hi hij he.symm)
  have hs := sortList_sorted l (oddElems_nodup L hinj)
  have hmem (x : Nat) (hx : x ∈ s) : ∃ i, i < L ∧ acceleratedOrbit i n = x :=
    oddElems_mem L x ((sortList_mem l x).mp hx)
  have hlo' (x : Nat) (hx : x ∈ s) : m ≤ x := by
    obtain ⟨i, _, hi⟩ := hmem x hx
    exact hi ▸ hlo i
  have hhi' (x : Nat) (hx : x ∈ s) : x ≤ M := by
    obtain ⟨i, _, hi⟩ := hmem x hx
    exact hi ▸ hhi i
  have ho (x : Nat) (hx : x ∈ s) : x % 2 = 1 :=
    oddElems_odd n L x ((sortList_mem l x).mp hx)
  have hinterval := sorted_interval_product (m := m) (M := M) (by omega) hs hlo' hhi' ho
  have hprod := shiftProd_fifth_le s (fun x hx => Nat.le_trans hm (hlo' x hx))
  have hlen : s.length = oddCount n L := by rw [sortList_length, oddElems_length]
  have he := cycle_prod_eq hn h.2
  change 2 ^ L * l.prod = shiftProd l at he
  rw [sortList_shiftProd, ← he, Nat.mul_pow, hlen] at hprod
  rw [sortList_prod] at hprod hinterval
  have hcancel : 0 < l.prod ^ 5 := Nat.pow_pos (prod_pos _ (fun x hx => by
    have ho' := oddElems_odd n L x hx
    omega))
  apply Nat.le_of_mul_le_mul_right _ hcancel
  calc
    _ = m * (((2 : Nat) ^ L) ^ 5 * l.prod ^ 5) := by ac_rfl
    _ ≤ m * ((3 ^ oddCount n L) ^ 5 * (l.prod ^ 4 * plusTwoProduct s)) :=
      Nat.mul_le_mul_left _ hprod
    _ = ((3 ^ oddCount n L) ^ 5 * l.prod ^ 4) * (m * plusTwoProduct s) := by ac_rfl
    _ ≤ ((3 ^ oddCount n L) ^ 5 * l.prod ^ 4) * ((M + 2) * l.prod) :=
      Nat.mul_le_mul_left _ hinterval
    _ = _ := by rw [show l.prod ^ 5 = l.prod ^ 4 * l.prod by rfl]; ac_rfl

/-- A discrepancy climb of at least r/s periods forces the endpoint
ratio to exceed the corresponding power of three times the cycle coefficient. -/
theorem endpoint_ratio_pow_of_large_walk {x L p r s : Nat} (hx : 0 < x) (h : AccIsCycleOf x L)
    (hp : p ≤ L) (hw : (r : Int) * L ≤ (s : Int) * walk x L p) :
    3 ^ r * (3 ^ oddCount x L * x) ^ s ≤ (2 ^ L * acceleratedOrbit p x) ^ s := by
  let y := acceleratedOrbit p x
  let q := L - p
  let a := oddCount x L
  let c := oddCount y q
  have hL := h.1
  have hpq : p + q = L := by dsimp [q]; omega
  have hy : AccIsCycleOf y L := accIsCycleOf_orbit h p
  have ha : oddCount y L = a := AccumulatorCap.oddCount_shift h.2 p
  have hback : acceleratedOrbit q y = x := by
    dsimp only [y]
    rw [acceleratedOrbit_add, Nat.add_comm q p, hpq, h.2]
  have hW : walk y L q = -walk x L p := by
    rw [walk_shift h.2 p q, hpq, walk_full, Int.zero_sub]
  have hc : L * (c * s + r) ≤ a * q * s := by
    have hh := hW
    unfold walk at hh
    rw [ha] at hh
    change (L : Int) * (c : Int) - (a : Int) * q = -walk x L p at hh
    have hscaled := congrArg (fun w : Int => (s : Int) * w) hh
    have h₁ : (s : Int) * ((L : Int) * c) = (L : Int) * ((c : Int) * s) := by ac_rfl
    have h₂ : (s : Int) * ((a : Int) * q) = (a : Int) * q * s := by ac_rfl
    change (s : Int) * ((L : Int) * c - (a : Int) * q) = (s : Int) * -walk x L p at hscaled
    rw [Int.mul_sub, h₁, h₂, Int.mul_neg] at hscaled
    have hcast : (L : Int) * ((c * s + r : Nat) : Int) ≤ (((a * q) * s : Nat) : Int) := by
      rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, Int.mul_add,
        Int.mul_comm (L : Int) (r : Int)]
      omega
    exact_mod_cast hcast
  have hgap : 3 ^ a < 2 ^ L := (accCycle_bounds hx h).2.2
  have hpower : (3 : Nat) ^ (c * s + r) ≤ (2 ^ q) ^ s := by
    apply (Nat.pow_le_pow_iff_left (n := L) (by omega)).mp
    calc
      _ = 3 ^ (L * (c * s + r)) := by rw [← Nat.pow_mul, Nat.mul_comm]
      _ ≤ 3 ^ (a * q * s) := Nat.pow_le_pow_right (by decide) hc
      _ = ((3 ^ a) ^ q) ^ s := by rw [Nat.pow_mul, Nat.pow_mul]
      _ ≤ ((2 ^ L) ^ q) ^ s := Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.le_of_lt hgap) q) s
      _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]; congr 1; ac_rfl
  have hup := Discrepancy.orbit_upper (acceleratedOrbit_positive hx p) hy
    (j := q) (by dsimp [q]; omega)
  rw [ha, hback] at hup
  change 3 ^ a * (2 ^ q * x) ≤ 2 ^ L * (3 ^ c * y) at hup
  have hprod : (3 ^ a * x) ^ s * (2 ^ q) ^ s ≤ (2 ^ L * y) ^ s * (3 ^ c) ^ s := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left (by rwa [Nat.mul_assoc, Nat.mul_comm x, Nat.mul_assoc, Nat.mul_comm y]) _
  have hh := Nat.le_trans (Nat.mul_le_mul_left ((3 ^ a * x) ^ s) hpower) hprod
  rw [Nat.pow_add, Nat.pow_mul] at hh
  have he : (3 ^ a * x) ^ s * ((3 ^ c) ^ s * (3 : Nat) ^ r) =
      (3 ^ r * (3 ^ a * x) ^ s) * (3 ^ c) ^ s := by ac_rfl
  rw [he] at hh
  exact Nat.le_of_mul_le_mul_right hh (Nat.pow_pos (Nat.pow_pos (by decide)))

/-- The comparison also bounds the full discrepancy spread. -/
theorem walk_width_lt_of_numerical_ratio_pow {n L m M r s : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hbound : (2 ^ L * M) ^ s < 3 ^ r * (3 ^ oddCount n L * m) ^ s) :
    ∀ i j, (s : Int) * (walk n L i - walk n L j) < (r : Int) * L := by
  intro i j
  rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
  apply Int.lt_of_not_ge
  intro hbig
  obtain ⟨p, hp, hW⟩ := walk_range' h.1 h.2 (Nat.mod_lt j h.1) (i % L)
  let x := acceleratedOrbit (j % L) n
  have hx : 0 < x := acceleratedOrbit_positive hn _
  have hxy := endpoint_ratio_pow_of_large_walk hx (accIsCycleOf_orbit h (j % L)) (Nat.le_of_lt hp)
    (r := r) (s := s) (by rwa [hW])
  rw [AccumulatorCap.oddCount_shift h.2 (j % L)] at hxy
  have htop : acceleratedOrbit p x ≤ M := by unfold x; rw [acceleratedOrbit_add]; exact hhi _
  have hl := Nat.pow_le_pow_left (Nat.mul_le_mul_left (3 ^ oddCount n L) (hlo (j % L))) s
  have hu := Nat.pow_le_pow_left (Nat.mul_le_mul_left (2 ^ L) htop) s
  exact Nat.not_le_of_gt hbound (Nat.le_trans (Nat.mul_le_mul_left _ hl) (Nat.le_trans hxy hu))

/-- A numerical bound below three to the power r times the cycle
coefficient excludes a discrepancy displacement of r full periods. -/
theorem walk_width_lt_of_numerical_ratio {n L m M r : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hbound : 2 ^ L * M < 3 ^ r * 3 ^ oddCount n L * m) :
    ∀ i j, walk n L i < walk n L j + (r : Int) * L := by
  have hp : (2 ^ L * M) ^ 1 < 3 ^ r * (3 ^ oddCount n L * m) ^ 1 := by
    simpa [Nat.mul_assoc] using hbound
  intro i j
  have hh := walk_width_lt_of_numerical_ratio_pow hn h hlo hhi hp i j
  simp only [Int.natCast_one, Int.one_mul] at hh
  omega

/-- Fifth-power room below nine to the fifth excludes a discrepancy
displacement of two full periods. -/
theorem walk_width_lt_twice_of_fifth_room {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hm : 4 ≤ m) (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hroom : M ^ 5 * (M + 2) < (9 : Nat) ^ 5 * m ^ 6) :
    ∀ i j, walk n L i < walk n L j + 2 * (L : Int) := by
  let A := 3 ^ oddCount n L
  let B := 2 ^ L
  have hratio : m * B ^ 5 ≤ (M + 2) * A ^ 5 := power_ratio_fifth_le_of_interval h hleast hm hlo hhi
  have hn : 0 < n := by have := hlo 0; simp at this; omega
  apply walk_width_lt_of_numerical_ratio (r := 2) hn h hlo hhi
  change B * M < 9 * A * m
  apply Nat.lt_of_not_ge
  intro hcompare
  have hcancel : 0 < A ^ 5 := Nat.pow_pos (Nat.pow_pos (by decide))
  have hpow := Nat.pow_le_pow_left hcompare 5
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow] at hpow
  have hh := Nat.mul_le_mul_left m hpow
  have he₁ : m * (((9 : Nat) ^ 5 * A ^ 5) * m ^ 5) = A ^ 5 * (9 ^ 5 * m ^ 5 * m) := by ac_rfl
  have he₂ : m * (B ^ 5 * M ^ 5) = M ^ 5 * (m * B ^ 5) := by ac_rfl
  rw [he₁, he₂] at hh
  have hcombine := Nat.le_trans hh (Nat.mul_le_mul_left (M ^ 5) hratio)
  have he₃ : M ^ 5 * ((M + 2) * A ^ 5) = A ^ 5 * (M ^ 5 * (M + 2)) := by ac_rfl
  rw [he₃] at hcombine
  have hbound := Nat.le_of_mul_le_mul_left hcombine hcancel
  have hroom' : M ^ 5 * (M + 2) < 9 ^ 5 * m ^ 5 * m := by
    have hm6 : m ^ 6 = m ^ 5 * m := by rw [Nat.pow_succ]
    rwa [hm6, ← Nat.mul_assoc] at hroom
  exact Nat.not_le_of_gt hroom' hbound

/-- The ratio `43/7` lies under the fifth-power ceiling `9^{5/6}`. -/
theorem ratio_43_7_below_fifth_ceiling : 43 ^ 6 < (9 : Nat) ^ 5 * 7 ^ 6 := by decide

/-- The ratio `56/9` lies under the same ceiling, and closer to it. -/
theorem ratio_56_9_below_fifth_ceiling : 56 ^ 6 < (9 : Nat) ^ 5 * 9 ^ 6 := by decide

/-- A rational band `M/m ≤ p/q` stays inside the fifth-power room once the
floor meets an explicit slack threshold. The threshold pays for the `+2`
in `M+2` against the positive gap `9^5 q^6 − p^6`. -/
theorem fifth_room_of_ratio {p q m0 m M : Nat}
    (hceil : p ^ 6 < (9 : Nat) ^ 5 * q ^ 6)
    (hslack : (2 * q) * p ^ 5 < ((9 : Nat) ^ 5 * q ^ 6 - p ^ 6) * m0)
    (hm0 : 0 < m0) (hm : m0 ≤ m) (hM : q * M ≤ p * m) :
    M ^ 5 * (M + 2) < (9 : Nat) ^ 5 * m ^ 6 := by
  have hfive : q ^ 5 * M ^ 5 ≤ p ^ 5 * m ^ 5 := by
    have h := Nat.pow_le_pow_left hM 5
    rwa [Nat.mul_pow, Nat.mul_pow] at h
  have hstep : q * (M + 2) ≤ p * m + 2 * q := by
    calc
      q * (M + 2) = q * M + q * 2 := by rw [Nat.mul_add]
      _ = q * M + 2 * q := by rw [Nat.mul_comm q 2]
      _ ≤ p * m + 2 * q := Nat.add_le_add_right hM _
  have hprod : q ^ 6 * (M ^ 5 * (M + 2)) ≤ p ^ 5 * m ^ 5 * (p * m + 2 * q) := by
    have h := Nat.mul_le_mul hfive hstep
    have he : q ^ 6 * (M ^ 5 * (M + 2)) = (q ^ 5 * M ^ 5) * (q * (M + 2)) := by
      rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_assoc q, Nat.mul_comm q (M ^ 5),
        Nat.mul_assoc (M ^ 5), ← Nat.mul_assoc]
    rwa [he]
  have hpos : p ^ 6 ≤ (9 : Nat) ^ 5 * q ^ 6 := Nat.le_of_lt hceil
  have hscale : ((9 : Nat) ^ 5 * q ^ 6 - p ^ 6) * m0 ≤ (9 ^ 5 * q ^ 6 - p ^ 6) * m :=
    Nat.mul_le_mul_left _ hm
  have hlt : (2 * q) * p ^ 5 < (9 ^ 5 * q ^ 6 - p ^ 6) * m :=
    Nat.lt_of_lt_of_le hslack hscale
  have hlinear : p ^ 5 * (p * m + 2 * q) < 9 ^ 5 * q ^ 6 * m := by
    calc
      _ = p ^ 6 * m + (2 * q) * p ^ 5 := by
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (p ^ 5) (2 * q), ← Nat.pow_succ]
      _ < p ^ 6 * m + (9 ^ 5 * q ^ 6 - p ^ 6) * m := Nat.add_lt_add_left hlt _
      _ = (p ^ 6 + (9 ^ 5 * q ^ 6 - p ^ 6)) * m := by rw [Nat.add_mul]
      _ = _ := by rw [Nat.add_sub_of_le hpos]
  have hm5 : 0 < m ^ 5 := Nat.pow_pos (by omega : 0 < m)
  have hstrict : q ^ 6 * (M ^ 5 * (M + 2)) < q ^ 6 * (9 ^ 5 * m ^ 6) := by
    calc
      _ ≤ p ^ 5 * m ^ 5 * (p * m + 2 * q) := hprod
      _ = p ^ 5 * (p * m + 2 * q) * m ^ 5 := by ac_rfl
      _ < (9 ^ 5 * q ^ 6 * m) * m ^ 5 := Nat.mul_lt_mul_of_pos_right hlinear hm5
      _ = (9 ^ 5 * q ^ 6) * (m * m ^ 5) := by rw [Nat.mul_assoc]
      _ = (9 ^ 5 * q ^ 6) * (m ^ 5 * m) := by rw [Nat.mul_comm m]
      _ = (9 ^ 5 * q ^ 6) * m ^ 6 := by rw [← Nat.pow_succ]
      _ = _ := by rw [Nat.mul_comm (9 ^ 5) (q ^ 6), Nat.mul_assoc]
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-- Every integer band of ratio at most `43/7`, with floor at least four,
satisfies the fifth-power room. -/
theorem fifth_room_of_ratio_43_7 {m M : Nat} (hm : 4 ≤ m) (hM : 7 * M ≤ 43 * m) :
    M ^ 5 * (M + 2) < (9 : Nat) ^ 5 * m ^ 6 :=
  fifth_room_of_ratio (p := 43) (q := 7) (m0 := 4) ratio_43_7_below_fifth_ceiling
    (by decide) (by decide) hm hM

/-- Every integer band of ratio at most `56/9`, with floor at least nineteen,
satisfies the fifth-power room. -/
theorem fifth_room_of_ratio_56_9 {m M : Nat} (hm : 19 ≤ m) (hM : 9 * M ≤ 56 * m) :
    M ^ 5 * (M + 2) < (9 : Nat) ^ 5 * m ^ 6 :=
  fifth_room_of_ratio (p := 56) (q := 9) (m0 := 19) ratio_56_9_below_fifth_ceiling
    (by decide) (by decide) hm hM

/-- A band of ratio at most `43/7` has discrepancy width strictly below
twice the least period. -/
theorem walk_width_lt_twice_of_ratio_43_7 {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hm : 4 ≤ m) (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hM : 7 * M ≤ 43 * m) : ∀ i j, walk n L i < walk n L j + 2 * (L : Int) :=
  walk_width_lt_twice_of_fifth_room h hleast hm hlo hhi (fifth_room_of_ratio_43_7 hm hM)

/-- A band of ratio at most `56/9` has discrepancy width strictly below
twice the least period. -/
theorem walk_width_lt_twice_of_ratio_56_9 {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hm : 19 ≤ m) (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hM : 9 * M ≤ 56 * m) : ∀ i j, walk n L i < walk n L j + 2 * (L : Int) :=
  walk_width_lt_twice_of_fifth_room h hleast (by omega) hlo hhi (fifth_room_of_ratio_56_9 hm hM)

/-- A band of numerical width at most six times its floor has
discrepancy width strictly below twice the least period. -/
theorem walk_width_lt_twice_of_sixfold {n L m M : Nat} (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hm : 4 ≤ m) (hlo : ∀ i, m ≤ acceleratedOrbit i n) (hhi : ∀ i, acceleratedOrbit i n ≤ M)
    (hM : M ≤ 6 * m) : ∀ i j, walk n L i < walk n L j + 2 * (L : Int) := by
  apply walk_width_lt_twice_of_fifth_room h hleast hm hlo hhi
  have h₁ := Nat.pow_le_pow_left hM 5
  have h₂ : M + 2 ≤ 7 * m := by omega
  have hm5 : 0 < m ^ 5 := Nat.pow_pos (by omega)
  calc
    _ ≤ (6 * m) ^ 5 * (7 * m) := Nat.mul_le_mul h₁ h₂
    _ = (6 ^ 5 * 7) * m ^ 5 * m := by rw [Nat.mul_pow]; ac_rfl
    _ < 9 ^ 5 * m ^ 5 * m :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by decide) hm5) (by omega)
    _ = _ := by rw [Nat.mul_assoc, ← Nat.pow_succ]

end Collatz.CycleNumericalWidth
