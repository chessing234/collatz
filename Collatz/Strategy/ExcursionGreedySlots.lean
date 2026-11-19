import Collatz.Strategy.ExcursionLattice

/-!
# Distinct sources in overlapping residue classes

Within one outgoing valuation stratum, the mixed periods are powers of three
times a common dyadic factor. Two such residue classes are nested or disjoint.
When assigning distinct sources, process the smallest classes first and take
the least available source in each class. A later class that could use this
source can also use the earlier class's displaced source.
-/

namespace Collatz.ExcursionGreedySlots

/-- A later class contains an earlier one whenever they meet. -/
def NestedOrder : List (Nat → Prop) → Prop
  | [] => True
  | p :: ps => (∀ q ∈ ps, (∃ x, p x ∧ q x) → ∀ y, p y → q y) ∧ NestedOrder ps

/-- An admissible residue assignment with no repeated or forbidden slots. -/
inductive Assignment : List Nat → List (Nat → Prop) → List Nat → Prop where
  | nil {used : List Nat} : Assignment used [] []
  | cons {used : List Nat} {p : Nat → Prop} {ps : List (Nat → Prop)} {x : Nat} {xs : List Nat} :
      x ∉ used → p x → Assignment (x :: used) ps xs → Assignment used (p :: ps) (x :: xs)

/-- A greedy assignment uses the least admissible available slot each time. -/
inductive Greedy : List Nat → List (Nat → Prop) → List Nat → Prop where
  | nil {used : List Nat} : Greedy used [] []
  | cons {used : List Nat} {p : Nat → Prop} {ps : List (Nat → Prop)} {x : Nat} {xs : List Nat} :
      x ∉ used → p x → (∀ y, y ∉ used → p y → x ≤ y) →
      Greedy (x :: used) ps xs → Greedy used (p :: ps) (x :: xs)

theorem Assignment.weaken {used used' : List Nat} {ps : List (Nat → Prop)} {xs : List Nat}
    (h : Assignment used ps xs) (hs : ∀ x ∈ used', x ∈ used) :
    Assignment used' ps xs := by
  induction h generalizing used' with
  | nil => exact Assignment.nil
  | cons hfree hp _ ih =>
    refine Assignment.cons (fun hu => hfree (hs _ hu)) hp (ih ?_)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs x ht)

/-- Congruence classes with nested moduli have the ordered intersection law. -/
theorem residue_subset {d e r s x : Nat} (hde : d ∣ e)
    (hx : x % e = r) (hy : x % d = s) :
    ∀ y, y % e = r → y % d = s := by
  intro y h
  calc
    _ = (y % e) % d := (Nat.mod_mod_of_dvd _ hde).symm
    _ = (x % e) % d := by rw [h, hx]
    _ = _ := (Nat.mod_mod_of_dvd _ hde).trans hy

/-- Ternary extensions of the same dyadic class are nested whenever they meet. -/
theorem mixed_class_subset {v p q r s x : Nat} (hqp : q ≤ p)
    (hx : x % (2 ^ (v + 1) * 3 ^ p) = r)
    (hy : x % (2 ^ (v + 1) * 3 ^ q) = s) :
    ∀ y, y % (2 ^ (v + 1) * 3 ^ p) = r → y % (2 ^ (v + 1) * 3 ^ q) = s := by
  apply residue_subset _ hx hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hqp
  refine ⟨3 ^ k, ?_⟩
  rw [show (3 : Nat) ^ (q + k) = 3 ^ q * 3 ^ k from Nat.pow_add .., Nat.mul_assoc]

private theorem Assignment.swap_used {a b : Nat} {used xs : List Nat}
    {ps : List (Nat → Prop)} (h : Assignment (a :: b :: used) ps xs) :
    Assignment (b :: a :: used) ps xs :=
  h.weaken (fun _ hx => (List.Perm.swap a b used).mem_iff.mp hx)

/-- Move the new greedy choice into the occupied list, exchanging it with
the previous choice if the new choice had been assigned in the suffix. -/
theorem Assignment.reassign {a g : Nat} {used xs : List Nat} {ps : List (Nat → Prop)}
    (h : Assignment (a :: used) ps xs) (ha : a ∉ used) (hg : g ∉ used) (hga : g ≠ a)
    (hallow : ∀ p ∈ ps, p g → p a) :
    Assignment (g :: used) ps (xs.replace g a) := by
  induction ps generalizing used xs with
  | nil =>
    cases h
    exact Assignment.nil
  | cons p ps ih =>
    cases h with
    | @cons _ _ _ x xs hfree hp ht =>
      by_cases hx : x = g
      · subst x
        rw [List.replace_cons_self]
        exact Assignment.cons (by simp [ha, Ne.symm hga])
          (hallow p List.mem_cons_self hp) ht.swap_used
      · rw [List.replace_cons]
        simp only [beq_eq_false_iff_ne.mpr (Ne.symm hx)]
        have hxa : x ≠ a := fun h => hfree (List.mem_cons.mpr (Or.inl h))
        have hxu : x ∉ used := fun h => hfree (List.mem_cons_of_mem _ h)
        have ht' := ih ht.swap_used (by simp [ha, Ne.symm hxa])
          (by simp [hg, Ne.symm hx]) (fun q hq => hallow q (List.mem_cons_of_mem _ hq))
        exact Assignment.cons (by simp [hx, hxu]) hp ht'.swap_used

private theorem replace_perm {g a : Nat} {xs : List Nat} (hg : g ∈ xs) :
    List.Perm (a :: xs) (g :: xs.replace g a) := by
  induction xs with
  | nil => simp at hg
  | cons x xs ih =>
    by_cases hx : x = g
    · subst x
      rw [List.replace_cons_self]
      exact List.Perm.swap g a xs
    · have ht : g ∈ xs := (List.mem_cons.mp hg).resolve_left (Ne.symm hx)
      rw [List.replace_cons]
      simp only [beq_eq_false_iff_ne.mpr (Ne.symm hx)]
      exact (List.Perm.swap x a xs).trans
        (((ih ht).cons x).trans (List.Perm.swap g x (xs.replace g a)))

open Collatz.ExcursionLattice

private theorem factor_cons {a c x y : Nat} {xs ys : List Nat} (hy : y ≤ x)
    (hrest : factors a c xs * ys.prod ≤ xs.prod * factors a c ys) :
    factors a c (x :: xs) * (y :: ys).prod ≤
      (x :: xs).prod * factors a c (y :: ys) := by
  change (a * x + c) * factors a c xs * (y * ys.prod) ≤
    x * xs.prod * ((a * y + c) * factors a c ys)
  calc
    _ = ((a * x + c) * y) * (factors a c xs * ys.prod) := by ac_rfl
    _ ≤ (x * (a * y + c)) * (xs.prod * factors a c ys) :=
      Nat.mul_le_mul (cross_factor a c hy) hrest
    _ = x * xs.prod * ((a * y + c) * factors a c ys) := by ac_rfl

/-- In a nested order, the greedy assignment maximizes the product of the
decreasing affine factors among all feasible assignments. -/
theorem greedy_product {used xs gs : List Nat} {ps : List (Nat → Prop)} {a c : Nat}
    (hg : Greedy used ps gs) (hx : Assignment used ps xs) (ho : NestedOrder ps) :
    factors a c xs * gs.prod ≤ xs.prod * factors a c gs := by
  induction hg generalizing xs with
  | nil =>
    cases hx
    simp [factors]
  | @cons used p ps g gs hfree hp hleast _ ih =>
    cases hx with
    | @cons _ _ _ x xs hxf hxp htail =>
      have hle := hleast x hxf hxp
      by_cases hgx : g = x
      · subst x
        exact factor_cons (Nat.le_refl g) (ih htail ho.2)
      · have hrep := htail.reassign hxf hfree hgx
          (fun q hq hqg => ho.1 q hq ⟨g, hp, hqg⟩ x hxp)
        by_cases hmem : g ∈ xs
        · have hperm := replace_perm (a := x) hmem
          have hcmp := factor_cons (Nat.le_refl g) (ih hrep ho.2)
          have hnum := (hperm.map (fun y => a * y + c)).prod_nat
          simpa only [factors, hnum, hperm.prod_nat] using hcmp
        · rw [List.replace_of_not_mem hmem] at hrep
          exact factor_cons hle (ih hrep ho.2)

theorem Greedy.assignment {used gs : List Nat} {ps : List (Nat → Prop)}
    (h : Greedy used ps gs) : Assignment used ps gs := by
  induction h with
  | nil => exact Assignment.nil
  | cons hfree hp _ _ ih => exact Assignment.cons hfree hp ih

/-- Any feasible assignment can be transformed into a greedy assignment. -/
theorem exists_greedy {used xs : List Nat} {ps : List (Nat → Prop)}
    (h : Assignment used ps xs) (ho : NestedOrder ps) : ∃ gs, Greedy used ps gs := by
  induction ps generalizing used xs with
  | nil => exact ⟨[], Greedy.nil⟩
  | cons p ps ih =>
    cases h with
    | @cons _ _ _ x xs hfree hpx htail =>
      have hex : ∃ g, g ∉ used ∧ p g := ⟨x, hfree, hpx⟩
      obtain ⟨g, ⟨hgf, hpg⟩, hmin⟩ := Collatz.Minimum.exists_min hex
      have hleast : ∀ y, y ∉ used → p y → g ≤ y := by
        intro y hy hpy
        exact Nat.le_of_not_gt (fun hlt => hmin y hlt ⟨hy, hpy⟩)
      by_cases hgx : g = x
      · subst g
        obtain ⟨gs, hgs⟩ := ih htail ho.2
        exact ⟨x :: gs, Greedy.cons hfree hpx hleast hgs⟩
      · have hr := htail.reassign hfree hgf hgx
          (fun q hq hqg => ho.1 q hq ⟨g, hpg, hqg⟩ x hpx)
        obtain ⟨gs, hgs⟩ := ih hr ho.2
        exact ⟨g :: gs, Greedy.cons hgf hpg hleast hgs⟩

/-- The comparison product is attained by a feasible assignment. -/
theorem exists_optimal_assignment {used xs : List Nat} {ps : List (Nat → Prop)}
    (h : Assignment used ps xs) (ho : NestedOrder ps) (a c : Nat) :
    ∃ gs, Assignment used ps gs ∧
      ∀ ys, Assignment used ps ys → factors a c ys * gs.prod ≤
        ys.prod * factors a c gs := by
  obtain ⟨gs, hg⟩ := exists_greedy h ho
  exact ⟨gs, hg.assignment, fun _ hy => greedy_product hg hy ho⟩

/-- Incoming congruence data for one source within an outgoing stratum. -/
structure SlotClass where
  ternarySteps : Nat
  residue : Nat

def SlotClass.admits (m v : Nat) (s : SlotClass) (x : Nat) : Prop :=
  m ≤ x ∧ x % (2 ^ (v + 1) * 3 ^ s.ternarySteps) = s.residue

/-- Sorting by decreasing ternary exponent is a valid greedy order. -/
theorem nested_mixed_order {m v : Nat} {classes : List SlotClass}
    (h : classes.Pairwise (fun p q => q.ternarySteps ≤ p.ternarySteps)) :
    NestedOrder (classes.map (SlotClass.admits m v)) := by
  induction classes with
  | nil => simp [NestedOrder]
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    refine ⟨?_, ih htail⟩
    intro q hq hmeet y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    obtain ⟨x, hxp, hxs⟩ := hmeet
    exact ⟨hy.1, mixed_class_subset (hhead s hs) hxp.2 hxs.2 y hy.2⟩

/-- The greedy assignment gives the optimal bound within a fixed odd-run
length, subject to the listed residues and distinctness. -/
theorem greedy_mixed_class_product {m v : Nat} {classes : List SlotClass} {xs gs : List Nat}
    (horder : classes.Pairwise (fun p q => q.ternarySteps ≤ p.ternarySteps))
    (hx : Assignment [] (classes.map (SlotClass.admits m v)) xs)
    (hg : Greedy [] (classes.map (SlotClass.admits m v)) gs) :
    factors (3 ^ v) (3 ^ v - 2 ^ v) xs * gs.prod ≤
      xs.prod * factors (3 ^ v) (3 ^ v - 2 ^ v) gs :=
  greedy_product hg hx (nested_mixed_order horder)

open Collatz.ExcursionBudget

/-- A valuation group with its ordered congruences and greedy comparison slots. -/
structure GreedyStratum where
  actual : Stratum
  classes : List SlotClass
  slots : List Nat

def GreedyStratum.Certified (m : Nat) (g : GreedyStratum) : Prop :=
  g.classes.Pairwise (fun p q => q.ternarySteps ≤ p.ternarySteps) ∧
  Assignment [] (g.classes.map (SlotClass.admits m g.actual.oddSteps)) g.actual.sources ∧
  Greedy [] (g.classes.map (SlotClass.admits m g.actual.oddSteps)) g.slots

def greedyDenominator (groups : List GreedyStratum) : Nat :=
  (groups.map (fun g => g.slots.prod)).prod

def greedyNumerator (groups : List GreedyStratum) : Nat :=
  (groups.map (fun g => g.actual.factorProduct g.slots)).prod

/-- A partition into certified greedy assignments gives a descent if the
resulting optimal product is below the accumulated denominator. -/
theorem trace_greedy_drop {n e m : Nat} {rs : List Run} {groups : List GreedyStratum}
    (ht : Trace n e rs) (hn : 0 < n)
    (hperm : List.Perm (visits n rs) (groups.flatMap (fun g => g.actual.entries)))
    (hcert : ∀ g ∈ groups, g.Certified m)
    (hgap : greedyNumerator groups < 2 ^ time rs * greedyDenominator groups) : e < n := by
  apply Nat.lt_of_not_ge
  intro hkeep
  have hcomp := collect_product_bounds GreedyStratum.actual GreedyStratum.slots
    (fun g hg => by
      obtain ⟨horder, hactual, hgreedy⟩ := hcert g hg
      exact greedy_mixed_class_product horder hactual hgreedy)
  rw [← (hperm.map Visit.source).prod_nat, ← (hperm.map Visit.numerator).prod_nat] at hcomp
  have hpos : ∀ r ∈ visits n rs, 0 < r.source := by
    intro r hr
    obtain ⟨_, _, _, hrun⟩ := visit_realized ht hr
    have hodd := hrun.1
    omega
  exact Nat.not_lt_of_ge (trace_denominator_le ht hn hkeep hpos hcomp) hgap

end Collatz.ExcursionGreedySlots
