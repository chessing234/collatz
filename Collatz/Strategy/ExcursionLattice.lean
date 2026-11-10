import Collatz.Strategy.ExcursionBudget

/-!
# Valuation-stratified excursion products

The source of an excursion of odd-run length `v` lies in a single residue
class modulo `2^(v+1)`. Distinct sources in this class therefore have their
own staircase. Grouping the exact excursion product by run length gives a
finite constraint for non-descending endpoints.
-/

namespace Collatz.ExcursionLattice

open Collatz.ExcursionBudget Collatz.ExcursionMap

/-- Distinct ordered sources of the same odd-run length are separated by
at least the modulus of that run length. -/
theorem source_spacing {x y v u u' W W' e e' : Nat}
    (hx : IsExcursion x v u W e) (hy : IsExcursion y v u' W' e')
    (hxy : x < y) : x + 2 ^ (v + 1) ≤ y := by
  have hsource := hx.2.2.2.2.2.1
  have htarget := hy.2.2.2.2.2.1
  have hscaled : 2 ^ v * u < 2 ^ v * u' := by omega
  have hu := Nat.lt_of_mul_lt_mul_left hscaled
  have hdiff : u + 2 ≤ u' := by
    have huodd := hx.2.1
    have hu'odd := hy.2.1
    omega
  have hstep := Nat.mul_le_mul_left (2 ^ v) hdiff
  rw [Nat.mul_add, ← Nat.pow_succ, ← hsource, ← htarget] at hstep
  omega

/-- The smallest `length` points of a grid with the given base and spacing. -/
def grid (base spacing : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => base :: grid (base + spacing) spacing k

/-- Product of affine numerators over a list of sources. -/
def factors (a c : Nat) (sources : List Nat) : Nat :=
  (sources.map (fun x => a * x + c)).prod

/-- First candidate source at or above the floor in the valuation class. -/
def classBase (m v : Nat) : Nat :=
  let r := 2 ^ v - 1
  let d := 2 ^ (v + 1)
  r + d * ((m - r + (d - 1)) / d)

theorem floor_le_classBase (m v : Nat) : m ≤ classBase m v := by
  let r := 2 ^ v - 1
  let d := 2 ^ (v + 1)
  have hd : 0 < d := Nat.two_pow_pos _
  have hdiv := Nat.mod_add_div (m - r + (d - 1)) d
  have hmod := Nat.mod_lt (m - r + (d - 1)) hd
  change m ≤ r + d * ((m - r + (d - 1)) / d)
  omega

theorem classBase_le_source {m x v u W y : Nat} (h : IsExcursion x v u W y)
    (hfloor : m ≤ x) : classBase m v ≤ x := by
  let r := 2 ^ v - 1
  let d := 2 ^ (v + 1)
  let k := u / 2
  have huodd := h.2.1
  have hu : u = 1 + 2 * k := by dsimp [k]; omega
  have heq := h.2.2.2.2.2.1
  rw [hu, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ] at heq
  have hx : x = r + d * k := by
    have hpos := Nat.two_pow_pos v
    change x + 1 = 2 ^ v + d * k at heq
    dsimp only [r]
    omega
  have hdiff : m - r ≤ d * k := by omega
  have hd : 0 < d := Nat.two_pow_pos _
  have hq : (m - r + (d - 1)) / d ≤ k := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [Nat.succ_mul, Nat.mul_comm k d]
    omega
  change r + d * ((m - r + (d - 1)) / d) ≤ x
  rw [hx]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left d hq) _

/-- Cross-multiplied monotonicity of an affine factor divided by its source. -/
theorem cross_factor (a c : Nat) {m x : Nat} (hm : m ≤ x) :
    (a * x + c) * m ≤ x * (a * m + c) := by
  simp only [Nat.add_mul, Nat.mul_add]
  have hmain : a * x * m = x * (a * m) := by ac_rfl
  rw [hmain, Nat.mul_comm x c]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left c hm) _

/-- A sorted, spaced list of sources has a smaller product of the factors
`a + c/x` than the grid of smallest possible sources. -/
theorem grid_product {a c spacing : Nat} {sources : List Nat}
    (hsorted : sources.Pairwise (fun x y => x + spacing ≤ y))
    {m : Nat} (hfloor : ∀ x ∈ sources, m ≤ x) :
    factors a c sources * (grid m spacing sources.length).prod ≤
      sources.prod * factors a c (grid m spacing sources.length) := by
  induction sources generalizing m with
  | nil => simp [grid, factors]
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    have hmx := hfloor x List.mem_cons_self
    have hmnext : ∀ y ∈ xs, m + spacing ≤ y :=
      fun y hy => Nat.le_trans (Nat.add_le_add_right hmx spacing) (hhead y hy)
    have hrest := ih htail hmnext
    change (a * x + c) * factors a c xs * (m * (grid (m + spacing) spacing xs.length).prod) ≤
      x * xs.prod * ((a * m + c) * factors a c (grid (m + spacing) spacing xs.length))
    calc
      _ = ((a * x + c) * m) *
          (factors a c xs * (grid (m + spacing) spacing xs.length).prod) := by ac_rfl
      _ ≤ (x * (a * m + c)) *
          (xs.prod * factors a c (grid (m + spacing) spacing xs.length)) :=
        Nat.mul_le_mul (cross_factor a c hmx) hrest
      _ = x * xs.prod * ((a * m + c) * factors a c (grid (m + spacing) spacing xs.length)) := by
        ac_rfl

/-- A sorted collection of distinct sources with the same run length uses
the corresponding valuation grid. -/
theorem run_class_product {sources : List Nat} {m v : Nat}
    (hsorted : sources.Pairwise (· < ·)) (hfloor : ∀ x ∈ sources, m ≤ x)
    (hclass : ∀ x ∈ sources, ∃ u W y, IsExcursion x v u W y) :
    let comparison := grid (classBase m v) (2 ^ (v + 1)) sources.length
    factors (3 ^ v) (3 ^ v - 2 ^ v) sources * comparison.prod ≤
      sources.prod * factors (3 ^ v) (3 ^ v - 2 ^ v) comparison := by
  apply grid_product
  · refine List.Pairwise.imp_of_mem ?_ hsorted
    intro x y hx hy hxy
    obtain ⟨ux, Wx, ex, hxrun⟩ := hclass x hx
    obtain ⟨uy, Wy, ey, hyrun⟩ := hclass y hy
    exact source_spacing hxrun hyrun hxy
  · intro x hx
    obtain ⟨u, W, y, hrun⟩ := hclass x hx
    exact classBase_le_source hrun (hfloor x hx)

/-- The run length and source of a visited excursion. -/
structure Visit where
  oddSteps : Nat
  source : Nat
  deriving DecidableEq

/-- Visit records in reverse chronological order, recovered from a trace's
run lengths and the shortcut orbit. -/
def visits (n : Nat) : List Run → List Visit
  | [] => []
  | r :: rs => ⟨r.oddSteps, Collatz.acceleratedOrbit (time rs) n⟩ :: visits n rs

theorem visit_time {n : Nat} {rs : List Run} {r : Visit} (hr : r ∈ visits n rs) :
    ∃ j ≤ time rs, r.source = Collatz.acceleratedOrbit j n := by
  induction rs with
  | nil => simp [visits] at hr
  | cons step rs ih =>
    have hle : time rs ≤ time (step :: rs) := Nat.le_add_left ..
    rcases List.mem_cons.mp hr with rfl | htail
    · exact ⟨time rs, hle, rfl⟩
    · obtain ⟨j, hj, heq⟩ := ih htail
      exact ⟨j, Nat.le_trans hj hle, heq⟩

def Visit.numerator (r : Visit) : Nat :=
  3 ^ r.oddSteps * r.source + (3 ^ r.oddSteps - 2 ^ r.oddSteps)

/-- The exact product retains the endpoint and all excursion sources. -/
theorem trace_product {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    2 ^ time rs * e * ((visits n rs).map Visit.source).prod =
      n * ((visits n rs).map Visit.numerator).prod := by
  induction h with
  | nil => simp [time, visits]
  | @step x y v u W rs hprev hstep ih =>
    calc
      _ = (2 ^ (v + W) * y) * (2 ^ time rs * x * ((visits n rs).map Visit.source).prod) := by
        simp only [visits, time, hprev.landing, List.map_cons, List.prod_cons, Nat.pow_add]
        ac_rfl
      _ = (3 ^ v * x + (3 ^ v - 2 ^ v)) * (n * ((visits n rs).map Visit.numerator).prod) := by
        rw [ih, single_affine hstep]
      _ = n * ((visits n (⟨v, W⟩ :: rs)).map Visit.numerator).prod := by
        simp only [visits, Visit.numerator, hprev.landing, List.map_cons, List.prod_cons]
        ac_rfl

theorem visit_realized {n e : Nat} {rs : List Run} (h : Trace n e rs)
    {r : Visit} (hr : r ∈ visits n rs) : ∃ u W y, IsExcursion r.source r.oddSteps u W y := by
  induction h with
  | nil => simp [visits] at hr
  | @step x y v u W rs hprev hstep ih =>
    rw [visits, hprev.landing] at hr
    rcases List.mem_cons.mp hr with rfl | htail
    · exact ⟨u, W, y, hstep⟩
    · exact ih htail

/-- A stratum contains sources with one common odd-run length. -/
structure Stratum where
  oddSteps : Nat
  sources : List Nat

def Stratum.entries (g : Stratum) : List Visit :=
  g.sources.map (fun x => ⟨g.oddSteps, x⟩)

def Stratum.grid (g : Stratum) (m : Nat) : List Nat :=
  ExcursionLattice.grid (classBase m g.oddSteps) (2 ^ (g.oddSteps + 1)) g.sources.length

def Stratum.gridNumerator (g : Stratum) (m : Nat) : Nat :=
  factors (3 ^ g.oddSteps) (3 ^ g.oddSteps - 2 ^ g.oddSteps) (g.grid m)

def gridDenominator (m : Nat) (groups : List Stratum) : Nat :=
  (groups.map (fun g => (g.grid m).prod)).prod

def gridNumerator (m : Nat) (groups : List Stratum) : Nat :=
  (groups.map (fun g => g.gridNumerator m)).prod

/-- Compare the orbit products with the product of the individual grids. -/
theorem stratified_product {m : Nat} {groups : List Stratum}
    (hsorted : ∀ g ∈ groups, g.sources.Pairwise (· < ·))
    (hfloor : ∀ r ∈ groups.flatMap Stratum.entries, m ≤ r.source)
    (hclass : ∀ r ∈ groups.flatMap Stratum.entries,
      ∃ u W y, IsExcursion r.source r.oddSteps u W y) :
    ((groups.flatMap Stratum.entries).map Visit.numerator).prod * gridDenominator m groups ≤
      ((groups.flatMap Stratum.entries).map Visit.source).prod * gridNumerator m groups := by
  induction groups with
  | nil => simp [gridDenominator, gridNumerator]
  | cons g gs ih =>
    have hmem {x : Nat} (hx : x ∈ g.sources) :
        (⟨g.oddSteps, x⟩ : Visit) ∈ (g :: gs).flatMap Stratum.entries := by
      apply List.mem_flatMap.mpr
      exact ⟨g, List.mem_cons_self, List.mem_map_of_mem hx⟩
    have hhead := run_class_product (hsorted g List.mem_cons_self)
      (fun _ hx => hfloor _ (hmem hx)) (fun _ hx => hclass _ (hmem hx))
    have hlift {r : Visit} (hr : r ∈ gs.flatMap Stratum.entries) :
        r ∈ (g :: gs).flatMap Stratum.entries := by
      simp only [List.flatMap_cons, List.mem_append]
      exact Or.inr hr
    have htail := ih (fun g hg => hsorted g (List.mem_cons_of_mem _ hg))
      (fun _ hr => hfloor _ (hlift hr)) (fun _ hr => hclass _ (hlift hr))
    have hden : (g.entries.map Visit.source).prod = g.sources.prod := by
      simp [Stratum.entries, List.map_map, Function.comp_def]
    have hnum : (g.entries.map Visit.numerator).prod =
        factors (3 ^ g.oddSteps) (3 ^ g.oddSteps - 2 ^ g.oddSteps) g.sources := by
      simp [Stratum.entries, List.map_map, Function.comp_def, Visit.numerator, factors]
    have hhead' : factors (3 ^ g.oddSteps) (3 ^ g.oddSteps - 2 ^ g.oddSteps) g.sources *
        (g.grid m).prod ≤ g.sources.prod * g.gridNumerator m := hhead
    simp only [List.flatMap_cons, List.map_append, List.prod_append_nat, hnum, hden,
      gridDenominator, gridNumerator, List.map_cons, List.prod_cons]
    change factors (3 ^ g.oddSteps) (3 ^ g.oddSteps - 2 ^ g.oddSteps) g.sources *
        ((gs.flatMap Stratum.entries).map Visit.numerator).prod *
        ((g.grid m).prod * gridDenominator m gs) ≤
      g.sources.prod * ((gs.flatMap Stratum.entries).map Visit.source).prod *
        (g.gridNumerator m * gridNumerator m gs)
    calc
      _ = (factors (3 ^ g.oddSteps) (3 ^ g.oddSteps - 2 ^ g.oddSteps) g.sources * (g.grid m).prod) *
          (((gs.flatMap Stratum.entries).map Visit.numerator).prod * gridDenominator m gs) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul hhead' htail
      _ = g.sources.prod * ((gs.flatMap Stratum.entries).map Visit.source).prod *
          (g.gridNumerator m * gridNumerator m gs) := by ac_rfl

/-- A cross-multiplied upper bound on the visit product also bounds the
accumulated denominator when the endpoint is at least the source. -/
theorem trace_denominator_le {n e lower upper : Nat} {rs : List Run} (h : Trace n e rs)
    (hn : 0 < n) (hkeep : n ≤ e) (hpos : ∀ r ∈ visits n rs, 0 < r.source)
    (hbound : ((visits n rs).map Visit.numerator).prod * lower ≤
      ((visits n rs).map Visit.source).prod * upper) :
    2 ^ time rs * lower ≤ upper := by
  let d := ((visits n rs).map Visit.source).prod
  let a := ((visits n rs).map Visit.numerator).prod
  have hsurvive : 2 ^ time rs * d ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ hn
    calc
      _ = 2 ^ time rs * n * d := by ac_rfl
      _ ≤ 2 ^ time rs * e * d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkeep)
      _ = n * a := trace_product h
  have hd : 0 < d := by
    apply List.prod_pos_iff_forall_pos_nat.mpr
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hpos r hr
  apply Nat.le_of_mul_le_mul_left _ hd
  calc
    _ = (2 ^ time rs * d) * lower := by ac_rfl
    _ ≤ a * lower := Nat.mul_le_mul_right _ hsurvive
    _ ≤ d * upper := hbound

/-- If the endpoint stays above the source, the accumulated denominator
fits below the product of the valuation grids. The partition may be
computed separately and supplied as a permutation certificate. -/
theorem trace_grid_bound {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hn : 0 < n) (hkeep : n ≤ e) {m : Nat} (hm : 0 < m) {groups : List Stratum}
    (hperm : List.Perm (visits n rs) (groups.flatMap Stratum.entries))
    (hsorted : ∀ g ∈ groups, g.sources.Pairwise (· < ·))
    (hfloor : ∀ r ∈ groups.flatMap Stratum.entries, m ≤ r.source) :
    2 ^ time rs * gridDenominator m groups ≤ gridNumerator m groups := by
  have hclass : ∀ r ∈ groups.flatMap Stratum.entries, ∃ u W y,
      IsExcursion r.source r.oddSteps u W y :=
    fun _ hr => visit_realized h (hperm.mem_iff.mpr hr)
  have hgrid := stratified_product hsorted hfloor hclass
  rw [← (hperm.map Visit.source).prod_nat, ← (hperm.map Visit.numerator).prod_nat] at hgrid
  exact trace_denominator_le h hn hkeep
    (fun r hr => Nat.lt_of_lt_of_le hm (hfloor r (hperm.mem_iff.mp hr))) hgrid

/-- A strict violation of the grid bound certifies a descent. -/
theorem trace_grid_drop {n e m : Nat} {rs : List Run} {groups : List Stratum}
    (h : Trace n e rs) (hn : 0 < n) (hm : 0 < m)
    (hperm : List.Perm (visits n rs) (groups.flatMap Stratum.entries))
    (hsorted : ∀ g ∈ groups, g.sources.Pairwise (· < ·))
    (hfloor : ∀ r ∈ groups.flatMap Stratum.entries, m ≤ r.source)
    (hcross : gridNumerator m groups < 2 ^ time rs * gridDenominator m groups) : e < n := by
  apply Nat.lt_of_not_ge
  intro hkeep
  exact Nat.not_lt_of_ge (trace_grid_bound h hn hkeep hm hperm hsorted hfloor) hcross

end Collatz.ExcursionLattice
