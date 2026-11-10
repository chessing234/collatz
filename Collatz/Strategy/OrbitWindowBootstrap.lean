import Collatz.Strategy.OrbitOccupationBootstrap

/-!
# Bootstrapped occupation in translated windows

An input interval meets at most two dyadic quotient classes. Within
each class, an odd count determines a translated interval containing
the images. Grouping their widths geometrically lets the smaller
windows use the same occupation bound recursively.
-/

namespace Collatz.OrbitWindowBootstrap

open Collatz.OrbitCapacity Collatz.OrbitOccupationBootstrap Collatz.Sum

private theorem quotient_cases {a x D : Nat} (hD : 0 < D) (ha : a ≤ x) (hx : x < a + D) :
    x / D = a / D ∨ x / D = a / D + 1 := by
  have hlo := Nat.div_le_div_right (c := D) ha
  have hhi : x / D < a / D + 2 := by
    apply (Nat.div_lt_iff_lt_mul hD).2
    have hsplit := Nat.mod_add_div a D
    have hmod := Nat.mod_lt a hD
    rw [Nat.add_mul, Nat.mul_comm (a / D), Nat.two_mul]
    omega
  omega

/-- For a prescribed odd count and input quotient, the endpoint lies in
one interval whose width is a power of three. -/
theorem image_interval (x k : Nat) :
    3 ^ oddCount x k * (x / 2 ^ k) ≤ acceleratedOrbit k x ∧
      acceleratedOrbit k x < 3 ^ oddCount x k * (x / 2 ^ k) + 3 ^ oddCount x k := by
  let D := 2 ^ k
  let r := x % D
  have hmod : r < D := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hodd : oddCount r k = oddCount x k := (Density.oddCount_mod x k).symm
  have hsplit : D * (x / D) + r = x := by
    simpa only [D, r, Nat.add_comm] using Nat.mod_add_div x D
  have h := Congruence.accOrbit_pow_two_mul_add k (x / D) r
  change acceleratedOrbit k (D * (x / D) + r) =
    3 ^ oddCount r k * (x / D) + acceleratedOrbit k r at h
  rw [hsplit, hodd] at h
  have hbound := image_lt (c := 1) (k := k) (x := r) (by simpa using hmod)
  rw [Nat.one_mul, hodd] at hbound
  rw [h]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hbound _⟩

private theorem mod_injective_in_window {a D x y : Nat} (hxa : a ≤ x) (hya : a ≤ y)
    (hx : x < a + D) (hy : y < a + D) (heq : x % D = y % D) : x = y := by
  have hxsub : (x - y) % D = 0 := Nat.sub_mod_eq_zero_of_mod_eq heq
  have hysub : (y - x) % D = 0 := Nat.sub_mod_eq_zero_of_mod_eq heq.symm
  rw [Nat.mod_eq_of_lt (by omega : x - y < D)] at hxsub
  rw [Nat.mod_eq_of_lt (by omega : y - x < D)] at hysub
  omega

private theorem exceptional_in_window (t : Tilt) (h a : Nat) {xs : List Nat}
    (hnd : xs.Nodup) (hx : ∀ x ∈ xs, a ≤ x ∧ x < a + 2 ^ (t.steps * h)) :
    (xs.filter (exceptional t h)).length ≤ 2 * t.cover ^ h := by
  let k := t.steps * h
  let high := xs.filter (exceptional t h)
  let residues := high.map (· % 2 ^ k)
  have hres : residues.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.filter_sublist.nodup hnd)
    intro x y hxmem hymem hne heq
    obtain ⟨hxa, hxb⟩ := hx x (List.mem_filter.mp hxmem).1
    obtain ⟨hya, hyb⟩ := hx y (List.mem_filter.mp hymem).1
    exact hne (mod_injective_in_window hxa hya hxb hyb heq)
  have hsub : residues ⊆ (List.range (2 ^ k * 2)).filter (exceptional t h) := by
    intro r hr
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hr
    have hlow : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hhigh : exceptional t h x = true := (List.mem_filter.mp hxm).2
    have hs : exceptional t h (x % 2 ^ k) = true := by
      dsimp [exceptional, k] at *
      rw [← Density.oddCount_mod]
      exact hhigh
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_of_lt_of_le hlow
      (Nat.le_mul_of_pos_right _ (by decide))), hs⟩
  exact Nat.le_trans (by simpa only [residues, List.length_map] using hres.length_le_of_subset hsub)
    (heavy_count t h)

private def inWindow (a D x : Nat) : Bool := decide (a ≤ x ∧ x < a + D)

private def countWindow (xs : List Nat) (a D : Nat) : Nat :=
  (xs.filter (inWindow a D)).length

private theorem countWindow_raw (xs : List Nat) (a D : Nat) (hnd : xs.Nodup) :
    countWindow xs a D ≤ D := by
  have hsub : xs.filter (inWindow a D) ⊆ List.range' a D := by
    intro x hx
    exact List.mem_range'_1.mpr (of_decide_eq_true (List.mem_filter.mp hx).2)
  simpa only [countWindow, List.length_range'] using
    (List.filter_sublist.nodup hnd).length_le_of_subset hsub

private theorem list_sum_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = sumRange n f := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, sumRange_succ, ih]

private theorem count_by_image_windows {xs : List Nat} (hnd : xs.Nodup) (q M : Nat)
    (hc : ∀ x ∈ xs, ∃ m, m ≤ M ∧
      (inWindow (3 ^ m * q) (3 ^ m) x = true ∨ inWindow (3 ^ m * (q + 1)) (3 ^ m) x = true)) :
    xs.length ≤ sumRange (M + 1) (fun m =>
      countWindow xs (3 ^ m * q) (3 ^ m) + countWindow xs (3 ^ m * (q + 1)) (3 ^ m)) := by
  let cover := (List.range (M + 1)).flatMap (fun m =>
    xs.filter (inWindow (3 ^ m * q) (3 ^ m)) ++
      xs.filter (inWindow (3 ^ m * (q + 1)) (3 ^ m)))
  have hsub : xs ⊆ cover := by
    intro x hx
    obtain ⟨m, hm, hl | hr⟩ := hc x hx
    · exact List.mem_flatMap.mpr ⟨m, List.mem_range.mpr (by omega),
        List.mem_append_left _ (List.mem_filter.mpr ⟨hx, hl⟩)⟩
    · exact List.mem_flatMap.mpr ⟨m, List.mem_range.mpr (by omega),
        List.mem_append_right _ (List.mem_filter.mpr ⟨hx, hr⟩)⟩
  simpa only [cover, List.length_flatMap, List.length_append, countWindow, list_sum_range]
    using hnd.length_le_of_subset hsub

private theorem group_sum {p h : Nat} (F G : Nat → Nat)
    (hblock : ∀ s, s < h → ∀ m, p * s < m → m ≤ p * (s + 1) → F m ≤ G s) :
    sumRange (p * h + 1) F ≤ F 0 + sumRange h (fun s => p * G s) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show p * (h + 1) + 1 = (p * h + 1) + p by rw [Nat.mul_succ]; omega,
      sumRange_split, sumRange_succ h (fun s => p * G s), ← Nat.add_assoc]
    apply Nat.add_le_add (ih (fun s hs => hblock s (Nat.lt_trans hs (Nat.lt_succ_self h))))
    rw [← sumRange_const p (G h)]
    apply sumRange_le
    intro i hi
    apply hblock h (Nat.lt_succ_self h)
    · omega
    · rw [Nat.mul_succ]
      omega

private theorem geometric_sum (W h : Nat) (hW : 0 < W) :
    (W - 1) * sumRange h (fun s => W ^ s) + 1 = W ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sumRange_succ, Nat.mul_add, Nat.add_right_comm, ih, Nat.pow_succ']
    calc
      _ = ((W - 1) + 1) * W ^ h := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ = _ := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hW)]

private theorem initial_sum_le (H h A : Nat) :
    sumRange h (fun s => if s < H then A else 0) ≤ H * A := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sumRange_succ]
    by_cases hh : h < H
    · rw [if_pos hh]
      have hsum : sumRange h (fun s => if s < H then A else 0) ≤ h * A := by
        rw [← sumRange_const]
        apply sumRange_le
        intro i hi
        rw [if_pos (Nat.lt_trans hi hh)]
        exact Nat.le_refl _
      exact Nat.le_trans (Nat.add_le_add_right hsum A) (by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hh))
    · simpa [hh] using ih

/-- Translated windows inherit the exceptional residue rate, uniformly
in their location and in the choice of the nonmerging orbit. -/
theorem window_bound (t : Tilt) (hcover : 8 * t.odd + 1 ≤ t.cover) :
    ∃ C, ∀ (states : Nat → Nat), NoMerging states →
      (∀ k i, ∃ j, states j = acceleratedOrbit k (states i)) →
      ∀ h a (xs : List Nat), xs.Nodup →
        (∀ x ∈ xs, a ≤ x ∧ x < a + 2 ^ (t.steps * h) ∧ ∃ i, states i = x) →
        xs.length ≤ C * t.cover ^ h := by
  obtain ⟨H, hscale⟩ := power_threshold t
  let D := 2 ^ t.steps
  let A := D ^ H
  let C0 := 2 + (2 * t.odd) * (H * A)
  let C := 4 * C0
  have hC0 : 2 ≤ C0 := Nat.le_add_right _ _
  have hW : 0 < t.cover := Nat.lt_of_lt_of_le (by decide) t.cover_ge_two
  refine ⟨C, ?_⟩
  intro states hmerge hclosed h
  induction h using Nat.strongRecOn with
  | ind h ih =>
    intro a xs hnd hx
    let k := t.steps * h
    let high := xs.filter (exceptional t h)
    let low := xs.filter (fun x => !(exceptional t h x))
    let images := low.map (acceleratedOrbit k)
    let q := a / 2 ^ k
    have hhigh : high.length ≤ 2 * t.cover ^ h :=
      exceptional_in_window t h a hnd (fun x hxm => ⟨(hx x hxm).1, (hx x hxm).2.1⟩)
    have hni : images.Nodup := by
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem _ (List.filter_sublist.nodup hnd)
      intro x y hxm hym hne heq
      obtain ⟨i, rfl⟩ := (hx x (List.mem_filter.mp hxm).1).2.2
      obtain ⟨j, rfl⟩ := (hx y (List.mem_filter.mp hym).1).2.2
      exact hne (hmerge k i j heq)
    have him (y : Nat) (hy : y ∈ images) : ∃ i, states i = y := by
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hy
      obtain ⟨i, rfl⟩ := (hx x (List.mem_filter.mp hxm).1).2.2
      exact hclosed k i
    let F := fun m =>
      countWindow images (3 ^ m * q) (3 ^ m) +
        countWindow images (3 ^ m * (q + 1)) (3 ^ m)
    let G := fun s => 2 * (if s < H then A else 0) + 2 * (C * t.cover ^ s)
    have hpieces : images.length ≤ sumRange (t.odd * h + 1) F := by
      apply count_by_image_windows hni q
      intro y hy
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hxm, hl⟩ := List.mem_filter.mp hxm
      obtain ⟨hxa, hxb, _⟩ := hx x hxm
      have ho : oddCount x k ≤ t.odd * h := by
        simpa [exceptional, k, Nat.not_lt] using hl
      refine ⟨oddCount x k, ho, ?_⟩
      have horbit := image_interval x k
      rcases quotient_cases (Nat.two_pow_pos k) hxa hxb with hq | hq
      · exact Or.inl (decide_eq_true (by simpa only [inWindow, q, hq] using horbit))
      · exact Or.inr (decide_eq_true (by simpa only [inWindow, q, hq] using horbit))
    have hzero : F 0 ≤ 2 := by
      have hl := countWindow_raw images (3 ^ 0 * q) (3 ^ 0) hni
      have hr := countWindow_raw images (3 ^ 0 * (q + 1)) (3 ^ 0) hni
      exact Nat.add_le_add hl hr
    have hgroup (s : Nat) (hs : s < h) (m : Nat) (_ : t.odd * s < m)
        (hm : m ≤ t.odd * (s + 1)) : F m ≤ G s := by
      have hpow : (3 : Nat) ^ m ≤ (3 ^ t.odd) ^ (s + 1) := by
        rw [← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) hm
      by_cases hinit : s < H
      · have hwidth : 3 ^ m ≤ A :=
          Nat.le_trans hpow (Nat.le_trans (Nat.pow_le_pow_left (Nat.le_of_lt t.compression) _)
            (Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.succ_le_of_lt hinit)))
        have hraw : F m ≤ 2 * A := by
          rw [Nat.two_mul]
          exact Nat.add_le_add
            (Nat.le_trans (countWindow_raw images _ _ hni) hwidth)
            (Nat.le_trans (countWindow_raw images _ _ hni) hwidth)
        exact Nat.le_trans hraw (by simp [G, hinit])
      · have hscale' := hscale (s + 1) (by omega)
        have hsmall : (3 ^ t.odd) ^ (s + 1) ≤ D ^ s := by
          change D * (3 ^ t.odd) ^ (s + 1) ≤ D ^ (s + 1) at hscale'
          rw [show D ^ (s + 1) = D * D ^ s from Nat.pow_succ'] at hscale'
          exact Nat.le_of_mul_le_mul_left hscale' (Nat.two_pow_pos _)
        have hwidth : 3 ^ m ≤ 2 ^ (t.steps * s) := by
          rw [Nat.pow_mul]
          exact Nat.le_trans hpow hsmall
        have hpart (a' : Nat) : countWindow images a' (3 ^ m) ≤ C * t.cover ^ s := by
          apply ih s hs a' _ (List.filter_sublist.nodup hni)
          intro y hy
          obtain ⟨hy, hb⟩ := List.mem_filter.mp hy
          have hw : a' ≤ y ∧ y < a' + 3 ^ m := of_decide_eq_true hb
          exact ⟨hw.1, Nat.lt_of_lt_of_le hw.2 (Nat.add_le_add_left hwidth _), him y hy⟩
        have hpair : F m ≤ 2 * (C * t.cover ^ s) := by
          rw [Nat.two_mul]
          exact Nat.add_le_add (hpart _) (hpart _)
        simpa [G, hinit] using hpair
    have hgrouped := group_sum F G hgroup
    let S := sumRange h (fun s => if s < H then A else 0)
    let Q := sumRange h (fun s => t.cover ^ s)
    have hsum : sumRange h (fun s => t.odd * G s) =
        (2 * t.odd) * S + (2 * t.odd * C) * Q := by
      have hterm (s : Nat) :
          t.odd * G s = (2 * t.odd) * (if s < H then A else 0) +
            (2 * t.odd * C) * t.cover ^ s := by
        dsimp only [G]
        rw [Nat.mul_add]
        ac_rfl
      rw [sumRange_congr (fun s _ => hterm s), sumRange_add,
        sumRange_const_mul, sumRange_const_mul]
    have hS : S ≤ H * A := initial_sum_le H h A
    have hQ : (8 * t.odd) * Q ≤ t.cover ^ h := by
      have hcoef : 8 * t.odd ≤ t.cover - 1 := by omega
      have he := geometric_sum t.cover h hW
      exact Nat.le_trans (Nat.mul_le_mul_right _ hcoef)
        (by change (t.cover - 1) * Q + 1 = t.cover ^ h at he; omega)
    have hlight : low.length ≤ C0 + C0 * t.cover ^ h := by
      have hlen : low.length = images.length := by simp [images]
      rw [hlen]
      calc
        _ ≤ _ := hpieces
        _ ≤ F 0 + sumRange h (fun s => t.odd * G s) := hgrouped
        _ = F 0 + ((2 * t.odd) * S + (2 * t.odd * C) * Q) := by rw [hsum]
        _ ≤ 2 + ((2 * t.odd) * (H * A) + C0 * t.cover ^ h) := by
          refine Nat.add_le_add hzero (Nat.add_le_add (Nat.mul_le_mul_left _ hS) ?_)
          calc
            _ = C0 * ((2 * 4 * t.odd) * Q) := by dsimp [C]; ac_rfl
            _ ≤ _ := Nat.mul_le_mul_left _ hQ
        _ = _ := by simp only [C0, Nat.add_assoc]
    have hsplit : high.length + low.length = xs.length := by
      simpa only [high, low, List.length_append] using
        (List.filter_append_perm (exceptional t h) xs).length_eq
    have hmono : C0 ≤ C0 * t.cover ^ h :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos hW)
    rw [← hsplit]
    calc
      _ ≤ 2 * t.cover ^ h + (C0 + C0 * t.cover ^ h) := Nat.add_le_add hhigh hlight
      _ ≤ C0 * t.cover ^ h + (C0 * t.cover ^ h + C0 * t.cover ^ h) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hC0) (Nat.add_le_add_right hmono _)
      _ ≤ C * t.cover ^ h := by
        change _ ≤ (4 * C0) * t.cover ^ h
        rw [Nat.mul_assoc]
        omega

/-- The `19/20` occupation bound holds uniformly in the starting point
of the value interval. -/
theorem orbit_window_power :
    ∃ C, ∀ {n a X : Nat}, 0 < X → NoMerging (fun i => acceleratedOrbit i n) →
      ∀ xs : List Nat, xs.Nodup →
        (∀ x ∈ xs, a ≤ x ∧ x < a + X ∧ ∃ i, acceleratedOrbit i n = x) →
        xs.length ^ 20 ≤ C * X ^ 19 := by
  obtain ⟨C, hC⟩ := window_bound tilt149 (by decide)
  refine ⟨C ^ 20 * ((2 : Nat) ^ 2980) ^ 19, ?_⟩
  intro n a X hX hmerge xs hnd hx
  apply power_of_aligned hX
  intro j hj
  have hsteps : tilt149.steps * (20 * j) = 2980 * j := by
    rw [← Nat.mul_assoc]
    rfl
  have hclosed (k i : Nat) :
      ∃ t, acceleratedOrbit t n = acceleratedOrbit k (acceleratedOrbit i n) :=
    ⟨k + i, (acceleratedOrbit_add k i n).symm⟩
  have hsmall (x : Nat) (hxm : x ∈ xs) :
      a ≤ x ∧ x < a + 2 ^ (tilt149.steps * (20 * j)) ∧ ∃ i, acceleratedOrbit i n = x := by
    obtain ⟨hlo, hhi, him⟩ := hx x hxm
    rw [hsteps]
    exact ⟨hlo, Nat.lt_of_lt_of_le hhi (Nat.add_le_add_left hj _), him⟩
  refine Nat.le_trans (hC _ hmerge hclosed _ a xs hnd hsmall) (Nat.mul_le_mul_left _ ?_)
  rw [Nat.pow_mul, Nat.pow_mul]
  exact Nat.pow_le_pow_left tilt149_rate j

open Collatz.Reach

private theorem standard_time (n k : Nat) (hn : 0 < n) :
    ∃ t, k ≤ t ∧ orbit t n = acceleratedOrbit k n := by
  induction k with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    obtain ⟨t, hkt, hval⟩ := ih
    have hpos := acceleratedOrbit_positive hn k
    rw [acceleratedOrbit_succ_step]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · refine ⟨1 + t, by omega, ?_⟩
      rw [orbit_add, hval, accStep_eq_step_of_even he]
      rfl
    · refine ⟨2 + t, by omega, ?_⟩
      rw [orbit_add, hval, accStep_eq_step_step_of_odd hpos ho]
      rfl

/-- Distinctness of the standard trajectory implies distinctness
at the shortcut states. -/
theorem shortcut_injective_of_standard {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, orbit i n = orbit j n → i = j) :
    ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j := by
  have hbad (i j : Nat) (hlt : i < j)
      (heq : acceleratedOrbit i n = acceleratedOrbit j n) : False := by
    obtain ⟨u, _, hu⟩ := standard_time n i hn
    obtain ⟨v, hvpos, hv⟩ := standard_time (acceleratedOrbit i n) (j - i)
      (acceleratedOrbit_positive hn i)
    rw [acceleratedOrbit_add, Nat.sub_add_cancel (Nat.le_of_lt hlt), ← heq] at hv
    have hraw : orbit (v + u) n = orbit u n := by rw [orbit_add, hu, hv]
    have htimes := hinj _ _ hraw
    omega
  intro i j heq
  rcases Nat.lt_trichotomy i j with hlt | hsame | hgt
  · exact (hbad i j hlt heq).elim
  · exact hsame
  · exact (hbad j i hgt heq.symm).elim

/-- Every standard orbit value is either a shortcut state or the
intermediate value after tripling an odd shortcut state. -/
theorem standard_value (n : Nat) (hn : 0 < n) (k : Nat) :
    (∃ i, acceleratedOrbit i n = orbit k n) ∨
      (∃ i, acceleratedOrbit i n % 2 = 1 ∧ 3 * acceleratedOrbit i n + 1 = orbit k n) := by
  induction k with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
    rw [orbit_succ_steps, orbit_step_commute]
    rcases ih with ⟨i, hi⟩ | ⟨i, ho, hi⟩
    · rw [← hi]
      rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i n) with he | ho
      · exact Or.inl ⟨i + 1, by rw [acceleratedOrbit_succ_step, accStep_eq_step_of_even he]⟩
      · exact Or.inr ⟨i, ho, (step_odd (acceleratedOrbit_positive hn i) ho).symm⟩
    · rw [← hi]
      refine Or.inl ⟨i + 1, ?_⟩
      have hpos := acceleratedOrbit_positive hn i
      rw [acceleratedOrbit_succ_step, accStep_eq_step_step_of_odd hpos ho, step_odd hpos ho]

/-- The same uniform power bound for the standard map with its
intermediate even states included. -/
theorem standard_window_power :
    ∃ C, ∀ {n a X : Nat}, 0 < n → 0 < X → NoMerging (fun i => acceleratedOrbit i n) →
      ∀ xs : List Nat, xs.Nodup →
        (∀ x ∈ xs, a ≤ x ∧ x < a + X ∧ ∃ i, orbit i n = x) →
        xs.length ^ 20 ≤ C * X ^ 19 := by
  classical
  obtain ⟨C, hC⟩ := orbit_window_power
  refine ⟨2 ^ 20 * C, ?_⟩
  intro n a X hn hX hmerge xs hnd hx
  let onShortcut := fun x => decide (∃ i, acceleratedOrbit i n = x)
  let shortcut := xs.filter onShortcut
  let intermediate := xs.filter (fun x => !onShortcut x)
  have hsplit : shortcut.length + intermediate.length = xs.length := by
    simpa only [shortcut, intermediate, List.length_append] using
      (List.filter_append_perm onShortcut xs).length_eq
  have hshort := hC hX hmerge shortcut (List.filter_sublist.nodup hnd) (a := a)
    (fun x hxm => by
      obtain ⟨hxmem, hs⟩ := List.mem_filter.mp hxm
      obtain ⟨hlo, hhi, _⟩ := hx x hxmem
      exact ⟨hlo, hhi, of_decide_eq_true hs⟩)
  have hsource (x : Nat) (hxm : x ∈ intermediate) : ∃ i, 3 * acceleratedOrbit i n + 1 = x := by
    obtain ⟨hxmem, htest⟩ := List.mem_filter.mp hxm
    obtain ⟨_, _, k, rfl⟩ := hx x hxmem
    rcases standard_value n hn k with hi | ⟨i, _, hi⟩
    · have htrue : onShortcut (orbit k n) = true := decide_eq_true hi
      simp [htrue] at htest
    · exact ⟨i, hi⟩
  let preimages := intermediate.map (· / 3)
  have hpre : preimages.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.filter_sublist.nodup hnd)
    intro x y hxm hym hne heq
    obtain ⟨i, hi⟩ := hsource x hxm
    obtain ⟨j, hj⟩ := hsource y hym
    exact hne (by omega)
  have hother' := hC hX hmerge preimages hpre (a := a / 3) (fun y hym => by
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hym
    obtain ⟨hlo, hhi, _⟩ := hx x (List.mem_filter.mp hxm).1
    obtain ⟨i, hi⟩ := hsource x hxm
    exact ⟨by omega, by omega, i, by omega⟩)
  have hother : intermediate.length ^ 20 ≤ C * X ^ 19 := by
    simpa only [preimages, List.length_map] using hother'
  let m := max shortcut.length intermediate.length
  have hm : m ^ 20 ≤ C * X ^ 19 := by
    rcases Nat.le_total shortcut.length intermediate.length with h | h
    · simpa [m, Nat.max_eq_right h] using hother
    · simpa [m, Nat.max_eq_left h] using hshort
  have hlen : xs.length ≤ 2 * m := by
    rw [← hsplit, Nat.two_mul]
    exact Nat.add_le_add (Nat.le_max_left ..) (Nat.le_max_right ..)
  calc
    _ ≤ (2 * m) ^ 20 := Nat.pow_le_pow_left hlen _
    _ = 2 ^ 20 * m ^ 20 := Nat.mul_pow ..
    _ ≤ 2 ^ 20 * (C * X ^ 19) := Nat.mul_le_mul_left _ hm
    _ = _ := by rw [Nat.mul_assoc]

/-- On a positive injective orbit, the number of times the multiplier
is at most `R` is bounded by a constant times `(R+1)^(19/20)`. -/
theorem multiplier_occupation {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) :
    ∃ C, ∀ R (times : List Nat), times.Nodup →
      (∀ i ∈ times, 3 ^ oddCount n i ≤ R * 2 ^ i) →
      times.length ^ 20 ≤ C * (R + 1) ^ 19 := by
  obtain ⟨B, hB⟩ := orbit_envelope hn hinj
  obtain ⟨C, hC⟩ := orbit_window_power
  refine ⟨C * (B * n + 1) ^ 19, ?_⟩
  intro R times hnd hsmall
  let xs := times.map (fun i => acceleratedOrbit i n)
  let X := (B * n + 1) * (R + 1)
  have hX : 0 < X := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hxs : xs.Nodup := List.pairwise_map.mpr
    (hnd.imp (fun hne heq => hne (hinj _ _ heq)))
  have hsubset : ∀ x ∈ xs, 0 ≤ x ∧ x < 0 + X ∧ ∃ i, acceleratedOrbit i n = x := by
    intro x hx
    obtain ⟨i, him, rfl⟩ := List.mem_map.mp hx
    have hs := hsmall i him
    have hle : 2 ^ i * acceleratedOrbit i n ≤ 2 ^ i * (B * n * R) := by
      calc
        _ ≤ B * n * 3 ^ oddCount n i := hB i
        _ ≤ B * n * (R * 2 ^ i) := Nat.mul_le_mul_left _ hs
        _ = _ := by ac_rfl
    have hval := Nat.le_of_mul_le_mul_left hle (Nat.two_pow_pos i)
    refine ⟨Nat.zero_le _, ?_, i, rfl⟩
    dsimp [X]
    rw [Nat.zero_add, Nat.mul_add, Nat.add_mul (B * n) 1 R, Nat.mul_one, Nat.one_mul]
    omega
  have hb := hC hX (no_merging_of_injective hinj) xs hxs hsubset
  simpa only [xs, List.length_map, X, Nat.mul_pow, ← Nat.mul_assoc] using hb

/-- A divergent orbit exceeds every power-law multiplier ceiling
with exponent below `20/19` at arbitrarily late times. -/
theorem exceeds_polynomial_multiplier {n : Nat} (hn : 0 < n)
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j)
    {p q : Nat} (hrate : 19 * p < 20 * q) (D H : Nat) :
    ∃ i, H ≤ i ∧ D * (i + 1) ^ p * (2 ^ i) ^ q < (3 ^ oddCount n i) ^ q := by
  classical
  have hq : 0 < q := by omega
  obtain ⟨C, hC⟩ := multiplier_occupation hn hinj
  let B := D * (H + 1) ^ p + 1
  let r := C * (B + 1) ^ 19 + 1
  let k := r ^ q
  let R := B * r ^ p
  have hr : 0 < r := Nat.succ_pos _
  have hk : 0 < k := Nat.pow_pos hr
  apply Classical.byContradiction
  intro hbad
  let times := List.range' H k
  have hall : ∀ i ∈ times, 3 ^ oddCount n i ≤ R * 2 ^ i := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hi
    have hle : (3 ^ oddCount n i) ^ q ≤ D * (i + 1) ^ p * (2 ^ i) ^ q :=
      Nat.le_of_not_gt (fun h => hbad ⟨i, hlo, h⟩)
    have ht : i + 1 ≤ (H + 1) * k := by
      rw [Nat.add_mul, Nat.one_mul]
      have hH := Nat.le_mul_of_pos_right H hk
      omega
    have hB : D * (H + 1) ^ p ≤ B ^ q :=
      Nat.le_trans (Nat.le_succ _) (Nat.le_pow hq)
    have hkp : k ^ p = (r ^ p) ^ q := by
      dsimp [k]
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm q p]
    apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hq)).mp
    calc
      _ ≤ D * (i + 1) ^ p * (2 ^ i) ^ q := hle
      _ ≤ D * ((H + 1) * k) ^ p * (2 ^ i) ^ q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht p))
      _ = (D * (H + 1) ^ p) * (r ^ p) ^ q * (2 ^ i) ^ q := by
        rw [Nat.mul_pow, hkp]
        ac_rfl
      _ ≤ B ^ q * (r ^ p) ^ q * (2 ^ i) ^ q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB)
      _ = (R * 2 ^ i) ^ q := by dsimp [R]; rw [Nat.mul_pow, Nat.mul_pow B]
  have hlen : k ^ 20 ≤ C * (R + 1) ^ 19 := by
    simpa only [times, List.length_range'] using hC R times List.nodup_range' hall
  have hR : R + 1 ≤ (B + 1) * r ^ p := by
    change B * r ^ p + 1 ≤ (B + 1) * r ^ p
    rw [Nat.add_mul B 1, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.pow_pos hr) _
  have hpow : r ^ (20 * q) ≤ C * (B + 1) ^ 19 * r ^ (19 * p) := by
    calc
      _ = k ^ 20 := by dsimp [k]; rw [← Nat.pow_mul, Nat.mul_comm 20 q]
      _ ≤ _ := hlen
      _ ≤ C * ((B + 1) * r ^ p) ^ 19 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 19)
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm p 19, Nat.mul_assoc]
  have hfactor : r ^ (20 * q - 19 * p) ≤ C * (B + 1) ^ 19 := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < r ^ (19 * p) from Nat.pow_pos hr)
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hrate)]
    exact hpow
  have hsmall := Nat.le_trans (Nat.le_pow (a := r) (by omega : 0 < 20 * q - 19 * p)) hfactor
  exact (Nat.not_le_of_gt (Nat.lt_succ_self (C * (B + 1) ^ 19))) hsmall

end Collatz.OrbitWindowBootstrap
