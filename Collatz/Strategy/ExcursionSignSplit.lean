import Collatz.Strategy.ExcursionContractionTail

/-!
# Separating neighboring factors by the sign of the floor drift

At a boundary with a nonnegative-drift excursion on the left and a
negative-drift excursion on the right, the midpoint of the shift band
simultaneously minimizes both adjacent factors while the other
coordinates are held fixed.
-/

namespace Collatz.ExcursionAnchor

theorem v_ge_two_of_negative_drift {n v W : Nat}
    (hn : 0 < n) (hv : 0 < v) (hW : 0 < W)
    (hd : (Edge.ofRun n v W).drift < 0) : 2 ≤ v := by
  apply Classical.byContradiction
  intro h
  have he : v = 1 := by omega
  subst v
  let b : Rat := ((2 : Nat) ^ (1 + W) : Nat)
  have hbNat : 2 ^ 2 ≤ 2 ^ (1 + W) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : (4 : Rat) ≤ b := Rat.natCast_le_natCast.mpr hbNat
  have hn' : (1 : Rat) ≤ n := Rat.natCast_le_natCast.mpr hn
  have hscale := Rat.mul_le_mul_of_nonneg_right hb (Rat.natCast_nonneg (a := n))
  change b * (n : Rat) + 2 - 3 * ((n : Rat) + 1) < 0 at hd
  grind

theorem Edge.ofRun_factor_half_left {n v W : Nat} (hn : 0 < n) (hW : 0 < W)
    (hd : 0 ≤ (Edge.ofRun n v W).drift) {p q : Rat}
    (hp : (n : Rat) ≤ p) (hp' : p ≤ (n : Rat) + 1) (hq : (n : Rat) ≤ q) :
    (Edge.ofRun n v W).factor p ((n : Rat) + 1 / 2) ≤ (Edge.ofRun n v W).factor p q := by
  let e := Edge.ofRun n v W
  let mid := (n : Rat) + 1 / 2
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hm : 0 < mid := by
    change 0 < (n : Rat) + 1 / 2
    have h : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hp0 : 0 < p := by grind
  have hq0 : 0 < q := by grind
  have htransport : e.transport p ≤ mid := output_half hW hp'
  have hunc := Rat.mul_le_mul_of_nonneg_left htransport (Rat.le_of_lt e.b_pos)
  rw [e.transport_spec] at hunc
  change e.factor p mid ≤ e.factor p q
  rw [e.factor_of_unclipped hp0 hm hunc, if_pos hd]
  exact e.factor_ge_arrival_at hp0 Rat.le_refl hq0 hd

theorem Edge.ofRun_factor_half_right {n v W : Nat} (hn : 0 < n) (hv : 0 < v) (hW : 0 < W)
    (hd : (Edge.ofRun n v W).drift < 0) {p q : Rat}
    (hp : (n : Rat) ≤ p) (hq : (n : Rat) ≤ q) :
    (Edge.ofRun n v W).factor ((n : Rat) + 1 / 2) q ≤ (Edge.ofRun n v W).factor p q := by
  let e := Edge.ofRun n v W
  let mid := (n : Rat) + 1 / 2
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hm : 0 < mid := by
    change 0 < (n : Rat) + 1 / 2
    have h : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hp0 : 0 < p := by grind
  have hq0 : 0 < q := by grind
  have hqtransport : (n : Rat) ≤ e.transport (e.inverse q) := by
    have he := e.inverse_spec q
    have ht := e.transport_spec (e.inverse q)
    have heq : e.transport (e.inverse q) = q := by
      apply Rat.le_antisymm
      · apply Rat.le_of_mul_le_mul_left _ e.b_pos
        grind
      · apply Rat.le_of_mul_le_mul_left _ e.b_pos
        grind
    rwa [heq]
  have hinput : (n : Rat) + 5 / 9 ≤ e.inverse q :=
    input_ge_five_ninths (v_ge_two_of_negative_drift hn hv hW hd) hqtransport
  have hmid : mid ≤ e.inverse q := by
    have h : (1 / 2 : Rat) ≤ 5 / 9 := by decide +kernel
    change (n : Rat) + 1 / 2 ≤ _
    grind
  have hscaled := Rat.mul_le_mul_of_nonneg_left hmid (Rat.le_of_lt e.a_pos)
  have he := e.inverse_spec q
  have hunc : e.a * mid + e.drift ≤ e.b * q := by grind
  change e.factor mid q ≤ e.factor p q
  rw [e.factor_of_unclipped hm hq0 hunc, if_neg ((Rat.not_le).mpr hd)]
  exact e.factor_ge_departure_at hp0 hq0 Rat.le_refl hd

/-- Split a product at a shared coordinate of two consecutive words. -/
theorem costOn_append_at (left right : List Edge) (before after : List Rat) (mid : Rat)
    (hlen : before.length = left.length) :
    costOn (left ++ right) (before ++ mid :: after) =
      costOn left (before ++ [mid]) * costOn right (mid :: after) := by
  induction left generalizing before with
  | nil =>
    have he : before = [] := List.length_eq_zero_iff.mp hlen
    subst before
    simp [costOn, Rat.one_mul]
  | cons e left ih =>
    cases before with
    | nil => simp at hlen
    | cons p before =>
      have hlen' : before.length = left.length := by simpa using hlen
      have h := ih before hlen'
      cases before with
      | nil =>
        have he : left = [] := List.length_eq_zero_iff.mp hlen'.symm
        subst left
        simp [costOn, Rat.mul_one]
      | cons q before =>
        simp only [List.cons_append, costOn] at h ⊢
        rw [h, Rat.mul_assoc]

theorem coordinates_cut (xs : List Rat) (k m : Nat) (hlen : xs.length = k + (m + 1)) :
    ∃ before mid after, xs = before ++ mid :: after ∧ before.length = k ∧ after.length = m := by
  let before := xs.take k
  have hbefore : before.length = k := by simp [before, hlen]
  have hdrop : (xs.drop k).length = m + 1 := by simp [hlen]
  cases he : xs.drop k with
  | nil => simp [he] at hdrop
  | cons p rest =>
    have hrest : rest.length = m := by simpa [he] using hdrop
    refine ⟨before, p, rest, ?_, hbefore, hrest⟩
    rw [← he, List.take_append_drop]

theorem anchorMinimum_le_coordinates {n : Rat} {word : List Edge} {xs : List Rat}
    (hn : 0 < n) (hlen : xs.length = word.length + 1)
    (hband : ∀ q ∈ xs, n ≤ q ∧ q ≤ n + 1) :
    ∃ best, anchorMinimum n word = some best ∧ best ≤ costOn word xs := by
  cases xs with
  | nil => simp at hlen
  | cons p rest =>
    exact anchorMinimum_le_schedule hn (by simpa using hlen) hband

private theorem costOn_nonneg_of_floor {n : Rat} (hn : 0 < n) (word : List Edge) (xs : List Rat)
    (h : ∀ p ∈ xs, n ≤ p ∧ p ≤ n + 1) : 0 ≤ costOn word xs := by
  apply costOn_nonneg
  intro p hp
  have := (h p hp).1
  grind

/-- The exact minimum splits into a product at every boundary from
nonnegative drift to negative drift. The same midpoint can join the
optimal schedules on both sides. -/
theorem anchorMinimum_split_of_sign {n v W v' W' : Nat} (hn : 0 < n)
    (hW : 0 < W) (hv' : 0 < v') (hW' : 0 < W')
    (hd : 0 ≤ (Edge.ofRun n v W).drift) (hd' : (Edge.ofRun n v' W').drift < 0)
    {left right : List Edge} {lopt ropt : Rat}
    (hleft : anchorMinimum n (left ++ [Edge.ofRun n v W]) = some lopt)
    (hright : anchorMinimum n (Edge.ofRun n v' W' :: right) = some ropt) :
    anchorMinimum n ((left ++ [Edge.ofRun n v W]) ++ Edge.ofRun n v' W' :: right) =
      some (lopt * ropt) := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let leftWord := left ++ [e]
  let rightWord := f :: right
  let mid := (n : Rat) + 1 / 2
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hmid : (n : Rat) ≤ mid ∧ mid ≤ (n : Rat) + 1 := by
    have hm₁ : (0 : Rat) ≤ 1 / 2 := by decide +kernel
    have hm₂ : (1 / 2 : Rat) ≤ 1 := by decide +kernel
    change _ ≤ (n : Rat) + 1 / 2 ∧ (n : Rat) + 1 / 2 ≤ _
    grind
  obtain ⟨lstart, lrest, llen, lband, lcost⟩ := anchorMinimum_attained_in_band hleft
  obtain ⟨rstart, rrest, rlen, rband, rcost⟩ := anchorMinimum_attained_in_band hright
  have hlen : (lstart :: lrest).length = left.length + (1 + 1) := by
    simp only [List.length_cons]
    simp only [List.length_append, List.length_singleton] at llen
    omega
  obtain ⟨earlier, source, trailing, hcoords, hprefix, htrailing⟩ :=
    coordinates_cut (lstart :: lrest) left.length 1 hlen
  have hsingle : ∃ dest, trailing = [dest] := by
    cases trailing with
    | nil => simp at htrailing
    | cons p ps =>
      have hps : ps = [] := List.length_eq_zero_iff.mp (by simpa using htrailing)
      exact ⟨p, by rw [hps]⟩
  obtain ⟨dest, rfl⟩ := hsingle
  cases rrest with
  | nil => simp at rlen
  | cons target after =>
    have hsource := lband source (by rw [hcoords]; simp)
    have hdest := lband dest (by rw [hcoords]; simp)
    have hstart := rband rstart List.mem_cons_self
    have htarget := rband target (List.mem_cons_of_mem _ List.mem_cons_self)
    have hprefband (p : Rat) (hp : p ∈ earlier ++ [source]) :
        (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
      apply lband
      rw [hcoords]
      rcases List.mem_append.mp hp with hp | hp
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (by simpa using hp)))
    have hleftchange : costOn leftWord (earlier ++ [source, mid]) ≤ lopt := by
      have he := Edge.ofRun_factor_half_left hn hW hd hsource.1 hsource.2 hdest.1
      have hl := costOn_nonneg_of_floor hn' left (earlier ++ [source]) hprefband
      rw [hcoords] at lcost
      rw [costOn_append_at left [e] earlier [dest] source hprefix, costOn] at lcost
      change costOn (left ++ [e]) (earlier ++ source :: [mid]) ≤ lopt
      rw [costOn_append_at left [e] earlier [mid] source hprefix, ← lcost]
      simpa only [costOn, Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left he hl
    have hrightchange : costOn rightWord (mid :: target :: after) ≤ ropt := by
      have he := Edge.ofRun_factor_half_right hn hv' hW' hd' hstart.1 htarget.1
      have hr := costOn_nonneg_of_floor hn' right (target :: after)
        (fun p hp => rband p (List.mem_cons_of_mem _ hp))
      rw [costOn] at rcost
      change costOn (f :: right) (mid :: target :: after) ≤ ropt
      rw [costOn, ← rcost]
      exact Rat.mul_le_mul_of_nonneg_right he hr
    let pre := earlier ++ [source]
    let tail := target :: after
    have hpre : pre.length = leftWord.length := by simp [pre, leftWord, hprefix]
    have htail : tail.length = rightWord.length := rlen
    have hlen' : (pre ++ mid :: tail).length = (leftWord ++ rightWord).length + 1 := by
      simp [hpre, htail, Nat.add_comm, Nat.add_left_comm]
    have hband (p : Rat) (hp : p ∈ pre ++ mid :: tail) :
        (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1 := by
      rcases List.mem_append.mp hp with hp | hp
      · exact hprefband p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hmid
      · exact rband p (List.mem_cons_of_mem _ hp)
    obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_coordinates hn' hlen' hband
    rw [costOn_append_at leftWord rightWord pre tail mid hpre] at hle
    have hrightnonneg : 0 ≤ costOn rightWord (mid :: tail) :=
      costOn_nonneg_of_floor hn' _ _ (fun p hp => hband p (List.mem_append_right _ hp))
    have hleftnonneg : 0 ≤ lopt := by
      rw [← lcost]
      exact costOn_nonneg_of_floor hn' _ _ lband
    have hlpre : costOn leftWord (pre ++ [mid]) ≤ lopt := by
      simpa only [pre, List.append_assoc, List.singleton_append] using hleftchange
    have hupper : best ≤ lopt * ropt :=
      Rat.le_trans hle (Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hlpre hrightnonneg)
        (Rat.mul_le_mul_of_nonneg_left hrightchange hleftnonneg))
    obtain ⟨p, rest, plen, pband, pcost⟩ := anchorMinimum_attained_in_band hbest
    have hpLen : (p :: rest).length = leftWord.length + (rightWord.length + 1) := by
      simp only [List.length_cons, List.length_append] at plen ⊢
      omega
    obtain ⟨first, split, last, hwhole, hfirst, hlast⟩ :=
      coordinates_cut (p :: rest) leftWord.length rightWord.length hpLen
    have hleftBand (q : Rat) (hq : q ∈ first ++ [split]) :
        (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1 := by
      apply pband
      rw [hwhole]
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (by simpa using hq)))
    have hrightBand (q : Rat) (hq : q ∈ split :: last) :
        (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1 :=
      pband q (by rw [hwhole]; exact List.mem_append_right _ hq)
    obtain ⟨l, hl, hll⟩ := anchorMinimum_le_coordinates (word := leftWord) hn'
      (by simp [hfirst]) hleftBand
    obtain ⟨r, hr, hrr⟩ := anchorMinimum_le_coordinates (word := rightWord) hn'
      (by simp [hlast]) hrightBand
    change anchorMinimum n leftWord = some lopt at hleft
    change anchorMinimum n rightWord = some ropt at hright
    rw [hleft] at hl
    rw [hright] at hr
    obtain rfl := Option.some.inj hl
    obtain rfl := Option.some.inj hr
    have hrightNonneg := costOn_nonneg_of_floor hn' rightWord (split :: last) hrightBand
    have hlower := Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hrr hleftnonneg)
      (Rat.mul_le_mul_of_nonneg_right hll hrightNonneg)
    rw [hwhole, costOn_append_at leftWord rightWord first last split hfirst] at pcost
    rw [pcost] at hlower
    rwa [Rat.le_antisymm hupper hlower] at hbest

/-- The reduced finite search has the same factorization on excursion
words. The two independent optima can be computed with six shifts per
boundary. -/
theorem localMinimum_split_of_sign {n v W v' W' : Nat} (hn : 0 < n)
    (hW : 0 < W) (hv' : 0 < v') (hW' : 0 < W')
    (hd : 0 ≤ (Edge.ofRun n v W).drift) (hd' : (Edge.ofRun n v' W').drift < 0)
    {left right : List Edge} {lopt ropt : Rat}
    (ha : ExcursionAlphabet n ((left ++ [Edge.ofRun n v W]) ++ Edge.ofRun n v' W' :: right))
    (hleft : localMinimum n (left ++ [Edge.ofRun n v W]) = some lopt)
    (hright : localMinimum n (Edge.ofRun n v' W' :: right) = some ropt) :
    localMinimum n ((left ++ [Edge.ofRun n v W]) ++ Edge.ofRun n v' W' :: right) =
      some (lopt * ropt) := by
  rw [localMinimum_eq_anchorMinimum ha]
  rw [localMinimum_eq_anchorMinimum (fun e he => ha e (List.mem_append_left _ he))] at hleft
  rw [localMinimum_eq_anchorMinimum (fun e he => ha e (List.mem_append_right _ he))] at hright
  exact anchorMinimum_split_of_sign hn hW hv' hW' hd hd' hleft hright

private def beforeSplit27 : List Edge := [Edge.ofRun 27 2 1, Edge.ofRun 27 5 1, unitEdge 27]
private def afterSplit27 : List Edge := [Edge.ofRun 27 2 1, Edge.ofRun 27 3 1]

/-- The five-excursion prefix from 27 has a split after the third
excursion. Its two exact optima multiply to the unsplit result. -/
theorem sign_split_27_exact :
    localMinimum 27 beforeSplit27 = some (875008 / 841995) ∧
    localMinimum 27 afterSplit27 = some (12224 / 11907) ∧
    localMinimum 27 (beforeSplit27 ++ afterSplit27) = some (10696097792 / 10025634465) := by
  decide +kernel

end Collatz.ExcursionAnchor
