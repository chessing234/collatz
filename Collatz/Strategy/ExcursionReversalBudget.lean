import Collatz.Strategy.ExcursionConflictThresholds

/-!
# A descent budget charged only at drift reversals

Each excursion has an individual ideal factor. The positive side
attains it at the smallest source, and the negative side attains it
at the largest target. Only a negative-to-nonnegative boundary asks
for opposite coordinates. We bound that pair by choosing a shared
shift for the worst outer shifts, and use the ideal factor everywhere
else.
-/

namespace Collatz.ExcursionAnchor

/-- The best factor of a single edge on its own. -/
def idealFactor (floor : Rat) (e : Edge) : Rat :=
  if 0 ≤ e.drift then e.factor floor floor else e.factor (floor + 1) (floor + 1)

private theorem ofRun_factor_at_floor {n v W : Nat} (hn : 0 < n) {q : Rat}
    (hq : (n : Rat) ≤ q) (hd : 0 ≤ (Edge.ofRun n v W).drift) :
    (Edge.ofRun n v W).factor n q = idealFactor n (Edge.ofRun n v W) := by
  let e := Edge.ofRun n v W
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have hq' : 0 < q := by grind
  change e.factor n q = idealFactor n e
  have hd₀ : 0 ≤ e.drift := hd
  have hqeq := e.factor_of_unclipped hn' hq' (ofRun_unclipped_at_floor hq)
  have hneq := e.factor_of_unclipped hn' hn' (ofRun_unclipped_at_floor Rat.le_refl)
  rw [if_pos hd₀] at hqeq hneq
  rw [idealFactor, if_pos hd₀]
  exact hqeq.trans hneq.symm

private theorem ofRun_factor_at_ceiling {n v W : Nat} (hn : 0 < n) {p : Rat}
    (hp : (n : Rat) ≤ p) (hp' : p ≤ (n : Rat) + 1) (hd : (Edge.ofRun n v W).drift < 0) :
    (Edge.ofRun n v W).factor p ((n : Rat) + 1) = idealFactor n (Edge.ofRun n v W) := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have htop : 0 < top := by dsimp [top]; grind
  have hp0 : 0 < p := by grind
  change e.factor p top = idealFactor n e
  have hd₀ : ¬ 0 ≤ e.drift := (Rat.not_le).mpr hd
  have hpeq := e.factor_of_unclipped hp0 htop (ofRun_unclipped_at_ceiling hp')
  have hteq := e.factor_of_unclipped htop htop (ofRun_unclipped_at_ceiling Rat.le_refl)
  rw [if_neg hd₀] at hpeq hteq
  rw [idealFactor, if_neg hd₀]
  exact hpeq.trans hteq.symm

theorem ofRun_factor_ge_ideal {n v W : Nat} (hn : 0 < n) {p q : Rat}
    (hp : (n : Rat) ≤ p) (hq : (n : Rat) ≤ q) (hq' : q ≤ (n : Rat) + 1) :
    idealFactor n (Edge.ofRun n v W) ≤ (Edge.ofRun n v W).factor p q := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have htop : 0 < top := by dsimp [top]; grind
  have hp' : 0 < p := by grind
  have hq0 : 0 < q := by grind
  change idealFactor n e ≤ e.factor p q
  by_cases hd : 0 ≤ e.drift
  · rw [idealFactor, if_pos hd,
      e.factor_of_unclipped hn' hn' (ofRun_unclipped_at_floor Rat.le_refl), if_pos hd]
    exact e.factor_ge_arrival_at hn' hp hq0 hd
  · rw [idealFactor, if_neg hd,
      e.factor_of_unclipped htop htop (ofRun_unclipped_at_ceiling Rat.le_refl), if_neg hd]
    exact e.factor_ge_departure_at hp' hq0 hq' ((Rat.not_le).mp hd)

private theorem idealFactor_ge_one {n v W : Nat} (hn : 0 < n) :
    1 ≤ idealFactor n (Edge.ofRun n v W) := by
  have htop : (n : Rat) ≤ (n : Rat) + 1 := by grind
  unfold idealFactor
  split
  · exact ofRun_factor_ge_one hn Rat.le_refl Rat.le_refl htop
  · exact ofRun_factor_ge_one hn htop htop Rat.le_refl

private theorem ofRun_factor_le_band_ratio {n v W : Nat} (hn : 0 < n) {p q : Rat}
    (hp : (n : Rat) ≤ p) (hp' : p ≤ (n : Rat) + 1) (hq : (n : Rat) ≤ q) :
    (Edge.ofRun n v W).factor p q ≤ ((n : Rat) + 1) / n := by
  let e := Edge.ofRun n v W
  let top := (n : Rat) + 1
  let c : Rat := ((2 : Nat) ^ v : Nat)
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  have htop : 0 < top := by dsimp [top]; grind
  have hp0 : 0 < p := by grind
  have hq0 : 0 < q := by grind
  have hclip : e.b * (n : Rat) ≤ e.a * top + e.drift := by
    have hd : e.drift = e.b * (n : Rat) + c - e.a * top := rfl
    have hc : 0 ≤ c := Rat.natCast_nonneg
    rw [hd]
    grind
  change e.factor p q ≤ top / (n : Rat)
  rw [← e.factor_of_clipped hclip]
  exact Rat.le_trans (e.factor_mono_source hp0 hp' hq0)
    (e.factor_antitone_target htop hn' hq)

/-- A boundary where independent ideal factors require opposite shifts. -/
def isReversal (e f : Edge) : Bool := decide (e.drift < 0 ∧ 0 ≤ f.drift)

private def preferredSource (floor : Rat) : Option Edge → Rat
  | none => floor + 1
  | some e => if 0 ≤ e.drift then floor else floor + 1

private def paidBoundary (floor : Rat) (e f : Edge) : Rat :=
  if idealFactor floor f ≤ idealFactor floor e then floor else floor + 1

private def policyTail (floor : Rat) (mid : Edge → Edge → Rat) : List Edge → List Rat
  | [] => []
  | [_] => [floor + 1]
  | e :: f :: rest =>
    if isReversal e f then
      mid e f :: preferredSource floor rest.head? :: policyTail floor mid rest
    else
      preferredSource floor (some f) :: policyTail floor mid (f :: rest)

private def policySchedule (floor : Rat) (mid : Edge → Edge → Rat) (word : List Edge) : List Rat :=
  preferredSource floor word.head? :: policyTail floor mid word

private def budgetWith (floor : Rat) (pair : Edge → Edge → Rat) : List Edge → Rat
  | [] => 1
  | [e] => idealFactor floor e
  | e :: f :: rest =>
    if isReversal e f then
      pair e f * budgetWith floor pair rest
    else
      idealFactor floor e * budgetWith floor pair (f :: rest)

/-- The binary budget keeps the smaller ideal factor at each reversal
and replaces the larger one by the band ratio. -/
def binaryReversalBudget (floor : Rat) : List Edge → Rat :=
  budgetWith floor (fun e f => ((floor + 1) / floor) * min (idealFactor floor e) (idealFactor floor f))

/-- The threshold budget uses two local factor evaluations per
reversal and the individual ideal factor on every other edge. -/
def reversalBudget (floor : Rat) : List Edge → Rat :=
  budgetWith floor (thresholdBudget floor)

private theorem preferredSource_in_band (n : Rat) (e : Option Edge) :
    n ≤ preferredSource n e ∧ preferredSource n e ≤ n + 1 := by
  have h : n ≤ n + 1 := by grind
  cases e with
  | none => exact ⟨h, Rat.le_refl⟩
  | some e =>
    unfold preferredSource
    split <;> grind

private theorem paidBoundary_in_band (n : Rat) (e f : Edge) :
    n ≤ paidBoundary n e f ∧ paidBoundary n e f ≤ n + 1 := by
  have h : n ≤ n + 1 := by grind
  unfold paidBoundary
  split <;> grind

private theorem edge_product_le_paid {n v W v' W' : Nat} (hn : 0 < n)
    (hd : (Edge.ofRun n v W).drift < 0) (hd' : 0 ≤ (Edge.ofRun n v' W').drift)
    {p r : Rat} (hp : (n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) (hr : (n : Rat) ≤ r) :
    let e := Edge.ofRun n v W
    let f := Edge.ofRun n v' W'
    let mid := paidBoundary n e f
    e.factor p mid * f.factor mid r ≤
      (((n : Rat) + 1) / (n : Rat)) * min (idealFactor n e) (idealFactor n f) := by
  let e := Edge.ofRun n v W
  let f := Edge.ofRun n v' W'
  let top := (n : Rat) + 1
  have ht : (n : Rat) ≤ top := by dsimp [top]; grind
  have he := idealFactor_ge_one (v := v) (W := W) hn
  have hf := idealFactor_ge_one (v := v') (W := W') hn
  change e.factor p (paidBoundary n e f) * f.factor (paidBoundary n e f) r ≤
    top / (n : Rat) * min (idealFactor n e) (idealFactor n f)
  by_cases h : idealFactor n f ≤ idealFactor n e
  · have hmin : min (idealFactor n e) (idealFactor n f) = idealFactor n f := by
      rw [Rat.min_def]
      split <;> grind
    rw [paidBoundary, if_pos h, ofRun_factor_at_floor hn hr hd', hmin]
    exact Rat.mul_le_mul_of_nonneg_right (ofRun_factor_le_band_ratio hn hp.1 hp.2 Rat.le_refl)
      (by grind)
  · have hmin : min (idealFactor n e) (idealFactor n f) = idealFactor n e := by
      rw [Rat.min_def, if_pos (Rat.le_of_lt ((Rat.not_le).mp h))]
    rw [paidBoundary, if_neg h, ofRun_factor_at_ceiling hn hp.1 hp.2 hd, hmin, Rat.mul_comm (top / (n : Rat))]
    exact Rat.mul_le_mul_of_nonneg_left (ofRun_factor_le_band_ratio hn ht Rat.le_refl hr)
      (by grind)

private structure PairPolicy (n : Nat) where
  mid : Edge → Edge → Rat
  upper : Edge → Edge → Rat
  valid : ∀ {v W v' W' : Nat}, 0 < v → 0 < W → 0 < v' → 0 < W' →
    let e := Edge.ofRun n v W
    let f := Edge.ofRun n v' W'
    e.drift < 0 → 0 ≤ f.drift →
    ((n : Rat) ≤ mid e f ∧ mid e f ≤ (n : Rat) + 1) ∧
      ∀ p q : Rat, ((n : Rat) ≤ p ∧ p ≤ (n : Rat) + 1) → (n : Rat) ≤ q →
        e.factor p (mid e f) * f.factor (mid e f) q ≤ upper e f

private def binaryPolicy {n : Nat} (hn : 0 < n) : PairPolicy n where
  mid := paidBoundary n
  upper e f := (((n : Rat) + 1) / n) * min (idealFactor n e) (idealFactor n f)
  valid _ _ _ _ hd hd' := ⟨paidBoundary_in_band _ _ _,
    fun _ _ hp hq => edge_product_le_paid hn hd hd' hp hq⟩

private def thresholdPolicy {n : Nat} (hn : 0 < n) : PairPolicy n where
  mid := thresholdShift n
  upper := thresholdBudget n
  valid _ hW hv' _ _ _ := ⟨thresholdShift_in_band hW hv',
    fun _ _ hp hq => thresholdBudget_bounds_pair hn hW hv' hp hq⟩

set_option maxHeartbeats 600000 in
private theorem policySchedule_spec {n : Nat} (hn : 0 < n) (policy : PairPolicy n)
    (word : List Edge) (ha : ExcursionAlphabet n word) :
    (policySchedule n policy.mid word).length = word.length + 1 ∧
      (∀ q ∈ policySchedule n policy.mid word, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) ∧
      costOn word (policySchedule n policy.mid word) ≤ budgetWith n policy.upper word := by
  suffices h : ∀ k (word : List Edge), word.length = k → ExcursionAlphabet n word →
      (policySchedule n policy.mid word).length = word.length + 1 ∧
        (∀ q ∈ policySchedule n policy.mid word, (n : Rat) ≤ q ∧ q ≤ (n : Rat) + 1) ∧
        costOn word (policySchedule n policy.mid word) ≤ budgetWith n policy.upper word by
    exact h word.length word rfl ha
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro word hlen ha
    let floor : Rat := n
    let top := floor + 1
    have hn' : 0 < floor := Rat.natCast_pos.mpr hn
    have ht : floor ≤ top := by dsimp [top]; grind
    cases word with
    | nil =>
      refine ⟨rfl, ?_, Rat.le_refl⟩
      intro q hq
      have he : q = top := by simpa [policySchedule, preferredSource, policyTail] using hq
      rw [he]
      exact ⟨ht, Rat.le_refl⟩
    | cons e word =>
      obtain ⟨v, W, hv, hW, rfl⟩ := ha e List.mem_cons_self
      let e := Edge.ofRun n v W
      have hsource := preferredSource_in_band floor (some e)
      cases word with
      | nil =>
        refine ⟨rfl, ?_, ?_⟩
        · intro q hq
          have hq' : q = preferredSource floor (some e) ∨ q = top := by
            simpa [policySchedule, policyTail] using hq
          rcases hq' with rfl | rfl
          · exact hsource
          · exact ⟨ht, Rat.le_refl⟩
        · change e.factor (preferredSource floor (some e)) top * 1 ≤ idealFactor floor e
          rw [Rat.mul_one]
          by_cases hd : 0 ≤ e.drift
          · rw [preferredSource, if_pos hd, ofRun_factor_at_floor hn ht hd]
            exact Rat.le_refl
          · rw [preferredSource, if_neg hd, ofRun_factor_at_ceiling hn ht Rat.le_refl ((Rat.not_le).mp hd)]
            exact Rat.le_refl
      | cons f rest =>
        obtain ⟨v', W', hv', hW', rfl⟩ := ha f (by simp)
        let f := Edge.ofRun n v' W'
        by_cases hrev : isReversal e f = true
        · obtain ⟨hd, hd'⟩ := of_decide_eq_true hrev
          have hab : ExcursionAlphabet n rest := fun g hg => ha g (by simp [hg])
          have hsmaller : rest.length < k := by rw [← hlen]; simp only [List.length_cons]; omega
          obtain ⟨hsize, hband, hcost⟩ := ih rest.length hsmaller rest rfl hab
          let mid := policy.mid e f
          obtain ⟨hmid, hbound⟩ := policy.valid hv hW hv' hW' hd hd'
          have hshape : policySchedule floor policy.mid (e :: f :: rest) =
              preferredSource floor (some e) :: mid :: policySchedule floor policy.mid rest := by
            change _ = preferredSource floor (some e) :: policy.mid e f :: policySchedule floor policy.mid rest
            simp only [policySchedule, policyTail, List.head?_cons, hrev, if_true]
          refine ⟨?_, ?_, ?_⟩
          · rw [hshape, List.length_cons, List.length_cons, hsize]
            rfl
          · intro q hq
            rw [hshape] at hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hsource
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hmid
            · exact hband q hq
          · let q := preferredSource floor rest.head?
            have hq := preferredSource_in_band floor rest.head?
            have hpay := hbound _ _ hsource hq.1
            have hnonneg : 0 ≤ costOn rest (policySchedule floor policy.mid rest) := by
              apply costOn_nonneg
              intro r hr
              have := (hband r hr).1
              grind
            have hbase : 0 ≤ policy.upper e f := by
              have hP : 0 < preferredSource floor (some e) := by have := hsource.1; grind
              have hM : 0 < mid := by have := hmid.1; grind
              have hQ : 0 < q := by have := hq.1; grind
              exact Rat.le_trans
                (Rat.mul_nonneg (Rat.le_of_lt (e.factor_pos hP hM)) (Rat.le_of_lt (f.factor_pos hM hQ)))
                hpay
            rw [hshape]
            change e.factor (preferredSource floor (some e)) mid *
              (f.factor mid q * costOn rest (policySchedule floor policy.mid rest)) ≤
              budgetWith floor policy.upper (e :: f :: rest)
            rw [budgetWith, if_pos hrev, ← Rat.mul_assoc]
            exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hpay hnonneg)
              (Rat.mul_le_mul_of_nonneg_left hcost hbase)
        · have hab : ExcursionAlphabet n (f :: rest) := fun g hg => ha g (List.mem_cons_of_mem _ hg)
          have hsmaller : (f :: rest).length < k := by rw [← hlen]; simp only [List.length_cons]; omega
          obtain ⟨hsize, hband, hcost⟩ := ih (f :: rest).length hsmaller (f :: rest) rfl hab
          let p := preferredSource floor (some e)
          let q := preferredSource floor (some f)
          have hq := preferredSource_in_band floor (some f)
          have hshape : policySchedule floor policy.mid (e :: f :: rest) = p :: policySchedule floor policy.mid (f :: rest) := by
            change _ = preferredSource floor (some e) :: policySchedule floor policy.mid (f :: rest)
            simp only [policySchedule, policyTail, List.head?_cons, hrev, Bool.false_eq_true, if_false]
          refine ⟨?_, ?_, ?_⟩
          · rw [hshape, List.length_cons, hsize]
            rfl
          · intro r hr
            rw [hshape] at hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hsource
            · exact hband r hr
          · have he : e.factor p q = idealFactor floor e := by
              by_cases hd : 0 ≤ e.drift
              · change e.factor (preferredSource floor (some e)) q = idealFactor floor e
                rw [preferredSource, if_pos hd, ofRun_factor_at_floor hn hq.1 hd]
              · have hd' : ¬ 0 ≤ f.drift := by
                  intro h
                  apply hrev
                  exact decide_eq_true ⟨(Rat.not_le).mp hd, h⟩
                change e.factor p (preferredSource floor (some f)) = idealFactor floor e
                rw [preferredSource, if_neg hd',
                  ofRun_factor_at_ceiling hn hsource.1 hsource.2 ((Rat.not_le).mp hd)]
            have hnonneg : 0 ≤ idealFactor floor e := by
              have := idealFactor_ge_one (v := v) (W := W) hn
              grind
            rw [hshape]
            change e.factor p q * costOn (f :: rest) (policySchedule floor policy.mid (f :: rest)) ≤
              budgetWith floor policy.upper (e :: f :: rest)
            rw [budgetWith, if_neg hrev, he]
            exact Rat.mul_le_mul_of_nonneg_left hcost hnonneg

private theorem anchorMinimum_le_policy {n : Nat} (hn : 0 < n) (policy : PairPolicy n)
    {word : List Edge} (ha : ExcursionAlphabet n word) :
    ∃ best, anchorMinimum n word = some best ∧ best ≤ budgetWith n policy.upper word := by
  obtain ⟨hlen, hband, hcost⟩ := policySchedule_spec hn policy word ha
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_coordinates (Rat.natCast_pos.mpr hn) hlen hband
  exact ⟨best, hbest, Rat.le_trans hle hcost⟩

/-- The binary budget is an upper bound for the exact optimum. -/
theorem anchorMinimum_le_binaryReversalBudget {n : Nat} (hn : 0 < n) {word : List Edge}
    (ha : ExcursionAlphabet n word) :
    ∃ best, anchorMinimum n word = some best ∧ best ≤ binaryReversalBudget n word :=
  anchorMinimum_le_policy hn (binaryPolicy hn) ha

/-- A search-free upper bound for the exact excursion optimizer. -/
theorem anchorMinimum_le_reversalBudget {n : Nat} (hn : 0 < n) {word : List Edge}
    (ha : ExcursionAlphabet n word) :
    ∃ best, anchorMinimum n word = some best ∧ best ≤ reversalBudget n word :=
  anchorMinimum_le_policy hn (thresholdPolicy hn) ha

/-- The reversal budget certifies descent using only one product of
explicit local factors. -/
theorem OrbitWord.drop_of_reversalBudget {n endpoint elapsed A B word}
    (h : OrbitWord n n word endpoint elapsed A B) (hn : 0 < n)
    (hcross : (A : Rat) * reversalBudget n word < (B : Rat)) :
    ∃ k, k ≤ elapsed ∧ acceleratedOrbit k n < n := by
  obtain ⟨best, hbest, hle⟩ := anchorMinimum_le_reversalBudget hn h.alphabet
  apply h.drop_of_anchorMinimum hn hbest
  have hc := Rat.mul_le_mul_of_nonneg_left hle (Rat.natCast_nonneg (a := A))
  grind

private def budgetWord63 : List Edge :=
  [Edge.ofRun 63 6 3, Edge.ofRun 63 2 1, Edge.ofRun 63 3 1, Edge.ofRun 63 4 1,
    Edge.ofRun 63 1 2, Edge.ofRun 63 3 1, Edge.ofRun 63 2 1, Edge.ofRun 63 6 2,
    Edge.ofRun 63 4 3, unitEdge 63, unitEdge 63, Edge.ofRun 63 1 3]

/-- The threshold budget for 63 crosses strictly, while the binary
pair budget leaves this crossing unresolved. -/
theorem reversal_budget_63_value :
    reversalBudget 63 budgetWord63 = 19334741418193510400 / 17917896630434357367 ∧
      (18014398509481984 : Rat) ≤ 16677181699666569 * binaryReversalBudget 63 budgetWord63 := by
  decide +kernel

theorem reversal_budget_drop_63 :
    ∃ k, k ≤ 54 ∧ Collatz.acceleratedOrbit k 63 < 63 := by
  have h63 : OrbitWord 63 63 budgetWord63 61 54 16677181699666569 18014398509481984 :=
    .cons (show Collatz.ExcursionMap.IsExcursion 63 6 1 3 91 by
      unfold Collatz.ExcursionMap.IsExcursion; decide)
      (.cons (show Collatz.ExcursionMap.IsExcursion 91 2 23 1 103 by
        unfold Collatz.ExcursionMap.IsExcursion; decide)
        (.cons (show Collatz.ExcursionMap.IsExcursion 103 3 13 1 175 by
          unfold Collatz.ExcursionMap.IsExcursion; decide)
          (.cons (show Collatz.ExcursionMap.IsExcursion 175 4 11 1 445 by
            unfold Collatz.ExcursionMap.IsExcursion; decide)
            (.cons (show Collatz.ExcursionMap.IsExcursion 445 1 223 2 167 by
              unfold Collatz.ExcursionMap.IsExcursion; decide)
              (.cons (show Collatz.ExcursionMap.IsExcursion 167 3 21 1 283 by
                unfold Collatz.ExcursionMap.IsExcursion; decide)
                (.cons (show Collatz.ExcursionMap.IsExcursion 283 2 71 1 319 by
                  unfold Collatz.ExcursionMap.IsExcursion; decide)
                  (.cons (show Collatz.ExcursionMap.IsExcursion 319 6 5 2 911 by
                    unfold Collatz.ExcursionMap.IsExcursion; decide)
                    (.cons (show Collatz.ExcursionMap.IsExcursion 911 4 57 3 577 by
                      unfold Collatz.ExcursionMap.IsExcursion; decide)
                      (.cons (show Collatz.ExcursionMap.IsExcursion 577 1 289 1 433 by
                        unfold Collatz.ExcursionMap.IsExcursion; decide)
                        (.cons (show Collatz.ExcursionMap.IsExcursion 433 1 217 1 325 by
                          unfold Collatz.ExcursionMap.IsExcursion; decide)
                          (.cons (show Collatz.ExcursionMap.IsExcursion 325 1 163 3 61 by
                            unfold Collatz.ExcursionMap.IsExcursion; decide)
                            .nil)))))))))))
  exact h63.drop_of_reversalBudget (by decide) (by decide +kernel)

end Collatz.ExcursionAnchor
