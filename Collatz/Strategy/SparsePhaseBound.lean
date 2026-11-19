import Collatz.Strategy.CubicPhaseNorm

/-! Sparse discrepancy polynomials and short binomials bound the cycle gap.
All quantitative comparisons use natural-number arithmetic. -/

namespace Collatz.SparsePhaseBound

open Collatz.Arith Collatz.AccCycle Collatz.CyclicOrder

private theorem odd_base_pow {B : Int} (hB : B % 2 = 1) (v : Nat) : B ^ v % 2 = 1 := by
  induction v with
  | zero => simp
  | succ v ih => rw [Int.pow_succ, Int.mul_emod, ih, hB]; decide

private theorem even_base_pow {A : Int} {u : Nat} (hA : A % 2 = 0) (hu : 0 < u) : A ^ u % 2 = 0 := by
  cases u with
  | zero => omega
  | succ u => rw [Int.pow_succ, Int.mul_emod, hA]; simp

private theorem grow_power {a b j k : Nat} (hb : 0 < b) (hab : a ≤ b) (hjk : j ≤ k) :
    a ^ j ≤ b ^ k :=
  Nat.le_trans (Nat.pow_le_pow_left hab _) (Nat.pow_le_pow_right hb hjk)

private theorem modulus_le_of_phase_powers {L a D Q M d w : Nat} {z A B : Int} {P : Nat → Int}
    (ha : a < L) (hQ : 0 < Q) (hA : A.natAbs = 2) (hB : B.natAbs = 3)
    (h₂ : (D : Int) ∣ A * z ^ a - 1) (h₃ : (D : Int) ∣ B * z ^ L - 1)
    (hd : 0 < d) (hdw : d ≤ w) (hP₀ : P 0 % 2 = 1) (hPd : P d % 2 = 1)
    (hP : Collatz.Sum.sumRange (d + 1) (fun i => (P i).natAbs) ≤ M)
    (hPz : (D : Int) ∣ PhaseResidueBox.evaluate (d + 1) P z) :
    D ≤ (2 * M + 1) ^ (w + L / Q) * (2 * 3 ^ Q + 1) ^ w * (2 * 2 ^ Q + 1) ^ w := by
  obtain ⟨u, v, e, hu, huQ, hv, he, hbin⟩ := CubicPhaseNorm.exists_short_binomial_of_bases ha hQ h₂ h₃
  have heQ : e ≤ L / Q := (Nat.le_div_iff_mul_le hQ).mpr (by rw [Nat.mul_comm]; omega)
  have hEven : A ^ u % 2 = 0 := even_base_pow (by omega) hu
  have hOdd : B ^ v % 2 = 1 := odd_base_pow (by omega) v
  have hbox : D ≤ (2 * M + 1) ^ (d + e) * (2 * 3 ^ v + 1) ^ d * (2 * 2 ^ u + 1) ^ d := by
    rcases hbin with hbin | hbin
    · have hh := PhaseResidueBox.modulus_le_of_binomial_of_odd_ends hd hP₀ hPd hP hPz hbin
        (Or.inl ⟨hOdd, hEven⟩)
      simpa only [Int.natAbs_pow, hA, hB] using hh
    · have hh := PhaseResidueBox.modulus_le_of_binomial_of_odd_ends hd hP₀ hPd hP hPz hbin
        (Or.inr ⟨hEven, hOdd⟩)
      rw [Nat.mul_right_comm] at hh
      simpa only [Int.natAbs_pow, hA, hB] using hh
  have h₀ : (2 * M + 1) ^ (d + e) ≤ (2 * M + 1) ^ (w + L / Q) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h₁ : (2 * 3 ^ v + 1) ^ d ≤ (2 * 3 ^ Q + 1) ^ w := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : v ≤ Q)
    exact grow_power (by omega) (by omega) hdw
  have h₂' : (2 * 2 ^ u + 1) ^ d ≤ (2 * 2 ^ Q + 1) ^ w := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) huQ
    exact grow_power (by omega) (by omega) hdw
  exact Nat.le_trans hbox (Nat.mul_le_mul (Nat.mul_le_mul h₀ h₁) h₂')

/-- For every approximation budget `Q>0`, the gap of a sparse phase root is
bounded by a box with only `2(r+1)` potentially large coordinate radii. -/
theorem gap_le_of_sparse_root {n L k r a D Q : Nat} {z : Int}
    (ha : a < L) (hD : 1 < D) (hQ : 0 < Q)
    (h₂ : (D : Int) ∣ 2 * z ^ a - 1) (h₃ : (D : Int) ∣ 3 * z ^ L - 1)
    (hroot : (D : Int) ∣ PhasePolynomial.sparseEvaluate n L k r z) :
    let M := PhasePolynomial.coefficientMass n L k r
    D ≤ (2 * M + 1) ^ (r + 1 + L / Q) * (2 * 3 ^ Q + 1) ^ (r + 1) * (2 * 2 ^ Q + 1) ^ (r + 1) := by
  obtain ⟨d, P, hd, hdr, hP₀, hPd, hP, heval⟩ := PhasePolynomial.sparse_polynomial_coefficients hD hroot
  have hPz : (D : Int) ∣ PhaseResidueBox.evaluate (d + 1) P z := by rwa [heval]
  exact modulus_le_of_phase_powers ha hQ rfl rfl h₂ h₃ hd hdr
    (by rw [hP₀]; decide) (by rw [hPd]; decide) (Nat.le_of_eq hP) hPz

private theorem box_le_two_pow (M w L Q : Nat) :
    (2 * M + 1) ^ (w + L / Q) * (2 * 3 ^ Q + 1) ^ w * (2 * 2 ^ Q + 1) ^ w ≤
      2 ^ (((2 * M + 1).log2 + 1) * (w + L / Q) + (3 * Q + 4) * w) := by
  have hA := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self (n := 2 * M + 1))) (w + L / Q)
  have hB : 2 * 3 ^ Q + 1 ≤ 2 ^ (2 * Q + 2) := by
    have h := Nat.pow_le_pow_left (by decide : 3 ≤ 2 ^ 2) Q
    have hpos := Nat.two_pow_pos (2 * Q)
    rw [← Nat.pow_mul] at h
    rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide]
    omega
  have hC : 2 * 2 ^ Q + 1 ≤ 2 ^ (Q + 2) := by
    have hpos := Nat.two_pow_pos Q
    rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide]
    omega
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hA (Nat.pow_le_pow_left hB w)) (Nat.pow_le_pow_left hC w)
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add] at hh
  have he : ((2 * M + 1).log2 + 1) * (w + L / Q) +
      (2 * Q + 2) * w + (Q + 2) * w =
        ((2 * M + 1).log2 + 1) * (w + L / Q) + (3 * Q + 4) * w := by grind
  rwa [he] at hh

private theorem small_log_exp (s : Nat) (hs : 10 ≤ s) : 4 * (1 + 14 * (s + 1)) ≤ 2 ^ s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
  clear hs
  induction j with
  | zero => decide
  | succ j ih =>
    let t := 10 + j
    change 4 * (1 + 14 * (t + 1)) ≤ 2 ^ t at ih
    change 4 * (1 + 14 * (t + 1 + 1)) ≤ 2 ^ (t + 1)
    rw [Nat.pow_succ]
    omega

private theorem small_log_of_large (L : Nat) (hL : 1024 ≤ L) :
    4 * (1 + 14 * (L.log2 + 1)) ≤ L := by
  have hzero : L ≠ 0 := by omega
  have h₁ : 10 ≤ L.log2 := (Nat.le_log2 hzero).mpr hL
  exact Nat.le_trans (small_log_exp L.log2 h₁) ((Nat.le_log2 hzero).mp (Nat.le_refl _))

private theorem log2_mono {u v : Nat} (hu : 0 < u) (h : u ≤ v) : u.log2 ≤ v.log2 := by
  exact (Nat.le_log2 (by omega : v ≠ 0)).mpr (Nat.le_trans (Nat.log2_self_le (by omega)) h)

/-- Power separation forces the product of the excess width and the
logarithmic height of the sparse coefficient mass to grow with the period. -/
theorem mass_bound_of_nonconvergent_coprime_cycle (hsep : PowerSeparation) {n L r : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ Reach.ReachesOne n)
    (hcop : (oddCount n L).Coprime L) (hr : r < L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    ∃ j k : Nat, j < L ∧ k < L ∧
      let M := PhasePolynomial.coefficientMass (acceleratedOrbit j n) L k r
      L ≤ 2 * (r + 1) * (13 * ((2 * M + 1).log2 + 1) + 4) := by
  let a := oddCount n L
  let D := 2 ^ L - 3 ^ a
  have hL := CycleLength1539.length_ge_1539 hn h hnr
  obtain ⟨_, ha, hgap⟩ := accCycle_bounds hn h
  have hD : 1 < D := by
    by_cases hd : D = 1
    · rcases (GapOne.gap_one_forces_trivial hn h hd).2.2 with h₁ | h₂
      · exact (hnr (h₁ ▸ Reach.reachesOne_one)).elim
      · exact (hnr (h₂ ▸ Reach.reachesOne_two)).elim
    · dsimp [D, a] at hd ⊢
      omega
  obtain ⟨j, k, hj, hk, z, h₂, h₃, hp⟩ := PhasePolynomial.cycle_sparse_root hn h hcop hr hw
  let M := PhasePolynomial.coefficientMass (acceleratedOrbit j n) L k r
  let s := (2 * M + 1).log2 + 1
  let Q := 4 * s
  have hQ : 0 < Q := by dsimp [Q, s]; omega
  refine ⟨j, k, hj, hk, ?_⟩
  have hbox := gap_le_of_sparse_root (Q := Q) ha hD hQ h₂ h₃ hp
  have hpow : D ≤ 2 ^ (s * (r + 1 + L / Q) + (3 * Q + 4) * (r + 1)) :=
    Nat.le_trans hbox (box_le_two_pow M (r + 1) L Q)
  let E := s * (r + 1 + L / Q) + (3 * Q + 4) * (r + 1)
  have hmain : L ≤ 1 + 14 * (L.log2 + 1) + E := by
    have hl := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self (n := L))) 14
    have hh : 2 ^ L ≤ 2 * (2 ^ (L.log2 + 1)) ^ 14 * 2 ^ E :=
      Nat.le_trans (hsep a L hgap) (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hl) hpow)
    rw [← Nat.pow_mul, Nat.mul_comm (L.log2 + 1) 14,
      ← Nat.pow_one 2, ← Nat.pow_add, ← Nat.pow_add] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hlog := small_log_of_large L (by omega)
  have hshare : 4 * (s * (L / Q)) ≤ L := by
    have hd := Nat.div_mul_le_self L Q
    have he : L / Q * Q = 4 * (s * (L / Q)) := by dsimp only [Q]; ac_rfl
    rw [he] at hd
    exact hd
  have hE : E = (r + 1) * (13 * s + 4) + s * (L / Q) := by
    dsimp only [E, Q]
    grind
  rw [hE] at hmain
  change L ≤ 2 * (r + 1) * (13 * s + 4)
  rw [Nat.mul_assoc]
  omega

/-- A nonconvergent coprime cycle confined to width `L+r<2L` must have
`L ≤ 2(r+1)(13 floor(log₂(2r+5))+17)`, assuming power separation. -/
theorem excess_bound_of_nonconvergent_coprime_cycle (hsep : PowerSeparation) {n L r : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ Reach.ReachesOne n)
    (hcop : (oddCount n L).Coprime L) (hr : r < L)
    (hw : ∀ i j, walk n L i ≤ walk n L j + L + r) :
    L ≤ 2 * (r + 1) * (13 * ((2 * r + 5).log2 + 1) + 4) := by
  obtain ⟨j, k, _, _, hbound⟩ := mass_bound_of_nonconvergent_coprime_cycle hsep hn h hnr hcop hr hw
  let M := PhasePolynomial.coefficientMass (acceleratedOrbit j n) L k r
  change L ≤ 2 * (r + 1) * (13 * ((2 * M + 1).log2 + 1) + 4) at hbound
  have hm : M ≤ r + 2 := PhasePolynomial.coefficientMass_le _ _ _ _
  have hlog := log2_mono (by omega : 0 < 2 * M + 1) (by omega : 2 * M + 1 ≤ 2 * r + 5)
  exact Nat.le_trans hbound (Nat.mul_le_mul_left _ (by omega))

/-- A nonconvergent least cycle with coprime period and odd count has
discrepancy spread at least its period plus an explicit growing margin. -/
theorem growing_width_of_nonconvergent_coprime_cycle (hsep : PowerSeparation) {n L : Nat}
    (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ Reach.ReachesOne n)
    (hleast : ∀ k, 0 < k → k < L → acceleratedOrbit k n ≠ n)
    (hcop : (oddCount n L).Coprime L) :
    let C := 2 * (13 * ((2 * L + 5).log2 + 1) + 4)
    ∃ i j, i < L ∧ j < L ∧
      walk n L j + L + (((L - 1) / C : Nat) : Int) ≤ walk n L i := by
  let C := 2 * (13 * ((2 * L + 5).log2 + 1) + 4)
  let t := (L - 1) / C
  have hL := h.1
  have ht : t < L := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  change ∃ i j, i < L ∧ j < L ∧ walk n L j + L + (t : Int) ≤ walk n L i
  by_cases hz : t = 0
  · have hnon : 2 < n := by
      by_cases hp : 2 < n
      · exact hp
      · rcases (show n = 1 ∨ n = 2 by omega) with he | he
        · exact (hnr (he ▸ Reach.reachesOne_one)).elim
        · exact (hnr (he ▸ Reach.reachesOne_two)).elim
    obtain ⟨i, j, hi, hj, hw⟩ := OneExtraCycle.nontrivial_cycle_needs_extra_width hn h hleast hnon
    exact ⟨i, j, hi, hj, by omega⟩
  · apply Classical.byContradiction
    intro hno
    let r := t - 1
    have hr : r < L := by dsimp only [r]; omega
    have hw (i j : Nat) : walk n L i ≤ walk n L j + L + r := by
      rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
      have hb : ¬ walk n L (j % L) + L + (t : Int) ≤ walk n L (i % L) := fun he =>
        hno ⟨i % L, j % L, Nat.mod_lt _ h.1, Nat.mod_lt _ h.1, he⟩
      dsimp only [r]
      omega
    have hbound := excess_bound_of_nonconvergent_coprime_cycle hsep hn h hnr hcop hr hw
    have hlog := log2_mono (by omega : 0 < 2 * r + 5) (by omega : 2 * r + 5 ≤ 2 * L + 5)
    have hle : 13 * ((2 * r + 5).log2 + 1) + 4 ≤ 13 * ((2 * L + 5).log2 + 1) + 4 := by omega
    have hCt : L ≤ C * t := by
      have he : r + 1 = t := Nat.sub_add_cancel (Nat.pos_of_ne_zero hz)
      calc
        _ ≤ 2 * (r + 1) * (13 * ((2 * r + 5).log2 + 1) + 4) := hbound
        _ ≤ 2 * (r + 1) * (13 * ((2 * L + 5).log2 + 1) + 4) := Nat.mul_le_mul_left _ hle
        _ = _ := by rw [he]; dsimp only [C]; ac_rfl
    have hdiv : C * t ≤ L - 1 := by
      rw [Nat.mul_comm C t]
      exact Nat.div_mul_le_self _ _
    omega

/-- A least period of length `2p` with `2b` odd steps and coprime `b,p`
requires growing discrepancy excess. The sum factor of the power gap
gives this bound directly. -/
theorem paired_width_excess_bound {n p b r : Nat} (hn : 0 < n) (h : AccIsCycleOf n (2 * p))
    (hleast : ∀ i, 0 < i → i < 2 * p → acceleratedOrbit i n ≠ n)
    (hb : oddCount n (2 * p) = 2 * b) (hbp : b.Coprime p) (hr : r < p)
    (hw : ∀ i j, walk n (2 * p) i ≤ walk n (2 * p) j + (2 * p : Nat) + (2 * r : Nat)) :
    p ≤ 2 * r * (7 * ((2 * r + 3).log2 + 1) + 4) := by
  let D := 2 ^ p + 3 ^ b
  let M := r + 1
  let s := (2 * M + 1).log2 + 1
  let Q := 2 * s
  have hQ : 0 < Q := by dsimp [Q, s]; omega
  have hcount := (accCycle_bounds hn h).2.1
  have hb' : b < p := by rw [hb] at hcount; omega
  obtain ⟨k, c, z, d, P, h₂, h₃, hd, hdr, hP₀, hPd, hmass, hroot⟩ :=
    PhasePolynomial.cycle_paired_phase_root hn h hleast hb hbp hr hw
  have hbox := modulus_le_of_phase_powers hb' hQ
    (by simp [Int.natAbs_mul, Int.natAbs_pow]) (by simp [Int.natAbs_mul, Int.natAbs_pow])
    h₂ h₃ hd hdr hP₀ hPd hmass hroot
  have hpow : 2 ^ p ≤ 2 ^ (s * (r + p / Q) + (3 * Q + 4) * r) :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hbox (box_le_two_pow M r p Q))
  have hp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hshare : 2 * (s * (p / Q)) ≤ p := by
    have he : 2 * (s * (p / Q)) = p / Q * Q := by dsimp only [Q]; ac_rfl
    rw [he]
    exact Nat.div_mul_le_self _ _
  have hE : s * (r + p / Q) + (3 * Q + 4) * r = r * (7 * s + 4) + s * (p / Q) := by
    dsimp only [Q]
    grind
  rw [hE] at hp
  have hs : s = (2 * r + 3).log2 + 1 := by
    dsimp only [s, M]
    rw [show 2 * (r + 1) + 1 = 2 * r + 3 by omega]
  rw [← hs, Nat.mul_assoc]
  omega

/-- An explicit discrepancy-width lower bound for a least cycle whose period
and odd count have greatest common divisor two. -/
theorem growing_width_of_gcd_two_cycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hleast : ∀ i, 0 < i → i < L → acceleratedOrbit i n ≠ n)
    (hg : (oddCount n L).gcd L = 2) :
    let p := L / 2
    let C := 2 * (7 * ((2 * p + 3).log2 + 1) + 4)
    ∃ i j, i < L ∧ j < L ∧
      walk n L j + L + ((2 * ((p - 1) / C + 1) : Nat) : Int) ≤ walk n L i := by
  have hL : 2 ∣ L := hg ▸ Nat.gcd_dvd_right (oddCount n L) L
  obtain ⟨p, rfl⟩ := hL
  have hA : 2 ∣ oddCount n (2 * p) := by
    simpa only [hg] using Nat.gcd_dvd_left (oddCount n (2 * p)) (2 * p)
  obtain ⟨b, hb⟩ := hA
  have hbp : b.Coprime p := by
    rw [hb, Nat.gcd_mul_left] at hg
    change b.gcd p = 1
    omega
  let C := 2 * (7 * ((2 * p + 3).log2 + 1) + 4)
  let r := (p - 1) / C
  have hp : 0 < p := by have := h.1; omega
  have hr : r < p := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [show 2 * p / 2 = p by omega]
  change ∃ i j, i < 2 * p ∧ j < 2 * p ∧
    walk n (2 * p) j + (2 * p : Nat) + (2 * (r + 1) : Nat) ≤ walk n (2 * p) i
  apply Classical.byContradiction
  intro hno
  have hw (i j : Nat) : walk n (2 * p) i ≤ walk n (2 * p) j + (2 * p : Nat) + (2 * r : Nat) := by
    rw [walk_mod h.1 h.2 i, walk_mod h.1 h.2 j]
    let a := i % (2 * p)
    let t := j % (2 * p)
    have hlt : ¬ walk n (2 * p) t + (2 * p : Nat) + (2 * (r + 1) : Nat) ≤ walk n (2 * p) a :=
      fun he => hno ⟨a, t, Nat.mod_lt _ h.1, Nat.mod_lt _ h.1, he⟩
    have heven (k : Nat) : ∃ v : Int, walk n (2 * p) k = 2 * v := by
      refine ⟨(p : Int) * oddCount n k - (b : Int) * k, ?_⟩
      unfold walk
      rw [hb, Int.natCast_mul, Int.natCast_mul]
      grind
    obtain ⟨x, hx⟩ := heven a
    obtain ⟨y, hy⟩ := heven t
    change walk n (2 * p) a ≤ walk n (2 * p) t + (2 * p : Nat) + (2 * r : Nat)
    rw [hx, hy] at hlt ⊢
    omega
  have hbound := paired_width_excess_bound hn h hleast hb hbp hr hw
  have hlog := log2_mono (by omega : 0 < 2 * r + 3) (by omega : 2 * r + 3 ≤ 2 * p + 3)
  have hCr : p ≤ r * C := by
    calc
      _ ≤ 2 * r * (7 * ((2 * r + 3).log2 + 1) + 4) := hbound
      _ ≤ 2 * r * (7 * ((2 * p + 3).log2 + 1) + 4) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by dsimp only [C]; ac_rfl
  have hdiv : r * C ≤ p - 1 := Nat.div_mul_le_self _ _
  omega

/-- The verified length floor rules out width at most `2p+18`
for any nonconvergent least cycle with two copies of each phase. -/
theorem reachesOne_of_paired_width_eighteen {n p b : Nat} (hn : 0 < n) (h : AccIsCycleOf n (2 * p))
    (hleast : ∀ i, 0 < i → i < 2 * p → acceleratedOrbit i n ≠ n)
    (hb : oddCount n (2 * p) = 2 * b) (hbp : b.Coprime p)
    (hw : ∀ i j, walk n (2 * p) i ≤ walk n (2 * p) j + (2 * p : Nat) + 18) :
    Reach.ReachesOne n := by
  apply Classical.byContradiction
  intro hnr
  have hlong := CycleLength1539.length_ge_1539 hn h hnr
  have hbound := paired_width_excess_bound (r := 9) hn h hleast hb hbp (by omega) hw
  have hnum : 2 * 9 * (7 * ((2 * 9 + 3).log2 + 1) + 4) = 702 := by decide
  omega

end Collatz.SparsePhaseBound
