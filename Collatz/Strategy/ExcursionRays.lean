import Collatz.Strategy.ExcursionHistoryGrid

/-!
# Arithmetic rays of excursion profiles

A finite excursion trace can be translated by a multiple of twice its
denominator without changing the odd-run lengths or the halving counts.
The translated endpoint changes by the same multiple of twice its
tripling coefficient. This gives an exact descent threshold on the ray.
-/

namespace Collatz.ExcursionRays

open Collatz.ExcursionMap Collatz.ExcursionBudget
open Collatz.ExcursionHistoryGrid Collatz.ExcursionMixedGrid

private theorem odd_after_shift {x : Nat} (hx : x % 2 = 1) (a k : Nat) :
    (x + a * (2 * k)) % 2 = 1 := by
  rw [Nat.mul_left_comm a 2]
  omega

/-- One excursion transports along its source progression, preserving both
odd cofactors and the exact valuations. -/
theorem lift_excursion {n v u W e : Nat} (h : IsExcursion n v u W e) (k : Nat) :
    IsExcursion (n + 2 ^ (v + W) * (2 * k)) v (u + 2 ^ W * (2 * k)) W
      (e + 3 ^ v * (2 * k)) := by
  obtain ⟨hn, hu, he, hv, hW, hsource, htarget⟩ := h
  refine ⟨odd_after_shift hn _ _, odd_after_shift hu _ _, odd_after_shift he _ _,
    hv, hW, ?_, ?_⟩
  · rw [Nat.mul_add, ← hsource, Nat.pow_add, Nat.mul_assoc, Nat.add_right_comm]
  · rw [Nat.mul_add, htarget, Nat.mul_add, Nat.add_right_comm]
    congr 1
    ac_rfl

/-- Removing a full source period leaves a valid excursion and removes
the corresponding endpoint period. -/
theorem lower_excursion {n v u W e k : Nat}
    (h : IsExcursion (n + 2 ^ (v + W) * (2 * k)) v u W e) :
    ∃ u₀ e₀, IsExcursion n v u₀ W e₀ ∧ e = e₀ + 3 ^ v * (2 * k) := by
  obtain ⟨hn, hu, he, hv, hW, hsource, htarget⟩ := h
  let du := 2 ^ W * (2 * k)
  let de := 3 ^ v * (2 * k)
  let u₀ := u - du
  let e₀ := e - de
  have hdu : du < u := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ v)
    rw [Nat.pow_add, Nat.mul_assoc] at hsource
    change n + 2 ^ v * du + 1 = 2 ^ v * u at hsource
    omega
  have hu₀ : u₀ + du = u := Nat.sub_add_cancel (Nat.le_of_lt hdu)
  have hsource₀ : n + 1 = 2 ^ v * u₀ := by
    rw [Nat.pow_add, Nat.mul_assoc, ← hu₀, Nat.mul_add] at hsource
    change n + 2 ^ v * du + 1 = 2 ^ v * u₀ + 2 ^ v * du at hsource
    omega
  have hshift : 3 ^ v * du = 2 ^ W * de := by dsimp [du, de]; ac_rfl
  have htarget' : 3 ^ v * u₀ + 2 ^ W * de = 2 ^ W * e + 1 := by
    rw [← hu₀, Nat.mul_add, hshift] at htarget
    exact htarget
  have hpos : 0 < 3 ^ v * u₀ :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.sub_pos_of_lt hdu)
  have hde : de ≤ e := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos W)
    omega
  have he₀ : e₀ + de = e := Nat.sub_add_cancel hde
  have htarget₀ : 3 ^ v * u₀ = 2 ^ W * e₀ + 1 := by
    rw [← he₀, Nat.mul_add] at htarget'
    omega
  have hn₀ : n % 2 = 1 := by
    rw [Nat.mul_left_comm (2 ^ (v + W)) 2] at hn
    omega
  have huodd : u₀ % 2 = 1 := by
    have hmod : du % 2 = 0 := by dsimp [du]; rw [Nat.mul_left_comm _ 2]; omega
    omega
  have heodd : e₀ % 2 = 1 := by
    have hmod : de % 2 = 0 := by dsimp [de]; rw [Nat.mul_left_comm _ 2]; omega
    omega
  exact ⟨u₀, e₀, ⟨hn₀, huodd, heodd, hv, hW, hsource₀, htarget₀⟩, he₀.symm⟩

/-- Transport a whole excursion profile along a dyadic ray. -/
theorem lift_trace {n e : Nat} {rs : List Run} (h : Trace n e rs) (k : Nat) :
    Trace (n + 2 ^ time rs * (2 * k)) (e + 3 ^ ExcursionBudget.oddCount rs * (2 * k)) rs := by
  induction h generalizing k with
  | nil => exact Trace.nil
  | @step x y v u W rs _ hstep ih =>
    have hp := ih (2 ^ (v + W) * k)
    have hnext := lift_excursion hstep (3 ^ ExcursionBudget.oddCount rs * k)
    have hsource : x + 3 ^ ExcursionBudget.oddCount rs * (2 * (2 ^ (v + W) * k)) =
        x + 2 ^ (v + W) * (2 * (3 ^ ExcursionBudget.oddCount rs * k)) := by
      ac_rfl
    rw [hsource] at hp
    have htrace := Trace.step hp hnext
    simpa only [time, ExcursionBudget.oddCount, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using htrace

/-- A trace on a translated source comes from a trace at the original source. -/
theorem lower_trace {n e k : Nat} {rs : List Run}
    (h : Trace (n + 2 ^ time rs * (2 * k)) e rs) :
    ∃ e₀, Trace n e₀ rs ∧ e = e₀ + 3 ^ ExcursionBudget.oddCount rs * (2 * k) := by
  induction rs generalizing n e k with
  | nil =>
    cases h
    exact ⟨n, Trace.nil, rfl⟩
  | cons r rs ih =>
    cases h with
    | @step x y v u W _ hprev hrun =>
      have hs : n + 2 ^ time (⟨v, W⟩ :: rs) * (2 * k) =
          n + 2 ^ time rs * (2 * (2 ^ (v + W) * k)) := by
        simp only [time, Nat.pow_add]
        ac_rfl
      rw [hs] at hprev
      obtain ⟨x₀, hp, heq⟩ := ih hprev
      have hx : x = x₀ + 2 ^ (v + W) * (2 * (3 ^ ExcursionBudget.oddCount rs * k)) := by
        rw [heq]
        ac_rfl
      rw [hx] at hrun
      obtain ⟨u₀, y₀, hrun₀, hlast⟩ := lower_excursion hrun
      refine ⟨y₀, Trace.step hp hrun₀, ?_⟩
      rw [hlast]
      simp only [ExcursionBudget.oddCount, Nat.pow_add]
      ac_rfl

private theorem odd_landing {n e : Nat} {r : Run} {rs : List Run} (h : Trace n e (r :: rs)) :
    e % 2 = 1 := by
  cases h with
  | step _ hrun => exact hrun.2.2.1

private theorem source_residue_of_le {n e m f : Nat} {r : Run} {rs : List Run}
    (h : Trace n e (r :: rs)) (h' : Trace m f (r :: rs)) (hnm : n ≤ m) :
    n % (2 ^ time (r :: rs) * 2) = m % (2 ^ time (r :: rs) * 2) := by
  let S := time (r :: rs)
  let V := ExcursionBudget.oddCount (r :: rs)
  have he := odd_landing h
  have hf := odd_landing h'
  have htwo : 2 ∣ f - e := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨k, hk⟩ := htwo
  have hdifference : 3 ^ V * (m - n) = 2 ^ S * (f - e) := by
    have ha := h.affine
    have hb := h'.affine
    change 3 ^ V * n + offset (r :: rs) = 2 ^ S * e at ha
    change 3 ^ V * m + offset (r :: rs) = 2 ^ S * f at hb
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have hdvd : 2 ^ (S + 1) ∣ 3 ^ V * (m - n) := by
    refine ⟨k, ?_⟩
    rw [hdifference, hk, Nat.pow_succ, Nat.mul_assoc]
  have hcoprime : Nat.gcd (2 ^ (S + 1)) (3 ^ V) = 1 :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide)
  have hcut := (Nat.dvd_gcd_mul_iff_dvd_mul).mpr hdvd
  rw [hcoprime, Nat.one_mul, Nat.pow_succ] at hcut
  obtain ⟨q, hq⟩ := hcut
  have hmq : m = n + (2 ^ S * 2) * q := by omega
  change n % (2 ^ S * 2) = m % (2 ^ S * 2)
  rw [hmq, Nat.add_mul_mod_self_left]

/-- A nonempty excursion profile determines its source residue. -/
theorem source_residue {n e m f : Nat} {r : Run} {rs : List Run}
    (h : Trace n e (r :: rs)) (h' : Trace m f (r :: rs)) :
    n % (2 ^ time (r :: rs) * 2) = m % (2 ^ time (r :: rs) * 2) := by
  rcases Nat.le_total n m with hle | hle
  · exact source_residue_of_le h h' hle
  · exact (source_residue_of_le h' h hle).symm

/-- The least nonnegative source representative realizes the same trace. -/
theorem canonical_trace {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    ∃ e₀, Trace (n % (2 ^ time rs * 2)) e₀ rs ∧
      e = e₀ + 3 ^ ExcursionBudget.oddCount rs * (2 * (n / (2 ^ time rs * 2))) := by
  let D := 2 ^ time rs * 2
  have hrep : n % D + 2 ^ time rs * (2 * (n / D)) = n := by
    rw [← Nat.mul_assoc]
    exact Nat.mod_add_div n D
  have h' : Trace (n % D + 2 ^ time rs * (2 * (n / D))) e rs := by rwa [hrep]
  exact lower_trace h'

/-- The source set of a realized nonempty profile is exactly one residue class. -/
theorem realizes_iff_mod {n e m : Nat} {r : Run} {rs : List Run}
    (h : Trace n e (r :: rs)) :
    (∃ f, Trace m f (r :: rs)) ↔
      m % (2 ^ time (r :: rs) * 2) = n % (2 ^ time (r :: rs) * 2) := by
  constructor
  · rintro ⟨_, ht⟩
    exact source_residue ht h
  · intro hm
    obtain ⟨e₀, h₀, _⟩ := canonical_trace h
    let B := 2 ^ time (r :: rs)
    let D := B * 2
    have hshift := lift_trace h₀ (m / D)
    have hrep : n % D + B * (2 * (m / D)) = m := by
      change m % D = n % D at hm
      rw [← hm, ← Nat.mul_assoc]
      exact Nat.mod_add_div m D
    change Trace (n % D + B * (2 * (m / D))) _ (r :: rs) at hshift
    rw [hrep] at hshift
    exact ⟨_, hshift⟩

private theorem excursion_source_ge_multiple {n v u W e k : Nat} (h : IsExcursion n v u W e)
    (he : 3 ^ v * k ≤ e) : 2 ^ (v + W) * k ≤ n := by
  have hscale : 3 ^ v * (2 ^ W * k) < 3 ^ v * u := by
    calc
      _ = 2 ^ W * (3 ^ v * k) := Nat.mul_left_comm ..
      _ ≤ 2 ^ W * e := Nat.mul_le_mul_left _ he
      _ < 2 ^ W * e + 1 := Nat.lt_succ_self _
      _ = 3 ^ v * u := h.2.2.2.2.2.2.symm
  have hcut : 2 ^ W * k + 1 ≤ u :=
    Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hscale)
  have hn := Nat.mul_le_mul_left (2 ^ v) hcut
  rw [← h.2.2.2.2.2.1, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_add] at hn
  have hpos := Nat.two_pow_pos v
  omega

/-- A multiple of the tripling coefficient at the endpoint forces the
same multiple of the denominator at the source. -/
theorem source_ge_of_endpoint_ge_multiple {n e k : Nat} {rs : List Run}
    (h : Trace n e rs) (he : 3 ^ ExcursionBudget.oddCount rs * k ≤ e) :
    2 ^ time rs * k ≤ n := by
  induction h generalizing k with
  | nil => simpa [time, ExcursionBudget.oddCount] using he
  | @step x y v u W rs _ hrun ih =>
    have hy : 3 ^ v * (3 ^ ExcursionBudget.oddCount rs * k) ≤ y := by
      simpa only [ExcursionBudget.oddCount, Nat.pow_add, Nat.mul_assoc] using he
    have hx := excursion_source_ge_multiple hrun hy
    rw [Nat.mul_left_comm] at hx
    have hn := ih hx
    simpa only [time, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn

/-- The source and endpoint have the same quotient by their respective
coefficient periods. -/
theorem quotient_eq {n e : Nat} {rs : List Run} (h : Trace n e rs) :
    e / 3 ^ ExcursionBudget.oddCount rs = n / 2 ^ time rs := by
  let A := 3 ^ ExcursionBudget.oddCount rs
  let B := 2 ^ time rs
  have hA : 0 < A := Nat.pow_pos (by decide)
  have hB : 0 < B := Nat.two_pow_pos _
  change e / A = n / B
  apply Nat.le_antisymm
  · apply (Nat.le_div_iff_mul_le hB).mpr
    rw [Nat.mul_comm]
    exact source_ge_of_endpoint_ge_multiple h (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self e A)
  · apply (Nat.le_div_iff_mul_le hA).mpr
    have hn : B * (n / B) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n B
    have he : B * (A * (n / B)) ≤ B * e := by
      calc
        _ = A * (B * (n / B)) := Nat.mul_left_comm ..
        _ ≤ A * n := Nat.mul_le_mul_left A hn
        _ ≤ A * n + offset rs := Nat.le_add_right _ _
        _ = B * e := h.affine
    rw [Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_left he hB

/-- Any source below a multiple of its denominator lands below the same
multiple of the tripling coefficient. -/
theorem endpoint_lt_of_source_lt_multiple {n e k : Nat} {rs : List Run}
    (h : Trace n e rs) (hn : n < 2 ^ time rs * k) :
    e < 3 ^ ExcursionBudget.oddCount rs * k :=
  Nat.lt_of_not_ge (fun he => Nat.not_le_of_gt hn (source_ge_of_endpoint_ge_multiple h he))

theorem time_append (later earlier : List Run) : time (later ++ earlier) = time later + time earlier := by
  induction later with
  | nil => simp [time]
  | cons r rs ih => simp [time, ih, Nat.add_assoc]

/-- Split a reverse-ordered profile at any excursion boundary. -/
theorem split_trace {n e : Nat} {later earlier : List Run} (h : Trace n e (later ++ earlier)) :
    ∃ x, Trace n x earlier ∧ Trace x e later := by
  induction later generalizing e with
  | nil => exact ⟨e, h, Trace.nil⟩
  | cons r rs ih =>
    cases h with
    | step hp hrun =>
      obtain ⟨x, hx, hrest⟩ := ih hp
      exact ⟨x, hx, Trace.step hrest hrun⟩

/-- A canonical source keeps a cut below the joint period of its incoming
tripling coefficient and its outgoing source period. -/
theorem cut_lt_period {n x : Nat} {later earlier : List Run} (hx : Trace n x earlier)
    (hn : n < 2 ^ time (later ++ earlier) * 2) :
    x < 3 ^ ExcursionBudget.oddCount earlier * (2 ^ time later * 2) := by
  have hbound : n < 2 ^ time earlier * (2 ^ time later * 2) := by
    rw [time_append, Nat.pow_add] at hn
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn
  exact endpoint_lt_of_source_lt_multiple hx hbound

theorem canonical_cut_lt_period {n e : Nat} {later earlier : List Run}
    (h : Trace n e (later ++ earlier)) (hn : n < 2 ^ time (later ++ earlier) * 2) :
    ∃ x, Trace n x earlier ∧ Trace x e later ∧
      x < 3 ^ ExcursionBudget.oddCount earlier * (2 ^ time later * 2) := by
  obtain ⟨x, hx, hf⟩ := split_trace h
  exact ⟨x, hx, hf, cut_lt_period hx hn⟩

/-- Translating the full source by its period translates a cut by exactly
its joint period. -/
theorem lift_cut {n x : Nat} {later earlier : List Run} (h : Trace n x earlier) (k : Nat) :
    Trace (n + 2 ^ time (later ++ earlier) * (2 * k))
      (x + (3 ^ ExcursionBudget.oddCount earlier * (2 ^ time later * 2)) * k) earlier := by
  have ht := lift_trace h (2 ^ time later * k)
  simpa only [time_append, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht

private theorem joint_dvd_difference {x y s v z : Nat}
    (hdyadic : x % 2 ^ s = y % 2 ^ s)
    (hternary : (2 ^ z * x) % 3 ^ v = (2 ^ z * y) % 3 ^ v) :
    2 ^ s * 3 ^ v ∣ y - x := by
  have ht := dvd_sub_of_residue hternary
  rw [← Nat.mul_sub_left_distrib] at ht
  have h3 := cancel_dyadic ht
  obtain ⟨k, hk⟩ := dvd_sub_of_residue hdyadic
  rw [hk] at h3
  obtain ⟨j, hj⟩ := cancel_dyadic h3
  refine ⟨j, ?_⟩
  rw [hk, hj, Nat.mul_assoc]

/-- The incoming ternary residue alone recovers the endpoint when the
source is below the trace denominator. -/
theorem recover_ternary {n x b : Nat} {rs : List Run} (h : Trace n x rs)
    (hn : n < 2 ^ time rs) (hb : b < 3 ^ ExcursionBudget.oddCount rs)
    (hc : (2 ^ time rs * b) % 3 ^ ExcursionBudget.oddCount rs =
      offset rs % 3 ^ ExcursionBudget.oddCount rs) : b = x := by
  have hx : x < 3 ^ ExcursionBudget.oddCount rs := by
    simpa only [Nat.mul_one] using endpoint_lt_of_source_lt_multiple (k := 1) h
      (by simpa only [Nat.mul_one] using hn)
  have hsub := dvd_sub_of_residue (hc.trans (history_residue h).symm)
  have hrev := dvd_sub_of_residue ((history_residue h).trans hc.symm)
  rw [← Nat.mul_sub_left_distrib] at hsub hrev
  have h1 := Nat.eq_zero_of_dvd_of_lt (cancel_dyadic hsub) (by omega : x - b < _)
  have h2 := Nat.eq_zero_of_dvd_of_lt (cancel_dyadic hrev) (by omega : b - x < _)
  omega

/-- At a cut of a canonical trace, the incoming ternary residue and
outgoing dyadic residue uniquely recover the value. -/
theorem recover_canonical_cut {n x b : Nat} {later earlier : List Run}
    (h : Trace n x earlier) (hn : n < 2 ^ time (later ++ earlier) * 2)
    (hb : b < 3 ^ ExcursionBudget.oddCount earlier * (2 ^ time later * 2))
    (hdyadic : b % (2 ^ time later * 2) = x % (2 ^ time later * 2))
    (hternary : (2 ^ time earlier * b) % 3 ^ ExcursionBudget.oddCount earlier =
      offset earlier % 3 ^ ExcursionBudget.oddCount earlier) : b = x := by
  have hx := cut_lt_period h hn
  rw [← Nat.pow_succ] at hdyadic hb hx
  have hjoint := joint_dvd_difference hdyadic (hternary.trans (history_residue h).symm)
  have hrev := joint_dvd_difference hdyadic.symm ((history_residue h).trans hternary.symm)
  have h1 := Nat.eq_zero_of_dvd_of_lt hjoint (by rw [Nat.mul_comm]; omega : x - b < _)
  have h2 := Nat.eq_zero_of_dvd_of_lt hrev (by rw [Nat.mul_comm]; omega : b - x < _)
  omega

/-- Two occurrences of the same past and future profiles lie in one joint
residue class at the cut. -/
theorem repeated_window_dvd_difference {n m x y e f : Nat}
    {earlier later : List Run} {r : Run}
    (hpx : Trace n x earlier) (hpy : Trace m y earlier)
    (hfx : Trace x e (r :: later)) (hfy : Trace y f (r :: later)) :
    (2 ^ time (r :: later) * 2) * 3 ^ ExcursionBudget.oddCount earlier ∣ y - x := by
  have hdyadic := source_residue hfx hfy
  rw [← Nat.pow_succ] at hdyadic ⊢
  exact joint_dvd_difference hdyadic ((history_residue hpx).trans (history_residue hpy).symm)

/-- A repeated two-sided profile either revisits the same point or forces
separation by at least its joint period. -/
theorem repeated_window_separation {n m x y e f : Nat}
    {earlier later : List Run} {r : Run}
    (hpx : Trace n x earlier) (hpy : Trace m y earlier)
    (hfx : Trace x e (r :: later)) (hfy : Trace y f (r :: later)) (hxy : x < y) :
    x + (2 ^ time (r :: later) * 2) * 3 ^ ExcursionBudget.oddCount earlier ≤ y := by
  have hdiv := repeated_window_dvd_difference hpx hpy hfx hfy
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hdiv
  omega

/-- A descent along the ray is equivalent to a single integer comparison. -/
theorem ray_drop_iff {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hcoef : 3 ^ ExcursionBudget.oddCount rs ≤ 2 ^ time rs) (k : Nat) :
    Collatz.acceleratedOrbit (time rs) (n + 2 ^ time rs * (2 * k)) <
        n + 2 ^ time rs * (2 * k) ↔
      e < n + (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs) * (2 * k) := by
  rw [(lift_trace h k).landing]
  have hsplit : 2 ^ time rs * (2 * k) =
      3 ^ ExcursionBudget.oddCount rs * (2 * k) +
        (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs) * (2 * k) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hcoef]
  rw [hsplit]
  omega

/-- If the coefficient contracts but the original landing is high, the
quotient gives the exact last shift index that can fail to descend. -/
theorem ray_drop_threshold {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hcoef : 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) (hkeep : n ≤ e) (k : Nat) :
    Collatz.acceleratedOrbit (time rs) (n + 2 ^ time rs * (2 * k)) <
        n + 2 ^ time rs * (2 * k) ↔
      (e - n) / (2 * (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs)) < k := by
  rw [ray_drop_iff h (Nat.le_of_lt hcoef)]
  let gap := 2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs
  have hgap : 0 < gap := Nat.sub_pos_of_lt hcoef
  rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide) hgap)]
  change e < n + gap * (2 * k) ↔ e - n < k * (2 * gap)
  have hmul : gap * (2 * k) = k * (2 * gap) := by ac_rfl
  rw [hmul]
  omega

/-- Once a finite profile has descended, every source on its ray descends
at the same shortcut time. -/
theorem descent_on_ray {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hdrop : e < n) (k : Nat) :
    Collatz.acceleratedOrbit (time rs) (n + 2 ^ time rs * (2 * k)) <
      n + 2 ^ time rs * (2 * k) := by
  have hcoef : 3 ^ ExcursionBudget.oddCount rs ≤ 2 ^ time rs := by
    apply Nat.le_of_not_gt
    intro hc
    have hle := Nat.mul_le_mul_right n (Nat.le_of_lt hc)
    have hlt := Nat.mul_lt_mul_of_pos_left hdrop (Nat.two_pow_pos (time rs))
    have ha := h.affine
    omega
  exact (ray_drop_iff h hcoef k).mpr (Nat.lt_of_lt_of_le hdrop (Nat.le_add_right _ _))

/-- The offset is bounded by placing the odd steps at the end. -/
theorem offset_add_denominator_le (rs : List Run) :
    2 ^ ExcursionBudget.oddCount rs * (offset rs + 2 ^ time rs) ≤
      2 ^ time rs * 3 ^ ExcursionBudget.oddCount rs := by
  induction rs with
  | nil => simp [ExcursionBudget.oddCount, offset, time]
  | cons r rs ih =>
    let Q := 2 ^ ExcursionBudget.oddCount rs
    let A := 3 ^ ExcursionBudget.oddCount rs
    let B := 2 ^ time rs
    let q := 2 ^ r.oddSteps
    let a := 3 ^ r.oddSteps
    let R := 2 ^ r.halvings
    have hqa : q ≤ a := Nat.pow_le_pow_left (by decide) _
    have hQA : Q ≤ A := Nat.pow_le_pow_left (by decide) _
    have hR : (R - 1) + 1 = R := Nat.sub_add_cancel (Nat.one_le_pow _ 2 (by decide))
    have hc : B * (a - q) + B * q = B * a := by rw [← Nat.mul_add, Nat.sub_add_cancel hqa]
    have hsum : a * offset rs + B * (a - q) + B * q * R =
        a * (offset rs + B) + B * q * (R - 1) := by
      calc
        _ = a * offset rs + B * (a - q) + (B * q * (R - 1) + B * q) := by
          have hr : B * q * ((R - 1) + 1) = B * q * (R - 1) + B * q := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [← hr, hR]
        _ = a * offset rs + (B * (a - q) + B * q) + B * q * (R - 1) := by ac_rfl
        _ = _ := by rw [hc, Nat.mul_add, Nat.mul_comm a B]
    have hmain : Q * (a * offset rs + B * (a - q) + B * q * R) ≤ B * (a * A) * R := by
      rw [hsum, Nat.mul_add, Nat.mul_left_comm Q a]
      have hscale : Q * (B * q * (R - 1)) ≤ B * (a * A) * (R - 1) := by
        have hh := Nat.mul_le_mul_right (B * (R - 1)) (Nat.mul_le_mul hqa hQA)
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
      calc
        _ ≤ a * (B * A) + B * (a * A) * (R - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left a ih) hscale
        _ = B * (a * A) + B * (a * A) * (R - 1) := by rw [Nat.mul_left_comm a B A]
        _ = B * (a * A) * R := by
          have hr : B * (a * A) * ((R - 1) + 1) =
              B * (a * A) * (R - 1) + B * (a * A) := by rw [Nat.mul_add, Nat.mul_one]
          rw [Nat.add_comm, ← hr, hR]
    simpa only [ExcursionBudget.oddCount, offset, time, Nat.pow_add, Q, A, B, q, a, R,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left q hmain

/-- The last halving run increases the denominator while leaving the
offset fixed, giving its full dyadic factor in the offset bound. -/
theorem offset_terminal_halvings_le (r : Run) (rs : List Run) :
    2 ^ ExcursionBudget.oddCount (r :: rs) *
        (2 ^ r.halvings * offset (r :: rs) + 2 ^ time (r :: rs)) ≤
      2 ^ time (r :: rs) * 3 ^ ExcursionBudget.oddCount (r :: rs) := by
  have h := Nat.mul_le_mul_left (2 ^ r.halvings)
    (offset_add_denominator_le (⟨r.oddSteps, 0⟩ :: rs))
  simpa only [ExcursionBudget.oddCount, offset, time, Nat.add_zero, Nat.pow_add,
    Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private theorem drop_of_scaled_gap {n e scale : Nat} {rs : List Run} (h : Trace n e rs)
    (hsize : 2 ^ time rs ≤ n)
    (hoffset : 2 ^ ExcursionBudget.oddCount rs * (scale * offset rs + 2 ^ time rs) ≤
      2 ^ time rs * 3 ^ ExcursionBudget.oddCount rs)
    (hgap : 3 ^ ExcursionBudget.oddCount rs ≤
      2 ^ ExcursionBudget.oddCount rs * (scale * (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs))) :
    e < n := by
  let A := 3 ^ ExcursionBudget.oddCount rs
  let B := 2 ^ time rs
  let Q := 2 ^ ExcursionBudget.oddCount rs
  let D := B - A
  have hQ : 0 < Q := Nat.two_pow_pos _
  have hB : 0 < B := Nat.two_pow_pos _
  have hA : 0 < A := Nat.pow_pos (by decide)
  have hD : 0 < D := by
    by_cases hz : D = 0
    · change A ≤ Q * (scale * D) at hgap
      rw [hz, Nat.mul_zero, Nat.mul_zero] at hgap
      omega
    · exact Nat.pos_of_ne_zero hz
  have hoffset' : scale * offset rs + B ≤ scale * (B * D) := by
    apply Nat.le_of_mul_le_mul_left _ hQ
    calc
      _ ≤ B * A := hoffset
      _ ≤ B * (Q * (scale * D)) := Nat.mul_le_mul_left B hgap
      _ = Q * (scale * (B * D)) := by ac_rfl
  have hlt : offset rs < n * D := by
    have hupper := Nat.mul_le_mul_right D hsize
    have hmul := Nat.mul_le_mul_left scale hupper
    change scale * (B * D) ≤ scale * (n * D) at hmul
    exact Nat.lt_of_mul_lt_mul_left (a := scale) (by omega)
  have hsum : A + D = B := Nat.add_sub_of_le (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hD))
  have hlanding : B * e < B * n := by
    calc
      _ = A * n + offset rs := h.affine.symm
      _ < A * n + n * D := Nat.add_lt_add_left hlt _
      _ = _ := by rw [Nat.mul_comm n D, ← Nat.add_mul, hsum]
  exact Nat.lt_of_mul_lt_mul_left hlanding

/-- A separation of at least the worst-case offset per denominator gives
descent for every realizing source at least the denominator. -/
theorem drop_of_gap_and_size {n e : Nat} {rs : List Run} (h : Trace n e rs)
    (hsize : 2 ^ time rs ≤ n)
    (hgap : 3 ^ ExcursionBudget.oddCount rs ≤
      2 ^ ExcursionBudget.oddCount rs * (2 ^ time rs - 3 ^ ExcursionBudget.oddCount rs)) :
    e < n :=
  drop_of_scaled_gap (scale := 1) h hsize
    (by simpa only [Nat.one_mul] using offset_add_denominator_le rs)
    (by simpa only [Nat.one_mul] using hgap)

/-- The terminal halvings allow a proportionally smaller separation. -/
theorem drop_of_terminal_gap_and_size {n e : Nat} {r : Run} {rs : List Run}
    (h : Trace n e (r :: rs)) (hsize : 2 ^ time (r :: rs) ≤ n)
    (hgap : 3 ^ ExcursionBudget.oddCount (r :: rs) ≤
      2 ^ ExcursionBudget.oddCount (r :: rs) *
        (2 ^ r.halvings * (2 ^ time (r :: rs) - 3 ^ ExcursionBudget.oddCount (r :: rs)))) :
    e < n :=
  drop_of_scaled_gap h hsize (offset_terminal_halvings_le r rs) hgap

/-- Non-descent at a translated source bounds its shift index using only
the profile coefficients and the terminal halving count. -/
theorem non_drop_shift_bound {n e k : Nat} {r : Run} {rs : List Run}
    (h : Trace (n + 2 ^ time (r :: rs) * (2 * k)) e (r :: rs))
    (hcoef : 3 ^ ExcursionBudget.oddCount (r :: rs) ≤ 2 ^ time (r :: rs))
    (hkeep : n + 2 ^ time (r :: rs) * (2 * k) ≤ e) :
    2 ^ ExcursionBudget.oddCount (r :: rs) *
      (2 ^ r.halvings * ((2 ^ time (r :: rs) - 3 ^ ExcursionBudget.oddCount (r :: rs)) *
        (2 * k)) + 1) ≤ 3 ^ ExcursionBudget.oddCount (r :: rs) := by
  let A := 3 ^ ExcursionBudget.oddCount (r :: rs)
  let B := 2 ^ time (r :: rs)
  let Q := 2 ^ ExcursionBudget.oddCount (r :: rs)
  let R := 2 ^ r.halvings
  let D := B - A
  let x := n + B * (2 * k)
  let C := offset (r :: rs)
  have hsum : A + D = B := Nat.add_sub_of_le hcoef
  have hCx : D * x ≤ C := by
    have hmul : A * x + D * x ≤ A * x + C := by
      rw [← Nat.add_mul, hsum, h.affine]
      exact Nat.mul_le_mul_left B hkeep
    exact Nat.le_of_add_le_add_left hmul
  have hClower : D * (B * (2 * k)) ≤ C :=
    Nat.le_trans (Nat.mul_le_mul_left D (Nat.le_add_left _ _)) hCx
  change Q * (R * (D * (2 * k)) + 1) ≤ A
  apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos (time (r :: rs)))
  calc
    B * (Q * (R * (D * (2 * k)) + 1)) =
        Q * (R * (D * (B * (2 * k))) + B) := by
      simp only [Nat.mul_add, Nat.mul_one]
      ac_rfl
    _ ≤ Q * (R * C + B) := Nat.mul_le_mul_left Q
      (Nat.add_le_add_right (Nat.mul_le_mul_left R hClower) B)
    _ ≤ B * A := offset_terminal_halvings_le r rs

/-- Shared exponents give enough separation by factoring the two powers. -/
theorem gap_of_shared_exponents {p q d : Nat} (hd : 2 ≤ d)
    (hc : 3 ^ (p * d) < 2 ^ (q * d)) :
    3 ^ (p * d) ≤ 2 ^ (p * d) * (2 ^ (q * d) - 3 ^ (p * d)) := by
  let a := 3 ^ p
  let b := 2 ^ q
  have hc' : a ^ d < b ^ d := by simpa only [a, b, Nat.pow_mul] using hc
  have hab : a < b := by
    apply Nat.lt_of_not_ge
    intro hba
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left hba d) hc'
  have hstep : a ^ d + a ^ (d - 1) ≤ b ^ d := by
    have hs : (d - 1).succ = d := by omega
    calc
      _ = (a + 1) * a ^ (d - 1) := by rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_succ', hs]
      _ ≤ b * b ^ (d - 1) := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.le_of_lt hab) _)
      _ = _ := by rw [← Nat.pow_succ', hs]
  have hgap : a ^ (d - 1) ≤ b ^ d - a ^ d := by omega
  have ha : a ≤ 2 ^ (p * d) := by
    calc
      _ ≤ 4 ^ p := Nat.pow_le_pow_left (by decide) _
      _ = 2 ^ (2 * p) := by rw [Nat.pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        rw [Nat.mul_comm 2 p]
        exact Nat.mul_le_mul_left p hd)
  rw [show (3 : Nat) ^ (p * d) = a ^ d from Nat.pow_mul ..,
    show (2 : Nat) ^ (q * d) = b ^ d from Nat.pow_mul ..]
  have hs : (d - 1).succ = d := by omega
  calc
    _ = a * a ^ (d - 1) := by rw [← Nat.pow_succ', hs]
    _ ≤ _ := Nat.mul_le_mul ha hgap

/-- A contracting profile whose exponents share a factor descends at
every source one or more full periods above its base. -/
theorem descent_after_period_of_shared_exponents {n e p q d : Nat} {rs : List Run}
    (h : Trace n e rs) (hd : 2 ≤ d)
    (hodd : ExcursionBudget.oddCount rs = p * d) (htime : time rs = q * d)
    (hcontract : 3 ^ ExcursionBudget.oddCount rs < 2 ^ time rs) (k : Nat) :
    Collatz.acceleratedOrbit (time rs) (n + 2 ^ time rs * (2 * (k + 1))) <
      n + 2 ^ time rs * (2 * (k + 1)) := by
  have ht := lift_trace h (k + 1)
  have hgap := gap_of_shared_exponents hd (by simpa only [hodd, htime] using hcontract)
  have hsize : 2 ^ time rs ≤ n + 2 ^ time rs * (2 * (k + 1)) :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_add_left _ _)
  rw [ht.landing]
  exact drop_of_gap_and_size ht hsize (by simpa only [hodd, htime] using hgap)

end Collatz.ExcursionRays
