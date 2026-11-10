import Collatz.Strategy.OrbitWindowBootstrap

/-!
# Near-critical visits from a future minimum

An orbit whose future stays above its current source has a small
multiplicative correction. The times with multiplier at most one
therefore land in a short translated window above that source.
-/

namespace Collatz.OrbitNearReturn

open Collatz.ExcursionSparseProduct Collatz.OrbitCapacity
open Collatz.OrbitOccupationBootstrap Collatz.OrbitWindowBootstrap

private theorem mass_capacity :
    ∃ A, ∀ {n : Nat}, NoMerging (fun i => acceleratedOrbit i n) →
      ∀ j (xs : List Nat), xs.Nodup →
        (∀ x ∈ xs, x < cutoff 20 j ∧ ∃ i, acceleratedOrbit i n = x) →
        xs.length ≤ A * 2 ^ (19 * j) := by
  obtain ⟨C, hC⟩ := orbit_count_power
  let A := C * 2 ^ 19 + 1
  refine ⟨A, ?_⟩
  intro n hmerge j xs hnd hx
  have hc := hC (Nat.mul_pos (Nat.two_pow_pos (20 * j)) (by decide)) hmerge xs hnd hx
  have hA : C * 2 ^ 19 ≤ A ^ 20 :=
    Nat.le_trans (Nat.le_succ _) (Nat.le_pow (by decide : 0 < 20))
  apply (Nat.pow_le_pow_iff_left (by decide : (20 : Nat) ≠ 0)).mp
  calc
    _ ≤ C * cutoff 20 j ^ 19 := hc
    _ = (C * 2 ^ 19) * (2 ^ (19 * j)) ^ 20 := by
      rw [cutoff, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        show 20 * j * 19 = 19 * j * 20 by omega]
      ac_rfl
    _ ≤ A ^ 20 * (2 ^ (19 * j)) ^ 20 := Nat.mul_le_mul_right _ hA
    _ = _ := (Nat.mul_pow ..).symm

/-- The correction error has the dyadic rate corresponding to
an inverse twentieth power of the size cutoff. -/
theorem tail_envelope :
    ∃ B, ∀ {n k q : Nat}, 0 < n → NoMerging (fun i => acceleratedOrbit i n) →
      (∀ i j, i < k → j < k → acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      (∀ i, i < k → cutoff 20 (B + q) ≤ acceleratedOrbit i n) →
      (2 ^ (q + 1) - 1) * (2 ^ k * acceleratedOrbit k n) ≤
        2 ^ (q + 1) * (n * 3 ^ oddCount n k) := by
  obtain ⟨A, hcap⟩ := mass_capacity
  let J := A.log2 + 1
  refine ⟨20 + J, ?_⟩
  intro n k q hn hmerge hinj hlo
  let xs := orbitPrefix n k
  have hnd := orbitPrefix_nodup hinj
  have hlow : ∀ x ∈ xs, cutoff 20 (20 + J + q) ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := orbitPrefix_member hx
    exact hlo i hi
  have hcounts (j : Nat) :
      (xs.filter (fun x => decide (x < cutoff 20 j))).length ≤ A * 2 ^ (19 * j) := by
    apply hcap hmerge j _ (List.filter_sublist.nodup hnd)
    intro x hx
    obtain ⟨hx, hlt⟩ := List.mem_filter.mp hx
    obtain ⟨i, _, hi⟩ := orbitPrefix_member hx
    exact ⟨of_decide_eq_true hlt, i, hi⟩
  exact scaled_envelope hn (reciprocal_tail_from_count (P := 20) (j := J)
    (by decide) (Nat.le_of_lt Nat.lt_log2_self) hlow hcounts)

/-- A nonexpanding multiplier from a future minimum forces the
endpoint into a narrow interval above that minimum. -/
theorem near_critical_window :
    ∃ B, ∀ {n q : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      (∀ i, n ≤ acceleratedOrbit i n) → cutoff 20 (B + q) ≤ n →
      ∀ k, 3 ^ oddCount n k ≤ 2 ^ k →
        n ≤ acceleratedOrbit k n ∧
          acceleratedOrbit k n < n + (n / (2 ^ (q + 1) - 1) + 1) := by
  obtain ⟨B, hB⟩ := tail_envelope
  refine ⟨B, ?_⟩
  intro n q hn hinj hmin hcut k hmul
  let K := 2 ^ (q + 1)
  let d := K - 1
  let x := acceleratedOrbit k n
  have hd : 0 < d := by
    dsimp [d, K]
    rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos q
    omega
  have hk := hB (k := k) hn (no_merging_of_injective hinj) (fun i j _ _ => hinj i j)
    (fun i _ => Nat.le_trans hcut (hmin i))
  have hdx : d * x ≤ K * n := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos k)
    calc
      _ = d * (2 ^ k * x) := Nat.mul_left_comm ..
      _ ≤ K * (n * 3 ^ oddCount n k) := hk
      _ ≤ K * (n * 2 ^ k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmul)
      _ = _ := by ac_rfl
  have hdiff : (x - n) * d ≤ n := by
    rw [Nat.sub_mul, Nat.mul_comm x, Nat.mul_comm n, Nat.sub_le_iff_le_add]
    have he : K = d + 1 := by dsimp [d]; omega
    simpa only [he, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hdx
  have hsmall := (Nat.le_div_iff_mul_le hd).mpr hdiff
  have hxmin : n ≤ x := hmin k
  exact ⟨hxmin, by change x < n + (n / d + 1); omega⟩

/-- Distinct nonexpanding multiplier times occupy the same narrow
value interval, even when they are scattered along the orbit. -/
theorem near_critical_count :
    ∃ B C, ∀ {n q : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      (∀ i, n ≤ acceleratedOrbit i n) → cutoff 20 (B + q) ≤ n →
      ∀ times : List Nat, times.Nodup → (∀ k ∈ times, 3 ^ oddCount n k ≤ 2 ^ k) →
        times.length ^ 20 ≤ C * (n / (2 ^ (q + 1) - 1) + 1) ^ 19 := by
  obtain ⟨B, hB⟩ := near_critical_window
  obtain ⟨C, hC⟩ := orbit_window_power
  refine ⟨B, C, ?_⟩
  intro n q hn hinj hmin hcut times hnd htimes
  let xs := times.map (fun i => acceleratedOrbit i n)
  have hxs : xs.Nodup := List.pairwise_map.mpr
    (hnd.imp (fun hne heq => hne (hinj _ _ heq)))
  have hc := hC (Nat.succ_pos (n / (2 ^ (q + 1) - 1))) (no_merging_of_injective hinj)
    xs hxs (a := n) (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hlo, hhi⟩ := hB hn hinj hmin hcut i (htimes i hi)
      exact ⟨hlo, hhi, i, rfl⟩)
  simpa only [xs, List.length_map] using hc

private theorem cutoff_choice {B n : Nat} (hn : 0 < n) (hcut : cutoff 20 B ≤ n) :
    ∃ q, cutoff 20 (B + q) ≤ n ∧ 2 ^ q ≤ n ∧
      n ≤ 2 ^ (20 * B + 21) * (2 ^ q) ^ 20 := by
  have hb : 20 * B + 1 ≤ n.log2 := by
    apply (Nat.le_log2 (Nat.ne_of_gt hn)).2
    simpa only [cutoff, Nat.pow_succ] using hcut
  let m := (n.log2 - 1) / 20
  have hm : B ≤ m := (Nat.le_div_iff_mul_le (by decide : 0 < 20)).2 (by omega)
  let q := m - B
  have hsum : B + q = m := Nat.add_sub_of_le hm
  have hlow : 20 * m + 1 ≤ n.log2 := by
    have hle := Nat.div_mul_le_self (n.log2 - 1) 20
    dsimp [m]
    omega
  have hhigh : n.log2 + 1 ≤ 20 * m + 21 := by
    have he := Nat.mod_add_div (n.log2 - 1) 20
    have hrem := Nat.mod_lt (n.log2 - 1) (by decide : 0 < 20)
    dsimp [m]
    omega
  have hpow : 2 ^ n.log2 ≤ n := Nat.log2_self_le (Nat.ne_of_gt hn)
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [cutoff, ← Nat.pow_succ, hsum]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hlow) hpow
  · exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : q ≤ n.log2)) hpow
  · have he : 20 * B + 21 + q * 20 = 20 * m + 21 := by omega
    rw [← Nat.pow_mul, ← Nat.pow_add, he]
    exact Nat.le_trans (Nat.le_of_lt Nat.lt_log2_self) (Nat.pow_le_pow_right (by decide) hhigh)

/-- Convert the band-dependent window width into a power bound. -/
theorem width_power {n q S : Nat} (hn : 0 < n) (hq : 2 ^ q ≤ n)
    (hscale : n ≤ S * (2 ^ q) ^ 20) :
    (n / (2 ^ (q + 1) - 1) + 1) ^ 20 ≤ (S * 2 ^ 20) * n ^ 19 := by
  let z := 2 ^ q
  let d := 2 ^ (q + 1) - 1
  let w := n / d + 1
  have hzd : z ≤ d := by
    dsimp [z, d]
    rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos q
    omega
  have hprod : z * w ≤ 2 * n := by
    change z * (n / d + 1) ≤ 2 * n
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm z (n / d), Nat.two_mul]
    exact Nat.add_le_add (Nat.le_trans (Nat.mul_le_mul_left _ hzd)
      (Nat.div_mul_le_self _ _)) hq
  apply Nat.le_of_mul_le_mul_left _ hn
  calc
    n * w ^ 20 ≤ (S * z ^ 20) * w ^ 20 := Nat.mul_le_mul_right _ hscale
    _ = S * (z * w) ^ 20 := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ S * (2 * n) ^ 20 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod 20)
    _ = n * ((S * 2 ^ 20) * n ^ 19) := by
      rw [Nat.mul_pow, show n ^ 20 = n ^ 19 * n from Nat.pow_succ n 19]
      ac_rfl

set_option exponentiation.threshold 500 in
/-- At a sufficiently large future minimum, the number of times
with multiplier at most one is bounded by a constant times the
`361/400` power of that minimum. -/
theorem near_critical_power :
    ∃ B E, ∀ {n : Nat}, 0 < n →
      (∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) →
      (∀ i, n ≤ acceleratedOrbit i n) → cutoff 20 B ≤ n →
      ∀ times : List Nat, times.Nodup → (∀ k ∈ times, 3 ^ oddCount n k ≤ 2 ^ k) →
        times.length ^ 400 ≤ E * n ^ 361 := by
  obtain ⟨B, C, hcount⟩ := near_critical_count
  let S := 2 ^ (20 * B + 21)
  refine ⟨B, C ^ 20 * (S * 2 ^ 20) ^ 19, ?_⟩
  intro n hn hinj hmin hcut times hnd htimes
  obtain ⟨q, hlo, hz, hscale⟩ := cutoff_choice hn hcut
  let w := n / (2 ^ (q + 1) - 1) + 1
  have hwidth : w ^ 20 ≤ (S * 2 ^ 20) * n ^ 19 := width_power hn hz hscale
  have hc : times.length ^ 20 ≤ C * w ^ 19 := hcount hn hinj hmin hlo times hnd htimes
  calc
    _ = (times.length ^ 20) ^ 20 := Nat.pow_mul ..
    _ ≤ (C * w ^ 19) ^ 20 := Nat.pow_le_pow_left hc 20
    _ = C ^ 20 * (w ^ 20) ^ 19 := by rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    _ ≤ C ^ 20 * ((S * 2 ^ 20) * n ^ 19) ^ 19 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 19)
    _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

/-- On an injective orbit, every tail has a future minimum, and
these minima exceed any prescribed bound sufficiently late. -/
theorem arbitrarily_late_minima {n : Nat}
    (hinj : ∀ i j, acceleratedOrbit i n = acceleratedOrbit j n → i = j) (A H : Nat) :
    ∃ k, H ≤ k ∧ A < acceleratedOrbit k n ∧
      ∀ t, acceleratedOrbit k n ≤ acceleratedOrbit (k + t) n := by
  obtain ⟨J, hJ⟩ := injective_eventually_above (fun i => acceleratedOrbit i n) hinj A
  let L := max H J
  have hex : ∃ x, ∃ k, L ≤ k ∧ acceleratedOrbit k n = x := ⟨_, L, Nat.le_refl _, rfl⟩
  obtain ⟨m, ⟨k, hk, heq⟩, hmin⟩ := Collatz.Minimum.exists_min hex
  refine ⟨k, Nat.le_trans (Nat.le_max_left ..) hk, hJ k (Nat.le_trans (Nat.le_max_right ..) hk), ?_⟩
  intro t
  rw [heq]
  apply Nat.le_of_not_gt
  intro ht
  exact hmin _ ht ⟨k + t, Nat.le_trans hk (Nat.le_add_right _ _), rfl⟩

end Collatz.OrbitNearReturn
