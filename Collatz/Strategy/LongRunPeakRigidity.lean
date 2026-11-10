import Collatz.Strategy.PeakSuffixTable
import Collatz.Strategy.BoundedEvenDefect
import Collatz.Strategy.PeakContraction

/-!
# Rigidity of short meetings after long odd runs

At any fixed suffix depth, sufficiently long odd runs admit a smaller
equal-time mate exactly when two shifted peaks, with the same cofactor
and different powers of three, meet in that suffix.
-/

namespace Collatz.LongRunPeakRigidity

open Collatz.InverseFiberTransport Collatz.PeakSuffixTable
  Collatz.SynchronousClasses Collatz.BoundedEvenDefect Collatz.OrbitCapacity

private def offsetFor (k B w : Nat) : Nat × Int :=
  let d := oddCount w k - oddCount (B - 1) k
  (d, ((B / 3 ^ d : Nat) : Int) - (w : Int))

private def offsets (k : Nat) : List (Nat × Int) :=
  (List.range (2 ^ k)).flatMap (fun r =>
    let B := 3 ^ k * (r + 1)
    (fiber k (acceleratedOrbit k (B - 1))).map (offsetFor k B))

private theorem lower_peak_offset {k A x : Nat} (hlarge : 2 ^ k * 3 ^ k < A)
    (hdiv : 3 ^ k ∣ A) (hlt : x < A - 1)
    (hmeet : acceleratedOrbit k x = acceleratedOrbit k (A - 1)) :
    ∃ d c, (d, c) ∈ offsets k ∧ d ≤ k ∧
      (x : Int) + c = ((A / 3 ^ d : Nat) : Int) := by
  obtain ⟨r, q, w, hA, hw, hx⟩ := inverse_peak_transport
    (Nat.lt_of_le_of_lt (Nat.zero_le _) hlarge) hdiv hmeet
  let D := 2 ^ k
  let M := 3 ^ k
  let B := M * (r.val + 1)
  let a := oddCount (B - 1) k
  let b := oddCount w k
  let I := D * (3 ^ (k - b) * (3 ^ a * q))
  have hAx : A = D * (M * q) + B := hA
  have hx' : x = w + I := hx
  have hB : B ≤ D * M := by
    rw [Nat.mul_comm D M]
    exact Nat.mul_le_mul_left M (Nat.succ_le_of_lt r.isLt)
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro he
    rw [he, Nat.mul_zero, Nat.mul_zero, Nat.zero_add] at hAx
    exact Nat.not_le_of_gt hlarge (hAx ▸ hB)
  have hb : b ≤ k := AffineExact.oddCount_le_self w k
  have hab : a ≤ b := by
    apply Nat.le_of_not_gt
    intro hbad
    have hpow : 3 ^ (k + 1) ≤ 3 ^ (k - b) * 3 ^ a := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
    have hinc : D * (M * (3 * q)) ≤ I := by
      dsimp only [I, M]
      rw [← Nat.mul_assoc (3 ^ (k - b)) (3 ^ a) q,
        ← Nat.mul_assoc (3 ^ k) 3 q, ← Nat.pow_succ]
      exact Nat.mul_le_mul_left D (Nat.mul_le_mul_right q hpow)
    have hM : M * q + M ≤ M * (3 * q) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left M (by omega)
    have hbound : A ≤ D * (M * (3 * q)) := by
      rw [hAx]
      refine Nat.le_trans (Nat.add_le_add_left hB _) ?_
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left D hM
    omega
  let d := b - a
  let c : Int := ((B / 3 ^ d : Nat) : Int) - (w : Int)
  have hd : d ≤ k := by dsimp only [d]; omega
  have hmem : (d, c) ∈ offsets k := by
    apply List.mem_flatMap.mpr
    exact ⟨r.val, List.mem_range.mpr r.isLt, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  refine ⟨d, c, hmem, hd, ?_⟩
  have hexp : d + (k - b) + a = k := by dsimp only [d]; omega
  have hscale : 3 ^ d * I = D * (M * q) := by
    calc
      _ = D * ((3 ^ d * 3 ^ (k - b) * 3 ^ a) * q) := by dsimp only [I]; ac_rfl
      _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add, hexp]
  have hBdiv : 3 ^ d ∣ B := Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 hd) _
  have hA' : A = 3 ^ d * (I + B / 3 ^ d) := by
    rw [Nat.mul_add, hscale, Nat.mul_div_cancel' hBdiv, hAx]
  have hquot : A / 3 ^ d = I + B / 3 ^ d := by
    rw [hA', Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  rw [hx', hquot, Int.natCast_add, Int.natCast_add]
  dsimp only [c]
  omega

private theorem uniform_offset_precision (xs : List (Nat × Int)) :
    ∃ N, ∀ d c, (d, c) ∈ xs → c ≠ 1 → c.natAbs ≤ N ∧
      ∃ p ≤ N, ∀ x j, j - d ≤ oddCount x j → p ≤ oddCount x j →
        ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + c := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons dc xs ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨d, c⟩ := dc
    by_cases hc : c = 1
    · refine ⟨N, fun b z hz hn => ?_⟩
      rcases List.mem_cons.mp hz with he | hmem
      · exact (hn ((congrArg Prod.snd he).trans hc)).elim
      · exact hN b z hmem hn
    · obtain ⟨p, hp⟩ := excludes_displacement d c hc
      let bound := max N (max c.natAbs p)
      have hprev : N ≤ bound := Nat.le_max_left _ _
      have hcur : max c.natAbs p ≤ bound := Nat.le_max_right _ _
      refine ⟨bound, fun b z hz hn => ?_⟩
      rcases List.mem_cons.mp hz with he | hmem
      · cases he
        exact ⟨Nat.le_trans (Nat.le_max_left _ _) hcur, p,
          Nat.le_trans (Nat.le_max_right _ _) hcur, hp⟩
      · obtain ⟨habs, q, hq, htest⟩ := hN b z hmem hn
        exact ⟨Nat.le_trans habs hprev, q, Nat.le_trans hq hprev, htest⟩

private theorem odd_count_near_peak {v d x u : Nat} {c : Int} (hu : 0 < u)
    (hx : x < 2 ^ v * u) (hd : d < v) (hc : c.natAbs ≤ 3 ^ (v - d - 1))
    (hy : (acceleratedOrbit v x : Int) + c = ((3 ^ (v - d) * u : Nat) : Int)) :
    v - d ≤ oddCount x v := by
  apply Nat.le_of_not_gt
  intro hshort
  let B := u * 3 ^ (v - d - 1)
  have himage := image_lt (k := v) (c := u) (x := x) (by simpa only [Nat.mul_comm] using hx)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 3)
    (show oddCount x v ≤ v - d - 1 by omega)
  have hlt : acceleratedOrbit v x < B :=
    Nat.lt_of_lt_of_le himage (Nat.mul_le_mul_left u hpow)
  have hmax : c.natAbs ≤ B := Nat.le_trans hc (Nat.le_mul_of_pos_left _ hu)
  have htriple : 3 ^ (v - d) * u = 3 * B := by
    rw [show v - d = (v - d - 1) + 1 by omega, Nat.pow_succ']
    dsimp only [B]
    ac_rfl
  rw [htriple, Int.natCast_mul, show ((3 : Nat) : Int) = 3 by rfl] at hy
  omega

/-- Every smaller equal-time partner of a sufficiently long odd run
has an exact scaled peak at the end of the prefix. -/
theorem scaled_peak_of_smaller_mate (k : Nat) :
    ∃ V, ∀ {v n m u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      m < n → acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n →
        ∃ d, 0 < d ∧ d ≤ k ∧ acceleratedOrbit v m = 3 ^ (v - d) * u - 1 := by
  obtain ⟨N, hN⟩ := uniform_offset_precision (offsets k)
  let L := 2 ^ k * 3 ^ k
  let V := 2 * k + N + 2
  refine ⟨V, ?_⟩
  intro v n m u hv hu hfac hsmall hfinal
  let A := 3 ^ v * u
  have hpeak : acceleratedOrbit v n + 1 = A := DeviceSwap.run_climb v u n hu hfac
  have hV : 2 * k + N + 2 ≤ v := hv
  let y := acceleratedOrbit v m
  change ∃ d, 0 < d ∧ d ≤ k ∧ y = 3 ^ (v - d) * u - 1
  have hm : m < 2 ^ v * u := by omega
  have hy : y < A - 1 := prefix_image_lt hu hfac hsmall
  have hmeet : acceleratedOrbit k y = acceleratedOrbit k (A - 1) := by
    have hpn : A - 1 = acceleratedOrbit v n := by omega
    change acceleratedOrbit k (acceleratedOrbit v m) = _
    rw [hpn, acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k]
    exact hfinal
  have hlarge : L < A := by
    have hL : L ≤ 3 ^ (2 * k) := by
      calc
        L = (2 * 3) ^ k := by rw [Nat.mul_pow]
        _ ≤ (3 * 3) ^ k := Nat.pow_le_pow_left (by decide) _
        _ = _ := by rw [show 3 * 3 = (3 : Nat) ^ 2 by decide, ← Nat.pow_mul]
    have hpow := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mpr
      (show 2 * k < v by omega)
    exact Nat.lt_of_le_of_lt hL (Nat.lt_of_lt_of_le hpow (Nat.le_mul_of_pos_right _ hu))
  have hdiv : 3 ^ k ∣ A := Nat.dvd_mul_right_of_dvd
    (Nat.pow_dvd_pow 3 (by omega : k ≤ v)) _
  obtain ⟨d, c, hdc, hd, hval⟩ := lower_peak_offset hlarge hdiv hy hmeet
  have hAquot : A / 3 ^ d = 3 ^ (v - d) * u := by
    have hs : 3 ^ v = 3 ^ d * 3 ^ (v - d) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega : d ≤ v)]
    dsimp only [A]
    rw [hs, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]
  rw [hAquot] at hval
  have hc : c = 1 := by
    by_cases hc : c = 1
    · exact hc
    exfalso
    obtain ⟨habs, p, hp, htest⟩ := hN d c hdc hc
    have hsize : c.natAbs ≤ 3 ^ (v - d - 1) :=
      Nat.le_trans habs (Nat.le_trans (by omega)
        (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 3))))
    have hcount := odd_count_near_peak hu hm (by omega) hsize hval
    have hpow : 3 ^ p ∣ 3 ^ (v - d) * u :=
      Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega)) _
    have hdvd : (3 : Int) ^ p ∣ (y : Int) + c := by
      rw [hval]
      simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
        (Int.ofNat_dvd.mpr hpow)
    exact htest m v hcount (by omega) hdvd
  have hresult : y = 3 ^ (v - d) * u - 1 := by omega
  have hpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.sub_zero] at hresult
    exact Nat.not_le_of_gt hy (by omega)
  exact ⟨d, hpos, hd, hresult⟩

/-- A smaller equal-time partner exists exactly when the original peak
meets a scaled peak in the prescribed suffix. A scaled peak meeting
constructs a smaller partner by adding leading halvings to the shorter run. -/
theorem smaller_iff_scaled_peak (k : Nat) :
    ∃ V, ∀ {v n u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      (leastAt (v + k) n < n ↔
        ∃ d, 0 < d ∧ d ≤ k ∧
          acceleratedOrbit k (3 ^ (v - d) * u - 1) =
            acceleratedOrbit k (3 ^ v * u - 1)) := by
  obtain ⟨V, hV⟩ := scaled_peak_of_smaller_mate k
  refine ⟨max V k, ?_⟩
  intro v n u hv hu hfac
  have hVk := Nat.le_trans (Nat.le_max_left V k) hv
  have hk := Nat.le_trans (Nat.le_max_right V k) hv
  constructor
  · intro hsmall
    obtain ⟨d, hpos, hd, hpeak⟩ := hV hVk hu hfac hsmall (leastAt_meets (v + k) n)
    have hrun := DeviceSwap.run_climb v u n hu hfac
    have htrue : 3 ^ v * u - 1 = acceleratedOrbit v n := by omega
    refine ⟨d, hpos, hd, ?_⟩
    rw [← hpeak, htrue, acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k]
    exact leastAt_meets (v + k) n
  · rintro ⟨d, hpos, hd, hmeet⟩
    have hsplit : v - d + d = v := Nat.sub_add_cancel (by omega)
    have hm : acceleratedOrbit k (3 ^ (v - d + d) * u - 1) =
        acceleratedOrbit k (3 ^ (v - d) * u - 1) := by rw [hsplit]; exact hmeet.symm
    have hlt := PeakContraction.leastAt_lt_of_peak_meet hu hpos hm
    have hn : 2 ^ v * u - 1 = n := by omega
    rw [hsplit, hn, Nat.add_comm k] at hlt
    exact hlt

end Collatz.LongRunPeakRigidity
