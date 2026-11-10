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

private theorem lower_peak_offset {k A x : Nat} (hlarge : 2 ^ k * 3 ^ k < A)
    (hdiv : 3 ^ k ∣ A) (hlt : x < A - 1)
    (hmeet : acceleratedOrbit k x = acceleratedOrbit k (A - 1)) :
    ∃ (d : Nat) (c : Int), d ≤ k ∧ 3 ^ d * c.natAbs ≤ 6 ^ k ∧
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
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hBpos : 0 < B := Nat.mul_pos hM (Nat.succ_pos _)
  have htarget : acceleratedOrbit k (B - 1) < M * 3 ^ a := by
    have hstart : B - 1 < M * D := by rw [Nat.mul_comm M D]; omega
    exact image_lt (k := k) (c := M) (x := B - 1) hstart
  have hwsize : 3 ^ d * w ≤ D * M := by
    have haff := AffineExact.affine_exact w k
    rw [mem_fiber.mp hw] at haff
    change D * acceleratedOrbit k (B - 1) = 3 ^ b * w + _ at haff
    have hb_eq : b = a + d := by dsimp only [d]; omega
    rw [hb_eq, Nat.pow_add, Nat.mul_assoc] at haff
    apply Nat.le_of_mul_le_mul_left _ (Nat.pow_pos (by decide : 0 < 3) (n := a))
    calc
      _ ≤ D * acceleratedOrbit k (B - 1) := by omega
      _ ≤ D * (M * 3 ^ a) := Nat.mul_le_mul_left _ (Nat.le_of_lt htarget)
      _ = _ := by ac_rfl
  have hc : 3 ^ d * c.natAbs ≤ 6 ^ k := by
    rw [show 6 ^ k = D * M by exact Nat.mul_pow 2 3 k]
    by_cases hw' : w ≤ B / 3 ^ d
    · have hnon : 0 ≤ c := by dsimp only [c]; omega
      have hcast := Int.natAbs_of_nonneg hnon
      change (c.natAbs : Int) = ((B / 3 ^ d : Nat) : Int) - (w : Int) at hcast
      have hc' : c.natAbs ≤ B / 3 ^ d := by omega
      exact Nat.le_trans (Nat.mul_le_mul_left _ hc') (Nat.le_trans (Nat.mul_div_le _ _) hB)
    · have hnon : c ≤ 0 := by dsimp only [c]; omega
      have hcast := Int.ofNat_natAbs_of_nonpos hnon
      change (c.natAbs : Int) = -(((B / 3 ^ d : Nat) : Int) - (w : Int)) at hcast
      have hnonquot : (0 : Int) ≤ ((B / 3 ^ d : Nat) : Int) := Int.natCast_nonneg _
      have hc' : c.natAbs ≤ w := by omega
      exact Nat.le_trans (Nat.mul_le_mul_left _ hc') hwsize
  refine ⟨d, c, hd, hc, ?_⟩
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

private theorem rigidity_precision (k C : Nat) (hC : C ≤ 2 * 6 ^ k) :
    2 ^ (5 * k + 2) * C < 3 ^ (5 * k + 2) := by
  calc
    _ ≤ 2 ^ (5 * k + 2) * (2 * 6 ^ k) := Nat.mul_le_mul_left _ hC
    _ = 8 * 192 ^ k := by
      rw [Nat.pow_add, Nat.pow_mul]
      calc
        _ = 8 * (((2 : Nat) ^ 5) ^ k * 6 ^ k) := by
          change (32 ^ k * 4) * (2 * 6 ^ k) = 8 * (32 ^ k * 6 ^ k)
          rw [show (8 : Nat) = 4 * 2 by decide]
          ac_rfl
        _ = _ := by rw [← Nat.mul_pow]
    _ < 9 * 243 ^ k := Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (by decide : 8 < 9) (Nat.pow_pos (by decide)))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
    _ = _ := by rw [Nat.pow_add, Nat.pow_mul]; exact Nat.mul_comm _ _

def rigidityCutoff (k : Nat) : Nat := 6 * k + 2

/-- Every smaller equal-time partner above the explicit linear
cutoff has an exact scaled peak at the end of the prefix. -/
theorem scaled_peak_at_cutoff {k v n m u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) (hsmall : m < n)
    (hfinal : acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n) :
    ∃ d, 0 < d ∧ d ≤ k ∧ acceleratedOrbit v m = 3 ^ (v - d) * u - 1 := by
  let L := 2 ^ k * 3 ^ k
  let A := 3 ^ v * u
  have hpeak : acceleratedOrbit v n + 1 = A := DeviceSwap.run_climb v u n hu hfac
  have hV : 6 * k + 2 ≤ v := hv
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
  obtain ⟨d, c, hd, hscale, hval⟩ := lower_peak_offset hlarge hdiv hy hmeet
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
    let p := 5 * k + 2
    have hp : p ≤ v - d := by dsimp only [p]; omega
    have hpowd : 3 ^ d ≤ 6 ^ k := Nat.le_trans
      (Nat.pow_le_pow_right (by decide) hd) (Nat.pow_le_pow_left (by decide) _)
    have hsizeC : 3 ^ d * (1 - c).natAbs ≤ 2 * 6 ^ k := by
      have ha : (1 - c).natAbs ≤ 1 + c.natAbs := Int.natAbs_sub_le 1 c
      refine Nat.le_trans (Nat.mul_le_mul_left _ ha) ?_
      rw [Nat.mul_add, Nat.mul_one, Nat.two_mul]
      exact Nat.add_le_add hpowd hscale
    have hbudget := rigidity_precision k _ hsizeC
    have habs : c.natAbs ≤ 6 ^ k :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))) hscale
    have hsize : c.natAbs ≤ 3 ^ (v - d - 1) :=
      Nat.le_trans habs (by
        calc
          _ ≤ (3 ^ 2) ^ k := Nat.pow_le_pow_left (by decide) _
          _ ≤ _ := by rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
    have hcount := odd_count_near_peak hu hm (by omega) hsize hval
    have hpow : 3 ^ p ∣ 3 ^ (v - d) * u :=
      Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega)) _
    have hdvd : (3 : Int) ^ p ∣ (y : Int) + c := by
      rw [hval]
      simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
        (Int.ofNat_dvd.mpr hpow)
    exact excludes_displacement_with_budget d p c hc hbudget
      m v hcount (Nat.le_trans hp hcount) hdvd
  have hresult : y = 3 ^ (v - d) * u - 1 := by omega
  have hpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.sub_zero] at hresult
    exact Nat.not_le_of_gt hy (by omega)
  exact ⟨d, hpos, hd, hresult⟩

/-- Every smaller equal-time partner of a sufficiently long odd run
has an exact scaled peak at the end of the prefix. -/
theorem scaled_peak_of_smaller_mate (k : Nat) :
    ∃ V, ∀ {v n m u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      m < n → acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n →
        ∃ d, 0 < d ∧ d ≤ k ∧ acceleratedOrbit v m = 3 ^ (v - d) * u - 1 :=
  ⟨rigidityCutoff k, scaled_peak_at_cutoff⟩

/-- Above the linear cutoff, a smaller equal-time partner exists
exactly when the original peak meets a scaled peak in the suffix. -/
theorem smaller_iff_scaled_peak_at_cutoff {k v n u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔
      ∃ d, 0 < d ∧ d ≤ k ∧
        acceleratedOrbit k (3 ^ (v - d) * u - 1) =
          acceleratedOrbit k (3 ^ v * u - 1) := by
  have hbase : 6 * k + 2 ≤ v := hv
  constructor
  · intro hsmall
    obtain ⟨d, hpos, hd, hpeak⟩ := scaled_peak_at_cutoff hv hu hfac hsmall (leastAt_meets (v + k) n)
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

/-- A fixed suffix length has a uniform threshold for the scaled-peak
characterization. -/
theorem smaller_iff_scaled_peak (k : Nat) :
    ∃ V, ∀ {v n u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      (leastAt (v + k) n < n ↔
        ∃ d, 0 < d ∧ d ≤ k ∧
          acceleratedOrbit k (3 ^ (v - d) * u - 1) =
            acceleratedOrbit k (3 ^ v * u - 1)) :=
  ⟨rigidityCutoff k, smaller_iff_scaled_peak_at_cutoff⟩

private theorem peak_certificate_iff {k v d u : Nat} (hv : rigidityCutoff k ≤ v)
    (hpos : 0 < d) (hd : d ≤ k) (hu : u % 2 = 1) :
    acceleratedOrbit k (3 ^ (v - d) * u - 1) = acceleratedOrbit k (3 ^ v * u - 1) ↔
      PeakContraction.Certificate k d ((3 ^ (v - d) * u) % 2 ^ k) := by
  let B := 3 ^ (v - d) * u
  have hV : 6 * k + 2 ≤ v := hv
  have hsize : 2 ^ k ≤ B := by
    calc
      _ ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) _
      _ ≤ 3 ^ (v - d) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hres : 0 < B % 2 ^ k := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hmod := congrArg (· % 2) hz
    have hdiv : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
    rw [Nat.mod_mod_of_dvd _ hdiv] at hmod
    dsimp only [B] at hmod
    rw [Nat.mul_mod, Arith.three_pow_odd, hu] at hmod
    contradiction
  have hscale : 3 ^ d * B = 3 ^ v * u := by
    dsimp only [B]
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' (by omega : d ≤ v)]
  change acceleratedOrbit k (B - 1) = acceleratedOrbit k (3 ^ v * u - 1) ↔ _
  rw [← hscale]
  exact ⟨fun h => PeakContraction.certificate_of_large_meeting hsize hres h.symm,
    fun h => (PeakContraction.meet_of_certificate hres rfl h).symm⟩

/-- Binary modular exponentiation avoids constructing the full shifted
peak just to test its dyadic residue. -/
def threePowMod (m e : Nat) : Nat :=
  if h : e = 0 then 1 % m else
    let r := threePowMod m (e / 2)
    (r * r * 3 ^ (e % 2)) % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem threePowMod_eq (m e : Nat) : threePowMod m e = 3 ^ e % m := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    by_cases he : e = 0
    · subst e
      rw [threePowMod, dif_pos rfl, Nat.pow_zero]
    · rw [threePowMod, dif_neg he, ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))]
      let A := 3 ^ (e / 2)
      have hp : 3 ^ e = A * A * 3 ^ (e % 2) := by
        conv => lhs; rw [show e = e / 2 + e / 2 + e % 2 by omega, Nat.pow_add, Nat.pow_add]
      rw [hp]
      have hs : ((A % m) * (A % m)) % m = (A * A) % m := by
        rw [Nat.mod_mul_mod, Nat.mul_mod_mod]
      calc
        _ = ((((A % m) * (A % m)) % m) * 3 ^ (e % 2)) % m :=
          (Nat.mod_mul_mod _ _ _).symm
        _ = (((A * A) % m) * 3 ^ (e % 2)) % m := by rw [hs]
        _ = _ := Nat.mod_mul_mod _ _ _

/-- Test the k candidate drops by suffix calculations at bounded
dyadic residues. -/
def shorterPeakCheck (k v u : Nat) : Bool :=
  (List.range k).any (fun i =>
    let d := i + 1
    let M := 2 ^ k
    decide (PeakContraction.Certificate k d ((threePowMod M (v - d) * (u % M)) % M)))

/-- When v is at least 6k+2, the finite parity test decides whether
there is a smaller equal-time partner at horizon v+k. -/
theorem smaller_iff_shorterPeakCheck {k v n u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔ shorterPeakCheck k v u = true := by
  rw [smaller_iff_scaled_peak_at_cutoff hv (by omega) hfac, shorterPeakCheck, List.any_eq_true]
  constructor
  · rintro ⟨d, hpos, hd, hmeet⟩
    refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
    apply decide_eq_true
    rw [show d - 1 + 1 = d by omega, threePowMod_eq, Nat.mod_mul_mod, Nat.mul_mod_mod]
    exact (peak_certificate_iff hv hpos hd hu).mp hmeet
  · rintro ⟨i, hi, hcheck⟩
    have hd : i + 1 ≤ k := Nat.succ_le_of_lt (List.mem_range.mp hi)
    have hc := of_decide_eq_true hcheck
    rw [threePowMod_eq, Nat.mod_mul_mod, Nat.mul_mod_mod] at hc
    exact ⟨i + 1, Nat.succ_pos _, hd, (peak_certificate_iff hv (Nat.succ_pos _) hd hu).mpr hc⟩

end Collatz.LongRunPeakRigidity
