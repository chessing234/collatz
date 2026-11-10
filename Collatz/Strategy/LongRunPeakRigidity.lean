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

private theorem lower_peak_offset {k A x : Nat} (hlarge : 2 ^ k ≤ A - 1)
    (hlt : x < A - 1) (hmeet : acceleratedOrbit k x = acceleratedOrbit k (A - 1)) :
    ∃ (d : Nat) (c : Int), d ≤ k - oddCount (A - 1) k ∧ c.natAbs ≤ 2 ^ k ∧
      (x : Int) + c = ((A / 3 ^ d : Nat) : Int) := by
  let D := 2 ^ k
  let Q := (A - 1) / D
  let R := (A - 1) % D
  let P := x / D
  let S := x % D
  let a := oddCount (A - 1) k
  let b := oddCount x k
  have hD : 0 < D := Nat.two_pow_pos _
  have hR : R < D := Nat.mod_lt _ hD
  have hS : S < D := Nat.mod_lt _ hD
  have hA : D * Q + R = A - 1 := Nat.div_add_mod _ _
  have hx : D * P + S = x := Nat.div_add_mod _ _
  have ha : oddCount R k = a := (Density.oddCount_mod (A - 1) k).symm
  have hb : oddCount S k = b := (Density.oddCount_mod x k).symm
  have hab : a ≤ b := by
    rcases (SynchronousDynamics.smaller_mate_iff hlarge hmeet.symm).mp hlt with h | ⟨h, _⟩
    · exact Nat.le_of_lt h
    · exact Nat.le_of_eq h
  let d := b - a
  have hbd : b = a + d := (Nat.add_sub_of_le hab).symm
  have hcap := AffineExact.oddCount_le_self x k
  have hd : d ≤ k - a := by dsimp [d]; omega
  have hcapR : acceleratedOrbit k R < 3 ^ a := by
    rw [← ha]
    exact by simpa only [Nat.one_mul] using
      (image_lt (k := k) (c := 1) (x := R) (by simpa only [Nat.one_mul] using hR))
  have hcapS : acceleratedOrbit k S < 3 ^ b := by
    rw [← hb]
    exact by simpa only [Nat.one_mul] using
      (image_lt (k := k) (c := 1) (x := S) (by simpa only [Nat.one_mul] using hS))
  have himA := Congruence.accOrbit_pow_two_mul_add k Q R
  have himx := Congruence.accOrbit_pow_two_mul_add k P S
  change acceleratedOrbit k (D * Q + R) = _ at himA
  change acceleratedOrbit k (D * P + S) = _ at himx
  rw [hA, ha] at himA
  rw [hx, hb] at himx
  have hAffine : 3 ^ b * P + acceleratedOrbit k S = 3 ^ a * Q + acceleratedOrbit k R :=
    himx.symm.trans (hmeet.trans himA)
  let U := 3 ^ a
  let t := acceleratedOrbit k S / U
  have hU : 0 < U := Nat.pow_pos (by decide)
  have ht : t < 3 ^ d := by
    apply (Nat.div_lt_iff_lt_mul hU).mpr
    rw [Nat.mul_comm]
    change acceleratedOrbit k S < 3 ^ a * 3 ^ d
    rw [← Nat.pow_add, ← hbd]
    exact hcapS
  have hquot : Q = 3 ^ d * P + t := by
    have hl : (3 ^ b * P + acceleratedOrbit k S) / U = 3 ^ d * P + t := by
      rw [hbd, Nat.pow_add, Nat.mul_assoc]
      change (U * (3 ^ d * P) + acceleratedOrbit k S) / U = _
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hU, Nat.add_comm]
    have hr : (3 ^ a * Q + acceleratedOrbit k R) / U = Q := by
      change (U * Q + acceleratedOrbit k R) / U = Q
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hU, Nat.div_eq_of_lt hcapR, Nat.zero_add]
    have he := congrArg (· / U) hAffine
    rw [hl, hr] at he
    exact he.symm
  let B := D * t + R + 1
  let C := B / 3 ^ d
  have hB : B ≤ D * 3 ^ d := by
    have hT := Nat.mul_le_mul_left D (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at hT
    dsimp [B]
    omega
  have hpow : 0 < (3 : Nat) ^ d := Nat.pow_pos (by decide)
  have hC : C ≤ D := by
    have h := Nat.div_le_div_right (c := 3 ^ d) hB
    rwa [Nat.mul_div_left _ hpow] at h
  let c : Int := (C : Int) - (S : Int)
  have hsmall : c.natAbs ≤ D := by
    by_cases hle : S ≤ C
    · have hnon : 0 ≤ c := by dsimp only [c]; omega
      have hcast := Int.natAbs_of_nonneg hnon
      change (c.natAbs : Int) = (C : Int) - (S : Int) at hcast
      omega
    · have hnon : c ≤ 0 := by dsimp only [c]; omega
      have hcast := Int.ofNat_natAbs_of_nonpos hnon
      change (c.natAbs : Int) = -((C : Int) - (S : Int)) at hcast
      have hnonC : (0 : Int) ≤ (C : Int) := Int.natCast_nonneg _
      omega
  have hApos : 0 < A := by change D ≤ A - 1 at hlarge; omega
  have hA' : A = 3 ^ d * (D * P) + B := by
    calc
      _ = D * Q + R + 1 := by omega
      _ = _ := by rw [hquot, Nat.mul_add]; dsimp only [B]; ac_rfl
  have hAquot : A / 3 ^ d = D * P + C := by
    rw [hA', Nat.add_comm, Nat.add_mul_div_left _ _ hpow, Nat.add_comm]
  refine ⟨d, c, hd, hsmall, ?_⟩
  rw [← hx, hAquot, Int.natCast_add, Int.natCast_add]
  dsimp only [c]
  omega

private theorem odd_count_of_shifted_height {j t x C A : Nat} {c : Int}
    (hx : x < 2 ^ j * C) (hcap : C * 3 ^ t + c.natAbs ≤ A)
    (hy : (acceleratedOrbit j x : Int) + c = (A : Int)) : t + 1 ≤ oddCount x j := by
  apply Nat.le_of_not_gt
  intro hshort
  have himage := image_lt (k := j) (c := C) (x := x) (by simpa only [Nat.mul_comm] using hx)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 3)
    (show oddCount x j ≤ t by omega)
  have hlt : acceleratedOrbit j x < C * 3 ^ t :=
    Nat.lt_of_lt_of_le himage (Nat.mul_le_mul_left C hpow)
  omega

/-- A source below the long-run input needs enough odd steps to
reach a nearby power-of-three fraction of its peak. -/
theorem odd_count_near_peak {v d x u : Nat} {c : Int} (hu : 0 < u)
    (hx : x < 2 ^ v * u) (hd : d < v) (hc : c.natAbs ≤ 3 ^ (v - d - 1))
    (hy : (acceleratedOrbit v x : Int) + c = ((3 ^ (v - d) * u : Nat) : Int)) :
    v - d ≤ oddCount x v := by
  let B := u * 3 ^ (v - d - 1)
  have hmax : c.natAbs ≤ B := Nat.le_trans hc (Nat.le_mul_of_pos_left _ hu)
  have htriple : 3 ^ (v - d) * u = 3 * B := by
    rw [show v - d = (v - d - 1) + 1 by omega, Nat.pow_succ']
    dsimp only [B]
    ac_rfl
  have h := odd_count_of_shifted_height hx
    (show B + c.natAbs ≤ 3 ^ (v - d) * u by rw [htriple]; omega) hy
  omega

def rigidityCutoff (k : Nat) : Nat := 6 * k + 2

def adaptiveRigidityCutoff (k a : Nat) : Nat := 2 * k + 2 + 4 * (k - a)

/-- A smaller source meeting the original orbit earlier by r steps
still enters an exact scaled peak before the common suffix. -/
theorem scaled_peak_after_shortened_prefix {k v r n m u : Nat}
    (hv : adaptiveRigidityCutoff k (oddCount (3 ^ v * u - 1) k) + r ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) (hsmall : m < n)
    (hfinal : acceleratedOrbit (v - r + k) m = acceleratedOrbit (v + k) n) :
    ∃ d, 0 < d ∧ d ≤ k - oddCount (3 ^ v * u - 1) k ∧
      acceleratedOrbit (v - r) m = 3 ^ (v - d) * u - 1 := by
  let A := 3 ^ v * u
  let a := oddCount (A - 1) k
  have hpeak : acceleratedOrbit v n + 1 = A := DeviceSwap.run_climb v u n hu hfac
  have hV : 2 * k + 2 + 4 * (k - a) + r ≤ v := hv
  let y := acceleratedOrbit (v - r) m
  change ∃ d, 0 < d ∧ d ≤ k - a ∧ y = 3 ^ (v - d) * u - 1
  have hm : m < 2 ^ v * u := by omega
  have hcap : m < 2 ^ (v - r) * (2 ^ r * u) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (by omega : r ≤ v)]
    exact hm
  have hy : y < A - 1 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simpa only [y, hr, Nat.sub_zero] using prefix_image_lt hu hfac hsmall
    · have hpow := Nat.pow_lt_pow_left (by decide : 2 < 3) (Nat.ne_of_gt hr)
      have himage := image_lt (k := v - r) (c := 2 ^ r * u) (x := m)
        (by simpa only [Nat.mul_comm (2 ^ (v - r))] using hcap)
      have hbound : (2 ^ r * u) * 3 ^ (v - r) < A := by
        calc
          _ < (3 ^ r * u) * 3 ^ (v - r) :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hpow hu) (Nat.pow_pos (by decide))
          _ = A := by
            dsimp only [A]
            rw [Nat.mul_right_comm, ← Nat.pow_add, Nat.add_sub_of_le (by omega : r ≤ v)]
      have hycap : y < (2 ^ r * u) * 3 ^ (v - r) :=
        Nat.lt_of_lt_of_le himage (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by decide) (AffineExact.oddCount_le_self m (v - r))))
      omega
  have hmeet : acceleratedOrbit k y = acceleratedOrbit k (A - 1) := by
    have hpn : A - 1 = acceleratedOrbit v n := by omega
    change acceleratedOrbit k (acceleratedOrbit (v - r) m) = _
    rw [hpn, acceleratedOrbit_add, acceleratedOrbit_add, Nat.add_comm k (v - r), Nat.add_comm k v]
    exact hfinal
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, acceleratedOrbit_zero, acceleratedOrbit_zero] at hmeet
    exact Nat.ne_of_lt hy hmeet
  have hlarge : 2 ^ k ≤ A - 1 := by
    have hbig : 2 ^ (k + 1) ≤ A := by
      calc
        _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_left (by decide) _
        _ ≤ 3 ^ v := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ _ := Nat.le_mul_of_pos_right _ hu
    rw [Nat.pow_succ'] at hbig
    have hD := Nat.two_pow_pos k
    omega
  obtain ⟨d, c, hd, habs, hval⟩ := lower_peak_offset hlarge hy hmeet
  change d ≤ k - a at hd
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
    let p := 2 * (k + 1) + 3 * d
    have hp : p ≤ v - r - d := by dsimp only [p]; omega
    have hsizeC : (1 - c).natAbs < 2 ^ (k + 1) := by
      have ha : (1 - c).natAbs ≤ 1 + c.natAbs := Int.natAbs_sub_le 1 c
      have hD : 2 ≤ 2 ^ k := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hk
      rw [Nat.pow_succ']
      omega
    have hsize : c.natAbs ≤ 3 ^ (v - d - 1) :=
      Nat.le_trans habs (by
        calc
          _ ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) _
          _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega))
    let t := v - r - d - 1
    let G := 3 ^ (v - d - 1) * u
    have hG : (2 ^ r * u) * 3 ^ t ≤ G := by
      calc
        _ ≤ (3 ^ r * u) * 3 ^ t :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _))
        _ = G := by
          rw [Nat.mul_right_comm, ← Nat.pow_add]
          dsimp only [G, t]
          rw [show r + (v - r - d - 1) = v - d - 1 by omega]
    have hC : c.natAbs ≤ G := Nat.le_trans hsize (Nat.le_mul_of_pos_right _ hu)
    have htriple : 3 ^ (v - d) * u = 3 * G := by
      rw [show v - d = (v - d - 1) + 1 by omega, Nat.pow_succ', Nat.mul_assoc]
    have htotal : (2 ^ r * u) * 3 ^ t + c.natAbs ≤ 3 ^ (v - d) * u := by
      rw [htriple]
      omega
    have hcount : (v - r) - d ≤ oddCount m (v - r) := by
      have h := odd_count_of_shifted_height hcap htotal hval
      dsimp only [t] at h
      omega
    have hpow : 3 ^ p ∣ 3 ^ (v - d) * u :=
      Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 3 (by omega)) _
    have hdvd : (3 : Int) ^ p ∣ (y : Int) + c := by
      rw [hval]
      simpa only [Int.natCast_pow, show ((3 : Nat) : Int) = 3 by rfl] using
        (Int.ofNat_dvd.mpr hpow)
    exact excludes_displacement_at_precision d (k + 1) c hc hsizeC
      m (v - r) hcount (Nat.le_trans hp hcount) hdvd
  have hresult : y = 3 ^ (v - d) * u - 1 := by omega
  have hpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.sub_zero] at hresult
    exact Nat.not_le_of_gt hy (by omega)
  exact ⟨d, hpos, hd, hresult⟩

/-- The odd count of the original suffix lowers the cutoff for
exact scaled peaks. -/
theorem scaled_peak_at_adaptive_cutoff {k v n m u : Nat}
    (hv : adaptiveRigidityCutoff k (oddCount (3 ^ v * u - 1) k) ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) (hsmall : m < n)
    (hfinal : acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n) :
    ∃ d, 0 < d ∧ d ≤ k - oddCount (3 ^ v * u - 1) k ∧
      acceleratedOrbit v m = 3 ^ (v - d) * u - 1 := by
  simpa only [Nat.sub_zero] using
    scaled_peak_after_shortened_prefix (r := 0) (by simpa only [Nat.add_zero] using hv)
      hu hfac hsmall (by simpa only [Nat.sub_zero] using hfinal)

private theorem adaptive_le_fixed (k a : Nat) : adaptiveRigidityCutoff k a ≤ rigidityCutoff k := by
  unfold adaptiveRigidityCutoff rigidityCutoff
  omega

theorem scaled_peak_at_cutoff {k v n m u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) (hsmall : m < n)
    (hfinal : acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n) :
    ∃ d, 0 < d ∧ d ≤ k ∧ acceleratedOrbit v m = 3 ^ (v - d) * u - 1 := by
  obtain ⟨d, hpos, hd, hpeak⟩ :=
    scaled_peak_at_adaptive_cutoff (Nat.le_trans (adaptive_le_fixed _ _) hv) hu hfac hsmall hfinal
  exact ⟨d, hpos, by omega, hpeak⟩

/-- Every smaller equal-time partner of a sufficiently long odd run
has an exact scaled peak at the end of the prefix. -/
theorem scaled_peak_of_smaller_mate (k : Nat) :
    ∃ V, ∀ {v n m u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      m < n → acceleratedOrbit (v + k) m = acceleratedOrbit (v + k) n →
        ∃ d, 0 < d ∧ d ≤ k ∧ acceleratedOrbit v m = 3 ^ (v - d) * u - 1 :=
  ⟨rigidityCutoff k, scaled_peak_at_cutoff⟩

/-- Above the adaptive cutoff, a smaller equal-time partner exists
exactly when the original peak meets a scaled peak in the suffix. -/
theorem smaller_iff_scaled_peak_at_adaptive_cutoff {k v n u : Nat}
    (hv : adaptiveRigidityCutoff k (oddCount (3 ^ v * u - 1) k) ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔
      ∃ d, 0 < d ∧ d ≤ k ∧
        acceleratedOrbit k (3 ^ (v - d) * u - 1) =
          acceleratedOrbit k (3 ^ v * u - 1) := by
  have hbase : 2 * k + 2 ≤ v := by unfold adaptiveRigidityCutoff at hv; omega
  constructor
  · intro hsmall
    obtain ⟨d, hpos, hd, hpeak⟩ :=
      scaled_peak_at_adaptive_cutoff hv hu hfac hsmall (leastAt_meets (v + k) n)
    have hrun := DeviceSwap.run_climb v u n hu hfac
    have htrue : 3 ^ v * u - 1 = acceleratedOrbit v n := by omega
    refine ⟨d, hpos, by omega, ?_⟩
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

theorem smaller_iff_scaled_peak_at_cutoff {k v n u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : 0 < u) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔
      ∃ d, 0 < d ∧ d ≤ k ∧
        acceleratedOrbit k (3 ^ (v - d) * u - 1) =
          acceleratedOrbit k (3 ^ v * u - 1) :=
  smaller_iff_scaled_peak_at_adaptive_cutoff (Nat.le_trans (adaptive_le_fixed _ _) hv) hu hfac

/-- A fixed suffix length has a uniform threshold for the scaled-peak
characterization. -/
theorem smaller_iff_scaled_peak (k : Nat) :
    ∃ V, ∀ {v n u : Nat}, V ≤ v → 0 < u → n + 1 = 2 ^ v * u →
      (leastAt (v + k) n < n ↔
        ∃ d, 0 < d ∧ d ≤ k ∧
          acceleratedOrbit k (3 ^ (v - d) * u - 1) =
            acceleratedOrbit k (3 ^ v * u - 1)) :=
  ⟨rigidityCutoff k, smaller_iff_scaled_peak_at_cutoff⟩

private theorem odd_peak_residue_pos {k e u : Nat} (hk : 0 < k) (hu : u % 2 = 1) :
    0 < (3 ^ e * u) % 2 ^ k := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hmod := congrArg (· % 2) hz
  have hdiv : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
  rw [Nat.mod_mod_of_dvd _ hdiv] at hmod
  rw [Nat.mul_mod, Arith.three_pow_odd, hu] at hmod
  contradiction

private theorem peak_certificate_iff {k v d u : Nat} (hv : 2 * k + 2 ≤ v)
    (hpos : 0 < d) (hd : d ≤ k) (hu : u % 2 = 1) :
    acceleratedOrbit k (3 ^ (v - d) * u - 1) = acceleratedOrbit k (3 ^ v * u - 1) ↔
      PeakContraction.Certificate k d ((3 ^ (v - d) * u) % 2 ^ k) := by
  let B := 3 ^ (v - d) * u
  have hsize : 2 ^ k ≤ B := by
    calc
      _ ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) _
      _ ≤ 3 ^ (v - d) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hres : 0 < B % 2 ^ k := odd_peak_residue_pos (by omega) hu
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

private def peakOddCountResidue (k v u : Nat) : Nat :=
  let M := 2 ^ k
  let A := (threePowMod M v * (u % M)) % M
  oddCount ((A + M - 1) % M) k

private theorem peakOddCountResidue_eq (k v u : Nat) (hu : 0 < u) :
    peakOddCountResidue k v u = oddCount (3 ^ v * u - 1) k := by
  simp only [peakOddCountResidue, threePowMod_eq, Nat.mod_mul_mod, Nat.mul_mod_mod]
  let M := 2 ^ k
  let A := 3 ^ v * u
  change oddCount ((A % M + M - 1) % M) k = oddCount (A - 1) k
  have hM : 0 < M := Nat.two_pow_pos _
  have hA : 0 < A := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have he : (A % M + M - 1) % M = (A - 1) % M := by
    calc
      _ = (A % M + (M - 1)) % M := by congr 1; omega
      _ = (A + (M - 1)) % M := Nat.mod_add_mod _ _ _
      _ = (A - 1 + M) % M := by congr 1; omega
      _ = _ := Nat.add_mod_right _ _
  rw [he, ← Density.oddCount_mod]

/-- Compute the adaptive cutoff using only the dyadic peak residue. -/
def requiredRunLength (k v u : Nat) : Nat :=
  adaptiveRigidityCutoff k (peakOddCountResidue k v u)

theorem requiredRunLength_eq (k v u : Nat) (hu : 0 < u) :
    requiredRunLength k v u = adaptiveRigidityCutoff k (oddCount (3 ^ v * u - 1) k) := by
  rw [requiredRunLength, peakOddCountResidue_eq k v u hu]

/-- The finite certificate for one prescribed exponent drop. -/
def scaledPeakCertificate (k v u d : Nat) : Bool :=
  let M := 2 ^ k
  decide (PeakContraction.Certificate k d ((threePowMod M (v - d) * (u % M)) % M))

theorem scaledPeakCertificate_iff {k v d u : Nat} (hv : 2 * k + 2 ≤ v)
    (hpos : 0 < d) (hd : d ≤ k) (hu : u % 2 = 1) :
    scaledPeakCertificate k v u d = true ↔
      acceleratedOrbit k (3 ^ (v - d) * u - 1) = acceleratedOrbit k (3 ^ v * u - 1) := by
  rw [peak_certificate_iff hv hpos hd hu, scaledPeakCertificate, threePowMod_eq,
    Nat.mod_mul_mod, Nat.mul_mod_mod]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- A certified drop has equal endpoints and an exact odd-count
difference, with no size cutoff for the initial run. -/
theorem scaledPeakCertificate_spec {k v d u : Nat} (hv : d ≤ v)
    (hk : 0 < k) (hu : u % 2 = 1) (hc : scaledPeakCertificate k v u d = true) :
    acceleratedOrbit k (3 ^ (v - d) * u - 1) = acceleratedOrbit k (3 ^ v * u - 1) ∧
      oddCount (3 ^ (v - d) * u - 1) k = oddCount (3 ^ v * u - 1) k + d := by
  rw [scaledPeakCertificate, threePowMod_eq, Nat.mod_mul_mod, Nat.mul_mod_mod] at hc
  have hr := odd_peak_residue_pos hk hu (e := v - d)
  have hmeet := PeakContraction.meet_of_certificate hr rfl (of_decide_eq_true hc)
  have hcount := PeakContraction.counts_of_certificate hr rfl (of_decide_eq_true hc)
  rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hv] at hmeet hcount
  exact ⟨hmeet.symm, hcount⟩

/-- A positive drop increases the odd count in the suffix by exactly
the amount removed from the initial odd run. -/
theorem counts_of_scaledPeakCertificate {k v d u : Nat} (hv : d ≤ v)
    (hk : 0 < k) (hu : u % 2 = 1) (hc : scaledPeakCertificate k v u d = true) :
    oddCount (3 ^ (v - d) * u - 1) k = oddCount (3 ^ v * u - 1) k + d :=
  (scaledPeakCertificate_spec hv hk hu hc).2

/-- Test the k candidate drops by suffix calculations at bounded
dyadic residues. -/
def shorterPeakCheck (k v u : Nat) : Bool :=
  (List.range k).any (fun i => scaledPeakCertificate k v u (i + 1))

/-- The finite parity test also works at the smaller adaptive cutoff. -/
theorem smaller_iff_shorterPeakCheck_adaptive {k v n u : Nat}
    (hv : adaptiveRigidityCutoff k (oddCount (3 ^ v * u - 1) k) ≤ v)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔ shorterPeakCheck k v u = true := by
  have hbase : 2 * k + 2 ≤ v := by unfold adaptiveRigidityCutoff at hv; omega
  rw [smaller_iff_scaled_peak_at_adaptive_cutoff hv (by omega) hfac, shorterPeakCheck, List.any_eq_true]
  constructor
  · rintro ⟨d, hpos, hd, hmeet⟩
    refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [show d - 1 + 1 = d by omega]
    exact (scaledPeakCertificate_iff hbase hpos hd hu).mpr hmeet
  · rintro ⟨i, hi, hcheck⟩
    have hd : i + 1 ≤ k := Nat.succ_le_of_lt (List.mem_range.mp hi)
    exact ⟨i + 1, Nat.succ_pos _, hd,
      (scaledPeakCertificate_iff hbase (Nat.succ_pos _) hd hu).mp hcheck⟩

/-- The fixed linear cutoff is a convenient sufficient bound for the
finite parity test. -/
theorem smaller_iff_shorterPeakCheck {k v n u : Nat} (hv : rigidityCutoff k ≤ v)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔ shorterPeakCheck k v u = true :=
  smaller_iff_shorterPeakCheck_adaptive (Nat.le_trans (adaptive_le_fixed _ _) hv) hu hfac

/-- Both the applicability test and the decision can be evaluated
without constructing the full shifted peak. -/
theorem shorterPeakCheck_correct {k v n u : Nat} (hv : requiredRunLength k v u ≤ v)
    (hu : u % 2 = 1) (hfac : n + 1 = 2 ^ v * u) :
    leastAt (v + k) n < n ↔ shorterPeakCheck k v u = true := by
  rw [requiredRunLength_eq k v u (by omega)] at hv
  exact smaller_iff_shorterPeakCheck_adaptive hv hu hfac

end Collatz.LongRunPeakRigidity
