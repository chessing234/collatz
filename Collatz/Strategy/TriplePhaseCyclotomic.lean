/-!
# The cyclotomic gap of a triple phase copy

For a hypothetical accelerated cycle whose period and odd-step count are
both divisible by three, write `L = 3p` and `a = 3b`. The usual power gap
`2^L - 3^a` factors as `(2^p - 3^b)` times

    D = 2^(2p) + 2^p · 3^b + 3^(2b).

`D` is the field norm, on the Eisenstein integers, of `2^p - 3^b · ω`,
where `ω` is a primitive cube root of unity. This file builds that norm
as an integer multiplication, proves it is multiplicative, and checks the
consequences used by a width argument:

* `D` is at least `2^(2p)` and, once `b > 0`, prime to six;
* the ratio `R ≡ 2^p · (3^b)⁻¹ (mod D)` satisfies `1 + R + R² ≡ 0`;
* `R` has order three modulo `D`;
* every nonempty proper subset sum of `{1, R, R²}` is a unit modulo `D`;
* every power of `R` reduces to a primitive pair of integer coordinates
  on the basis `(1, R)`, and those coordinates repeat every three steps.

The comparison of this modulus with a Sylvester box, which would force the
discrepancy width to grow, is not proved here. Nothing in this file asserts
that every Collatz orbit reaches one.
-/

namespace Collatz.TriplePhaseCyclotomic

/-- Multiplication in `ℤ[ω]/(1 + ω + ω²)`, on coordinates of `x + yω`. -/
def mul (z w : Int × Int) : Int × Int :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1 - z.2 * w.2)

/-- The nontrivial automorphism, sending `ω` to `ω² = -1 - ω`. -/
def conj (z : Int × Int) : Int × Int := (z.1 - z.2, -z.2)

/-- Field norm `x² - xy + y²` of the element `x + yω`. -/
def fieldNorm (x y : Int) : Int := x ^ 2 - x * y + y ^ 2

theorem mul_comm (z w : Int × Int) : mul z w = mul w z := by
  unfold mul
  grind

theorem mul_assoc (a b c : Int × Int) : mul (mul a b) c = mul a (mul b c) := by
  unfold mul
  grind

theorem conj_mul (z w : Int × Int) : conj (mul z w) = mul (conj z) (conj w) := by
  unfold conj mul
  grind

theorem mul_scalar (m n : Int) : mul (m, 0) (n, 0) = (m * n, 0) := by
  unfold mul
  grind

theorem conj_hom_scalar (x y : Int) :
    mul (x, y) (conj (x, y)) = (fieldNorm x y, 0) := by
  unfold mul conj fieldNorm
  apply Prod.ext
  · grind
  · grind

/-- The norm of a product is the product of the norms. -/
theorem fieldNorm_mul (x1 y1 x2 y2 : Int) :
    fieldNorm (mul (x1, y1) (x2, y2)).1 (mul (x1, y1) (x2, y2)).2 =
      fieldNorm x1 y1 * fieldNorm x2 y2 := by
  have hre (a b c d : Int × Int) :
      mul (mul a b) (mul c d) = mul (mul a c) (mul b d) := by
    calc
      mul (mul a b) (mul c d) = mul a (mul b (mul c d)) := by rw [mul_assoc]
      _ = mul a (mul (mul b c) d) := by rw [← mul_assoc b c d]
      _ = mul a (mul (mul c b) d) := by rw [mul_comm b c]
      _ = mul a (mul c (mul b d)) := by rw [mul_assoc c b d]
      _ = mul (mul a c) (mul b d) := by rw [← mul_assoc a c (mul b d)]
  have hconj := conj_mul (x1, y1) (x2, y2)
  have hprod := hre (x1, y1) (x2, y2) (conj (x1, y1)) (conj (x2, y2))
  have hz := conj_hom_scalar x1 y1
  have hw := conj_hom_scalar x2 y2
  have hpair :
      mul (mul (x1, y1) (x2, y2)) (conj (mul (x1, y1) (x2, y2))) =
        (fieldNorm x1 y1 * fieldNorm x2 y2, 0) := by
    rw [hconj, hprod, hz, hw, mul_scalar]
  have hself := conj_hom_scalar (mul (x1, y1) (x2, y2)).1 (mul (x1, y1) (x2, y2)).2
  have heta :
      ((mul (x1, y1) (x2, y2)).1, (mul (x1, y1) (x2, y2)).2) = mul (x1, y1) (x2, y2) := by
    exact Prod.ext rfl rfl
  rw [heta] at hself
  have hpair' :
      (fieldNorm (mul (x1, y1) (x2, y2)).1 (mul (x1, y1) (x2, y2)).2, (0 : Int)) =
        (fieldNorm x1 y1 * fieldNorm x2 y2, 0) := by
    rw [← hself, hpair]
  exact congrArg Prod.fst hpair'

/-- The larger factor of a three-copy power gap. -/
def gapFactor (p b : Nat) : Nat := 2 ^ (2 * p) + 2 ^ p * 3 ^ b + 3 ^ (2 * b)

theorem gapFactor_ge (p b : Nat) : 2 ^ (2 * p) ≤ gapFactor p b := by
  dsimp [gapFactor]
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

private theorem three_pow_odd (b : Nat) : 3 ^ b % 2 = 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, show (3 : Nat) % 2 = 1 by decide]

private theorem two_pow_even {p : Nat} (hp : 0 < p) : 2 ^ p % 2 = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    rw [Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 (2 ^ p))

private theorem two_sq_mod_three (p : Nat) : 2 ^ (2 * p) % 3 = 1 := by
  induction p with
  | zero => decide
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 by omega, Nat.pow_add, Nat.mul_mod, ih,
      show (2 ^ 2 : Nat) % 3 = 1 by decide]

private theorem three_pow_mod_three {b : Nat} (hb : 0 < b) : 3 ^ b % 3 = 0 := by
  cases b with
  | zero => omega
  | succ b =>
    rw [Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 3 (3 ^ b))

private theorem add_mod_two_sum {a b c : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0) (hc : c % 2 = 1) :
    (a + b + c) % 2 = 1 := by
  have hab : (a + b) % 2 = 0 := by
    rw [Nat.add_mod, ha, hb]
  rw [Nat.add_mod, hab, hc]

private theorem add_mod_three_sum {a b c : Nat} (ha : a % 3 = 1) (hb : b % 3 = 0) (hc : c % 3 = 0) :
    (a + b + c) % 3 = 1 := by
  have hab : (a + b) % 3 = 1 := by
    rw [Nat.add_mod, ha, hb]
  rw [Nat.add_mod, hab, hc]

theorem gapFactor_mod_two {p b : Nat} (hp : 0 < p) : gapFactor p b % 2 = 1 := by
  have h2 : (2 ^ p * 3 ^ b) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (two_pow_even hp)) (Nat.dvd_mul_right _ _))
  simpa [gapFactor] using
    add_mod_two_sum (two_pow_even (by omega : 0 < 2 * p)) h2 (three_pow_odd (2 * b))

theorem gapFactor_mod_three {p b : Nat} (hb : 0 < b) : gapFactor p b % 3 = 1 := by
  have h2 : (2 ^ p * 3 ^ b) % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (three_pow_mod_three hb)) (Nat.dvd_mul_left _ _))
  simpa [gapFactor] using
    add_mod_three_sum (two_sq_mod_three p) h2 (three_pow_mod_three (by omega : 0 < 2 * b))

theorem gapFactor_coprime_two {p b : Nat} (hp : 0 < p) : (gapFactor p b).Coprime 2 := by
  have hmod := gapFactor_mod_two (b := b) hp
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod]
  decide

theorem gapFactor_coprime_three {p b : Nat} (hb : 0 < b) : (gapFactor p b).Coprime 3 := by
  have hmod := gapFactor_mod_three (p := p) hb
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod]
  decide

/-- A positive odd count makes the large factor prime to two and to three. -/
theorem gapFactor_coprime_six {p b : Nat} (hp : 0 < p) (hb : 0 < b) :
    (gapFactor p b).Coprime 6 :=
  (gapFactor_coprime_two (b := b) hp).mul_right (gapFactor_coprime_three (p := p) hb)

private theorem cube_diff (x y : Int) :
    (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 := by
  grind

private theorem pow_sq (a k : Nat) : (a ^ k) ^ 2 = a ^ (2 * k) := by
  rw [← Nat.pow_mul, Nat.mul_comm]

private theorem pow_cube (a k : Nat) : (a ^ k) ^ 3 = a ^ (3 * k) := by
  rw [← Nat.pow_mul, Nat.mul_comm]

/-- `(2^p - 3^b)` times the norm factor is the three-copy power gap. -/
theorem factor_mul {p b : Nat} (h : 3 ^ b ≤ 2 ^ p) :
    (2 ^ p - 3 ^ b) * gapFactor p b = 2 ^ (3 * p) - 3 ^ (3 * b) := by
  have hcube : (3 ^ b) ^ 3 ≤ (2 ^ p) ^ 3 := Nat.pow_le_pow_left h 3
  have hcube' : 3 ^ (3 * b) ≤ 2 ^ (3 * p) := by
    rwa [pow_cube, pow_cube] at hcube
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mul, Int.ofNat_sub h, Int.ofNat_sub hcube']
  have hs2 : ((2 ^ p : Nat) : Int) ^ 2 = ((2 ^ (2 * p) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_sq]
  have hs3 : ((3 ^ b : Nat) : Int) ^ 2 = ((3 ^ (2 * b) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_sq]
  have hc2 : ((2 ^ p : Nat) : Int) ^ 3 = ((2 ^ (3 * p) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_cube]
  have hc3 : ((3 ^ b : Nat) : Int) ^ 3 = ((3 ^ (3 * b) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_cube]
  have hpoly := cube_diff ((2 ^ p : Nat) : Int) ((3 ^ b : Nat) : Int)
  rw [hs2, hs3, hc2, hc3] at hpoly
  have hsum : (gapFactor p b : Int) = ↑(2 ^ (2 * p)) + ↑(2 ^ p) * ↑(3 ^ b) + ↑(3 ^ (2 * b)) := by
    simp [gapFactor, Int.natCast_add, Int.natCast_mul]
  rw [hsum]
  exact hpoly

/-- A strict cube inequality gives a strict root inequality. -/
theorem root_lt_of_cube_lt {p b : Nat} (h : 3 ^ (3 * b) < 2 ^ (3 * p)) : 3 ^ b < 2 ^ p := by
  apply Classical.byContradiction
  intro hn
  have hle : 2 ^ p ≤ 3 ^ b := Nat.le_of_not_gt hn
  have hcube : (2 ^ p) ^ 3 ≤ (3 ^ b) ^ 3 := Nat.pow_le_pow_left hle 3
  rw [pow_cube, pow_cube] at hcube
  omega

theorem gapFactor_eq_fieldNorm (p b : Nat) :
    (gapFactor p b : Int) = fieldNorm ((2 ^ p : Nat) : Int) (-((3 ^ b : Nat) : Int)) := by
  have hs2 : ((2 ^ p : Nat) : Int) ^ 2 = ((2 ^ (2 * p) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_sq]
  have hs3 : ((3 ^ b : Nat) : Int) ^ 2 = ((3 ^ (2 * b) : Nat) : Int) := by
    rw [← Int.natCast_pow, pow_sq]
  unfold fieldNorm
  have hneg : (-((3 ^ b : Nat) : Int)) ^ 2 = ((3 ^ b : Nat) : Int) ^ 2 := by
    grind
  rw [hneg, hs2, hs3]
  have hmove :
      ((2 ^ (2 * p) : Nat) : Int) - ((2 ^ p : Nat) : Int) * -((3 ^ b : Nat) : Int) =
        ((2 ^ (2 * p) : Nat) : Int) + ((2 ^ p : Nat) : Int) * ((3 ^ b : Nat) : Int) := by
    rw [Int.mul_neg, Int.sub_neg]
  rw [hmove]
  simp [gapFactor, Int.natCast_add, Int.natCast_mul]

/-! ## Congruences and the ratio root -/

private def Cong (d : Nat) (x y : Int) : Prop := (d : Int) ∣ x - y

private theorem Cong.refl (d : Nat) (x : Int) : Cong d x x := by
  simp [Cong]

private theorem Cong.symm {d : Nat} {x y : Int} (h : Cong d x y) : Cong d y x := by
  unfold Cong at *
  simpa only [Int.neg_sub] using Int.dvd_neg.mpr h

private theorem Cong.trans {d : Nat} {x y z : Int} (h : Cong d x y) (g : Cong d y z) :
    Cong d x z := by
  unfold Cong at *
  rw [show x - z = (x - y) + (y - z) by omega]
  exact Int.dvd_add h g

private theorem Cong.mul {d : Nat} {x y u v : Int} (h : Cong d x y) (g : Cong d u v) :
    Cong d (x * u) (y * v) := by
  unfold Cong at *
  rw [show x * u - y * v = (x - y) * u + y * (u - v) by grind]
  exact Int.dvd_add (Int.dvd_trans h (Int.dvd_mul_right _ _))
    (Int.dvd_trans g (Int.dvd_mul_left _ _))

private theorem Cong.add {d : Nat} {x y u v : Int} (h : Cong d x y) (g : Cong d u v) :
    Cong d (x + u) (y + v) := by
  unfold Cong at *
  rw [show x + u - (y + v) = (x - y) + (u - v) by omega]
  exact Int.dvd_add h g

private theorem Cong.pow {d : Nat} {x y : Int} (h : Cong d x y) (n : Nat) :
    Cong d (x ^ n) (y ^ n) := by
  induction n with
  | zero => simp [Cong]
  | succ n ih =>
    rw [Int.pow_succ, Int.pow_succ]
    exact ih.mul h

private theorem exists_three_inverse {d : Nat} (hd : d % 3 ≠ 0) : ∃ u : Int, Cong d (3 * u) 1 := by
  have _ := Nat.div_add_mod d 3
  rcases (show d % 3 = 1 ∨ d % 3 = 2 by omega) with hr | hr
  · exact ⟨-((d / 3 : Nat) : Int), -1, by omega⟩
  · exact ⟨((d / 3 : Nat) : Int) + 1, 1, by omega⟩

private theorem ofNat_dvd_of_dvd_natAbs {g : Nat} {a : Int} (h : g ∣ a.natAbs) : (g : Int) ∣ a :=
  (Int.dvd_natAbs).mp (Int.ofNat_dvd.mpr h)

private theorem dvd_natAbs_of_ofNat_dvd {g : Nat} {a : Int} (h : (g : Int) ∣ a) : g ∣ a.natAbs :=
  (Int.ofNat_dvd).mp ((Int.dvd_natAbs).mpr h)

private theorem coprime_of_cong {d : Nat} {a b : Int} (h : Cong d a b)
    (hc : Nat.Coprime b.natAbs d) : Nat.Coprime a.natAbs d := by
  let g := a.natAbs.gcd d
  have hga : g ∣ a.natAbs := Nat.gcd_dvd_left _ _
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgaI : (g : Int) ∣ a := ofNat_dvd_of_dvd_natAbs hga
  have hsub : (g : Int) ∣ a - b := Int.dvd_trans (Int.ofNat_dvd.mpr hgd) h
  have hgbI : (g : Int) ∣ b := by
    have hdiff : (g : Int) ∣ a - (a - b) := Int.dvd_sub hgaI hsub
    have heq : a - (a - b) = b := by omega
    rwa [heq] at hdiff
  have hgb : g ∣ b.natAbs := dvd_natAbs_of_ofNat_dvd hgbI
  have hg1 : g ∣ Nat.gcd b.natAbs d := Nat.dvd_gcd hgb hgd
  rw [show Nat.gcd b.natAbs d = 1 from hc] at hg1
  exact Nat.dvd_one.mp hg1

private theorem coprime_of_linear {d a b : Nat} {R : Int} (ha : d.Coprime a)
    (h : Cong d ((b : Int) * R) (a : Int)) : Nat.Coprime R.natAbs d := by
  let g := R.natAbs.gcd d
  have hga : g ∣ R.natAbs := Nat.gcd_dvd_left _ _
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgaI : (g : Int) ∣ R := ofNat_dvd_of_dvd_natAbs hga
  have hmul : (g : Int) ∣ (b : Int) * R := Int.dvd_trans hgaI (Int.dvd_mul_left _ _)
  have hsub : (g : Int) ∣ (b : Int) * R - (a : Int) := Int.dvd_trans (Int.ofNat_dvd.mpr hgd) h
  have haI : (g : Int) ∣ (a : Int) := by
    have hdiff : (g : Int) ∣ (b : Int) * R - ((b : Int) * R - (a : Int)) := Int.dvd_sub hmul hsub
    have heq : (b : Int) * R - ((b : Int) * R - (a : Int)) = (a : Int) := by omega
    rwa [heq] at hdiff
  have hgaNat : g ∣ a := (Int.ofNat_dvd).mp haI
  have hg1 : g ∣ 1 := by
    have hgcd : g ∣ a.gcd d := Nat.dvd_gcd hgaNat hgd
    unfold Nat.Coprime at ha
    rw [Nat.gcd_comm] at ha
    rwa [ha] at hgcd
  simpa [g] using (Nat.dvd_one.mp hg1)

theorem cube_divides {d : Nat} {R : Int} (h : (d : Int) ∣ 1 + R + R ^ 2) :
    (d : Int) ∣ R ^ 3 - 1 := by
  have hpoly : R ^ 3 - 1 = (R - 1) * (1 + R + R ^ 2) := by grind
  rw [hpoly]
  exact Int.dvd_trans h (Int.dvd_mul_left _ _)

theorem three_of_fixed_root {d : Nat} {R : Int} (hΦ : (d : Int) ∣ 1 + R + R ^ 2)
    (h1 : (d : Int) ∣ R - 1) : (d : Int) ∣ 3 := by
  have hsq : R ^ 2 - 1 = (R - 1) * (R + 1) := by grind
  have hR2 : (d : Int) ∣ R ^ 2 - 1 := by
    rw [hsq]
    exact Int.dvd_trans h1 (Int.dvd_mul_right _ _)
  have hdiff : 1 + R + R ^ 2 - 3 = (R - 1) + (R ^ 2 - 1) := by grind
  have hd : (d : Int) ∣ 1 + R + R ^ 2 - 3 := by
    rw [hdiff]
    exact Int.dvd_add h1 hR2
  have hsub : (d : Int) ∣ (1 + R + R ^ 2) - (1 + R + R ^ 2 - 3) := Int.dvd_sub hΦ hd
  have heq : (1 + R + R ^ 2) - (1 + R + R ^ 2 - 3) = 3 := by omega
  rwa [heq] at hsub

theorem trivial_of_fixed_root {d : Nat} {R : Int} (hΦ : (d : Int) ∣ 1 + R + R ^ 2)
    (h1 : (d : Int) ∣ R - 1) (hc : d.Coprime 3) : d = 1 := by
  have h3 : d ∣ 3 := (Int.ofNat_dvd).mp (three_of_fixed_root hΦ h1)
  have h1d : d ∣ 1 := by
    have hgcd : d ∣ d.gcd 3 := Nat.dvd_gcd (Nat.dvd_refl d) h3
    change d.gcd 3 = 1 at hc
    rwa [hc] at hgcd
  exact Nat.dvd_one.mp h1d

/-- Coordinates of `R^n` on the basis `(1, R)`, using `R² = -1 - R`. -/
def basis : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 =>
    let p := basis n
    (-p.2, p.1 - p.2)

private theorem step_reduce (A B R : Int) :
    R * (A + B * R) - (-B + (A - B) * R) = B * (1 + R + R ^ 2) := by
  grind

private theorem gcd_sub (A B : Int) : (A - B).gcd B = A.gcd B := by
  apply Nat.dvd_antisymm
  · exact Int.dvd_gcd
      (by
        have h1 := Int.gcd_dvd_left (A - B) B
        have h2 := Int.gcd_dvd_right (A - B) B
        have : (↑((A - B).gcd B) : Int) ∣ (A - B) + B := Int.dvd_add h1 h2
        simpa using this)
      (Int.gcd_dvd_right (A - B) B)
  · exact Int.dvd_gcd (Int.dvd_sub (Int.gcd_dvd_left A B) (Int.gcd_dvd_right A B))
      (Int.gcd_dvd_right A B)

private theorem gcd_neg_left (A B : Int) : (-A).gcd B = A.gcd B := by
  apply Nat.dvd_antisymm
  · exact Int.dvd_gcd ((Int.dvd_neg).mp (Int.gcd_dvd_left (-A) B)) (Int.gcd_dvd_right (-A) B)
  · exact Int.dvd_gcd ((Int.dvd_neg).mpr (Int.gcd_dvd_left A B)) (Int.gcd_dvd_right A B)

theorem basis_gcd (n : Nat) : (basis n).1.gcd (basis n).2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [basis]
    rw [gcd_neg_left, Int.gcd_comm, gcd_sub]
    exact ih

private theorem basis_step (n : Nat) :
    basis (n + 1) = (-(basis n).2, (basis n).1 - (basis n).2) := by
  simp [basis]

theorem basis_add_three (n : Nat) : basis (n + 3) = basis n := by
  induction n with
  | zero => simp [basis]
  | succ n ih =>
    rw [show n + 1 + 3 = n + 3 + 1 by omega, basis_step, ih, ← basis_step]

private theorem basis_three_mul_add (q r : Nat) : basis (3 * q + r) = basis r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3 * (q + 1) + r = 3 * q + r + 3 by omega, basis_add_three, ih]

theorem basis_mod_three (n : Nat) : basis n = basis (n % 3) := by
  have hn : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hleft : basis (3 * (n / 3) + n % 3) = basis (n % 3) :=
    basis_three_mul_add (n / 3) (n % 3)
  rwa [hn] at hleft

/-- Every power of a cube root reduces to its basis pair. -/
theorem divides_power {d : Nat} {R : Int} (h : (d : Int) ∣ 1 + R + R ^ 2) (n : Nat) :
    (d : Int) ∣ R ^ n - ((basis n).1 + (basis n).2 * R) := by
  induction n with
  | zero =>
    simp [basis]
  | succ n ih =>
    let A := (basis n).1
    let B := (basis n).2
    have hstep := step_reduce A B R
    have hnext : basis (n + 1) = (-B, A - B) := by simp [basis, A, B]
    rw [hnext]
    have hδ : (d : Int) ∣ R ^ n - (A + B * R) := ih
    have hpoly : (d : Int) ∣ B * (1 + R + R ^ 2) := Int.dvd_trans h (Int.dvd_mul_left _ _)
    have : R ^ (n + 1) - (-B + (A - B) * R) =
        R * (R ^ n - (A + B * R)) + B * (1 + R + R ^ 2) := by
      rw [Int.pow_succ]
      grind
    rw [this]
    exact Int.dvd_add (Int.dvd_trans hδ (Int.dvd_mul_left _ _)) hpoly

/-- A nonempty proper subset of the three cube roots, encoded as a bit mask. -/
def subsetSum (mask : Nat) (R : Int) : Int :=
  (if mask % 2 = 1 then 1 else 0) + (if (mask / 2) % 2 = 1 then R else 0) +
    (if (mask / 4) % 2 = 1 then R ^ 2 else 0)

theorem subsetSum_coprime {d : Nat} {R : Int} (hΦ : (d : Int) ∣ 1 + R + R ^ 2)
    (hR : Nat.Coprime R.natAbs d) {mask : Nat} (h0 : mask ≠ 0) (h7 : mask < 7) :
    Nat.Coprime (subsetSum mask R).natAbs d := by
  have hpow : Nat.Coprime (R ^ 2).natAbs d := by
    rw [Int.natAbs_pow]
    exact hR.pow_left 2
  have hneg (t : Int) (ht : Nat.Coprime t.natAbs d) : Nat.Coprime (-t).natAbs d := by
    rwa [Int.natAbs_neg]
  match mask with
  | 0 => omega
  | 1 =>
    simp [subsetSum]
  | 2 =>
    simpa [subsetSum] using hR
  | 3 =>
    have hcong : Cong d (subsetSum 3 R) (-(R ^ 2)) := by
      unfold Cong subsetSum
      simpa using hΦ
    exact coprime_of_cong hcong (hneg _ hpow)
  | 4 =>
    simpa [subsetSum] using hpow
  | 5 =>
    have hs : subsetSum 5 R = 1 + R ^ 2 := by simp [subsetSum]
    have hcong : Cong d (subsetSum 5 R) (-R) := by
      unfold Cong
      rw [hs]
      have heq : 1 + R ^ 2 - (-R) = 1 + R + R ^ 2 := by omega
      rw [heq]
      exact hΦ
    exact coprime_of_cong hcong (hneg _ hR)
  | 6 =>
    have hs : subsetSum 6 R = R + R ^ 2 := by simp [subsetSum]
    have hcong : Cong d (subsetSum 6 R) (-1) := by
      unfold Cong
      rw [hs]
      have heq : R + R ^ 2 - (-1) = 1 + R + R ^ 2 := by omega
      rw [heq]
      exact hΦ
    exact coprime_of_cong hcong (by
      change Nat.Coprime ((-1 : Int).natAbs) d
      rw [Int.natAbs_neg, Int.natAbs_one]
      exact Nat.coprime_one_left d)
  | n + 7 =>
    omega

private theorem ratio_root_of_factor {p b : Nat} (hp : 0 < p) (hb : 0 < b) :
    let D := gapFactor p b
    ∃ R : Int,
      Cong D ((3 : Int) ^ b * R) ((2 : Int) ^ p) ∧
      Cong D (1 + R + R ^ 2) 0 ∧
      Nat.Coprime R.natAbs D := by
  intro D
  have hthree : D % 3 ≠ 0 := by
    have := gapFactor_mod_three (p := p) hb
    omega
  obtain ⟨u, hu⟩ := exists_three_inverse hthree
  let x : Int := (2 ^ p : Nat)
  let y : Int := (3 ^ b : Nat)
  let v : Int := u ^ b
  have hv : Cong D (y * v) 1 := by
    have h := hu.pow b
    rwa [Int.mul_pow, Int.one_pow] at h
  let R : Int := x * v
  have hR : Cong D (y * R) x := by
    have h := (Cong.refl D x).mul hv
    simpa [R, Int.mul_left_comm, Int.mul_comm, Int.mul_assoc] using h
  have hsum : x ^ 2 + x * y + y ^ 2 = (D : Int) := by
    simp only [x, y]
    have hs2 : ((2 ^ p : Nat) : Int) ^ 2 = ((2 ^ (2 * p) : Nat) : Int) := by
      rw [← Int.natCast_pow, pow_sq]
    have hs3 : ((3 ^ b : Nat) : Int) ^ 2 = ((3 ^ (2 * b) : Nat) : Int) := by
      rw [← Int.natCast_pow, pow_sq]
    rw [hs2, hs3]
    simp [D, gapFactor, Int.natCast_add, Int.natCast_mul]
  have hzero : Cong D (x ^ 2 + x * y + y ^ 2) 0 := by
    unfold Cong
    rw [hsum]
    exact ⟨1, by simp⟩
  have hscaled : Cong D (v ^ 2 * (x ^ 2 + x * y + y ^ 2)) 0 := by
    have h := (Cong.refl D (v ^ 2)).mul hzero
    simpa using h
  have hid : v ^ 2 * (x ^ 2 + x * y + y ^ 2) = R ^ 2 + R * (y * v) + (y * v) ^ 2 := by
    dsimp [R]
    grind
  have hroot : Cong D (R ^ 2 + R * (y * v) + (y * v) ^ 2) (R ^ 2 + R * 1 + 1 ^ 2) := by
    exact ((Cong.refl D (R ^ 2)).add ((Cong.refl D R).mul hv)).add (hv.pow 2)
  have hΦ : Cong D (1 + R + R ^ 2) 0 := by
    have h0 : Cong D (R ^ 2 + R * (y * v) + (y * v) ^ 2) 0 := by simpa [hid] using hscaled
    have hperm : R ^ 2 + R * 1 + 1 ^ 2 = 1 + R + R ^ 2 := by omega
    rw [← hperm]
    exact (hroot.symm).trans h0
  have hcopR : Nat.Coprime R.natAbs D := by
    have ha : D.Coprime (2 ^ p) := (gapFactor_coprime_two (b := b) hp).pow_right p
    exact coprime_of_linear ha hR
  exact ⟨R, hR, hΦ, hcopR⟩

/-- All arithmetic consequences of a three-copy power gap with positive odd count. -/
theorem triple_copy_data {p b : Nat} (hb : 0 < b) (hgap : 3 ^ (3 * b) < 2 ^ (3 * p)) :
    let D := gapFactor p b
    0 < p ∧ 3 ^ b < 2 ^ p ∧ 2 ^ (2 * p) ≤ D ∧ (2 ^ p - 3 ^ b) * D = 2 ^ (3 * p) - 3 ^ (3 * b) ∧
      D.Coprime 6 ∧
      ∃ R : Int,
        (D : Int) ∣ (3 : Int) ^ b * R - (2 : Int) ^ p ∧
        (D : Int) ∣ 1 + R + R ^ 2 ∧
        (D : Int) ∣ R ^ 3 - 1 ∧
        ¬ (D : Int) ∣ R - 1 ∧
        Nat.Coprime R.natAbs D ∧
        (∀ mask, mask ≠ 0 → mask < 7 → Nat.Coprime (subsetSum mask R).natAbs D) ∧
        (∀ n, (D : Int) ∣ R ^ n - ((basis (n % 3)).1 + (basis (n % 3)).2 * R)) ∧
        (∀ n, (basis n).1.gcd (basis n).2 = 1) := by
  let D := gapFactor p b
  have hroot : 3 ^ b < 2 ^ p := root_lt_of_cube_lt hgap
  have hp : 0 < p := by
    cases p with
    | zero => simp at hroot
    | succ p => exact Nat.succ_pos p
  have hfac := factor_mul (Nat.le_of_lt hroot)
  have hsix := gapFactor_coprime_six hp hb
  obtain ⟨R, hR, hΦ, hcop⟩ := ratio_root_of_factor (p := p) (b := b) hp hb
  have hΦd : (D : Int) ∣ 1 + R + R ^ 2 := by
    simpa [Cong] using hΦ
  have hthree : D.Coprime 3 := by
    have hmul : D.Coprime (2 * 3) := by
      have h6 : 2 * 3 = 6 := by decide
      simpa [D, h6] using hsix
    exact (Nat.coprime_mul_iff_right.mp hmul).2
  have horder : ¬ (D : Int) ∣ R - 1 := by
    intro h1
    have hd : D = 1 := trivial_of_fixed_root hΦd h1 hthree
    have hbig : 1 < D := by
      have hpow : 2 ≤ 2 ^ (2 * p) := by
        have hone : 1 ≤ 2 * p := by omega
        exact Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hone)
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hpow (gapFactor_ge p b))
    omega
  exact ⟨hp, hroot, gapFactor_ge p b, hfac, hsix, R, by simpa [Cong] using hR, hΦd,
    cube_divides hΦd, horder, hcop, fun mask h0 h7 => subsetSum_coprime hΦd hcop h0 h7,
    fun n => by
      have hpow := divides_power hΦd n
      rwa [basis_mod_three n] at hpow,
    basis_gcd⟩
