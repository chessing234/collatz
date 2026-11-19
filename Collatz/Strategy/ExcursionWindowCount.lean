import Collatz.Strategy.ExcursionRays
import Collatz.Core.Pigeonhole

/-!
# Dispersion of excursion windows over a finite alphabet

A boundary is coded by its past and future excursion symbols. Equal codes
force equality of the boundary values when both are below their joint
period. Pigeonholing therefore converts a restriction on the alphabet into
a lower bound on the size of a family of distinct boundary values.
-/

namespace Collatz.ExcursionWindowCount

open Collatz.ExcursionBudget Collatz.ExcursionRays

private def encode {K : Nat} : List (Fin K) → Nat
  | [] => 0
  | d :: ds => d.val + K * encode ds

private theorem encode_lt {K : Nat} (digits : List (Fin K)) :
    encode digits < K ^ digits.length := by
  induction digits with
  | nil => simp [encode]
  | cons d ds ih =>
    have hd : d.val < K := d.isLt
    calc
      encode (d :: ds) = d.val + K * encode ds := rfl
      _ < K + K * encode ds := Nat.add_lt_add_right hd _
      _ = K * (encode ds + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ K * K ^ ds.length := Nat.mul_le_mul_left K (Nat.succ_le_of_lt ih)
      _ = K ^ (d :: ds).length := by simp [Nat.pow_succ, Nat.mul_comm]

private theorem encode_injective_at_length {K : Nat} {xs ys : List (Fin K)}
    (hlen : xs.length = ys.length) (heq : encode xs = encode ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hmod := congrArg (· % K) heq
      simp only [encode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt,
        Nat.mod_eq_of_lt b.isLt] at hmod
      have hab : a = b := Fin.eq_of_val_eq hmod
      subst b
      have htail : K * encode xs = K * encode ys := by
        simp only [encode] at heq
        omega
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
      rw [ih hlen' (Nat.eq_of_mul_eq_mul_left hK htail)]

/-- A cut and its two local excursion profiles, coded in a finite alphabet. -/
structure Window {K : Nat} (alphabet : Fin K → Run) where
  left : Nat
  value : Nat
  right : Nat
  past : List (Fin K)
  future : List (Fin K)
  pastTrace : Trace left value (past.map alphabet)
  futureTrace : Trace value right (future.map alphabet)

def Window.period {K : Nat} {alphabet : Fin K → Run} (w : Window alphabet) : Nat :=
  (2 ^ time (w.future.map alphabet) * 2) * 3 ^ ExcursionBudget.oddCount (w.past.map alphabet)

private theorem equal_of_small_matching_windows {K : Nat} {alphabet : Fin K → Run}
    {a b : Window alphabet} (hp : a.past = b.past) (hf : a.future = b.future)
    (hne : a.future ≠ []) (ha : a.value < a.period) (hb : b.value < b.period) :
    a.value = b.value := by
  cases a with
  | mk al x ar past future hpx hfx =>
    cases b with
    | mk bl y br bpast bfuture hpy hfy =>
      dsimp at hp hf hne
      subst bpast
      subst bfuture
      cases future with
      | nil => exact (hne rfl).elim
      | cons d ds =>
        simp only [Window.period, List.map_cons] at ha hb
        have hd := repeated_window_dvd_difference hpx hpy hfx hfy
        have hd' := repeated_window_dvd_difference hpy hpx hfy hfx
        have h1 := Nat.eq_zero_of_dvd_of_lt hd (by omega : y - x < _)
        have h2 := Nat.eq_zero_of_dvd_of_lt hd' (by omega : x - y < _)
        change x = y
        omega

/-- If more than `K^(p+q)` cuts fit below their periods, some two cuts
have the same value. -/
theorem repeat_of_small_windows {K p q N : Nat} {alphabet : Fin K → Run}
    (samples : Nat → Window alphabet) (hq : 0 < q) (hN : K ^ (p + q) ≤ N)
    (hshape : ∀ i ≤ N, (samples i).past.length = p ∧ (samples i).future.length = q)
    (hsmall : ∀ i ≤ N, (samples i).value < (samples i).period) :
    ∃ i j : Nat, i < j ∧ j ≤ N ∧ (samples i).value = (samples j).value := by
  let code := fun i => encode ((samples i).past ++ (samples i).future)
  have hcode : ∀ i ≤ N, code i < K ^ (p + q) := by
    intro i hi
    have h := encode_lt ((samples i).past ++ (samples i).future)
    simpa only [code, List.length_append, (hshape i hi).1, (hshape i hi).2] using h
  obtain ⟨i, j, hij, hj, heq⟩ := Collatz.Pigeonhole.exists_repeat hcode hN
  have hi : i ≤ N := by omega
  have hpi := (hshape i hi).1
  have hpj := (hshape j hj).1
  have hfi := (hshape i hi).2
  have hfj := (hshape j hj).2
  have hwords : (samples i).past ++ (samples i).future =
      (samples j).past ++ (samples j).future :=
    encode_injective_at_length (by simp [hpi, hpj, hfi, hfj]) heq
  have hp : (samples i).past = (samples j).past := by
    have ht := congrArg (List.take p) hwords
    rw [← hpi] at ht
    have hh : (samples i).past.length = (samples j).past.length := hpi.trans hpj.symm
    conv at ht => rhs; rw [hh]
    simpa using ht
  have hf : (samples i).future = (samples j).future := by
    rw [hp] at hwords
    exact List.append_cancel_left hwords
  have hne : (samples i).future ≠ [] := by
    intro hnil
    rw [hnil] at hfi
    simp at hfi
    omega
  exact ⟨i, j, hij, hj, equal_of_small_matching_windows hp hf hne (hsmall i hi) (hsmall j hj)⟩

private theorem time_lower {K steps : Nat} (alphabet : Fin K → Run)
    (h : ∀ a, steps ≤ (alphabet a).oddSteps + (alphabet a).halvings) (ds : List (Fin K)) :
    ds.length * steps ≤ time (ds.map alphabet) := by
  induction ds with
  | nil => simp [time]
  | cons d ds ih =>
    have hd := h d
    simp only [List.length_cons, List.map_cons, time, Nat.add_mul, Nat.one_mul]
    omega

private theorem odd_lower {K odd : Nat} (alphabet : Fin K → Run)
    (h : ∀ a, odd ≤ (alphabet a).oddSteps) (ds : List (Fin K)) :
    ds.length * odd ≤ ExcursionBudget.oddCount (ds.map alphabet) := by
  induction ds with
  | nil => simp [ExcursionBudget.oddCount]
  | cons d ds ih =>
    have hd := h d
    simp only [List.length_cons, List.map_cons, ExcursionBudget.oddCount, Nat.add_mul, Nat.one_mul]
    omega

/-- A finite-alphabet family of distinct cuts must contain a large value.
The bound uses the minimum odd count in the past and minimum elapsed time
in the future. -/
theorem large_of_distinct_windows {K p q N odd steps : Nat} {alphabet : Fin K → Run}
    (samples : Nat → Window alphabet) (hq : 0 < q) (hN : K ^ (p + q) ≤ N)
    (hshape : ∀ i ≤ N, (samples i).past.length = p ∧ (samples i).future.length = q)
    (hodd : ∀ a, odd ≤ (alphabet a).oddSteps)
    (hsteps : ∀ a, steps ≤ (alphabet a).oddSteps + (alphabet a).halvings)
    (hdistinct : ∀ i j, i < j → j ≤ N → (samples i).value ≠ (samples j).value) :
    ∃ i ≤ N, (2 ^ (q * steps) * 2) * 3 ^ (p * odd) ≤ (samples i).value := by
  apply Classical.byContradiction
  intro hno
  have hsmall : ∀ i ≤ N, (samples i).value < (samples i).period := by
    intro i hi
    have hupper : (samples i).value < (2 ^ (q * steps) * 2) * 3 ^ (p * odd) :=
      Nat.lt_of_not_ge (fun h => hno ⟨i, hi, h⟩)
    have ht := time_lower alphabet hsteps (samples i).future
    have hv := odd_lower alphabet hodd (samples i).past
    rw [(hshape i hi).2] at ht
    rw [(hshape i hi).1] at hv
    have hperiod : (2 ^ (q * steps) * 2) * 3 ^ (p * odd) ≤ (samples i).period :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by decide) ht))
        (Nat.pow_le_pow_right (by decide) hv)
    exact Nat.lt_of_lt_of_le hupper hperiod
  obtain ⟨i, j, hij, hj, heq⟩ := repeat_of_small_windows samples hq hN hshape hsmall
  exact hdistinct i j hij hj heq

end Collatz.ExcursionWindowCount
