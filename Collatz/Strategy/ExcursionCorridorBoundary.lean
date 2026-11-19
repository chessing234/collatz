import Collatz.Strategy.ExcursionBoundaryCap
import Collatz.Strategy.ExcursionPhaseWords

/-! The phase-uniform source barrier inside any surviving boundary trace. -/

namespace Collatz.ExcursionBudget

private theorem proper_of_append {later earlier : List Run}
    (h : ProperPrefixBound 1 1 (later ++ earlier)) : ProperPrefixBound 1 1 earlier := by
  induction later with
  | nil => exact h
  | cons r rs ih => exact ih h.2

/-- A failed first crossing in the eight-pair range contains no
thirty-run balanced corridor, at any phase or position. -/
theorem Trace.first_crossing_failure_no_long_corridor {n e : Nat}
    {later block earlier : List Run} (h : Trace n e (later ++ block ++ earlier))
    (hproper : ProperPrefixBound 1 1 (later ++ block ++ earlier))
    (hcross : 3 ^ oddCount (later ++ block ++ earlier) < 2 ^ time (later ++ block ++ earlier))
    (hbound : oddCount (later ++ block ++ earlier) < 325000000000)
    (hlarge : 2 ^ 71 ≤ n) (hkeep : n ≤ e)
    (hc : ExcursionPhaseWords.Corridor (2 ^ time earlier) (3 ^ oddCount earlier) block)
    (hshape : ∀ r ∈ block, r = ⟨1, 1⟩ ∨ r = ⟨2, 1⟩) : block.length < 30 := by
  have hn : n < 2 ^ 75 := Nat.lt_of_le_of_lt hkeep
    (h.first_crossing_failure_cap hproper hcross hbound hlarge hkeep)
  have hsplit : Trace n e ((later ++ block) ++ earlier) := by
    simpa only [List.append_assoc] using h
  obtain ⟨x, hpre, hrest⟩ := ExcursionRays.split_trace hsplit
  obtain ⟨y, hblock, _⟩ := ExcursionRays.split_trace hrest
  have hlen := h.length_le_oddCount
  have hshort : earlier.length < 325000000000 := by
    simp only [List.length_append] at hlen
    omega
  exact ExcursionPhaseWords.corridor_length_lt_thirty_after_bounded_prefix hpre
    (proper_of_append (later := later ++ block) (by simpa only [List.append_assoc] using hproper))
    hn hshort hblock hc hshape

end Collatz.ExcursionBudget
