import Collatz.Strategy.ExcursionCanonicalArithmetic

open Collatz.ExcursionBudget Collatz.ExcursionRays

def unitProfile : List Run := [⟨1, 1⟩]
def highLandingProfile : List Run :=
  [⟨1, 2⟩, ⟨4, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨5, 1⟩, ⟨1, 3⟩]

example : canonicalSource unitProfile = 1 ∧
    canonicalLanding unitProfile = 1 ∧ failureCutoff unitProfile = 1 := by decide +kernel

example : canonicalSource highLandingProfile = 165 ∧
    canonicalLanding highLandingProfile = 167 ∧ failureCutoff highLandingProfile = 217 := by
  decide +kernel

example : firstCrossingFailure highLandingProfile = false := by decide +kernel

#print axioms trace_of_affine
#print axioms canonical_trace_of_positive_profile
#print axioms firstCrossingFailure_spec
#print axioms collatz_of_coverage_and_canonical_offset
