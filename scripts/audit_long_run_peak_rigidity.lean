import Collatz.Strategy.LongRunPeakRigidity

open Collatz Collatz.BoundedEvenDefect Collatz.PeakSuffixTable Collatz.LongRunPeakRigidity

example : ∃ p, ∀ x j, j - 2 ≤ oddCount x j → p ≤ oddCount x j →
    ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + 7 :=
  excludes_displacement 2 7 (by decide)

#guard shorterPeakCheck 8 (10 ^ 18 + 31) 1
#guard !shorterPeakCheck 8 65 1
#guard requiredRunLength 8 43 17 == 42
#guard shorterPeakCheck 8 43 17
#guard requiredRunLength 8 24 223 == 22
#guard !shorterPeakCheck 8 24 223

#print axioms last_even
#print axioms avoids_bounded_integer
#print axioms avoids_nonzero_integer
#print axioms excludes_displacement
#print axioms inverse_peak_transport
#print axioms prefix_image_lt
#print axioms scaled_peak_at_cutoff
#print axioms scaled_peak_at_adaptive_cutoff
#print axioms scaled_peak_of_smaller_mate
#print axioms smaller_iff_scaled_peak
#print axioms PeakContraction.certificate_of_large_meeting
#print axioms threePowMod_eq
#print axioms smaller_iff_shorterPeakCheck
#print axioms shorterPeakCheck_correct
