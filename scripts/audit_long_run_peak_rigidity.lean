import Collatz.Strategy.LongRunPeakRigidity

open Collatz Collatz.BoundedEvenDefect Collatz.PeakSuffixTable Collatz.LongRunPeakRigidity

example : ∃ p, ∀ x j, j - 2 ≤ oddCount x j → p ≤ oddCount x j →
    ¬ (3 : Int) ^ p ∣ (acceleratedOrbit j x : Int) + 7 :=
  excludes_displacement 2 7 (by decide)

#print axioms last_even
#print axioms avoids_nonzero_integer
#print axioms excludes_displacement
#print axioms inverse_peak_transport
#print axioms prefix_image_lt
#print axioms scaled_peak_of_smaller_mate
#print axioms smaller_iff_scaled_peak
