import Collatz.Strategy.FasterPeakMates

open Collatz Collatz.FasterPeakMates

#guard fasterPeakCheck 8 95 1 5
#guard !fasterPeakCheck 8 95 1 6
#guard !fasterPeakCheck 8 (10^18 + 31) 1 (10^17)

set_option maxRecDepth 8192 in
example : acceleratedOrbit (90 + 8) (2 ^ 90 * 27 - 1) =
    acceleratedOrbit (95 + 8) (2 ^ 95 - 1) := by decide

#print axioms Collatz.LongRunPeakRigidity.scaled_peak_after_shortened_prefix
#print axioms faster_iff_scaled
#print axioms fasterPeakCheck_correct
