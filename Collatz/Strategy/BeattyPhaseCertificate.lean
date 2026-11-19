import Collatz.Strategy.RealizableBound

/-! Exact finite data for the uniform Beatty phase-block bound. -/

namespace Collatz.BeattyPhaseCertificate

open RealizableBound

def bucketWeight (D z i : Nat) : Nat :=
  let A := 3 ^ i
  let P := 2 ^ A.log2
  if (z - 1) * (2 * P) < D * A then 2 * P else P

def bucketSum (D z : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => 3 * bucketSum D z i + bucketWeight D z i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem bucket_certificate :
    (List.range 513).all (fun z =>
      decide (10000 * z * bucketSum 512 z 53 ≤ 512 * (2431 * 53) * 3 ^ 53)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem tail_certificate :
    (List.range 53).all (fun r => decide (10000 * Bcap r ≤ (2431 * r + 1500) * 3 ^ r)) = true := by
  decide +kernel

end Collatz.BeattyPhaseCertificate
