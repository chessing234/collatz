import Collatz.Strategy.ForbiddenParity
import Collatz.Strategy.OrbitCapacity

open Collatz Collatz.OrbitCapacity

example : acceleratedOrbit 5 31 = 242 ∧ acceleratedOrbit 5 31 < 3 ^ oddCount 31 5 :=
  ⟨by decide, by simpa using image_lt (c := 1) (k := 5) (x := 31) (by decide)⟩

example : acceleratedOrbit 5 63 = 485 ∧ acceleratedOrbit 5 63 < 2 * 3 ^ oddCount 63 5 :=
  ⟨by decide, image_lt (c := 2) (k := 5) (x := 63) (by decide)⟩

private theorem trivialCycleAvoids : ∀ k, acceleratedOrbit k 1 % 2 ^ 2 ≠ 0
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    rw [← acceleratedOrbit_add k 2]
    simpa only [show acceleratedOrbit 2 1 = 1 by decide] using trivialCycleAvoids k

example : ForbiddenParity.Avoids 2 0 1 := trivialCycleAvoids

#print axioms ForbiddenParity.count
#print axioms ForbiddenParity.capacity
#print axioms occupation
#print axioms orbit_envelope
#print axioms multiplier_escapes
