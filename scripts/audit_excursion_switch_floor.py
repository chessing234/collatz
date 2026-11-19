#!/usr/bin/env python3
"""Check the coordinate-switching certificate using exact rational arithmetic."""

from collections import Counter
from fractions import Fraction

from audit_excursion_crossing import next_excursion


def transition(n, a, b, power_two, source, target):
    offset = max(0, a * (1 - source) + b * target - power_two)
    departure = Fraction(a * (n + source) + offset, a * (n + target))
    arrival_denominator = b * (n + target) - offset
    if arrival_denominator <= 0:
        return departure
    return min(departure, Fraction(b * (n + source), arrival_denominator))


def first_crossing(n):
    x, a, b = n, 1, 1
    fixed = best = (Fraction(1), Fraction(1))
    descended = False
    for _ in range(100):
        x, v, w = next_excursion(x)
        descended |= x < n
        step_a, step_b = 3**v, 2**(v + w)
        a *= step_a
        b *= step_b
        factors = tuple(
            tuple(transition(n, step_a, step_b, 2**v, s, t) for t in (0, 1))
            for s in (0, 1)
        )
        fixed = tuple(fixed[t] * factors[t][t] for t in (0, 1))
        best = tuple(min(best[s] * factors[s][t] for s in (0, 1)) for t in (0, 1))
        assert all(best[t] <= fixed[t] for t in (0, 1))
        if b > a:
            ratio = Fraction(b, a)
            certificates = (ratio > fixed[0], ratio > fixed[1], ratio > min(best))
            assert not any(certificates) or descended
            return certificates
    raise AssertionError(f"no coefficient crossing for {n}")


def main():
    counts = Counter(first_crossing(n) for n in range(3, 20_000, 2))
    assert counts == {(True, True, True): 9_997, (False, False, True): 2}
    assert first_crossing(27) == first_crossing(63) == (False, False, True)
    assert first_crossing(1) == (False, False, False)
    print("Coordinate switching certified all 9,999 first crossings.")
    print("Either fixed coordinate certified 9,997, missing 27 and 63.")


if __name__ == "__main__":
    main()
