#!/usr/bin/env python3
"""Reconstruct canonical sources independently with Python modular inverses."""

from itertools import product
from random import Random

from audit_excursion_crossing import next_excursion


def check_profile(profile):
    A = B = 1
    C = 0
    for v, w in profile:
        a, b = 3**v, 2**(v + w)
        C = a * C + B * (a - 2**v)
        A *= a
        B *= b
    period = 2 * B
    canonical = (B - C) * pow(A, -1, period) % period
    endpoint = (A * canonical + C) // B
    assert A * canonical + C == B * endpoint
    assert canonical % 2 == endpoint % 2 == 1
    for index in (0, 1, 3):
        start = value = canonical + index * period
        for expected in profile:
            value, v, w = next_excursion(value)
            assert (v, w) == expected
        assert value == endpoint + 2 * A * index
        if A < B:
            assert (start <= value) == (start <= C // (B - A))
    return canonical, endpoint


def audit():
    runs = tuple(product(range(1, 5), repeat=2))
    count = 0
    for length in range(1, 4):
        for profile in product(runs, repeat=length):
            check_profile(profile)
            count += 1
    rng = Random(470923)
    for _ in range(1_000):
        check_profile(tuple(rng.choice(runs) for _ in range(rng.randrange(4, 31))))
        count += 1
    assert check_profile(((1, 3), (5, 1), (1, 1), (2, 1), (3, 1), (4, 1), (1, 2))) == (165, 167)
    print(f"Checked {count:,} legal profiles and three realizations of each.")


if __name__ == "__main__":
    audit()
