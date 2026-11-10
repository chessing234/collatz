#!/usr/bin/env python3
"""Check the inverse gap with rational logarithm bounds and direct orbits."""

from fractions import Fraction
from functools import cache


FLOOR = 2**71
ALLOWANCE = 6_443_285_299
ODD, TIME = 72_057_431_991, 114_208_327_604
LOWER_TIME, LOWER_ODD = 539_722_056_247, 340_526_703_945
UPPER_TIME, UPPER_ODD = 217_976_794_617, 137_528_045_312


@cache
def log_bounds(value: Fraction, terms: int) -> tuple[Fraction, Fraction]:
    """Bound log(value) for value >= 1 by the series for twice atanh."""
    z = (value - 1) / (value + 1)
    square = z * z
    term = z
    lower = Fraction(0)
    for j in range(terms):
        lower += 2 * term / (2 * j + 1)
        term *= square
    remainder = 2 * term / ((2 * terms + 1) * (1 - square))
    return lower, lower + remainder


def log_gap(odd: int, time: int) -> tuple[Fraction, Fraction]:
    lo2, hi2 = log_bounds(Fraction(2), 90)
    lo3, hi3 = log_bounds(Fraction(3), 90)
    return odd * lo3 - time * hi2, odd * hi3 - time * lo2


def audit_comparisons() -> None:
    assert LOWER_ODD * UPPER_TIME - UPPER_ODD * LOWER_TIME == 1
    assert log_gap(UPPER_ODD, UPPER_TIME)[1] < 0
    allowance_lo, allowance_hi = log_bounds(Fraction(FLOOR + ALLOWANCE, FLOOR), 4)
    assert allowance_hi < log_gap(LOWER_ODD, LOWER_TIME)[0]
    next_odd, next_time = LOWER_ODD + UPPER_ODD, LOWER_TIME + UPPER_TIME
    next_lo, next_hi = log_gap(next_odd, next_time)
    assert next_odd == 478_054_749_257 and 0 < next_lo <= next_hi < allowance_lo

    charge = 81 * ODD + 24
    lo, hi = log_gap(ODD, TIME)
    bound = Fraction(300 * FLOOR + charge, 300 * (FLOOR + ALLOWANCE))
    assert hi + log_bounds(bound, 4)[1] < 0
    previous_bound = Fraction(300 * FLOOR + charge, 300 * (FLOOR + ALLOWANCE - 1))
    assert 0 < lo + log_bounds(previous_bound, 4)[0]

    power = 1
    for _ in range(1, 5_000):
        power *= 3
        largest_lower_power = 1 << (power.bit_length() - 1)
        assert (FLOOR + ALLOWANCE) * largest_lower_power <= FLOOR * power


def audit_inverse_words() -> None:
    for residue, word in ((4, (2, 1)), (10, (2, 2, 1, 1))):
        modulus = 3 ** len(word)
        first = FLOOR + (residue - FLOOR) % modulus
        if first % 2 == 0:
            first += modulus
        for index in range(100):
            landing = first + 2 * modulus * index + 2 * modulus * ALLOWANCE * index**2
            ancestor = landing
            for exponent in word:
                ancestor, remainder = divmod((ancestor << exponent) - 1, 3)
                assert remainder == 0 and ancestor % 2 == 1
            orbit = ancestor
            for _ in range(sum(word)):
                orbit = (3 * orbit + 1) // 2 if orbit % 2 else orbit // 2
            assert orbit == landing
            assert 0 < ancestor < max(FLOOR, landing - ALLOWANCE + 1)


if __name__ == "__main__":
    audit_comparisons()
    audit_inverse_words()
    print("Checked rational gap bounds, 4,999 exact exponent gaps and 200 inverse orbits.")
