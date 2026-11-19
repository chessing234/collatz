#!/usr/bin/env python3
"""Audit the phase-grid bound and its exceptional-crossing comparisons."""

from fractions import Fraction

from audit_excursion_inverse_gap import log_bounds, log_gap


SCALE, CHARGE, CREDIT = 10_000, 2_431, 1_500
WIDTH, GRID = 53, 512
FLOOR, ALLOWANCE = 2**71, 4_504_940_378
SOURCE_CAP = 3_178_644_722_122_268_046_850
ODD, TIME = 72_057_431_991, 114_208_327_604


def powers(count: int) -> tuple[list[int], list[int]]:
    ternary = [3**i for i in range(count)]
    binary = [1 << (a.bit_length() - 1) for a in ternary]
    return ternary, binary


def bucket_weight(phase: int, i: int) -> int:
    ternary = 3**i
    binary = 1 << (ternary.bit_length() - 1)
    return binary * (2 if (phase - 1) * 2 * binary < GRID * ternary else 1)


def audit_blocks() -> None:
    for phase in range(GRID + 1):
        block = sum(3 ** (WIDTH - 1 - i) * bucket_weight(phase, i) for i in range(WIDTH))
        assert SCALE * phase * block <= GRID * CHARGE * WIDTH * 3**WIDTH
    ternary, binary = powers(20_054)
    accumulator = 0
    for a in range(20_001):
        assert SCALE * accumulator <= (CHARGE * a + CREDIT) * ternary[a]
        if a % 37 == 0:
            phase = (GRID * binary[a] - 1) // ternary[a] + 1
            assert 1 <= phase <= GRID
            for i in range(WIDTH):
                assert binary[a + i] <= binary[a] * bucket_weight(phase, i)
        accumulator = 3 * accumulator + binary[a]


def audit_large_comparisons() -> None:
    gap_lo, gap_hi = log_gap(ODD, TIME)
    total_charge = CHARGE * ODD + CREDIT
    allowance_ratio = Fraction(SCALE * FLOOR + total_charge, SCALE * (FLOOR + ALLOWANCE))
    assert gap_hi + log_bounds(allowance_ratio, 4)[1] < 0
    previous_ratio = Fraction(SCALE * FLOOR + total_charge, SCALE * (FLOOR + ALLOWANCE - 1))
    assert 0 < gap_lo + log_bounds(previous_ratio, 4)[0]
    source_ratio = Fraction(SCALE * SOURCE_CAP + total_charge, SCALE * SOURCE_CAP)
    assert gap_hi + log_bounds(source_ratio, 4)[1] < 0
    previous_source = Fraction(SCALE * (SOURCE_CAP - 1) + total_charge, SCALE * (SOURCE_CAP - 1))
    assert 0 < gap_lo + log_bounds(previous_source, 4)[0]
    allowance_lo, allowance_hi = log_bounds(Fraction(FLOOR + ALLOWANCE, FLOOR), 4)
    assert allowance_hi < log_gap(478_054_749_257, 757_698_850_864)[0]
    next_lo, next_hi = log_gap(615_582_794_569, 975_675_645_481)
    assert 0 < next_lo <= next_hi < allowance_lo


if __name__ == "__main__":
    audit_blocks()
    audit_large_comparisons()
    print("Checked 513 phase buckets, 20,001 exact accumulators and the large-power comparisons.")
