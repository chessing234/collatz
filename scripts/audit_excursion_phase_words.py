#!/usr/bin/env python3
"""Use rational phase intervals to check the pruned corridor language."""

from fractions import Fraction

from audit_excursion_boundary_cone import EXPECTED
from audit_excursion_inverse_gap import log_bounds, log_gap


SOURCE_BOUND = 204_661_442_731_210_757_479_531


def valuation_two(value: int) -> int:
    return (value & -value).bit_length() - 1


def excursion(source: int) -> tuple[int, int, int]:
    odd_steps = valuation_two(source + 1)
    peak = 3**odd_steps * ((source + 1) >> odd_steps) - 1
    halvings = valuation_two(peak)
    return odd_steps, halvings, peak >> halvings


def corridor_languages() -> list[set[tuple[int, ...]]]:
    states = [(Fraction(2, 3), Fraction(1), 1, 1, 0, ())]
    languages = [{()}]
    for depth in range(1, 31):
        next_states = []
        for lo, hi, a, b, c, word in states:
            for v in (1, 2):
                new_a, new_b = 3**v * a, 2 ** (v + 1) * b
                new_c = 3**v * c + b * (3**v - 2**v)
                lower = max(lo, Fraction(2 * new_a, 3 * new_b))
                upper = min(hi, Fraction(new_a, new_b))
                if lower < upper:
                    next_states.append((lower, upper, new_a, new_b, new_c, word + (v,)))
        states = next_states
        assert len(states) == depth + 1
        languages.append({state[-1] for state in states})

    sources = []
    for lo, hi, a, b, c, word in states:
        source = ((b - c) * pow(a, -1, 2 * b)) % (2 * b)
        sources.append(source)
        phase = (lo + hi) / 2
        current = source
        prefix_a, prefix_b = 1, 1
        for expected_v in word:
            v, w, current = excursion(current)
            assert (v, w) == (expected_v, 1)
            prefix_a *= 3**v
            prefix_b *= 2 ** (v + w)
            assert Fraction(2, 3) < phase * prefix_b / prefix_a <= 1
        assert a * source + c == b * current and current % 2 == 1
    assert min(sources) == SOURCE_BOUND
    return languages


def audit_small_orbits(languages: list[set[tuple[int, ...]]]) -> None:
    longest = (0, 0)
    for source in range(3, 200_000, 2):
        current, a, b, word = source, 1, 1, ()
        lo, hi = Fraction(2, 3), Fraction(1)
        for depth in range(1, 31):
            v, w, current = excursion(current)
            if w != 1 or v not in (1, 2):
                break
            a *= 3**v
            b *= 2 ** (v + 1)
            lo, hi = max(lo, Fraction(2 * a, 3 * b)), min(hi, Fraction(a, b))
            if lo >= hi:
                break
            word += (v,)
            assert word in languages[depth]
            longest = max(longest, (depth, source))
        assert len(word) < 30
    print(f"Checked 99,999 real sources. Longest initial corridor was {longest}.")


def audit_boundary_cap() -> None:
    cap = 2**75
    for odd, time in EXPECTED:
        charge = 2431 * odd + 1500
        ratio = Fraction(10_000 * cap + charge, 10_000 * cap)
        assert log_gap(odd, time)[1] + log_bounds(ratio, 4)[1] < 0
    assert 3 * (cap + 325_000_000_000) < 2 * SOURCE_BOUND


if __name__ == "__main__":
    audit_small_orbits(corridor_languages())
    audit_boundary_cap()
    print("Checked all 31 phase words, their genuine realizations and the eight-pair cap.")
