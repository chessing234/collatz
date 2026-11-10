#!/usr/bin/env python3
"""Check the finite gap implication on independently generated excursions."""


def audit(limit=100_000, max_excursions=24):
    checked = 0
    longest = 0
    for start in range(3, limit, 2):
        state = start
        smallest = None
        odd_coefficient = dyadic_coefficient = 1
        heavy = True
        for runs in range(1, max_excursions + 1):
            while state % 2:
                odd_coefficient *= 3
                dyadic_coefficient *= 2
                state = (3 * state + 1) // 2
                heavy &= dyadic_coefficient <= odd_coefficient
                smallest = state if smallest is None else min(smallest, state)
            while state % 2 == 0:
                dyadic_coefficient *= 2
                state //= 2
                heavy &= dyadic_coefficient <= odd_coefficient
                smallest = min(smallest, state)
            if smallest < start + runs:
                break
            assert heavy, (start, runs, smallest)
            checked += 1
            longest = max(longest, runs)
    assert checked > 0 and longest > 1
    print(f"Checked {checked:,} genuine prefixes with the required gap, up to {longest} excursions.")


if __name__ == "__main__":
    audit()
