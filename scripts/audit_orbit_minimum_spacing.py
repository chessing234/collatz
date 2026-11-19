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


def audit_coefficient_gaps(limit=2_000, horizon=48):
    checked = exact = 0
    for start in range(1, limit):
        states, odd_counts, floors = [start], [0], [start]
        for k in range(1, horizon + 1):
            odd = states[-1] % 2
            value = (3 * states[-1] + 1) // 2 if odd else states[-1] // 2
            states.append(value)
            odd_counts.append(odd_counts[-1] + odd)
            floors.append(start * 3**odd_counts[-1] // 2**k)
        for i in range(horizon):
            for j in range(i + 1, horizon + 1):
                gap = floors[j] - floors[i]
                if gap > 0:
                    a, b = 3**(odd_counts[j] - odd_counts[i]), 2**(j - i)
                    assert b < a
                    assert (states[i] + gap) * b < (states[i] + 1) * a
                    assert states[i] + gap <= states[j]
                    checked += 1
                    exact += states[i] + gap == states[j]
    assert exact > 0
    print(f"Checked {checked:,} positive coefficient-floor gaps, including {exact:,} exact value gaps.")


if __name__ == "__main__":
    audit()
    audit_coefficient_gaps()
