#!/usr/bin/env python3
"""Check the excursion budgets against direct accelerated iteration."""

from collections import Counter


RATIOS = ((3, 2), (2, 1), (3, 1))
MAX_START = 199_999
MAX_EXCURSIONS = 100


def next_excursion(x):
    odd_steps = 0
    while x % 2:
        x = (3 * x + 1) // 2
        odd_steps += 1
    halvings = 0
    while x % 2 == 0:
        x //= 2
        halvings += 1
    return x, odd_steps, halvings


def first_crossings(n):
    pending = set(RATIOS)
    crossings = {}
    x, a, b, offset, cost = n, 1, 1, 0, 0
    for k in range(1, MAX_EXCURSIONS + 1):
        x, v, w = next_excursion(x)
        multiplier = 3**v
        a *= multiplier
        b <<= v + w
        offset = multiplier * offset + b - (b >> w)
        cost += 1 if w == 1 else 2
        assert b * (x + 1) == a * (n + 1) + offset
        for p, q in tuple(pending):
            if q * b <= p * a:
                assert 2 * q * offset <= p * a * cost
                continue
            assert 2 * offset <= b * cost
            funded = p * cost + 2 * q * (n + 1) <= 2 * p * (n + 1)
            if funded:
                assert x < n
            crossings[p, q] = (k, x, cost, funded)
            pending.remove((p, q))
        if not pending:
            break
    return crossings


def main():
    assert first_crossings(1)[2, 1] == (3, 1, 3, False)
    assert first_crossings(27)[2, 1] == (16, 5, 22, True)
    assert first_crossings(47)[2, 1] == (14, 23, 19, True)
    counted = Counter()
    funded = Counter()
    discounted = Counter()
    longest_doubling = 0
    for n in range(3, MAX_START + 1, 2):
        for (p, q), (k, _, cost, paid) in first_crossings(n).items():
            counted[p, q] += 1
            funded[p, q] += paid
            discounted[p, q] += paid and p * (2 * k) > 2 * (p - q) * (n + 1)
            if (p, q) == (2, 1):
                longest_doubling = max(longest_doubling, k)
    assert all(counted[ratio] == (MAX_START - 1) // 2 for ratio in RATIOS)
    assert longest_doubling == 33
    for p, q in RATIOS:
        print(f"{p}/{q}: {counted[p, q]} crossings, {funded[p, q]} funded, "
              f"{discounted[p, q]} funded only after discount")
    print(f"Longest factor-two crossing in the scan: {longest_doubling} excursions")


if __name__ == "__main__":
    main()
