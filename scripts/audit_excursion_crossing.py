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


def analyze(n):
    pending = set(RATIOS)
    crossings = {}
    x, a, b, offset, cost = n, 1, 1, 0, 0
    floor_lower = floor_upper = 1
    first_drop = first_product = None
    for k in range(1, MAX_EXCURSIONS + 1):
        x, v, w = next_excursion(x)
        multiplier = 3**v
        a *= multiplier
        b <<= v + w
        offset = multiplier * offset + b - (b >> w)
        charge = 1 if w == 1 else 2
        cost += charge
        floor_lower *= (2 * n)**charge
        floor_upper *= (2 * n + 1)**charge
        if first_drop is None and x < n:
            first_drop = k
        if first_product is None and a * floor_upper < b * floor_lower:
            assert first_drop is not None
            first_product = k
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
    return crossings, first_drop, first_product


def rounded_certificates(n):
    scales = (1, 2, 4)
    debts = [0] * len(scales)
    x, a, b = n, 1, 1
    for k in range(1, MAX_EXCURSIONS + 1):
        x, v, w = next_excursion(x)
        a *= 3**v
        b <<= v + w
        charge = 1 if w == 1 else 2
        if b > a:
            certified = tuple(
                scale for scale, debt in zip(scales, debts)
                if a * debt + scale * b * charge < 2 * scale * (b - a) * (n + 1)
            )
            assert not certified or x < n
            return k, x, certified
        for i, scale in enumerate(scales):
            numerator = (scale * b + a - 1) // a
            assert scale * b <= a * numerator < scale * b + a
            debts[i] += charge * numerator
    return None


def main():
    assert analyze(1)[0][2, 1] == (3, 1, 3, False)
    assert analyze(27)[0][2, 1] == (16, 5, 22, True)
    assert analyze(47)[0][2, 1] == (14, 23, 19, True)
    counted = Counter()
    funded = Counter()
    discounted = Counter()
    assert analyze(7)[1:] == (2, 2)
    longest_doubling = 0
    earlier_products = exact_products = 0
    rounded_counts = Counter()
    assert rounded_certificates(1) == (1, 1, ())
    assert rounded_certificates(27) == (15, 23, (2, 4))
    assert rounded_certificates(63) == (12, 61, (4,))
    for n in range(3, MAX_START + 1, 2):
        crossings, first_drop, first_product = analyze(n)
        _, _, certificates = rounded_certificates(n)
        rounded_counts.update(certificates)
        for (p, q), (k, _, cost, paid) in crossings.items():
            counted[p, q] += 1
            funded[p, q] += paid
            discounted[p, q] += paid and p * (2 * k) > 2 * (p - q) * (n + 1)
            if (p, q) == (2, 1):
                longest_doubling = max(longest_doubling, k)
                assert first_product is not None and first_product <= k
                earlier_products += first_product < k
                exact_products += first_product == first_drop
    assert all(counted[ratio] == (MAX_START - 1) // 2 for ratio in RATIOS)
    assert longest_doubling == 33
    assert earlier_products == 49_929
    assert exact_products == 99_997
    assert rounded_counts == {1: 99_997, 2: 99_998, 4: 99_999}
    for p, q in RATIOS:
        print(f"{p}/{q}: {counted[p, q]} crossings, {funded[p, q]} funded, "
              f"{discounted[p, q]} funded only after discount")
    print(f"Longest factor-two crossing in the scan: {longest_doubling} excursions")
    print(f"Product bound beat the factor-two crossing for {earlier_products} starts")
    print(f"Product bound detected the first excursion descent for {exact_products} starts")
    for scale in (1, 2, 4):
        print(f"Rounding to units of 1/{scale} certified {rounded_counts[scale]} first crossings")


if __name__ == "__main__":
    main()
