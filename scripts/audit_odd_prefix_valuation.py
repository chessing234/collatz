"""Exhaustive short fibers and long odd-prefix compression examples."""

from itertools import combinations

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


def ternary_valuation(number):
    result = 0
    while number % 3 == 0:
        number //= 3
        result += 1
    return result


def check_meetings(source, depth, overhead):
    endpoint, bits = parity_run(source, depth)
    assert all(bits)
    checked = compressed = 0
    for smaller in inverse_fiber(depth + overhead, endpoint):
        if not 0 < smaller < source:
            continue
        _, competing = parity_run(smaller, depth + overhead)
        odds = sum(competing)
        assert odds > depth + ternary_valuation(source)
        evens = depth + overhead - odds
        if source % 3 == 0:
            assert evens >= 3
            assert overhead >= ternary_valuation(source) + 4
        length = 3 * max(evens - 1, 0)
        if length <= depth:
            assert parity_run(smaller, overhead + length)[0] == parity_run(source, length)[0]
            compressed += 1
        checked += 1
    return checked, compressed


def leading_digit_checks():
    checked = 0
    for length in range(1, 65):
        for even_count in (1, 2):
            for evens in combinations(range(length), even_count):
                defect = sum(
                    2**index * 3 ** (length - index - even_count + order)
                    for order, index in enumerate(evens)
                )
                valuation = ternary_valuation(defect)
                assert valuation < length
                assert (defect // 3**valuation) % 3 == pow(2, length - valuation - 1, 3)
                checked += 1
    return checked


if __name__ == "__main__":
    meetings = compressed = exclusions = 0
    for source in range(3, 1200, 2):
        depth = 1
        while (source + 1) % 2**depth == 0:
            for overhead in range(13):
                count, short = check_meetings(source, depth, overhead)
                meetings += count
                compressed += short
                exclusions += 1
            depth += 1

    for depth in range(6, 25):
        modulus = 2**depth
        index = (-1 - 273) * pow(729, -1, modulus) % modulus
        source = 273 + 729 * (index + 2 * modulus)
        smaller = (512 * source - 537) // 729
        endpoint, bits = parity_run(smaller, depth + 9)
        assert source % 3 == 0 and 0 < smaller < source
        assert endpoint == parity_run(source, depth)[0]
        assert len(bits) - sum(bits) == 3
        assert parity_run(smaller, 15)[0] == parity_run(source, 6)[0]
        meetings += 1
        compressed += 1
    for index in (0, 1, 3, 31, 10**6, 10**30):
        source = 1458 * index + 273
        smaller = 1024 * index + 191
        endpoint, bits = parity_run(smaller, 10)
        assert 0 < smaller < source
        assert source % 3 == 0 and sum(bits) == 7
        assert endpoint == parity_run(source, 1)[0]
    print(f"{exclusions:,} fibers, {meetings:,} smaller meetings and "
          f"{compressed:,} compressed meetings checked.")
    print(f"{leading_digit_checks():,} leading ternary digits with at most two even steps checked.")
