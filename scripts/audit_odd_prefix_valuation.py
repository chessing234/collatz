"""Exhaustive short fibers and long odd-prefix compression examples."""

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
        length = 3 * max(evens - 1, 0)
        if length <= depth:
            assert parity_run(smaller, overhead + length)[0] == parity_run(source, length)[0]
            compressed += 1
        checked += 1
    return checked, compressed


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
    print(f"{exclusions:,} fibers, {meetings:,} smaller meetings and "
          f"{compressed:,} compressed meetings checked.")
