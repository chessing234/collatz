"""Check residual arithmetic, rational separation, and high-valuation fibers."""

from itertools import combinations

from audit_orbit_capacity import parity_run


def defect(length, evens, twos, threes):
    count = len(evens)
    return sum(
        twos[index] * threes[length - index - count + order]
        for order, index in enumerate(evens)
    )


def residual_checks():
    checked = 0
    for denominator in range(11):
        for numerator in range(3**denominator, 3**denominator + 51):
            if denominator and numerator % 2 == 0:
                continue
            odd_run = 0
            while numerator % 3**odd_run == 0:
                quotient = numerator // 3**odd_run
                following = max(denominator - odd_run - 1, 0)
                common = min(denominator, odd_run + 1)
                residual = 2 ** max(odd_run + 1 - denominator, 0) * quotient - 2**following
                assert residual >= 3**following
                assert not following or residual % 2 == 1
                assert 2 ** (odd_run + 1) * quotient == 2**denominator + 2**common * residual
                assert 3**odd_run * residual <= 2 ** (odd_run + 1) * numerator
                checked += 1
                odd_run += 1
    return checked


def separation_checks():
    checked = 0
    for budget in range(5):
        for denominator in range(6):
            for numerator in range(3**denominator, 3**denominator + 12):
                if denominator and numerator % 2 == 0:
                    continue
                precision = 0
                while 2 ** (precision + budget) * numerator >= 3**precision:
                    precision += 1
                for length in range(11):
                    twos = [2**i for i in range(length + 1)]
                    threes = [3**i for i in range(length + 1)]
                    for count in range(min(budget, length) + 1):
                        for evens in combinations(range(length), count):
                            value = defect(length, evens, twos, threes)
                            assert (2**length * numerator - 2**denominator * value) % 3**precision
                            checked += 1
    return checked


def valuation_checks():
    checked = 0
    for evens, valuation in ((3, 1), (3, 19), (3, 26), (4, 27)):
        depth = 3 * (evens - 1)
        modulus = 2**depth
        unit = (-pow(3**valuation, -1, modulus)) % modulus + modulus
        source = 3**valuation * unit
        assert (source + 1) % modulus == 0
        for overhead in (valuation + evens + 1, valuation + 2 * evens + 3):
            length = depth + overhead
            twos = [2**i for i in range(length + 1)]
            threes = [3**i for i in range(length + 1)]
            for positions in combinations(range(length), evens):
                value = defect(length, positions, twos, threes)
                numerator = 2**overhead * 3**depth * (source + 1) - value
                denominator = 3 ** (length - evens)
                if numerator <= 0 or numerator % denominator:
                    checked += 1
                    continue
                smaller = numerator // denominator - 1
                if 0 < smaller < source:
                    assert valuation + 6 <= 8 * evens
                    target, bits = parity_run(smaller, length)
                    assert target == parity_run(source, depth)[0]
                    assert len(bits) - sum(bits) == evens
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"{residual_checks():,} residuals and {separation_checks():,} rational separations checked.")
    print(f"{valuation_checks():,} candidate paths at prescribed ternary valuations checked.")
