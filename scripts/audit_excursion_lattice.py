"""Audit the valuation-stratified excursion product with exact rational arithmetic."""

from collections import Counter, defaultdict
from fractions import Fraction


def bounds(groups, floor):
    actual = common = spaced = snapped = Fraction(1)
    for odd_steps, sources in groups.items():
        a = 3**odd_steps
        c = a - 2**odd_steps
        residue = 2**odd_steps - 1
        stride = 2 ** (odd_steps + 1)
        base = floor + (residue - floor) % stride
        for index, source in enumerate(sorted(sources)):
            assert source % stride == residue
            assert source >= base + index * stride
            actual *= Fraction(a * source + c, source)
            common *= Fraction(a * floor + c, floor)
            unshifted = floor + index * stride
            spaced *= Fraction(a * unshifted + c, unshifted)
            comparison = base + index * stride
            snapped *= Fraction(a * comparison + c, comparison)
    return actual, snapped, spaced, common


def audit(start):
    groups = defaultdict(list)
    source = start
    elapsed = 0
    for _ in range(100):
        landing = source
        odd_steps = 0
        while landing % 2:
            landing = (3 * landing + 1) // 2
            odd_steps += 1
            elapsed += 1
        while landing % 2 == 0:
            landing //= 2
            elapsed += 1
        assert source not in groups[odd_steps]
        groups[odd_steps].append(source)

        actual, snapped, spaced, common = bounds(groups, start)
        denominator = 1 << elapsed
        assert actual == Fraction(denominator * landing, start)
        assert actual <= snapped <= spaced <= common
        if landing < start:
            return (landing, elapsed), tuple(denominator > cap for cap in (snapped, spaced, common))
        assert denominator <= snapped
        source = landing
    raise AssertionError(f"No excursion descent found from {start}")


def main():
    counts = Counter(audit(n)[1] for n in range(3, 2**16, 2))
    assert counts == {
        (True, True, True): 32_765,
        (True, False, False): 1,
        (False, False, False): 1,
    }
    assert audit(27) == ((23, 59), (True, False, False))
    assert audit(63) == ((61, 54), (False, False, False))
    print("32,767 odd starts checked; 32,766 first excursion drops certified by the valuation grid.")


if __name__ == "__main__":
    main()
