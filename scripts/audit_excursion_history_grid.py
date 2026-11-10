"""Compare one-excursion and full-prefix residue floors using exact products."""

from collections import Counter
from fractions import Fraction
from itertools import chain
from random import Random


def combined_residue(v, a, b, c):
    stride = 2 ** (v + 1)
    residue = 2**v - 1
    if a > 1:
        ternary = c * pow(b, -1, a) % a
        residue += stride * ((ternary - residue) * pow(stride, -1, a) % a)
    return residue, stride * a


def audit(start):
    a = b = 1
    c = 0
    previous = (1, 1, 0)
    one = full = actual = Fraction(1)
    source = start
    recoveries = 0
    for _ in range(1000):
        landing = source
        v = w = 0
        while landing % 2:
            v += 1
            landing = (3 * landing + 1) // 2
        while landing % 2 == 0:
            w += 1
            landing //= 2

        recent_residue, recent_period = combined_residue(v, *previous)
        history_residue, history_period = combined_residue(v, a, b, c)
        recent_floor = start + (recent_residue - start) % recent_period
        history_floor = start + (history_residue - start) % history_period
        assert start <= recent_floor <= history_floor <= source
        if start < b:
            assert history_residue == history_floor == source
            recoveries += 1

        tripling = 3**v
        denominator = 2 ** (v + w)
        offset = tripling - 2**v
        one *= Fraction(tripling * recent_floor + offset, recent_floor)
        full *= Fraction(tripling * history_floor + offset, history_floor)
        actual *= Fraction(tripling * source + offset, source)
        previous = tripling, denominator, offset
        c = tripling * c + b * offset
        a *= tripling
        b *= denominator
        assert Fraction(b * landing, start) == actual <= full <= one

        if landing < start:
            return (one > full, b > one, b > full), recoveries, (one - full) / b
        source = landing
    raise AssertionError(f"No excursion descent from {start}")


def main():
    rng = Random(1)
    larger = (rng.randrange(2**55, 2**64) | 1 for _ in range(20_000))
    counts = Counter()
    recovered = 0
    largest = (Fraction(0), 0)
    for n in chain(range(3, 2**18, 2), larger):
        outcome, recoveries, margin = audit(n)
        counts[outcome] += 1
        recovered += recoveries
        largest = max(largest, (margin, n))
    assert counts == {(False, True, True): 130_409, (True, True, True): 20_662}
    assert largest[1] == 27
    print(f"151,071 starts; 20,662 tighter bounds; {recovered:,} exact recovered visits.")


if __name__ == "__main__":
    main()
