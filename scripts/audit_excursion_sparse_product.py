"""Check dyadic weights and the exact correction ratio independently of Lean."""

from fractions import Fraction
from math import prod
from random import Random

from audit_excursion_rays import excursion


def weighted_samples():
    rng = Random(73)
    checked = 0
    for stride in range(1, 6):
        def cutoff(level):
            return 2 ** (stride * level + 1)

        def capacity(level):
            return 2 ** ((stride - 1) * level)

        for upper in range(stride, stride + 5):
            denominator = cutoff(upper)
            for sample in range(120):
                points = []
                for level in range(stride, upper + 1):
                    room = min(capacity(level + 1) - len(points), 160 - len(points))
                    band = range(cutoff(level) | 1, cutoff(level + 1), 2)
                    limit = min(room, len(band))
                    count = limit if sample == 0 else rng.randint(0, limit)
                    points.extend(rng.sample(band, count))

                weights = [
                    sum(
                        2 ** (stride * (upper - level))
                        for level in range(stride, upper + 1)
                        if point < cutoff(level + 1)
                    )
                    for point in points
                ]
                assert len(set(points)) == len(points)
                assert all(point * weight >= denominator for point, weight in zip(points, weights))
                assert 2 * sum(weights) <= denominator
                assert prod(Fraction(point + 1, point) for point in points) <= 2
                checked += 1
    return checked


def exact_ratios():
    checked = 0
    for start in range(1, 2**15, 2):
        value = start
        sources = set()
        odd = elapsed = 0
        correction = majorant = Fraction(1)
        for _ in range(12):
            if value in sources:
                break
            sources.add(value)
            (v, w), endpoint = excursion(value)
            odd += v
            elapsed += v + w
            correction *= 1 + Fraction(3**v - 2**v, 3**v * value)
            majorant *= Fraction(value + 1, value)
            assert Fraction(2**elapsed * endpoint, 3**odd * start) == correction
            assert 1 < correction <= majorant
            value = endpoint
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"{weighted_samples():,} sparse weighted samples; {exact_ratios():,} exact orbit ratios.")
