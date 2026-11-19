"""Check the affine inverse fibers against direct inverse iteration."""

from collections import defaultdict
from random import Random

from audit_orbit_capacity import parity_run


def profiles(depth):
    by_multiplier = defaultdict(lambda: defaultdict(list))
    for residue in range(2**depth):
        endpoint, bits = parity_run(residue, depth)
        coefficient = 3 ** sum(bits)
        assert endpoint < coefficient
        by_multiplier[coefficient][endpoint].append(residue)
    return by_multiplier


def affine_fiber(depth, target, table):
    width = 2**depth
    result = set()
    for coefficient, endpoints in table.items():
        high, low = divmod(target, coefficient)
        result.update(width * high + residue for residue in endpoints.get(low, ()))
    return result


def inverse_fiber(depth, target):
    current = {target}
    for _ in range(depth):
        following = {2 * value for value in current}
        following.update((2 * value - 1) // 3 for value in current if value % 3 == 2)
        current = following
    return current


def fiber_checks():
    rng = Random(3929)
    checked = 0
    tables = [profiles(depth) for depth in range(13)]
    for depth, table in enumerate(tables):
        targets = [*range(128), *(rng.randrange(2**32) for _ in range(64))]
        for target in targets:
            assert affine_fiber(depth, target, table) == inverse_fiber(depth, target)
            checked += 1
        for periods in range(1, 17):
            source = periods * 2**depth - 1
            target, _ = parity_run(source, depth)
            assert target == periods * 3**depth - 1
            assert min(affine_fiber(depth, target, table)) == source
            checked += 1
    return checked


def mixed_checks():
    checked = 0
    for t in range(4096):
        for depth, source, partner in (
            (7, 384 * t + 177, 128 * t + 59),
            (11, 6144 * t + 3929, 2048 * t + 1311),
        ):
            assert parity_run(source, depth)[0] == parity_run(partner, depth)[0]
            assert 3 * partner < 2 * source
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"{fiber_checks():,} inverse-fiber and extremal checks; {mixed_checks():,} mixed meetings.")
