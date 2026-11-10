"""Check the odd-count ordering of equal-time partners."""

from random import Random

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import affine_fiber, profiles


def ordering_checks():
    rng = Random(3359)
    checks = contractions = 0
    for depth in range(1, 13):
        width = 2**depth
        table = profiles(depth)
        for source in [*range(width, width + 64), *(rng.randrange(width, 16 * width) for _ in range(128))]:
            target, bits = parity_run(source, depth)
            odd = sum(bits)
            for mate in affine_fiber(depth, target, table):
                endpoint, mate_bits = parity_run(mate, depth)
                mate_odd = sum(mate_bits)
                assert endpoint == target
                earlier = mate_odd > odd or (mate_odd == odd and mate % width < source % width)
                assert (mate < source) == earlier
                if source >= 2 * width and mate_odd > odd:
                    assert 3 * mate < 2 * source
                    contractions += 1
                checks += 1
    return checks, contractions


def finite_halving():
    checks = 0
    tables = [profiles(depth) for depth in range(10)]
    for depth in range(1, 10):
        for half in range(1, 513):
            endpoint, _ = parity_run(half, depth - 1)
            if min(affine_fiber(depth, endpoint, tables[depth])) == 2 * half:
                assert min(affine_fiber(depth - 1, endpoint, tables[depth - 1])) == half
                assert half % 3 != 2
                checks += 1
    return checks


if __name__ == "__main__":
    checked, contracted = ordering_checks()
    print(f"{checked:,} partner orderings; {contracted:,} strict contractions; "
          f"{finite_halving():,} finite halving checks.")
