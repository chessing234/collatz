"""Check seven-step inverse branches and their short prefix exclusions."""

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber

REJECTIONS = {
    (0, 2): 1,
    (0, 3): 1,
    (0, 6): 1,
    (0, 7): 2,
    (0, 11): 1,
    (1, 0): 1,
    (1, 3): 1,
    (1, 4): 2,
    (1, 5): 3,
    (1, 9): 1,
    (2, 2): 2,
}


def defect_checks():
    checks = 0
    for (drop, displacement), precision in REJECTIONS.items():
        depth = drop + precision
        for residue in range(2**depth):
            _, word = parity_run(residue, depth)
            defect = sum(
                2**index * 3 ** sum(word[index + 1 :])
                for index, odd in enumerate(word)
                if not odd
            )
            if sum(word) >= precision:
                assert (defect + 2**depth * (displacement - 1)) % 3**precision
            checks += 1
    return checks


def lifted_peak_checks():
    depth = 7
    dyadic, ternary = 2**depth, 3**depth
    checks = 0
    for base in range(1, dyadic + 1):
        for q in (0, 1, 2, 31, 257):
            peak = ternary * (base + dyadic * q)
            if peak % 8 != 3:
                continue
            endpoint, _ = parity_run(peak - 1, depth)
            for smaller_peak in inverse_fiber(depth, endpoint):
                if smaller_peak < peak - 1:
                    assert any(3**drop * (smaller_peak + offset) == peak for drop, offset in REJECTIONS)
                    checks += 1
    return checks


def minima_checks():
    checks = 0
    for run in range(7, 15):
        for cofactor in range(1, 256, 2):
            peak = 3**run * cofactor
            if peak % 8 != 3:
                continue
            source = 2**run * cofactor - 1
            endpoint, _ = parity_run(source, run + 7)
            assert min(inverse_fiber(run + 7, endpoint)) == source
            checks += 1
    return checks


if __name__ == "__main__":
    print(
        f"{defect_checks():,} short defect checks, "
        f"{lifted_peak_checks():,} lifted inverse branches, "
        f"{minima_checks():,} exact minima."
    )
