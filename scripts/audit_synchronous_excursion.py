"""Check the first synchronous minima using direct backward iteration."""

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


def excursion_checks():
    checks = dict(first_halving=0, two_halvings=0, odd_after_halving=0,
                  third_step=0, fourth_and_fifth_steps=0)
    for length in range(1, 13):
        for cofactor in range(1, 1024, 2):
            source = 2**length * cofactor - 1
            shifted_peak = 3**length * cofactor

            target, _ = parity_run(source, length + 1)
            assert min(inverse_fiber(length + 1, target)) == source
            checks["first_halving"] += 1

            target, _ = parity_run(source, length + 2)
            if shifted_peak % 4 == 1 and length >= 2:
                expected = 2**length * (cofactor // 3) - 1 if cofactor % 3 == 0 else source - 1
                assert min(inverse_fiber(length + 2, target)) == expected
                checks["two_halvings"] += 1
            if shifted_peak % 4 == 3:
                assert min(inverse_fiber(length + 2, target)) == source
                checks["odd_after_halving"] += 1
            if shifted_peak % 8 == 3:
                target, _ = parity_run(source, length + 3)
                assert min(inverse_fiber(length + 3, target)) == source
                checks["third_step"] += 1
                if length >= 2:
                    for offset in (4, 5):
                        target, _ = parity_run(source, length + offset)
                        assert min(inverse_fiber(length + offset, target)) == source
                        checks["fourth_and_fifth_steps"] += 1
    return checks


if __name__ == "__main__":
    print(", ".join(f"{count:,} {kind} checks" for kind, count in excursion_checks().items()))
