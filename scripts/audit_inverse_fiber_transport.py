"""Check ternary target transport by independent backward enumeration."""

from random import Random

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


def transport_checks():
    rng = Random(1543)
    checks = minimum_checks = 0
    for depth in range(13):
        period = 3**depth
        source_modulus = 2**depth
        for target in (*range(48), *(rng.randrange(period) for _ in range(64))):
            original = inverse_fiber(depth, target)
            profiles = {x: parity_run(x, depth)[1] for x in original}
            selected = min(original, key=lambda x: (-sum(profiles[x]), x % source_modulus))
            for q in (0, 1, 2, 19, 511):
                lifted = {
                    x + source_modulus * 3 ** (depth - sum(bits)) * q: bits
                    for x, bits in profiles.items()
                }
                actual = inverse_fiber(depth, target + period * q)
                assert set(lifted) == actual
                for source, bits in lifted.items():
                    assert parity_run(source, depth)[1] == bits
                    checks += 1
                if q > 0:
                    minimum = selected + source_modulus * 3 ** (depth - sum(profiles[selected])) * q
                    assert min(actual) == minimum
                    minimum_checks += 1
    return checks, minimum_checks


if __name__ == "__main__":
    fibers, minima = transport_checks()
    print(f"{fibers:,} transported sources and {minima:,} stable minima checked.")
