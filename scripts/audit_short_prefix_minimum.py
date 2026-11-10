"""Compare short-fiber minima with complete pruned backward search."""

from audit_long_run_peak_rigidity import peak_certificate, smaller_sources
from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


def short_minimum(depth, run, cofactor):
    source = 2**run * cofactor - 1
    values = [source]
    for drop in range(1, depth + 1):
        if not peak_certificate(depth, run, cofactor, drop):
            continue
        length = 4 * drop - 3
        target = 2 ** (run - length) * 3 ** (length - drop) * cofactor - 1
        values.append(min(inverse_fiber(length, target)))
    return min(values)


def exact_checks():
    checked = partners = 0
    for depth in range(1, 11):
        for run in (6 * depth + 2, 6 * depth + 7):
            for cofactor in range(1, 32, 2):
                source = 2**run * cofactor - 1
                actual = smaller_sources(run, cofactor, depth)
                assert short_minimum(depth, run, cofactor) == min(actual | {source})
                lower_peaks = {3 ** (run - drop) * cofactor - 1: drop for drop in range(1, depth + 1)}
                for partner in actual:
                    peak, bits = parity_run(partner, run)
                    drop = lower_peaks[peak]
                    length = 4 * drop - 3
                    assert all(bits[length:])
                    short_peak, _ = parity_run(partner, length)
                    assert short_peak + 1 == 2 ** (run - length) * 3 ** (length - drop) * cofactor
                    partners += 1
                checked += 1
    return checked, partners


if __name__ == "__main__":
    assert short_minimum(8, 10015, 1) == (2**10015 - 5) // 3
    checks, partners = exact_checks()
    print(f"{checks:,} exact minima and {partners:,} bounded even-step prefixes checked.")
