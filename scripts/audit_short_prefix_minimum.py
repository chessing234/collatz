"""Compare short-fiber minima with complete pruned backward search."""

from functools import cache

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


def exact_checks(cases):
    checked = partners = 0
    for depth, run, cofactor in cases:
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


def adaptive_cases():
    for depth in range(1, 10):
        for run in range(2 * depth + 2, 6 * depth + 2):
            for cofactor in range(1, 16, 2):
                _, bits = parity_run(3**run * cofactor - 1, depth)
                if run >= 2 * depth + 2 + 4 * (depth - sum(bits)):
                    yield depth, run, cofactor


def chain_checks():
    checked = 0
    for cofactor in range(1, 12, 2):
        @cache
        def signature(run, depth):
            endpoint, bits = parity_run(3**run * cofactor - 1, depth)
            return endpoint, sum(bits)

        @cache
        def descendants(run):
            result = {run}
            for depth in range(1, run // 2):
                endpoint, odds = signature(run, depth)
                if run < 2 * depth + 2 + 4 * (depth - odds):
                    continue
                for drop in range(1, depth + 1):
                    if signature(run - drop, depth)[0] == endpoint:
                        assert peak_certificate(depth, run, cofactor, drop)
                        result.update(descendants(run - drop))
            return result

        for run in range(1, 120):
            horizon = run // 2
            endpoint, odds = signature(run, horizon)
            for final in descendants(run) - {run}:
                assert signature(final, horizon) == (endpoint, odds + run - final)
                assert run - final <= horizon - odds
                checked += 1
    return checked


if __name__ == "__main__":
    assert short_minimum(8, 10015, 1) == (2**10015 - 5) // 3
    fixed = (
        (depth, run, cofactor)
        for depth in range(1, 11)
        for run in (6 * depth + 2, 6 * depth + 7)
        for cofactor in range(1, 32, 2)
    )
    for label, cases in (("Fixed", fixed), ("Adaptive below fixed", adaptive_cases())):
        checks, partners = exact_checks(cases)
        print(f"{label}: {checks:,} exact minima and {partners:,} bounded even-step prefixes.")
    print(f"{chain_checks():,} nontrivial adaptive chain endpoints checked.")
