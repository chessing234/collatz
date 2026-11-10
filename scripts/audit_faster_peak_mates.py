"""Compare the time-lead criterion with complete pruned backward search."""

from audit_long_run_peak_rigidity import peak_certificate, smaller_sources
from audit_orbit_capacity import parity_run


def check(depth, run, cofactor, lead, odd_count):
    target = 2**run * cofactor - 1
    drops = {
        drop
        for drop in range(1, depth + 1)
        if 3**lead < 2**lead * 3**drop and peak_certificate(depth, run, cofactor, drop)
    }
    actual = smaller_sources(run, cofactor, depth, lead=lead) - {0}
    actual_peaks = {parity_run(source, run - lead)[0] for source in actual}
    expected_peaks = {3 ** (run - drop) * cofactor - 1 for drop in drops}
    assert actual_peaks == expected_peaks
    for drop in drops:
        assert drop <= depth - odd_count
        if lead <= drop:
            source = 2 ** (drop - lead) * (2 ** (run - drop) * cofactor - 1)
        else:
            source = 2 ** (run - lead) * 3 ** (lead - drop) * cofactor - 1
        assert 0 < source < target
        assert source in actual
    return bool(actual), any(lead > drop for drop in drops)


if __name__ == "__main__":
    checked = meetings = cofactor_changes = 0
    for depth in range(1, 9):
        for run in range(2 * depth + 2, 6 * depth + 17, 4):
            for cofactor in range(1, 14, 2):
                _, bits = parity_run(3**run * cofactor - 1, depth)
                odd_count = sum(bits)
                available = run - (2 * depth + 2 + 4 * (depth - odd_count))
                for lead in range(1, min(available, 8) + 1):
                    found, changed = check(depth, run, cofactor, lead, odd_count)
                    checked += 1
                    meetings += found
                    cofactor_changes += changed
    assert check(8, 95, 1, 5, sum(parity_run(3**95 - 1, 8)[1])) == (True, True)
    assert check(8, 95, 1, 6, sum(parity_run(3**95 - 1, 8)[1])) == (False, False)
    print(f"{checked:,} time-lead cases, {meetings:,} with meetings and "
          f"{cofactor_changes:,} with a cofactor-changing witness.")
