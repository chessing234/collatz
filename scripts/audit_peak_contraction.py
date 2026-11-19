"""Check symbolic peak meetings against independent shortcut iteration."""

from audit_orbit_capacity import parity_run


def certificate_checks():
    checked = 0
    for depth in range(2, 11):
        period = 2**depth
        for drop in range(1, min(6, depth) + 1):
            multiplier = 3**drop
            for residue in range(1, period, 2):
                left, left_word = parity_run(multiplier * residue - 1, depth)
                right, right_word = parity_run(residue - 1, depth)
                certified = left == right and sum(left_word) + drop == sum(right_word)
                meetings = 0
                for quotient in (0, 1, 2, 3, 257):
                    peak = period * quotient + residue
                    actual_left, _ = parity_run(multiplier * peak - 1, depth)
                    actual_right, _ = parity_run(peak - 1, depth)
                    meetings += actual_left == actual_right
                    checked += 1
                if certified:
                    assert meetings == 5
                else:
                    assert meetings <= 1
    return checked


def exponent_checks():
    checks = 0
    rules = ((31, 64, 2, 8), (79, 128, 2, 9), (111, 256, 2, 10), (2047, 4096, 4, 14))
    for start, period, drop, depth in rules:
        for lift in range(32):
            exponent = start + period * lift
            peak = 3**exponent - 1
            smaller_peak = 3 ** (exponent - drop) - 1
            assert parity_run(peak, depth)[0] == parity_run(smaller_peak, depth)[0]
            checks += 1
        for lift in range(2):
            exponent = start + period * lift
            source = 2**exponent - 1
            partner = 2**drop * (2 ** (exponent - drop) - 1)
            assert 0 < partner < source
            assert parity_run(source, exponent + depth)[0] == parity_run(partner, exponent + depth)[0]
            checks += 1
    return checks


def separation_checks():
    checks = 0
    for depth in range(3, 13):
        for lift in range(1, 13):
            exponent = 1 + 2 ** (depth - 2) * lift
            peaks = [3 ** (exponent - drop) - 1 for drop in range(3)]
            longest, middle, shortest = (parity_run(peak, depth)[0] for peak in peaks)
            assert shortest == middle < longest
            checks += 1
    return checks


if __name__ == "__main__":
    print(f"{certificate_checks():,} lifted peak checks and {exponent_checks():,} exponent checks.")
    print(f"{separation_checks():,} separated exponent checks.")
