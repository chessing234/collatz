"""Check signed ternary separation and the scaled-peak characterization."""

from functools import cache
from itertools import combinations

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


@cache
def precision(budget, integer):
    assert integer
    trailing = 0
    quotient = integer
    while quotient % 3 == 0:
        trailing += 1
        quotient //= 3
    bound = trailing + 1
    if budget:
        for odds in range(trailing + 1):
            residual = 2 ** (odds + 1) * (integer // 3**odds) - 1
            bound = max(bound, odds + precision(budget - 1, residual))
    return bound


def defect_checks():
    checks = 0
    for length in range(13):
        for budget in range(min(length, 5) + 1):
            for count in range(budget + 1):
                for even in combinations(range(length), count):
                    defect = sum(
                        2**index * 3 ** (length - index - count + order)
                        for order, index in enumerate(even)
                    )
                    for integer in range(-24, 25):
                        if integer:
                            modulus = 3 ** precision(budget, integer)
                            assert (2**length * integer - defect) % modulus
                            checks += 1
    return checks


def safe_run_length(depth):
    lower_bound = 2 * depth + 1
    for quotient in range(1, 2**depth + 1):
        peak = 3**depth * quotient
        target, bits = parity_run(peak - 1, depth)
        true_count = sum(bits)
        for predecessor in inverse_fiber(depth, target):
            _, profile = parity_run(predecessor, depth)
            drop = sum(profile) - true_count
            if drop < 0:
                continue
            offset = peak // 3**drop - predecessor
            if offset == 1:
                continue
            magnitude = 0
            while 3**magnitude < abs(offset):
                magnitude += 1
            lower_bound = max(lower_bound, drop + precision(drop, 1 - offset), drop + 1 + magnitude)
    return lower_bound


def smaller_sources(run, cofactor, suffix):
    source = 2**run * cofactor - 1
    endpoint, _ = parity_run(source, run + suffix)
    current = {endpoint}
    for index in range(run + suffix - 1, -1, -1):
        following = {2 * value for value in current}
        following.update((2 * value - 1) // 3 for value in current if value % 3 == 2)
        if index <= run:
            # An input below 2**run * cofactor has this affine image cap at time index.
            cap = 2 ** (run - index) * 3**index * cofactor
            if index == 0:
                cap = source
            following = {value for value in following if value < cap}
        current = following
    return current


def rigidity_checks():
    checks = meetings = 0
    for depth in range(10):
        start = safe_run_length(depth)
        for run in (start, start + 1, start + 7):
            for cofactor in range(1, 32, 2):
                peak = 3**run * cofactor - 1
                endpoint, _ = parity_run(peak, depth)
                scaled = {
                    3 ** (run - drop) * cofactor - 1
                    for drop in range(1, depth + 1)
                    if parity_run(3 ** (run - drop) * cofactor - 1, depth)[0] == endpoint
                }
                actual_peaks = {parity_run(source, run)[0] for source in smaller_sources(run, cofactor, depth)}
                assert actual_peaks == scaled
                meetings += bool(scaled)
                checks += 1
    return checks, meetings


if __name__ == "__main__":
    print(f"{defect_checks():,} signed defect checks.", flush=True)
    samples, meetings = rigidity_checks()
    print(f"{samples:,} exact rigidity checks, including {meetings:,} with smaller partners.")
