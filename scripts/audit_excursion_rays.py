"""Check canonical sources and exact descent thresholds on excursion rays."""

from math import gcd


def excursion(source):
    v = w = 0
    while source % 2:
        v += 1
        source = (3 * source + 1) // 2
    while source % 2 == 0:
        w += 1
        source //= 2
    return (v, w), source


def follow(source, length):
    profile = []
    for _ in range(length):
        run, source = excursion(source)
        profile.append(run)
    return tuple(profile), source


def audit_cuts(start, base, profile, visits, coefficients):
    full_denominator = coefficients[-1][1]
    shift = start // (2 * full_denominator)
    canonical = base
    for index, (source, (a, b, c)) in enumerate(zip(visits, coefficients)):
        outgoing_period = 2 * (full_denominator // b)
        outgoing = source % outgoing_period
        incoming = c * pow(b, -1, a) % a if a > 1 else 0
        adjustment = (incoming - outgoing) * pow(outgoing_period, -1, a) % a if a > 1 else 0
        reconstructed = outgoing + outgoing_period * adjustment
        assert source // a == start // b
        assert canonical == reconstructed
        assert source == canonical + outgoing_period * a * shift
        if index < len(profile):
            run, canonical = excursion(canonical)
            assert run == profile[index]
    return canonical


def main():
    profiles = {}
    high = 0
    shared = 0
    checks = 0
    cuts = 0
    for start in range(1, 2**14, 2):
        current = start
        a = b = 1
        odd_steps = elapsed = 0
        history = []
        visits = [start]
        coefficients = [(1, 1, 0)]
        for length in range(1, 9):
            (v, w), current = excursion(current)
            history.append((v, w))
            a *= 3**v
            b <<= v + w
            odd_steps += v
            elapsed += v + w
            offset = b * current - a * start
            visits.append(current)
            coefficients.append((a, b, offset))
            assert 0 <= offset
            assert (1 << odd_steps) * (offset + b) <= b * a
            assert (1 << odd_steps) * ((1 << w) * offset + b) <= b * a
            if b >= a and current >= start:
                index = start // (2 * b)
                assert (1 << odd_steps) * ((1 << w) * (b - a) * (2 * index) + 1) <= a
            shared_contraction = b > a and gcd(odd_steps, elapsed) > 1
            if shared_contraction:
                assert a <= (1 << odd_steps) * (b - a)
                shared += 1
            profile = tuple(history)
            base = start % (2 * b)
            assert profiles.setdefault(profile, base) == base
            original_landing = audit_cuts(start, base, profile, visits, coefficients)
            cuts += len(visits)
            assert current == original_landing + 2 * a * (start // (2 * b))
            for shift in (1, 3, 2**65):
                moved = base + 2 * b * shift
                moved_profile, moved_landing = follow(moved, length)
                assert moved_profile == profile
                assert moved_landing == original_landing + 2 * a * shift
                if b > a and original_landing >= base:
                    cutoff = (original_landing - base) // (2 * (b - a))
                    assert (moved_landing < moved) == (cutoff < shift)
                if shared_contraction:
                    assert moved_landing < moved
                checks += 1
            high += b > a and original_landing >= base
    profile, endpoint = follow(165, 7)
    assert endpoint == 167
    assert follow(165 + 2**28, 7) == (profile, 167 + 2 * 3**17)
    print(f"{len(profiles):,} profiles; {checks:,} shifted traces; {high:,} high base endpoints.")
    print(f"{shared:,} contracting prefixes with a common exponent factor.")
    print(f"{cuts:,} canonical cuts reconstructed from both residues.")


if __name__ == "__main__":
    main()
