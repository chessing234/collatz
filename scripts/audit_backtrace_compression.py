"""Shorten reverse paths and verify them by independent forward iteration."""

from random import Random

from audit_orbit_capacity import parity_run


def compressed(source, length, modulus, clock):
    target, word = parity_run(source, length)
    odd_count = sum(word)
    precision = 3**odd_count * modulus
    reverse = [*reversed(word), 1]
    value = target
    steps = even = 0
    for index, odd in enumerate(reverse):
        if not odd:
            even += 1
            continue
        residue = pow(2, even, precision)
        short = next(
            shift for shift in range(even % clock, even + 1, clock)
            if pow(2, shift, precision) == residue
        )
        value <<= short
        steps += short
        even = 0
        if index + 1 < len(reverse):
            assert value % 3 == 2
            value = (2 * value - 1) // 3
            assert value % 2 == 1
            precision //= 3
            steps += 1
    assert value <= source and steps <= length and value % modulus == source % modulus
    assert steps % clock == length % clock
    assert steps < (odd_count + 1) * clock * 3**odd_count * modulus
    endpoint, bits = parity_run(value, steps)
    assert endpoint == target and sum(bits) == odd_count
    return value, steps


def general_checks():
    rng = Random(1907)
    shortened = 0
    for i in range(2048):
        clock = 1 + rng.randrange(9)
        modulus = 1 + rng.randrange(96)
        leading = rng.randrange(121) if i % 2 else 0
        source = rng.randrange(2**18) << leading
        length = leading + rng.randrange(41)
        _, steps = compressed(source, length, modulus, clock)
        shortened += steps < length
    return shortened


def periodic_checks():
    checked = 0
    for clock in (2, 4, 6, 10):
        for modulus in (1, 2, 5, 12, 27, 35, 64):
            for length in (36, 91, 100, 157):
                source = 2**length
                value, _ = compressed(source, length, modulus, clock)
                assert parity_run(value, length)[0] == 1
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"2,048 general checks, {general_checks():,} shortened paths, "
          f"and {periodic_checks():,} periodic-target checks.")
