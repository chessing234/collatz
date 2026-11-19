"""Verify gap minima and construct ancestors by direct modular iteration."""

from audit_orbit_capacity import parity_run
from audit_synchronous_classes import inverse_fiber


def leading_halving_checks():
    checked = 0
    for depth in range(1, 12):
        for cofactor in range(1, 128):
            source = 2**depth * cofactor - 2
            endpoint, _ = parity_run(source, depth)
            expected = 2**depth * (cofactor // 3) - 1 if cofactor % 3 == 0 else source
            assert min(inverse_fiber(depth, endpoint)) == expected
            checked += 1
    return checked


def delay_checks():
    checked = 0
    for run in range(1, 11):
        for suffix in range(1, 11):
            modulus = 2**suffix
            base = -pow(3**run, -1, modulus) % modulus
            for t in range(10):
                cofactor = base + modulus * t
                source = 2**run * cofactor - 1
                endpoint, word = parity_run(source, run + suffix)
                assert word == [1] * run + [0] + [1] * (suffix - 1)
                assert min(inverse_fiber(run + suffix, endpoint)) == source
                checked += 1
    return checked


def ancestor(k, s, residue, target, cutoff):
    dyadic = 2**k
    high, low = divmod(residue, dyadic)
    end, word = parity_run(low, k)
    offset = 3 ** sum(word) * high + end
    scale = 3 ** (sum(word) + s)
    parity = 1 - offset % 2
    offset = (3 * (offset + scale * parity) + 1) // 2
    modulus = 3 * scale
    period = 2 * scale
    exponent = 0
    remainder = target % modulus
    while remainder != offset % modulus:
        exponent += 1
        assert exponent < period
        remainder = 2 * remainder % modulus
    while (target << exponent) <= modulus * cutoff + offset:
        exponent += period
    threshold = modulus * cutoff + offset
    assert exponent <= threshold.bit_length() + 2 * period
    q = 2 * (((target << exponent) - offset) // modulus) + parity
    source = dyadic * 3**s * q + residue
    assert q > cutoff and source > 0
    assert parity_run(source, k + 1)[0] == target << exponent
    assert parity_run(source, k + 1 + exponent)[0] == target
    assert source <= target << (k + 1 + exponent)
    return source


def progression_checks():
    checked = 0
    for k in range(5):
        for s in range(3):
            for residue in (0, 1, 2**k * 3**s - 1, 2**k * 3**s + 7):
                for target in range(1, 21):
                    if target % 3:
                        ancestor(k, s, residue, target, 11)
                        checked += 1
    return checked


def delayed_ancestor_checks():
    checked = 0
    for run in range(1, 4):
        for suffix in range(3, 6):
            modulus = 2**suffix
            cofactor = -pow(3**run, -1, modulus) % modulus
            for target in (1, 5, 7, 11, 19):
                source = ancestor(run + suffix, 0, 2**run * cofactor - 1, target, 2)
                endpoint, _ = parity_run(source, run + suffix)
                assert min(inverse_fiber(run + suffix, endpoint)) == source
                checked += 1
    return checked


if __name__ == "__main__":
    print(
        f"{leading_halving_checks():,} leading-halving minima, "
        f"{delay_checks():,} fixed-run delays, "
        f"{progression_checks():,} mixed ancestors, "
        f"{delayed_ancestor_checks():,} delayed ancestors."
    )
