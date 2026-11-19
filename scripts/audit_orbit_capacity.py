"""Independently check finite ingredients of dyadic occupation."""

from fractions import Fraction


def parity_run(source, steps):
    bits = []
    for _ in range(steps):
        bit = source % 2
        bits.append(bit)
        source = (3 * source + 1) // 2 if bit else source // 2
    return source, bits


def occupation():
    checks = 0
    for h in range(1, 4):
        k = 5 * h
        light_images = set()
        heavy = 0
        moment = 0
        for n in range(2 ** (k + 1)):
            endpoint, bits = parity_run(n, k)
            odd = sum(bits)
            assert endpoint < 2 * 3**odd
            if n < 2**k:
                assert endpoint < 3**odd
            moment += 2**odd
            if odd <= 3 * h:
                light_images.add(endpoint)
            else:
                heavy += 1
            checks += 1
        assert moment == 2 * 3**k
        assert len(light_images) <= 2 * 27**h
        assert heavy <= 2 * 31**h
        assert len(light_images) + heavy <= 4 * 31**h
    return checks


def forbidden_words():
    checks = 0
    for length in range(1, 5):
        for depth in range(1, 4):
            horizon = length * depth
            words = [parity_run(x, horizon + 1)[1] for x in range(2 ** (horizon + 1))]
            for residue in range(2**length):
                _, forbidden = parity_run(residue, length)
                allowed = sum(
                    all(word[i : i + length] != forbidden for i in range(0, horizon, length))
                    for word in words
                )
                assert allowed == 2 * (2**length - 1) ** depth
                checks += 1
    return checks


def affine_corrections():
    checks = 0
    for seed in range(1, 4096):
        value = seed
        exact = upper = Fraction(1)
        odd = 0
        for k in range(1, 33):
            bit = value % 2
            if bit:
                exact *= Fraction(3 * value + 1, 3 * value)
            upper *= Fraction(value + 1, value)
            odd += bit
            value = (3 * value + 1) // 2 if bit else value // 2
            assert 1 <= exact == Fraction(2**k * value, seed * 3**odd) <= upper
            checks += 1
    return checks


if __name__ == "__main__":
    print(f"{occupation():,} finite images; {forbidden_words()} forbidden-word counts; "
          f"{affine_corrections():,} exact shortcut correction ratios.")
