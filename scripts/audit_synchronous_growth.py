"""Check that descending odd steps can be omitted from the finite product."""

from random import Random


def reduced_products():
    rng = Random(4124)
    checked = omitted = 0
    for seed in range(1, 4097):
        value = seed
        rises = halves = 0
        num = den = 1
        for _ in range(24):
            source = value
            if source % 2 == 0:
                value = source // 2
                halves += 1
            else:
                upper = (3 * source + 1) // 2
                value = upper if rng.randrange(3) else rng.randrange(1, upper + 1)
                if source < value:
                    rises += 1
                else:
                    omitted += 1
            num *= source + 1
            den *= source
            assert 2 ** (rises + halves) * value * den <= seed * 3**rises * num
            checked += 1
    return checked, omitted


if __name__ == "__main__":
    checks, omitted = reduced_products()
    print(f"{checks:,} exact finite products; {omitted:,} omitted odd steps.")
