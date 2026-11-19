"""Check the cutoff rounding and near-critical integer window arithmetic."""

from random import Random


def widths():
    rng = Random(20)
    checked = 0
    for base in range(6):
        for band in range(14):
            lower = 2 ** (20 * (base + band) + 1)
            upper = lower * 2**20
            samples = [lower, lower + 1, upper - 1]
            samples.extend(rng.randrange(lower, upper) for _ in range(64))
            for n in samples:
                q = (n.bit_length() - 2) // 20 - base
                assert q == band
                assert 2 ** (20 * (base + q) + 1) <= n
                scale = 2 ** (20 * base + 21)
                assert 2**q <= n <= scale * 2 ** (20 * q)
                d = 2 ** (q + 1) - 1
                width = n // d + 1
                assert width**20 <= scale * 2**20 * n**19
                assert d * (n + width - 1) <= (d + 1) * n < d * (n + width)
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"{widths():,} cutoff and sharp endpoint rounding checks.")
