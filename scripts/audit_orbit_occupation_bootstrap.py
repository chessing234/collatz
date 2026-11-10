"""Check exact tilt constants and compressed image counts."""

from math import comb
from random import Random

from audit_orbit_capacity import parity_run


def tilt_constants():
    cover = 4081199576119298850484664607591547430685275
    odd, even = 94, 55
    k = odd + even
    moment_weight = odd**odd * even**even
    assert 3**odd < 2**k
    assert (cover - 1) * moment_weight < k**k <= cover * moment_weight
    assert cover**20 < 2**2831
    for blocks in range(1, 5):
        exceptional_words = sum(comb(k * blocks, m) for m in range(odd * blocks + 1, k * blocks + 1))
        assert exceptional_words <= cover**blocks


def compressed_images():
    rng = Random(1727)
    checks = 0
    for odd, even in ((1, 1), (3, 2), (17, 10)):
        k = odd + even
        height = 1
        while 2**k * 3 ** (odd * height) > 2 ** (k * height):
            height += 1
        for blocks in (height, height + 1, height + 2):
            steps = k * blocks
            cutoff = 2 ** (steps + 1)
            sources = range(cutoff) if cutoff <= 2**15 else [rng.randrange(cutoff) for _ in range(64)]
            images = set()
            for source in sources:
                endpoint, parity = parity_run(source, steps)
                if sum(parity) <= odd * blocks:
                    assert endpoint < 2 ** (k * (blocks - 1) + 1)
                    images.add(endpoint)
                    checks += 1
            assert len(images) <= 2 ** (k * (blocks - 1) + 1)
    return checks


if __name__ == "__main__":
    tilt_constants()
    print(f"Exact tilt and binomial checks; {compressed_images():,} compressed images.")
