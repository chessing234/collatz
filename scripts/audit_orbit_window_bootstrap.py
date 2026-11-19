"""Check the translated image windows and standard-map value cover."""

from random import Random

from audit_orbit_capacity import parity_run


def translated_windows():
    rng = Random(149)
    checked = 0
    for steps in (1, 2, 3, 5, 9, 17, 27, 65, 149):
        width = 2**steps
        for _ in range(40):
            start = rng.randrange(2 ** (2 * steps + 3))
            sources = range(start, start + width) if width <= 32 else [
                start, start + width - 1, *[start + rng.randrange(width) for _ in range(30)]
            ]
            residues = set()
            source_values = set()
            for x in sources:
                q, r = divmod(x, width)
                endpoint, bits = parity_run(x, steps)
                base, base_bits = parity_run(r, steps)
                odd = sum(bits)
                scale = 3**odd
                assert q in (start // width, start // width + 1)
                assert bits == base_bits
                assert endpoint == q * scale + base
                assert q * scale <= endpoint < (q + 1) * scale
                if x not in source_values:
                    assert r not in residues
                source_values.add(x)
                residues.add(r)
                checked += 1
    return checked


def standard_cover():
    checked = 0
    for seed in range(1, 2048):
        shortcut_values = set()
        value = seed
        for _ in range(65):
            shortcut_values.add(value)
            if value % 2:
                shortcut_values.add(3 * value + 1)
                value = (3 * value + 1) // 2
            else:
                value //= 2
        value = seed
        for _ in range(65):
            assert value in shortcut_values
            value = 3 * value + 1 if value % 2 else value // 2
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"{translated_windows():,} translated image checks; {standard_cover():,} standard orbit values.")
