#!/usr/bin/env python3
"""Compare rational shift grids with exact per-edge factor minimization."""

from fractions import Fraction

from audit_excursion_crossing import next_excursion


def edge(n, d, a, b, c, s, t):
    """Evaluate the shared affine-floor decision."""
    p, q = d * n + s, d * n + t
    offset = max(0, a * (d - s) + b * t - d * c)
    if a * (n + 1) <= b * n + c:
        return Fraction(b * p, b * q - offset)
    return Fraction(a * p + offset, a * q)


def reference_edge(n, d, a, b, c, s, t):
    p, q = d * n + s, d * n + t
    offset = max(0, a * (d - s) + b * t - d * c)
    departure = Fraction(a * p + offset, a * q)
    if b * q <= offset:
        return departure
    return min(departure, Fraction(b * p, b * q - offset))


def uniform(*scales):
    return {d: tuple(range(d + 1)) for d in scales}


def first_crossing(n, grids):
    x, a, b = n, 1, 1
    tables = {d: [Fraction(1)] * len(shifts) for d, shifts in grids.items()}
    descended = False
    for k in range(1, 101):
        x, v, w = next_excursion(x)
        descended |= x < n
        a_step, b_step, c_step = 3**v, 2**(v + w), 2**v
        a *= a_step
        b *= b_step
        for d, table in tables.items():
            tables[d] = [
                min(value * edge(n, d, a_step, b_step, c_step, s, t)
                    for s, value in zip(grids[d], table))
                for t in grids[d]
            ]
        if b > a:
            slope = Fraction(b, a)
            bounds = {d: min(table) for d, table in tables.items()}
            assert not any(slope > bound for bound in bounds.values()) or descended
            for d, bound in bounds.items():
                for finer, finer_bound in bounds.items():
                    if finer % d == 0 and all(
                        s * (finer // d) in grids[finer] for s in grids[d]
                    ):
                        assert finer_bound <= bound
            return k, x, slope, bounds
    raise AssertionError(f"no coefficient crossing for {n}")


def main():
    checks = 0
    for n in (1, 2, 3, 27, 63, 999):
        for d in (1, 2, 4, 8):
            for v in range(1, 7):
                for w in range(1, 9):
                    a, b, c = 3**v, 2**(v + w), 2**v
                    for s in range(d + 1):
                        for t in range(d + 1):
                            chosen = edge(n, d, a, b, c, s, t)
                            assert chosen == reference_edge(n, d, a, b, c, s, t)
                            assert chosen == edge(n, 3 * d, a, b, c, 3 * s, 3 * t)
                            checks += 1
    for n in range(3, 20_000, 2):
        _, _, slope, bounds = first_crossing(n, uniform(1, 2))
        assert bounds[2] <= bounds[1] < slope
    k, y, slope, bounds = first_crossing(63, uniform(1, 2, 4, 8))
    assert (k, y) == (12, 61)
    assert bounds[8] < Fraction(10776, 10000) < bounds[1] < slope
    _, _, slope_one, bounds_one = first_crossing(1, uniform(1, 2, 4))
    assert all(slope_one <= bound for bound in bounds_one.values())
    _, _, _, sparse = first_crossing(127, {3: (0, 1, 3), **uniform(16)})
    assert sparse[3] == Fraction(1343488, 1331883) < sparse[16]
    print(f"Checked {checks:,} local factors against independent minimization and refinement.")
    print("The half-unit grid certified all 9,999 first crossings.")
    print(f"For 63 the ceiling decreases from {float(bounds[1]):.9f} to {float(bounds[8]):.9f}.")
    print("For 127 the three shifts 0, 1/3, 1 beat the sixteenth-unit grid.")


if __name__ == "__main__":
    main()
