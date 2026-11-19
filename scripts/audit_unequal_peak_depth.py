"""Compare short orbit windows at several common shifted cofactors."""

from itertools import product

from audit_orbit_capacity import parity_run


def check_window(cofactor, short, long):
    short_images = {parity_run(3**exponent * cofactor - 1, short)[0] for exponent in range(12)}
    long_images = {parity_run(3**exponent * cofactor - 1, long)[0] for exponent in range(12)}
    assert short_images.isdisjoint(long_images)


if __name__ == "__main__":
    checked = 0
    for long in range(1, 13):
        for short in range(long):
            threshold = 2 ** (2 * long - short)
            for multiplier, increment in product((1, 2, 7), range(1, 5)):
                check_window(multiplier * threshold + increment, short, long)
                checked += 12**2
    assert parity_run(9 - 1, 0)[0] == parity_run(3**2 * 9 - 1, 5)[0]
    print(f"{checked:,} pairs of unequal-depth scaled-peak images checked.")
