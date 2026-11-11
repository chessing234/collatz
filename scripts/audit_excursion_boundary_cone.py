#!/usr/bin/env python3
"""Check the boundary cone and every lattice point in its exponent window."""

from fractions import Fraction

from audit_excursion_inverse_gap import log_bounds, log_gap


LIMIT = 325_000_000_000
LOWER_ODD, LOWER_TIME = 65_470_613_321, 103_768_467_013
SPECIAL_ODD, SPECIAL_TIME = 72_057_431_991, 114_208_327_604
UPPER_ODD, UPPER_TIME = 137_528_045_312, 217_976_794_617
EXPECTED = {
    (72_057_431_991, 114_208_327_604),
    (137_528_045_312, 217_976_794_617),
    (144_114_863_982, 228_416_655_208),
    (209_585_477_303, 332_185_122_221),
    (216_172_295_973, 342_624_982_812),
    (275_056_090_624, 435_953_589_234),
    (281_642_909_294, 446_393_449_825),
    (288_229_727_964, 456_833_310_416),
}


def audit() -> None:
    assert LOWER_ODD * SPECIAL_TIME - SPECIAL_ODD * LOWER_TIME == 1
    assert log_gap(LOWER_ODD, LOWER_TIME)[0] > 0
    assert log_gap(615_582_794_569, 975_675_645_481)[0] > 0
    scale = 4 * 2**71
    enlargement = log_bounds(Fraction(scale + 1, scale), 4)[1]
    lower_ln2 = log_bounds(Fraction(2), 90)[0]
    upper_special_gap = log_gap(SPECIAL_ODD, SPECIAL_TIME)[1]
    assert LIMIT * (upper_special_gap + SPECIAL_ODD * enlargement) < lower_ln2
    assert 4 * (2_431 * 22 + 1_500) <= 10_000 * 22

    found = set()
    for i in range(5):
        for j in range(1, 5):
            odd = LOWER_ODD * i + SPECIAL_ODD * j
            time = LOWER_TIME * i + SPECIAL_TIME * j
            if odd >= LIMIT:
                continue
            lo, hi = log_gap(odd, time)
            assert lo * hi > 0
            contracting = hi < 0
            assert contracting == (i <= j)
            if contracting:
                u, v = j - i, i
                assert odd == SPECIAL_ODD * u + UPPER_ODD * v
                assert time == SPECIAL_TIME * u + UPPER_TIME * v
                found.add((odd, time))
    assert found == EXPECTED
    print("Checked the enlarged-base comparison, determinant coordinates and all eight boundary pairs.")


if __name__ == "__main__":
    audit()
