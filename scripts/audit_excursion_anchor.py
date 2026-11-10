#!/usr/bin/env python3
"""Audit the exact anchor search using independent rational factors."""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import product
from math import ceil, gcd, prod
from random import Random

from audit_excursion_crossing import next_excursion
from audit_excursion_shift_grid import first_crossing, uniform


def first_word(n):
    x, a, b = n, 1, 1
    word = []
    descended = False
    for _ in range(100):
        x, v, w = next_excursion(x)
        aa, bb, c = 3**v, 2**(v + w), 2**v
        word.append((aa, bb, c))
        a *= aa
        b *= bb
        descended |= x < n
        if b > a:
            return word, Fraction(b, a), descended
    raise AssertionError(f"no coefficient crossing for {n}")


def candidate_layers(word):
    layers = [{Fraction(0), Fraction(1)} for _ in range(len(word) + 1)]
    for i in range(len(layers)):
        for anchor in (Fraction(0), Fraction(1)):
            shift = anchor
            for j in range(i, len(word)):
                a, b, c = word[j]
                shift = (a * shift + c - a) / b
                if 0 <= shift <= 1:
                    layers[j + 1].add(shift)
            shift = anchor
            for j in range(i - 1, -1, -1):
                a, b, c = word[j]
                shift = (b * shift + a - c) / a
                if 0 <= shift <= 1:
                    layers[j].add(shift)
    assert all(len(layer) <= 2 * (len(word) + 2) for layer in layers)
    return layers



def transport(edge, shift):
    a, b, c = edge
    return (a * shift + c - a) / b


def inverse(edge, shift):
    a, b, c = edge
    return (b * shift + a - c) / a


def local_layers(word):
    layers = []
    for i in range(len(word) + 1):
        shifts = {Fraction(0), Fraction(1)}
        if i >= 1:
            shifts.add(transport(word[i - 1], Fraction(1)))
        if i >= 2:
            shifts.add(transport(word[i - 1], transport(word[i - 2], Fraction(1))))
        if i < len(word):
            shifts.add(inverse(word[i], Fraction(0)))
        if i + 1 < len(word):
            shifts.add(inverse(word[i], inverse(word[i + 1], Fraction(0))))
        layers.append({shift for shift in shifts if 0 <= shift <= 1})
    assert all(len(layer) <= 6 for layer in layers)
    return layers


def zero_links_feasible(word):
    lower, upper = Fraction(0), Fraction(1)
    scale, offset = Fraction(1), Fraction(0)
    for a, b, c in word:
        scale = a * scale / b
        offset = (a * offset + c - a) / b
        lower = max(lower, -offset / scale)
        upper = min(upper, (1 - offset) / scale)
    return lower <= upper


def factor(n, edge, s, t):
    a, b, c = edge
    p, q = n + s, n + t
    offset = max(Fraction(0), a * (1 - s) + b * t - c)
    departure = (a * p + offset) / (a * q)
    arrival_denominator = b * q - offset
    if arrival_denominator <= 0:
        return departure
    return min(departure, b * p / arrival_denominator)


def cost(n, word, shifts):
    return prod(factor(n, edge, s, t) for edge, s, t in zip(word, shifts, shifts[1:]))


def optimum(n, word, layers):
    table = {s: Fraction(1) for s in layers[0]}
    for edge, layer in zip(word, layers[1:]):
        table = {
            t: min(value * factor(n, edge, s, t) for s, value in table.items())
            for t in layer
        }
    return min(table.values())


def flat_weight(n, word):
    numerator, denominator = 1, 1
    for a, b, c in word:
        offset = a - c
        if a * n + offset <= b * n:
            numerator *= a * n
            denominator *= b * n - offset
        else:
            numerator *= a * n + offset
            denominator *= b * n
    return Fraction(numerator, denominator)


def check_flat_schedule():
    misses = []
    for n in range(3, 200_000, 2):
        word, ratio, descended = first_word(n)
        bound = flat_weight(n, word)
        if bound >= 1:
            assert descended and optimum(n, word, local_layers(word)) < ratio
            misses.append(n)
    assert misses == [27, 63]
    for n in (2, 3, 27, 63, 127, 10**20):
        one_loop = Fraction(3 * n, 4 * n - 1)
        assert 0 < one_loop < 1
        for cost in (Fraction(1, 2), Fraction(1), Fraction(5, 4), Fraction(13, 4)):
            target = (cost - 1) / (1 / one_loop - 1)
            copies = max(0, ceil(target)) + 1
            assert cost * flat_weight(n, [(3, 4, 2)] * copies) < 1
    print("The constant floor missed only 27 and 63 on 99,999 first crossings. The local search certified both.")


def check_unit_tails():
    edge = (3, 4, 2)
    for n in (1, 2, 3, 7, 127):
        for length in range(1, 8):
            word = [edge] * length
            assert optimum(n, word, local_layers(word)) == Fraction(4 * n, 4 * n - 1)**length
    for length in range(1, 5):
        modulus = 2 * 4**length
        for x in range(1, 3 * modulus, 2):
            y = x
            for _ in range(length):
                y, v, w = next_excursion(y)
                if (v, w) != (1, 1):
                    assert (x - 1) % modulus != 0
                    break
            else:
                assert (x - 1) % modulus == 0
                assert y == 1 + 2 * 3**length * ((x - 1) // modulus)
    synthetic = [(27, 16, 8), edge, edge]
    bound = optimum(7, synthetic, local_layers(synthetic))
    assert bound == Fraction(1792, 1539) > Fraction(256, 243)
    assert next_excursion(7) == (13, 3, 1) and next_excursion(13) == (5, 1, 2)
    print("Checked 35 exact unit-block optima, four complete residue ranges, and the synthetic tail from 7.")


def sign_parts(n, word):
    parts = []
    first = 0
    previous_positive = False
    for i, (a, b, c) in enumerate(word):
        positive = b * n + c >= a * (n + 1)
        if previous_positive and not positive:
            parts.append(word[first:i])
            first = i
        previous_positive = positive
    parts.append(word[first:])
    return parts


def check_conflicting_pairs():
    runs = [(3**v, 2**(v + w), 2**v) for v, w in product(range(1, 6), repeat=2)]
    checked = 0
    choices = set()
    for n in (1, 3, 7, 27, 63, 127):
        for e, f in product(runs, repeat=2):
            a, b, c = e
            aa, bb, cc = f
            drift = b * n + c - a * (n + 1)
            next_drift = bb * n + cc - aa * (n + 1)
            if not drift < 0 <= next_drift:
                continue
            word = [e, f]
            zero, one = Fraction(0), Fraction(1)
            bottom = cost(n, word, [zero, zero, one])
            top = cost(n, word, [zero, one, one])
            assert (bottom <= top) == (0 <= b * next_drift + aa * drift)
            assert optimum(n, word, local_layers(word)) == min(bottom, top)
            checked += 1
            choices.add((bottom > top) - (bottom < top))
    assert {-1, 1} <= choices
    print(f"Checked both endpoint choices against exact optimization on {checked:,} conflicting pairs.")


def greedy_schedule(part, cut, middle):
    left = [middle]
    for edge in reversed(part[:cut]):
        left.append(min(Fraction(1), inverse(edge, left[-1])))
    right = [middle]
    for edge in part[cut:]:
        right.append(max(Fraction(0), transport(edge, right[-1])))
    assert all(value == 1 for value in left[2:])
    assert all(value == 0 for value in right[3:])
    return list(reversed(left[1:])) + right


def check_greedy_part(n, part):
    cut = next((i for i, (a, b, c) in enumerate(part) if b * n + c >= a * (n + 1)), len(part))
    assert all(b * n + c >= a * (n + 1) for a, b, c in part[cut:])
    layers = local_layers(part)
    best = min(cost(n, part, greedy_schedule(part, cut, q)) for q in layers[cut])
    assert best == optimum(n, part, layers)


def check_greedy_blocks():
    checked = 0
    for n in range(3, 2_000, 2):
        word, _, _ = first_word(n)
        for part in sign_parts(n, word):
            check_greedy_part(n, part)
            checked += 1
    rng = Random(25031)
    for _ in range(30):
        n = rng.randrange(1, 300)
        word = [rng.choice([(9, 8, 4), (27, 16, 8)]) for _ in range(rng.randrange(3, 9))]
        word.extend(rng.choice([(3, 4, 2), (3, 8, 2)]) for _ in range(rng.randrange(4, 10)))
        check_greedy_part(n, word)
    word, _, _ = first_word(199)
    assert len(local_layers(word)[1]) == 5
    word, _, _ = first_word(543)
    prices = {q: cost(543, word, greedy_schedule(word, 1, q)) for q in local_layers(word)[1]}
    assert prices[Fraction(7, 9)] == Fraction(2719744, 2714067)
    assert all(prices[Fraction(7, 9)] < value for q, value in prices.items() if q != Fraction(7, 9))
    print(f"Checked one-coordinate greedy minima on {checked:,} genuine sign blocks and 30 longer words.")


def check_reversal_budgets():
    zero, one = Fraction(0), Fraction(1)
    uniform_misses, binary_misses, threshold_misses = [], [], []
    for n in range(3, 200_000, 2):
        word, inverse_coefficient, _ = first_word(n)
        positive = [b * n + c >= a * (n + 1) for a, b, c in word]
        ideal = [
            Fraction(b * n, b * n + c - a) if sign else Fraction(a * (n + 1) + b - c, a * (n + 1))
            for (a, b, c), sign in zip(word, positive)
        ]
        ratio = Fraction(n + 1, n)
        conflicts = [i for i in range(len(word) - 1) if not positive[i] and positive[i + 1]]
        uniform = prod(ideal) * ratio**len(conflicts)
        binary = prod(ideal) * prod(ratio / max(ideal[i], ideal[i + 1]) for i in conflicts)
        threshold = prod(ideal)
        for i in conflicts:
            e, f = word[i:i + 2]
            left, right = transport(e, one), inverse(f, zero)
            assert zero <= left <= one and zero <= right <= one
            pair = min(factor(n, e, one, q) * factor(n, f, q, zero) for q in (left, right))
            threshold *= pair / (ideal[i] * ideal[i + 1])
        assert threshold <= binary <= uniform
        if n < 2_000:
            assert optimum(n, word, local_layers(word)) <= threshold
        if uniform >= inverse_coefficient:
            uniform_misses.append(n)
        if binary >= inverse_coefficient:
            binary_misses.append(n)
        if threshold >= inverse_coefficient:
            threshold_misses.append(n)
        if n == 63:
            assert threshold == Fraction(19334741418193510400, 17917896630434357367)
    assert uniform_misses == [27, 63] and binary_misses == [63] and not threshold_misses
    print("The two-threshold budget certified all 99,999 first crossings. The binary budget missed 63.")


def check_floor_monotonicity():
    rng = Random(88433)
    for _ in range(8_192):
        v, w = rng.randrange(1, 14), rng.randrange(1, 8)
        edge = (3**v, 2**(v + w), 2**v)
        low = rng.randrange(1, 50)
        high = low + rng.randrange(1, 50)
        source, target = Fraction(rng.randrange(65), 64), Fraction(rng.randrange(65), 64)
        assert factor(high, edge, source, target) < factor(low, edge, source, target)
    for n in range(3, 2_000, 2):
        word, ratio, _ = first_word(n)
        layers = local_layers(word)
        low, high = max(1, n // 2), n + 1
        assert optimum(high, word, layers) < optimum(low, word, layers)
        cutoff = ratio.numerator * len(word) // (ratio.numerator - ratio.denominator) + 1
        assert optimum(cutoff, word, layers) < ratio
    word, ratio, _ = first_word(63)
    layers = local_layers(word)
    assert optimum(61, word, layers) < ratio <= optimum(60, word, layers)
    print("Checked 8,192 translated factors, 999 complete words, and the exact threshold 61 for the word from 63.")


def check_floor_fibres():
    common_exponents = 0
    for n in range(3, 2_000, 2):
        word, inverse_coefficient, _ = first_word(n)
        a, b = inverse_coefficient.denominator, inverse_coefficient.numerator
        lifted = n + 2 * b
        assert first_word(lifted)[:2] == (word, inverse_coefficient)
        x, y = n, lifted
        elapsed, odd_count = 0, 0
        for _ in word:
            x, v, w = next_excursion(x)
            y, vv, ww = next_excursion(y)
            assert (v, w) == (vv, ww)
            elapsed += v + w
            odd_count += v
        assert y - x == 2 * a
        if len(word) < 2 * (b - a):
            assert b * len(word) < (b - a) * lifted
            assert y < lifted
        if gcd(elapsed, odd_count) > 1:
            assert len(word) < 2 * (b - a)
            common_exponents += 1
    assert common_exponents > 0
    print(f"Checked 999 first source lifts, including {common_exponents} with a common exponent divisor.")


def check_power_gap_bracket():
    lower_num, lower_den = 1054, 665
    upper_num, upper_den = 4701, 2966
    assert upper_num * lower_den - lower_num * upper_den == 1
    assert 2**lower_num < 3**lower_den
    assert 2049 * 3**upper_den <= 2048 * 2**upper_num
    assert 2049 * upper_den * 17 < 3**17
    power = 1
    for exponent in range(1, lower_den + upper_den):
        power *= 3
        assert exponent < 2 * ((1 << power.bit_length()) - power)
    second_upper_num, second_upper_den = 8917, 5626
    assert second_upper_num * lower_den - lower_num * second_upper_den == 1
    assert 2049 * 3**second_upper_den <= 2048 * 2**second_upper_num
    assert 2049 * second_upper_den <= 2**24
    power = 1
    for exponent in range(1, lower_den + second_upper_den):
        power *= 3
        gap = (1 << power.bit_length()) - power
        assert 2**(exponent + 1) * gap >= power
    log_two_lower = 2 * (Fraction(1, 3) + Fraction(1, 81))
    log_three_upper = 2 * sum(Fraction(1, 2)**(2*k+1) / (2*k+1) for k in range(3))
    log_three_upper += 2 * Fraction(1, 2)**7 / (7 * (1 - Fraction(1, 4)))
    assert log_two_lower > Fraction(69, 100)
    assert log_three_upper < Fraction(11, 10)
    z = Fraction(1, 5)
    log_ratio_upper = 2 * (z + z**3 / 3 + z**5 / (5 * (1 - z*z)))
    assert log_ratio_upper < Fraction(41, 100)
    assert Fraction(8, 3)**10 > 18_000
    coefficient = Fraction(252, 10) * Fraction(11, 10)
    assert 5000 * Fraction(69, 100) - coefficient * 11**2 - 10 > 0
    assert Fraction(69, 100) - (2 * coefficient * 11 + 1) / 5000 > 0
    endpoint_slope = Fraction(69, 100) - Fraction(2, 3) * Fraction(41, 100)
    assert 9000 * endpoint_slope - coefficient * 11**2 > 0
    assert endpoint_slope - 2 * coefficient * 11 / 9000 > 0
    print("Checked both power-gap brackets, 6,290 endpoint exponents, and rational bounds for the external tail.")


def dyadic_interval(base, exponent, precision):
    def multiply(x, y, round_up):
        value, shift = x[0] * y[0], x[1] + y[1]
        cut = max(0, value.bit_length() - precision)
        unit = 1 << cut
        return (value + (unit - 1 if round_up else 0)) // unit, shift + cut

    low = high = (1, 0)
    for bit in bin(exponent)[2:]:
        low, high = multiply(low, low, False), multiply(high, high, True)
        if bit == "1":
            low = multiply(low, (base, 0), False)
            high = multiply(high, (base, 0), True)
    return low, high


def dyadic_less(x, y):
    shift = min(x[1], y[1])
    return (x[0] << (x[1] - shift)) < (y[0] << (y[1] - shift))


def check_wide_power_bracket():
    rng = Random(21967)
    for _ in range(500):
        base, exponent, precision = rng.randrange(40), rng.randrange(500), rng.randrange(1, 129)
        low, high = dyadic_interval(base, exponent, precision)
        assert low[0] << low[1] <= base**exponent <= high[0] << high[1]
    p, q = 9_809_721_694, 6_189_245_291
    r, s = 630_138_897, 397_573_379
    k = 9_448_000_000
    assert q * r - s * p == 1
    low, _ = dyadic_interval(3, q, 128)
    assert dyadic_less((1, p), low)
    _, high = dyadic_interval(3, s, 128)
    assert dyadic_less(((k + 1) * high[0], high[1]), (k, r))
    assert s * (k + q + s) < 6_400_000_000_000_000_000
    print("Checked 500 small interval enclosures and both billion-scale bracket comparisons.")


def scan_coefficient_crossings(limit, check_interior=False):
    exceptions = {}
    for n in range(3, limit, 2):
        x, a, b = n, 1, 1
        for j in range(1, 101):
            y, v, w = next_excursion(x)
            if check_interior:
                z, odd, dyadic = x, a, b
                for _ in range(v + w):
                    if z % 2:
                        z = (3 * z + 1) // 2
                        odd *= 3
                    else:
                        z //= 2
                    dyadic *= 2
                    if dyadic > odd:
                        break
                assert (dyadic > odd) == (b * 2**(v + w) > a * 3**v)
            x, a, b = y, a * 3**v, b * 2**(v + w)
            if b > a:
                assert x < n
                if b * j >= (b - a) * n:
                    word, ratio, _ = first_word(n)
                    layers = local_layers(word)
                    assert optimum(n, word, layers) < ratio
                    low, high = 0, n
                    while high - low > 1:
                        mid = (low + high) // 2
                        if optimum(mid, word, layers) < ratio:
                            high = mid
                        else:
                            low = mid
                    exceptions[n] = high
                break
        else:
            raise AssertionError(f"no crossing within 100 excursions for {n}")
    print(f"All first crossings below {limit:,} landed below their start.")
    print(f"Coarse bound exceptions and exact optimizer cutoffs: {exceptions}")
    return exceptions


def main():
    rng = Random(61527)
    sign_cuts = 0
    for n in range(3, 20_000, 2):
        word, ratio, descended = first_word(n)
        layers = candidate_layers(word)
        short = local_layers(word)
        assert layers == short
        bound = optimum(n, word, short)
        assert bound < ratio and descended
        parts = sign_parts(n, word)
        if len(parts) > 1:
            sign_cuts += len(parts) - 1
            assert bound == prod(optimum(n, part, local_layers(part)) for part in parts)
        _, _, _, reference = first_crossing(n, uniform(1, 2))
        assert bound <= reference[2]
        if n < 1_000:
            trial = [Fraction(rng.randrange(38), 37) for _ in layers]
            assert bound <= cost(n, word, trial)
    small_runs = [(3**v, 2**(v + w), 2**v) for v in range(1, 5) for w in range(1, 5)]
    assert all(not zero_links_feasible(word) for word in product(small_runs, repeat=3))
    assert zero_links_feasible([small_runs[0], small_runs[0]])
    for _ in range(20):
        word = [rng.choice(small_runs) for _ in range(32)]
        assert local_layers(word) == candidate_layers(word)
        n = rng.randrange(1, 200)
        assert optimum(n, word, local_layers(word)) == prod(
            optimum(n, part, local_layers(part)) for part in sign_parts(n, word)
        )
    for n in (7, 9, 127, 255):
        word, _, _ = first_word(n)
        layers = candidate_layers(word)
        assert optimum(n, word, layers) == min(cost(n, word, shifts) for shifts in product(*layers))
    word, _, _ = first_word(127)
    assert optimum(127, word, candidate_layers(word)) == Fraction(1343488, 1331883)
    word, ratio, descended = first_word(1)
    assert not descended and ratio <= optimum(1, word, candidate_layers(word))
    print("The six-candidate layers matched unrestricted enumeration on all 9,999 first crossings.")
    print("Checked 4,096 triples of small runs by exact affine interval intersection.")
    print("The exact rational optimizer certified all 9,999 first crossings.")
    print("For 127 the exact product is 1343488/1331883, below the sixteenth-grid ceiling.")
    print(f"The sign split preserved the optimum at {sign_cuts:,} boundaries on the audited orbits.")
    check_flat_schedule()
    check_unit_tails()
    check_conflicting_pairs()
    check_greedy_blocks()
    check_reversal_budgets()
    check_floor_monotonicity()
    check_floor_fibres()
    check_power_gap_bracket()
    check_wide_power_bracket()
    assert scan_coefficient_crossings(20_000, check_interior=True) == {
        27: 21, 31: 13, 63: 61, 71: 25
    }


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--coarse-limit", type=int, help="Run only the first-crossing scan below this bound.")
    args = parser.parse_args()
    if args.coarse_limit is None:
        main()
    else:
        scan_coefficient_crossings(args.coarse_limit)
