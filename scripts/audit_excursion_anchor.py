#!/usr/bin/env python3
"""Audit the exact anchor search using independent rational factors."""

from fractions import Fraction
from itertools import product
from math import prod
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


def main():
    rng = Random(61527)
    for n in range(3, 20_000, 2):
        word, ratio, descended = first_word(n)
        layers = candidate_layers(word)
        short = local_layers(word)
        assert layers == short
        bound = optimum(n, word, short)
        assert bound < ratio and descended
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


if __name__ == "__main__":
    main()
