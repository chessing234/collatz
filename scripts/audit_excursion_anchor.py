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
        bound = optimum(n, word, layers)
        assert bound < ratio and descended
        _, _, _, reference = first_crossing(n, uniform(1, 2))
        assert bound <= reference[2]
        if n < 1_000:
            trial = [Fraction(rng.randrange(38), 37) for _ in layers]
            assert bound <= cost(n, word, trial)
    for n in (7, 9, 127, 255):
        word, _, _ = first_word(n)
        layers = candidate_layers(word)
        assert optimum(n, word, layers) == min(cost(n, word, shifts) for shifts in product(*layers))
    word, _, _ = first_word(127)
    assert optimum(127, word, candidate_layers(word)) == Fraction(1343488, 1331883)
    word, ratio, descended = first_word(1)
    assert not descended and ratio <= optimum(1, word, candidate_layers(word))
    print("The exact rational optimizer certified all 9,999 first crossings.")
    print("For 127 the exact product is 1343488/1331883, below the sixteenth-grid ceiling.")


if __name__ == "__main__":
    main()
