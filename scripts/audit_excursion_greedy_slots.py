"""Test distinct-slot bounds for nested mixed excursion residues."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement, product

from audit_excursion_lattice import mixed_class


def assign(classes, floor):
    used = set()
    for residue, modulus in sorted(classes, key=lambda pair: -pair[1]):
        slot = floor + (residue - floor) % modulus
        while slot in used:
            slot += modulus
        used.add(slot)
    return sorted(used)


def exhaustive_check():
    floor = 25
    domain = range(floor, 58, 4)
    classes = [(1 + 4 * r, 4 * 3**p) for p in range(3) for r in range(3**p)]
    checked = 0
    for size in range(1, 5):
        for required in combinations_with_replacement(classes, size):
            options = [[x for x in domain if x % d == r] for r, d in required]
            greedy = assign(required, floor)
            for competitor in product(*options):
                if len(set(competitor)) == size:
                    assert all(g <= x for g, x in zip(greedy, sorted(competitor)))
                    checked += 1
    return checked


def audit(start):
    landing = start
    previous = None
    groups = defaultdict(list)
    elapsed = 0
    for _ in range(100):
        source = landing
        v = w = 0
        while landing % 2:
            landing = (3 * landing + 1) // 2
            v += 1
        while landing % 2 == 0:
            landing //= 2
            w += 1
        elapsed += v + w
        r, d = mixed_class(v, previous)
        assert source % d == r
        groups[v].append((r, d, source))
        previous = v, w
        if landing < start:
            break
    else:
        raise AssertionError(f"No excursion descent from {start}")

    mixed = greedy = actual = Fraction(1)
    for v, visits in groups.items():
        sources = sorted(x for _, _, x in visits)
        assert len(set(sources)) == len(sources)
        slots = assign([(r, d) for r, d, _ in visits], start)
        assert all(g <= x for g, x in zip(slots, sources))
        a = 3**v
        c = a - 2**v
        for x, slot, (r, d, _) in zip(sources, slots, visits):
            candidate = start + (r - start) % d
            mixed *= Fraction(a * candidate + c, candidate)
            greedy *= Fraction(a * slot + c, slot)
            actual *= Fraction(a * x + c, x)
    denominator = 2**elapsed
    assert actual == Fraction(denominator * landing, start)
    assert actual <= greedy <= mixed
    return greedy < mixed, denominator > mixed, denominator > greedy


def main():
    checked = exhaustive_check()
    counts = Counter(audit(n) for n in range(3, 2**17, 2))
    assert counts == {(False, True, True): 62_566, (True, True, True): 2_969}
    assert audit(27) == (True, True, True)
    print(f"{checked:,} feasible assignments checked; 2,969 tighter first-drop bounds over 65,535 starts.")


if __name__ == "__main__":
    main()
