"""Check the excursion budget against the step-by-step shortcut orbit."""

RATIOS = ((2, 1), (3, 2), (5, 4), (9, 8), (17, 16), (65, 64))


def shortcut_excursions(start):
    current = start
    for _ in range(100):
        odd = halvings = 0
        while current % 2:
            current = (3 * current + 1) // 2
            odd += 1
        while current % 2 == 0:
            current //= 2
            halvings += 1
        yield odd, halvings, current


def audit(start):
    crossings = {}
    a = b = 1
    offset = weight = 0
    minimum = start
    for length, (odd, halvings, landing) in enumerate(shortcut_excursions(start), 1):
        tripling = 3**odd
        offset = tripling * offset + b * (tripling - 2**odd)
        a *= tripling
        b <<= odd + halvings
        weight += (0, 3, 5, 9)[min(odd, 3)]
        minimum = min(minimum, landing)
        assert a * start + offset == b * landing
        if minimum == start:
            assert (9 * start - weight) * b <= 9 * start * a

        for p, d in RATIOS:
            if (p, d) in crossings:
                continue
            assert 9 * d * offset <= p * a * weight
            if p * a < d * b:
                paid = p * weight <= 9 * (p - d) * start
                if paid:
                    assert landing < start
                crossings[p, d] = (length, landing, weight, paid)
        if len(crossings) == len(RATIOS):
            break
    return crossings


def main():
    totals = dict.fromkeys(RATIOS, 0)
    for start in range(3, 2**17, 2):
        for ratio, (_, _, _, paid) in audit(start).items():
            totals[ratio] += paid
    assert audit(47)[2, 1] == (14, 23, 82, True)
    assert audit(3)[5, 4] == (1, 1, 5, True)
    assert audit(1)[2, 1] == (3, 1, 9, False)
    print(f"65,535 odd starts; certified first crossings by ratio: {totals}")


if __name__ == "__main__":
    main()
