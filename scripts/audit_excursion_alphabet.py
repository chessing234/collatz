"""Count bounded profiles and check the spacing of repeated windows."""

from audit_excursion_rays import excursion


def counts():
    checked = 0
    for u, w in ((1, 1), (1, 3), (2, 2), (2, 3), (3, 3)):
        length = u + w
        weight = (2**u - 1) * (2**w - 1)
        for depth in range(4):
            for time in range(length * depth, min(length * depth + 2, 16) + 1):
                found = 0
                for seed in range(1, 2 ** (time + 1), 2):
                    value = seed
                    for _ in range(depth):
                        (v, W), value = excursion(value)
                        if v > u or W > w:
                            break
                    else:
                        found += 1
                assert found == 2 ** (time - length * depth) * weight**depth
                checked += 1
    return checked


def windows():
    residues = {}
    small = {}
    checked = 0
    for seed in range(1, 2**14, 2):
        profile = []
        sources = [seed]
        for _ in range(6):
            run, value = excursion(sources[-1])
            profile.append(run)
            sources.append(value)

        for before, after in ((1, 1), (1, 2), (2, 2), (3, 1)):
            for cut in range(before, len(profile) - after + 1):
                past = tuple(profile[cut - before : cut])
                future = tuple(profile[cut : cut + after])
                period = 3 ** sum(v for v, _ in past) * 2 ** (1 + sum(v + w for v, w in future))
                key = past, future
                value = sources[cut]
                assert residues.setdefault(key, value % period) == value % period
                if value < period:
                    assert small.setdefault(key, value) == value
                checked += 1
    return checked, len(residues)


def main():
    checks = counts()
    seen, distinct = windows()
    print(f"{checks} exact finite box counts; {seen:,} windows over {distinct:,} distinct profiles.")


if __name__ == "__main__":
    main()
