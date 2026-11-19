#!/usr/bin/env python3
"""Centered finite-memory defect of the odd-to-odd Collatz step.

The uniform defect is proved separately to equal one unit of log 2 at every
level. This script measures the mean-square defect of the best potential that
depends only on the residue modulo 2^k. The centered increment of a step with
valuation v is 2-v.
"""

from __future__ import annotations

import math


def trailing(x: int) -> int:
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def zero_potential_second_moment(limit: int = 80) -> float:
    """E[(2-v)^2] for P(v = j) = 2^{-j}."""
    return sum((2 - j) ** 2 * 2.0 ** (-j) for j in range(1, limit + 1))


def solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    a = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(a[r][col]))
        if abs(a[pivot][col]) < 1e-12:
            raise RuntimeError("singular normal matrix")
        a[col], a[pivot] = a[pivot], a[col]
        scale = a[col][col]
        for j in range(col, n + 1):
            a[col][j] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = a[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                a[row][j] -= factor * a[col][j]
    return [a[i][n] for i in range(n)]


def level_rms(k: int, extra: int) -> tuple[float, float, float, float]:
    """Return rms, positive-part rms, worst centered excess, omitted mass."""
    coarse = 1 << k
    fine = 1 << (k + extra)
    index = {a: i for i, a in enumerate(range(1, coarse, 2))}
    nvar = len(index)
    rows: list[tuple[int, int, int]] = []
    omitted = 0
    seen = 0
    for b in range(1, fine, 2):
        seen += 1
        w = 3 * b + 1
        v = trailing(w)
        # v extra bits are required before the image is known modulo 2^k.
        if v > extra:
            omitted += 1
            continue
        image = (w >> v) % coarse
        rows.append((index[b % coarse], index[image], 2 - v))
    ata = [[0.0] * nvar for _ in range(nvar)]
    atb = [0.0] * nvar
    for i, j, c in rows:
        ata[i][i] += 1.0
        ata[j][j] += 1.0
        ata[i][j] -= 1.0
        ata[j][i] -= 1.0
        atb[i] -= float(c)
        atb[j] += float(c)
    for j in range(nvar):
        ata[0][j] = 0.0
    ata[0][0] = 1.0
    atb[0] = 0.0
    solution = solve(ata, atb)
    square = 0.0
    for i, j, c in rows:
        gap = (solution[j] - solution[i]) - c
        square += gap * gap
    positive = 0.0
    worst = -1e300
    for i, j, c in rows:
        residual = c - (solution[j] - solution[i])
        if residual > 0.0:
            positive += residual * residual
        worst = max(worst, residual)
    return (
        math.sqrt(square / len(rows)),
        math.sqrt(positive / len(rows)),
        worst,
        omitted / seen,
    )


def main() -> None:
    baseline = math.sqrt(zero_potential_second_moment())
    print(f"zero potential rms = {baseline:.6f}")
    print(f"{'k':>3} {'extra':>5} {'rms':>10} {'pos':>10} {'worst':>10} {'omitted':>10}")
    for k in range(2, 9):
        rms, positive, worst, omitted = level_rms(k, 6)
        print(f"{k:3d} {6:5d} {rms:10.6f} {positive:10.6f} {worst:10.6f} {omitted:10.4f}")


if __name__ == "__main__":
    main()
