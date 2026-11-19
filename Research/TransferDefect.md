# Finite-memory transfer functions

The odd-to-odd Collatz step is `T(n) = (3n+1) / 2^v` with `v = v₂(3n+1)` and
increment `φ(n) = log 3 − v log 2`. On the odd 2-adic units, `v` is geometric
with `P(v = j) = 2^{−j}`, so the mean of `φ` is `log(3/4)`. The centered
increment is

    φ(n) − log(3/4) = (2 − v) log 2.

A level-`k` potential depends on an odd input only through `n mod 2^k`. The
uniform defect of such a potential is the least `D` such that

    φ(n) − log(3/4) ≤ D + h(T(n)) − h(n)

for every odd `n`. Equivalently, in units of `log 2`, the weights are `2 − v`
and `D / log 2` is the maximum cycle mean of those weights on the legal residue
graph.

## The defect does not decay

For every `k ≥ 1` the odd integer `n = 2^{k+1} − 1` satisfies

    T(n) = 3·2^k − 1,    v = 1,
    n ≡ T(n) ≡ −1  (mod 2^k),    T(n) > n.

The centered weight of this step is `1`. Any level-`k` potential takes the same
value at `n` and at `T(n)`, so the defect is at least `log 2`.

No step has valuation `0`, so every centered weight is at most `1`. The zero
potential therefore meets the same bound. For every `k ≥ 1`,

    D_k = log 2.

The maximum cycle mean is realized by a self-loop of the residue `−1`, which is
the 2-adic fixed point `T(−1) = −1`. It is legal as a one-step transition of
positive integers, and it can be repeated in the residue graph. The worst-case
path gain on that graph is consequently infinite. Both quantities that a
min-plus computation would return are independent of `k`: the cycle mean is
`log 2`, and the path gain does not exist as a finite number.

The same obstruction is multiplicative and does not use logarithms. If `q` is
positive and constant on residue classes modulo `2^k`, the ghost step has
`T(n)/n > (3/2) q(T(n))/q(n)`. `TransferDefect.lean` records this witness.
Finite memory in the uniform norm is not a hierarchy. It is the same
obstruction at every level, already visible modulo `4`.

## What still moves

The mean-square size of the centered residual can fall, because the ghost class
has Haar mass `2^{−k}`. Least squares for a level-`k` potential, using every odd
residue modulo `2^{k+6}` whose valuation is at most `6` (so the image modulo
`2^k` is determined), gives:

| k | rms | positive-part rms | worst excess | omitted mass |
|---|-----|-------------------|--------------|--------------|
| 2 | 1.002 | 0.603 | 1 | 0.0156 |
| 3 | 0.874 | 0.534 | 1 | 0.0156 |
| 4 | 0.789 | 0.484 | 1 | 0.0156 |
| 5 | 0.730 | 0.451 | 1 | 0.0156 |
| 6 | 0.684 | 0.424 | 1 | 0.0156 |
| 7 | 0.629 | 0.403 | 1 | 0.0156 |
| 8 | 0.590 | 0.385 | 1 | 0.0156 |

The zero potential has rms `√2 ≈ 1.414` on the exact geometric law. The
least-squares worst excess remains `1` at every computed level, in agreement
with the uniform theorem. The rms decreases through eight bits, and the
successive ratios are moving back toward `1`, so these values do not identify
a Collatz regularity exponent. The script is `scripts/transfer_defect.py`.

A proof in this language has to use a potential that is not locally constant,
or a norm that gives the ghost class vanishing weight. The uniform cocycle on
residue classes is settled, and it does not tend to zero.
