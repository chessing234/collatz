# Weighted excursion crossings

An excursion consists of a maximal odd run of length `v` in the accelerated
Collatz map, followed by `W` halvings. After any number of excursions, let
`A = 3^Σv`, `B = 2^Σ(v+W)`, and let `y` be the landing from `n`.
In the shifted coordinate, `B(y+1) = A(n+1) + C`.

Extending by one excursion multiplies the old offset by `3^v` and adds
`B_new(1 − 2^(−W))`. The new term is exactly half of `B_new` for
`W = 1` and is at most `B_new` for every `W`. Count one unit for the
first case and two for the second, and write `c` for the total charge.

Suppose that every proper excursion prefix has `B/A ≤ p/q` and the last
excursion gives `B/A > p/q`. Each earlier offset, when carried forward to
the crossing, contributes at most half its charge times the final `B`.
The same bound holds for the crossing excursion, so `2C ≤ cB`. It follows
that `y < n` if `p c ≤ 2(p−q)(n+1)`. In particular, for the first crossing
of `B/A > 2`, it suffices that `c ≤ n+1`.

[The Lean proof](../Collatz/Strategy/ExcursionCrossing.lean) also shows that
an orbit minimum stays below the coefficient cap as long as its charge
fits the budget. A universal proof of a crossing within that budget for
odd starts greater than 1 would imply Collatz. The crossing theorem itself
is conditional.

## Multiplicative bound for an orbit floor

For an excursion ending at `y ≥ n`, write `w = 1` when `W = 1` and
`w = 2` otherwise. Its affine identity implies

```text
2^(v+W) (2n)^w (y+1) ≤ 3^v (2n+1)^w (x+1).
```

Multiplying along a prefix whose landings all stay above or at `n` and
cancelling the intermediate shifted states gives
`B (2n)^c ≤ A (2n+1)^c`. A strict violation forces a descent somewhere in
the prefix, regardless of whether its coefficient ratio ever passed two.
The two-excursion prefix from 7 to 5 is a checked example.

## Rounded budgets for individual prefixes

The previous coefficient ratios need not share a single upper bound.
For a grid of size `1/s`, each proper prefix with denominator `Bᵢ`,
numerator `Aᵢ`, and charge `wᵢ) contributes
`wᵢ ceil(s Bᵢ/Aᵢ)` to an integer debt `D`. This avoids charging a
prefix that expands strongly as much as one near contraction. The last
excursion keeps its actual coefficient. The exact affine offset appears
only in the proof of the budget invariant. The landing is below the start
whenever

```text
A D + s B w_last < 2 s (B − A) (n+1).
```

The Lean proof gives a strict one-grid-unit bound on each ratio's
rounding error. The first excursion coefficient crossing of 63 lands
at 61 with a proper-prefix debt of 24 at scale four.

## Checks

Lean certifies the first factor-two crossing from 27 to 5. It uses 16
excursions with charge 22 and a budget of 28. A uniform charge of two
would cost 32. The [independent scan](../scripts/audit_excursion_crossing.py)
uses elementary accelerated steps and integer arithmetic. All 99,999 odd
starts from 3 through 199,999 crossed each of the thresholds 3/2, 2 and 3
within 100 excursions. The longest factor-two crossing took 33 excursions.
Every factor-two crossing met the budget. At threshold 3/2, the bound was
inconclusive for 27, whose crossing still landed below its start. The
multiplicative bound certified a descent before the factor-two crossing for
49,929 starts and detected the first excursion descent for 99,997 starts.
The rounded budget certified the first excursion coefficient crossing
`B/A > 1` for 99,997 starts at scale one, 99,998 at scale two, and all
99,999 at scale four.

## Relation to published results

- Terras proved that the set of starts with finite stopping time has natural
  density one. His coefficient stopping time uses the first crossing of
  `B/A > 1` at individual accelerated steps.
  [Terras (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)
- Bernstein and Lagarias conjugated the 2-adic Collatz map to the shift.
  This gives a precise parity encoding for finite coefficient profiles.
  [Bernstein and Lagarias (1996)](https://websites.umich.edu/~lagarias/doc/bernstein.pdf)
- Tao proved that for every function `f(n) → ∞`, the orbit minimum is below
  `f(n)` for logarithmic-density-almost-all starts.
  [Tao (2022)](https://doi.org/10.1017/fmp.2022.8)
- Bařina's distributed verification covers every positive start below
  `2^71`. [Verification project](https://pcbarina.fit.vut.cz/)
- Hercher ruled out nontrivial cycles with at most 91 local minima.
  [Hercher (2023), with corrigendum](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
