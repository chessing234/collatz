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

## Switching the shifted coordinate

The product bound can switch between `x/n` and `(x+1)/(n+1)` at each
excursion boundary. For a switch from `s` to `t`, let
`a=3^v`, `b=2^(v+W)`, and
`E=max(0, a(1−s)+bt−2^v)`. A prefix staying at or above `n` has two
valid local upper factors:

- Departure bound `[a(n+s)+E]/[a(n+t)]`.
- Arrival bound `b(n+s)/[b(n+t)−E]` when the denominator is positive.

The normalized state ratios telescope even when the coordinate changes.
Keeping the better factor at each transition gives a two-state dynamic
program. The [Lean proof](../Collatz/Strategy/ExcursionSwitchFloor.lean)
checks the computed factor products and certifies descent from 63 by
accelerated time 54. The [audit](../scripts/audit_excursion_switch_floor.py) computes
the minimum over schedules with exact rational arithmetic. In 9,999 odd
starts below 20,000, switching certified every first excursion coefficient
crossing. Each fixed coordinate missed the crossings from 27 and 63.

## Rational shift grids

The coordinates can use any shifts `s/d` and `t/d` in `[0,1]`.
Set `P=dn+s`, `Q=dn+t`, and
`E=max(0,a(d−s)+bt−d·2^v)`. The scaled departure and arrival factors are
`(aP+E)/(aQ)` and `bP/(bQ−E)`. Their cross-product difference is
`E(bQ−aP−E)`. When `E>0`, the sign is the sign of
`bn+2^v−a(n+1)`, independent of both shifts. When `E=0`, the factors
agree. If the floor test chooses arrival, its denominator is positive.

[Lean](../Collatz/Strategy/ExcursionShiftGrid.lean) checks this reduction,
the grid computation, and the embedding of each schedule into every
integer refinement of its grid. For 63 it verifies an eighth-unit factor
product below `1.0776` by accelerated time 54. The
[independent audit](../scripts/audit_excursion_shift_grid.py) compares
the shared rule with per-edge rational minimization and reproduces the
tighter bound. On the first 9,999 odd starts greater than one, the
half-unit grid certified each first excursion coefficient crossing.

The permitted shifts can also change with the boundary. On the
three-excursion trace from 127 to 77, the three shifts `0, 1/3, 1`
produce a strictly better bound than the entire sixteenth-unit grid.
The schedule using `1/3` before the second excursion and zero after it
makes that transition's affine offset zero. Lean verifies the strict
comparison with every output entry of the uniform table.

## Exact optimization over rational shifts

A finite excursion word admits an exact search over rational shifts in
`[0,1]`. Use the normalized coordinates `P=n+s` and `Q=n+t`, and set
`δ=bn+2^v−a(n+1)`. The shared factor is

- `P/Q` if `bQ ≤ aP+δ`, where the clipped offset is zero.
- `bP/(aP+δ)` on the positive-offset side if `δ ≥ 0`.
- `(bQ−δ)/(aQ)` on the positive-offset side if `δ < 0`.

Consecutive zero offsets link coordinates by affine transport. Their
internal factors telescope. Keeping the neighboring clipping regimes
fixed, the contribution of a whole linked block is a quotient of two
affine functions of its first coordinate. Its determinant fixes the
direction of monotonicity. A feasible endpoint therefore gives a bound
at least as tight as the original one.

At such an endpoint, a coordinate hits `n` or `n+1`, or an exterior
offset becomes zero. In the first case the block has an anchor. In the
second it joins a neighboring block. Either action reduces the number of
unanchored blocks. This gives a schedule of equal or lower cost in which
every coordinate is obtained by transporting a band endpoint along a
consecutive part of the word. A word of length `m` gives at most
`2(m+2)` candidates per boundary, including duplicate endpoints.

[Lean](../Collatz/Strategy/ExcursionAnchorCertificate.lean) verifies the
finite reduction, the backward minimum computation, and the descent
certificate on genuine excursions. For 127 it computes the exact optimum
`1343488/1331883` and certifies descent by accelerated step 15.
The [audit](../scripts/audit_excursion_anchor.py) compared the search with
exhaustive products on small examples and certified 9,999 first crossings.

The remaining universal condition is a strict crossing of the optimal
rational product by the inverse coefficient for every start greater than
one congruent to three modulo four. A finite scan supplies evidence for
this condition on its tested range.

## Six shifts per boundary suffice

A zero-offset transition in the relative shifts `s,t ∈ [0,1]` satisfies
`2^(v+W)t = 3^v(s−1)+2^v`. Its input is at least `1/3` and its output
is at most `1/2`. If the first of two links has `W ≥ 2`, its output
is at most `1/4`, too small for the second. If the second link has
`v ≥ 2`, its input is at least `5/9`, too large for the first.
Thus a pair requires `W_first=1` and `v_second=1`. Its final shift is
at most `1/8`, which excludes a third link.

Forward transports from the lower endpoint leave the band permanently.
Backward transports from the upper endpoint do the same. Consequently
the candidates at a boundary are its two endpoints, up to two forward
transports from the upper endpoint, and up to two backward transports
from the lower endpoint. A one-pass enumeration and a backward dynamic
program use at most 36 factor evaluations per excursion. This counts
rational arithmetic operations. The bit lengths of the operands can
grow along the word.

[Lean](../Collatz/Strategy/ExcursionLocalAnchors.lean) proves equality
with the unrestricted rational optimum for every positive excursion
word. The independent audit checks the reduced layers against the full
enumeration and tests all 4,096 triples with `1 ≤ v,W ≤ 4` by exact
interval intersection.

## The universal crossing criterion is equivalent to Collatz

Suppose an odd start `n > 1` reaches 1. There is a genuine excursion
prefix landing at 1. Append copies of the excursion from 1 back to 1.
With both coordinates fixed at the lower endpoint `n`, each copy
multiplies the product scaled by `A/B` by `3n/(4n−1) < 1`. Enough
copies make the scaled product less than one. The optimal shift
schedule achieves at most the constant schedule's product.

[Lean](../Collatz/Strategy/ExcursionCrossingEquivalence.lean) checks this
implication and the converse via descent induction. The universal
criterion asks for some finite crossing word from each `n > 1`
congruent to three modulo four. Requiring certification at the
*first* coefficient crossing is stronger. It would also give descent
there, the phenomenon studied by
[Garner](https://www.ams.org/journals/proc/1981-082-01/S0002-9939-1981-0603593-2/).

An exact audit of the first 99,999 odd starts greater than one found
two constant-floor misses at the first excursion coefficient crossing.
The local search certified both 27 and 63.

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
- Rozier and Terracol separate the affine coefficient and remainder
  to study finite paths that return above their starting value despite
  coefficient contraction.
  [Rozier and Terracol (2026)](https://doi.org/10.1016/j.disc.2026.115167)
- Tao proved that for every function `f(n) → ∞`, the orbit minimum is below
  `f(n)` for logarithmic-density-almost-all starts.
  [Tao (2022)](https://doi.org/10.1017/fmp.2022.8)
- Bařina's distributed verification covers every positive start below
  `2^71`. [Verification project](https://pcbarina.fit.vut.cz/)
- Hercher ruled out nontrivial cycles with at most 91 local minima.
  [Hercher (2023), with corrigendum](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
