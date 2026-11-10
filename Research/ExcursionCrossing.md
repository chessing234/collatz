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

## A symbolic crossing obstructed by its entry residue

For a unit excursion `(v,W)=(1,1)` the floor drift is `n−1`. The
factor is at least `4P/(3P+n−1)`, including when it is clipped. This
quantity increases with `P` on the band and equals `4n/(4n−1)` at
`P=n`. The constant floor attains this bound simultaneously on
every unit edge, so a length-`j` unit block has exact minimum
`(4n/(4n−1))^j`.

Genuine unit blocks satisfy `4^j(y−1)=3^j(x−1)`. Since their exit
is odd, their entry obeys `x≡1 (mod 2·4^j)`. Conversely, an entry
`1+2·4^j d` has this block and exits at `1+2·3^j d`. If a single
preceding excursion begins at `n`, lands at `x>1`, and the total
homogeneous coefficient is less than one, then `n≥2·3^j`.

For example, the first genuine excursion from 7 lands at 13 with
`(v,W)=(3,1)`. Appending two symbolic unit edges gives its first
homogeneous crossing `B/A=256/243`, below the exact product
`1792/1539`. The required entry residue is 1 modulo 32, which
excludes 13. The actual next excursion lands at 5 with `(1,2)`.
[Lean](../Collatz/Strategy/ExcursionContractionTail.lean) checks the
exact unit optimum, the residue criterion, and the example.

## Independent optimization at a drift sign boundary

A nonnegative-drift edge prefers the arrival expression, and its
transport of any source in the band is at most `n+1/2`. A
negative-drift edge prefers the departure expression. Its odd run
has length at least two, so the inverse transport of any target in
the band is at least `n+5/9`.

At a boundary from nonnegative drift to negative drift, setting the
shared coordinate to `n+1/2` leaves both edges unclipped. With the
other coordinates fixed, each then attains its best factor. Hence
one can optimize both parts independently and join them at the
midpoint. Conversely, any full schedule restricts to a feasible
schedule on each part. The exact full minimum is therefore the
product of the separate minima. This applies at every such boundary.

[Lean](../Collatz/Strategy/ExcursionSignSplit.lean) checks the
factorization and the five-excursion prefix from 27, which splits
after the third excursion. The two products are `875008/841995`
and `12224/11907`.

## Two excursions in the opposite drift order

Each factor increases weakly with its source shift and decreases
weakly with its target shift. For a pair with negative drift first
and nonnegative drift second, set the first coordinate to `n` and
the last to `n+1`. Both edges are then unclipped for every common
coordinate `q` in the band. Their product is

```text
(b₂/a₁) (b₁ q − δ₁) / (a₂ q + δ₂).
```

It is minimized at an endpoint. The lower endpoint is at least as
good as the upper exactly when `b₁δ₂ + a₂δ₁ ≥ 0`.
[Lean](../Collatz/Strategy/ExcursionPairMinimum.lean) checks the
formula for the exact optimum and both strict outcomes. The first
two excursions from 7 prefer the lower endpoint, while the second
and third excursions from 27 prefer the upper.

## One coordinate controls a whole drift reversal

The quotient of a factor by its source shift decreases as that
source increases. The product of a factor with its target shift
increases as that target increases. Together with ordinary shift
monotonicity, these inequalities give two optimal moves with the
outer coordinates fixed.

- After a nonnegative-drift edge, choose the greater of the floor
  and its transport of the previous coordinate.
- Before a negative-drift edge, choose the lesser of the ceiling
  and its inverse transport of the next coordinate.

Starting from the common coordinate, apply the second rule backwards
through the negative block and the first forwards through the
nonnegative block. These schedules attain the exact optimum for that
common coordinate. The backward schedule reaches the ceiling by its
second move, and the forward schedule reaches the floor by its third.
Every later coordinate stays at the corresponding endpoint. At most
five excursions around the reversal contribute a shift-dependent
factor.

[Lean](../Collatz/Strategy/ExcursionGreedyShifts.lean) proves the two
greedy optima and proves that testing the local anchors at the
common boundary suffices. At a genuine reversal there are at most
five candidates. The last negative edge has odd-run length at least
two and therefore cannot end a two-edge forward zero-offset block.
The crossing from 199 attains five distinct candidates. On the
crossing from 543 the unique best shift is `7/9`, obtained by
transporting backwards over two excursions. The crossing from 127
has exact product `1343488/1331883`.

## A direct budget at drift reversals

The individual ideal factors are
`bn/(bn+2^v−a)` for nonnegative drift and
`[a(n+1)+b−2^v]/[a(n+1)]` for negative drift. The first is attained
whenever the source shift is the floor. The second is attained
whenever the target shift is the ceiling. The two requirements
conflict only when a negative edge is followed by a nonnegative one.

At a conflicting pair, a binary schedule can retain the smaller
ideal factor and replace the larger by `(n+1)/n`. The sharper rule
places the outer coordinates at their worst values, source `n+1`
and target `n`, and compares the two clipping thresholds for the
common coordinate. Outside the thresholds weighted monotonicity
moves the product toward one of them. Between them the product is
linear-fractional, so a threshold attains the minimum there as well.

The conflicting pairs are disjoint. For each pair take its two-
threshold bound, and for every remaining edge take its ideal factor.
The product bounds the exact optimizer and certifies descent when
it is strictly below the inverse homogeneous coefficient.
[Lean](../Collatz/Strategy/ExcursionReversalBudget.lean) checks the
schedule construction and the crossing from 63. The independent
audit found that charging the full band ratio at each reversal
missed 27 and 63, charging the larger ideal factor missed only 63,
and the two-threshold budget certified all 99,999 tested first
crossings.

## Certificate thresholds for a fixed word

Keep the run parameters and relative shifts fixed while raising the
proposed floor. The clipping inequality is independent of that floor.
On a clipped edge the source shift is larger than the target shift,
so their coordinate ratio decreases strictly as the floor rises. In
the unclipped case each affine quotient has a strictly decreasing
determinant. If the drift changes sign, the new arrival formula is
at most the departure formula at the same floor.

It follows that the optimal rational product of any nonempty word
strictly decreases with the floor. Equality with the inverse
coefficient at a smaller floor is enough to certify a larger
genuine realization. For a word of length `j` with coefficients
`A<B`, the explicit condition `B j < (B−A)n` ensures a crossing.
It follows by bounding each factor by `(n+1)/n` and using
`((n+1)/n)^j ≤ n/(n−j)` for `j<n`.

The certifying positive floors therefore form an upper interval
with an effectively bounded first element. [Lean](../Collatz/Strategy/ExcursionFloorMonotonicity.lean)
checks the threshold exactly for the word of the first crossing from
63. Its abstract threshold is 61. A floor in this interval certifies
an actual start when that start follows the word.

## Spacing restricts the unresolved starts of a word

Two starts following the same excursion word satisfy
`B(y₂−y₁)=A(n₂−n₁)`. Both exits are odd. Since `A` is a power
of three and `B` is a power of two, the starts differ by a multiple
of `2B`.

If `2(B−A)>j`, where `j` is the number of excursions, every
realization after the least one is above the certificate cutoff.
More generally, a realization at distance `2Bq` from an earlier
one can avoid descent through the word only if `2(B−A)q≤j`.
The gap condition is automatic when the total odd and accelerated
step counts share a divisor greater than one and `B>A`. Factoring
the difference of powers leaves a term at least as large as the
penultimate power of three.

[Lean](../Collatz/Strategy/ExcursionFloorFibres.lean) verifies
the spacing, the bound on the index, and descent from 139 along
the first crossing word from 11. These two starts are one source
period apart, with three odd steps in six accelerated steps.

## A power-gap bracket removes larger realizations

Write `A=3^a` and `B=2^b>A`. When `17≤a<3631`, a putative
gap `2(B−A)≤a` forces

```text
1054/665 < b/a < 4701/2966.
```

The lower comparison follows from `2^1054<3^665`. For the upper,
`2049·3^2966≤2048·2^4701`, while the small gap and
`2049·2966·a<3^a` imply
`2048·(B/A)^2966<2049`. The latter inequality follows from an
integer binomial bound. The bracket has determinant one, so any
integer fraction strictly between its endpoints has denominator
at least `665+2966=3631`. Below 17 a small finite check suffices.
[Lean](../Collatz/Strategy/ExcursionPowerGap.lean) checks all
these integer steps and gives descent on all nonminimal genuine
realizations with fewer than 3,631 odd steps.

For the remaining exponents, [Laurent's positive-real bound](https://www.impan.pl/shop/en/publication/transaction/download/product/82485),
Corollary 2 with table parameter 10, gives the following external
analytic argument. Set `Λ=b log 2−a log 3>0`. Use logarithmic
height parameters 1 and `log 3` and `b'<2b`. The bound gives
`log Λ ≥ −25.2 log 3·max(10,log(2b)+0.38)^2`. When `b≥5000`,
the expression
`b log 2 − 25.2 log 3·max(10,log(2b)+0.38)^2 − log b`
is positive. At 5000 it exceeds
`5000·0.69−25.2·1.1·11²−10`. On the variable branch its
derivative is positive since `(log(2b)+0.38)/b` decreases there
and is at most `11/5000`. On the constant branch the derivative
is `log 2−1/b`. If `B<2A`, the inequality
`Λ<(B−A)/A` gives `2(B−A)>BΛ>b>a`. If `B≥2A`,
the gap is at least `A`, which is greater than `a`.
The case `b<5000` lies in the Lean range because `3a<2b`.

The Lean theorem takes this analytic tail as a named hypothesis.
With that input, only the least realization of each contracting
word can still need a descent argument.

## Sources at least the tripling coefficient descend

A stronger bracket uses the same lower fraction `1054/665`
and upper fraction `8917/5626`. Its determinant is one and
its denominator sum is 6,291. For `a≥23`, failure of
`3^a≤2^(a+1)(2^b−3^a)` makes the relative gap small enough
for the same integer binomial comparison. Below 23 a finite
integer check handles the remaining small exponents.

For `b≥9000`, Laurent's bound as above supplies this stronger
gap. Use `3a<2b` and subtract `(2b/3)log(3/2)` from
`b log 2−25.2 log 3·max(10,log(2b)+0.38)^2`. The result is
positive at 9000 by `log 2>0.69`, `log(3/2)<0.41`,
`log 3<1.1`, and `log(18000)+0.38<11`. The same derivative
bound proves positivity thereafter. Thus `BΛ>(3/2)^a`,
which gives the desired gap if `B<2A`. The case `B≥2A`
follows from `B−A≥A`. The case `b<9000` has `a<6291`.
[Laurent, Corollary 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82485)

For `n≥B`, the terminal-halving offset bound on `main` gives
`2^a(2^W C+B)≤BA`, where `By=An+C` and `W≥1` is the last
even run. The gap yields `2^a 2^W(B−A)n≥BA>2^a 2^W C`, so
the last landing satisfies `y<n`. If `A≤n<B`, the source and
landing quotient identity already gives `y<A≤n`.
This holds for any genuine contracting coefficient word, including
canonical sources between `A` and `2B`.
[Lean](../Collatz/Strategy/ExcursionCanonicalCrossing.lean) checks
the finite range and keeps the analytic tail explicit.

For a first-crossing proof, the two remaining tasks are universal
coefficient coverage and descent at canonical sources below
the tripling coefficient of their first-crossing word. A finite
trace with a crossing contains a first crossing whose proper
excursion prefixes are all heavy.

## Coefficient coverage and divergence

During an excursion, the homogeneous coefficient increases
through its odd steps and decreases through its even steps.
Thus any shortcut coefficient crossing from an odd start
forces an excursion boundary crossing. A repeated shortcut
state gives a positive period whose homogeneous coefficient
is strictly below one. Enough repeats then outweigh the
coefficient of the initial segment.

Conversely, universal coverage gives arbitrarily late odd
states whose coefficients measured from the original start
are at most one, by concatenating crossings. The multiplier
escape theorem on `main` makes this impossible on an
injective orbit. [Lean](../Collatz/Strategy/ExcursionCoefficientCoverage.lean)
therefore identifies universal coverage with the absence of
injective shortcut orbits from odd starts.

## A finite reduction with billion-scale exponents

The fractions `9809721694/6189245291` and
`630138897/397573379` bracket `log₂ 3` and have
determinant one. Lean checks both sides by outward-rounded
dyadic interval squaring with 128-bit precision. Only the
small significands are multiplied. Binary shifts cancel
when the intervals are compared.

Write `p/q` for the lower fraction, `r/s` for the upper,
and let `K=9448000000`. If `a<q+s` and `A=3^a<B=2^b`,
then `b/a≥r/s`. The verified upper comparison
`(K+1)3^s≤K·2^r` implies `(K+a)A^s≤K·B^s` by
Bernoulli's inequality. The gap estimate
`(A−s(B−A))B^s≤A^(s+1)` then gives
`aA≤s(K+a)(B−A)`. The same conclusion is immediate
when `s(B−A)≥A`.

At a failed first excursion crossing, `(B−A)n≤C≤aA`.
Thus `n<6.4·10^18` whenever `a<6,586,818,670`.
The first shortcut coefficient crossing lies in the final
halving run of that same excursion word. Its orbit value
is at least the excursion landing. So the published
coefficient-stopping-time equality through `2.8·10^19`
excludes every failure in the bracket's range. Lean keeps
that finite verification as an explicit premise of the
descent theorem and proves the source bound independently.
[Lean](../Collatz/Strategy/ExcursionFiniteCrossing.lean)
[Rozier and Terracol, Corollary 5.4](https://arxiv.org/pdf/2502.00948)

The [integer scan](../scripts/audit_excursion_anchor.py) checks
the boundary argument against individual shortcut steps on
9,999 odd starts. With `--coarse-limit 10000000`, it checks
4,999,999 odd starts. Every first excursion crossing lands
below its start. The coarse bound `Bj<(B−A)n` is inconclusive
at 27, 31, 63 and 71. Their exact optimizer cutoffs are
21, 13, 61 and 25 respectively.

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
