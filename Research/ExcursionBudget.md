# Weighted excursion crossings

Write $V$ for the number of odd steps in an excursion chain and $S$ for
its total number of shortcut steps. Its multiplier is $3^V/2^S$. A run of
$v$ odd steps has an offset of $3^v-2^v$ before division by its full
excursion denominator. In the offset divided by $3^V$, the run contributes
its normalized offset $1-(2/3)^v$ times the inverse multiplier immediately
before that run.

Give an excursion weight $3$ for $v=1$, $5$ for $v=2$, and $9$
for $v≥3$. The first two are exact ninths of the normalized offset.
The third bounds the offset uniformly, even for very long runs.

Let $H$ be the sum of the weights. If all proper excursion prefixes have
inverse multiplier at most $p/d$, and the final prefix has inverse
multiplier strictly above $p/d$, then the final landing is below the
positive source $n$ whenever $pH≤9(p-d)n$. Lean proves a generic
version for any per-run majorant. In particular, a first half-multiplier
crossing descends when $2H≤9n$, with no fixed bound on the chain length.
For 47 the first half-multiplier crossing at an excursion endpoint occurs
on excursion 14, at shortcut time 55, and lands at 23 with $H=82$.

There is also a finite survival constraint. If the shortcut orbit stays at
or above $n$ through time $S$, then

$$
  \max(9n-H,0)\,2^S \le 9n\,3^V.
$$

The affine expansion and coefficient crossing framework are classical.
Terras's stopping-time threshold is a multiplier of one and is measured
at individual shortcut steps. The result here uses run-dependent charges
at complete excursion endpoints and an arbitrary rational threshold below
one. The repository's earlier `RunRefined` development already exploited
adjacent odd steps to refine a heavy-prefix offset bound. The new formal
result is the all-length excursion criterion and finite survival bound.
Priority for this precise formulation remains unverified.
[Terras (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)

The criterion requires a crossing and enough budget. For comparison,
Tao's theorem gives almost-bounded orbit minima in logarithmic density,
Barina published computational verification through $2^{71}$, and
Hercher bounded the number of local minima in any nontrivial cycle.
These are different kinds of evidence about the conjecture.
[Tao (2022)](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/almost-all-orbits-of-the-collatz-map-attain-almost-bounded-values/1008CC2DF91AF87F66D190C5E01C907F),
[Barina (2025)](https://link.springer.com/article/10.1007/s11227-025-07337-0),
[Hercher](https://arxiv.org/abs/2201.00406)

The independent audit advances the shortcut map one step at a time for
65,535 odd starts and checks the affine identity, the survival inequality,
and first crossings at six rational thresholds. The Lean audit checks the
fourteen-excursion witness for 47 and a $5/4$ inverse-multiplier crossing
from 3 where the length-two charge of five is needed for the stated budget.

The odd-run budget and the shifted-coordinate halving budget from PR #34
can certify different crossings. For the $5/4$ crossing from 3 the
odd-run budget passes and the halving budget fails. For the $16/13$
crossing along $7\to13\to5$, the odd-run test requires $192≤189$ and
the halving test requires $48≤48$.
