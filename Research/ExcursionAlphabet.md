# Counting bounded excursion profiles

A realized profile of duration $S$ has one source class modulo
$2^{S+1}$. For a list of allowed runs with maximum duration $L$, set
$W=\sum_r 2^{L-\operatorname{duration}(r)}$. Among odd sources below
$2^{T+1}$, at most $2^{T-Lk}W^k$ distinct sources can realize $k$
runs from that list when $Lk\le T$. The weight factors as a power
because each extra symbol contributes its own dyadic cost.

For the rectangle of odd-run lengths at most $u$ and halving lengths
at most $w$, the weight is $(2^u-1)(2^w-1)$, strictly below $2^{u+w}$.
Lean proves that the proportion of eligible sources can be made
arbitrarily small by increasing the profile depth. A consequence is
that an injective sequence of excursion states whose future runs
stay in one such rectangle cannot be bounded above by a linear
function of the sample index. For a hypothetical divergent orbit,
this leaves the cases of superlinear spread or unbounded run lengths.
The stronger geometric estimate gives a positive scale spacing $P$
with at most $2^{(P-1)j}$ such distinct states below $2^{Pj+1}$.

The separate window argument uses both sides of a boundary. Among
more than $K^{p+q}$ sampled windows over $K$ symbols with $p$ past and
$q>0$ future excursions, two share their code. If all values lie
below their joint periods, the two values coincide. Otherwise a
distinct family has a value at least the joint period lower bound,
using the minimum odd count in its past and elapsed time in its future.

Lean checks the counting and dispersion theorems and concrete
examples. The audit matches the integer count formula in 56 finite
cases and checks joint residues for 122,880 windows. The parity
cylinder method is classical. The development uses compressed
excursion words and applies the weighted count to distinct states.
[Terras (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)
