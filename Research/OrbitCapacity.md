# Dyadic occupation and the Collatz multiplier

Write $T(x)=x/2$ for even $x$ and $T(x)=(3x+1)/2$ for odd $x$. Let
$a_k(x)$ count the odd sources among the first $k$ shortcut steps.

For $x<c2^k$, the inequality $T^k(x)<c3^{a_k(x)}$ follows by induction
on the first step. This supplies the compression half of the
Garcia–Tal occupation argument. At depth $5h$, sources below
$2^{5h+1}$ with at most $3h$ odd steps have images below $2\cdot27^h$.
If the sources belong to one injective orbit, their images are
distinct. There are therefore at most $2\cdot27^h$ such sources.

For the complementary sources, summing $2^{a_{5h}(x)}$ over the two
complete dyadic periods gives $2\cdot243^h$. Each source counted in the
complement has weight at least $8^h$. Hence there are at most
$2\cdot31^h$ of them. Together the two bounds give occupation at most
$4\cdot31^h$ below $2^{5h+1}$, so taking sufficiently spaced cutoffs
gives the geometric capacity required by the reciprocal product lemma.

For any positive injective orbit and some fixed $C$, Lean now proves
that $2^kT^k(x)\le Cx3^{a_k(x)}$ at every shortcut step. Since
$T^k(x)$ tends to infinity on such an orbit, the multiplier
$3^{a_k(x)}/2^k$ must also tend to infinity. The result gives a
necessary condition on a divergent orbit. Excluding such growth and
excluding nontrivial positive cycles remain open.

Garcia and Tal's Lemma 3 and equation (6) give the counting argument
and a bound in translated intervals. Pulowski previously noted the
reciprocal consequence of their estimate. This formalization uses an
explicit integer moment and a finite product in place of a real series.
[Garcia and Tal (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf),
[Pulowski's derivation](https://mathoverflow.net/questions/513539/is-it-known-that-a-divergent-collatz-trajectory-must-have-summable-reciprocals)

`ForbiddenParity.lean` gives a separate counting result for collections
of positive starts whose futures omit one common parity block. At depth
$Lk+1$ each such start uses $k$ allowed length-$L$ blocks and one last bit.
The Terras residue bijection then bounds the number of distinct starts
below $2^{Lk+1}$ by $2(2^L-1)^k$.
[Terras (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)

## Large segments and least periods

The occupation argument only requires distinct states to have distinct
images after a common number of steps. Both injective orbits and the
distinct states on a cycle satisfy this condition.

Let $P$ be the universal dyadic stride, and let $K=2^{q+1}$.
For a segment of distinct sources all at least $2^{P(P+q)+1}$,
the common-denominator calculation bounds its correction by
$K/(K-1)$. In particular, a multiplier below $(K-1)/K$
forces the endpoint below the start. For a positive cycle of least
shortcut period $L$ with all states above the cutoff, the endpoint
equals the start, so its normalized gap satisfies

$$
0 < 1-\frac{3^{a_L}}{2^L} \le \frac{1}{K}.
$$

The bound on the normalized gap depends on the size cutoff and applies
uniformly in the least period. The stride supplied by the elementary
moment bound gives very large cutoffs. The result supplies a
necessary constraint on large cycles.
