# Dyadic-rational separation and growing even budgets

Write \(A_j\) for the shifted accumulator, so
\(2^j(T^j(x)+1)=3^{a_j}(x+1)+A_j\). Let \(N/2^h\) be a
positive dyadic rational in lowest terms, with \(N\ge3^h\).
For \(h=0\), any positive integer numerator is allowed.

If the path has at most \(d\) even steps and
\(2^{p+d}N<3^p\), then

\[
3^p\nmid 2^jN-2^hA_j.
\]

At the last even step, let \(t\) be the following odd count.
The congruence first forces \(3^t\mid N\). Put
\(R=N/3^t\), \(h'=\max(h-t-1,0)\), and
\(c=\min(h,t+1)\). The next numerator is

\[
M=2^{\max(t+1-h,0)}R-2^{h'}.
\]

It satisfies \(M\ge3^{h'}\), and is odd when \(h'>0\).
The exact factorization reduces the even budget by one and
the ternary precision by \(t\). The size estimate
\(3^tM\le2^{t+1}N\) preserves the displayed hypothesis.
After the even budget is exhausted, the nonzero numerator
itself would have to be divisible by too large a power.

For the odd-run ratio \((3/2)^h\), the explicit precision
\(p=2d+3h+1\) suffices, using \(8<9\).

Now suppose \(3^t\mid n\), the first \(i\) steps from \(n\)
are odd, and a smaller source meets that endpoint after
\(i+s\) steps with \(e\) even steps. Combining the two
shifted affine equations forces the rational comparison to
be divisible by \(3^{i+t}\). Separation gives
\(t\le2i+2e\).

Meeting compression replaces \(i\) by at most \(3(e-1)\)
while retaining at most \(e\) even steps. Consequently,
for \(t>0\),

\[
t+6\le8e.
\]

Thus the required even count is unbounded as the original
start's ternary valuation increases, independently of the
allowed time overhead and the original odd-run length.
