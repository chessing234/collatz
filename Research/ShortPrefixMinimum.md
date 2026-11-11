# Computing exact minima after long odd runs

Let \(T\) be the shortcut map. Start at \(n=2^v u-1\) with odd
\(u>0\), and take a suffix of length \(k\) after the initial
odd run. Write \(a\) for the suffix odd count and suppose
\(v\ge2k+2+4(k-a)\). Each smaller equal-time partner
has a scaled peak \(3^{v-d}u-1\) for some \(1\le d\le k-a\).
For each such drop, set \(J=4d-3\). The entire corresponding
family of smaller partners has the same \(J\)-step image.

\[
T^J(m)=2^{v-J}3^{J-d}u-1.
\]

The scaled peak requires at most \(d\) even steps in the
prefix and forces its shifted defect to be divisible by
\(3^{v-d}\). If its last even step is at index \(i\), followed
by \(t\) odd steps, then the defect is
\(3^t(\operatorname{runA}(i,m)+2^i)\).
The separation estimate for \(C=-1\) and \(d-1\) even steps
rules out \(3^{3(d-1)+1}\) dividing the parenthesized term.
Therefore \(i+1\le4d-3\). The remaining steps after \(J\) are
all odd, which gives the displayed image.

For each certified drop, the padded shorter odd run supplies
one source in the corresponding \(J\)-step fiber. The least
source of that short fiber still meets \(n\) at horizon
\(v+k\). Taking the minimum of \(n\) and these short-fiber
minima therefore gives the exact least equal-time partner.
The search depths depend on the drops and the suffix length.
For example, the executable Lean check handles \(v=10015\),
\(u=1\), and \(k=8\), giving the exact minimum
\((2^{10015}-5)/3\).

## Chains with varying suffix lengths

A certified drop from \(v\) to \(w\) gives a common endpoint at
suffix horizon \(k\), with \(v-w\) more odd steps on the shorter
peak's path. At every later common horizon \(K\), both paths
have the same additional odd steps. The quantity
\(v+a_K(3^v u-1)\) is therefore constant along a chain of
certificates with horizons at most \(K\).

If the chain starts at \(v_0\) and ends at \(v_N\), its total
drop is at most \(K-a_K(3^{v_0}u-1)\). The adaptive cutoff lets
us choose \(K=\lfloor v_0/2\rfloor\) for the entire chain, and
the fixed cutoff lets us choose \(K=\lfloor v_0/6\rfloor\).
The cofactor stays fixed throughout. For example, the drop from
79 to 78 has a certificate at horizon 9, and the drop from 78
to 77 has one at horizon 2. Their combined drop increases the
odd count at horizon 9 by exactly two.
