# Computing exact minima after long odd runs

Let \(T\) be the shortcut map. Start at \(n=2^v u-1\) with odd
\(u>0\), and take a suffix of length \(k\) after the initial
odd run. Suppose \(v\ge6k+2\). Each smaller equal-time partner
has a scaled peak \(3^{v-d}u-1\) for some \(1\le d\le k\).
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
