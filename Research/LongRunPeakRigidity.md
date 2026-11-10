# Rigidity of fixed-depth meetings after long odd runs

Let \(T\) be the shortcut Collatz map. Fix a suffix length \(k\).
For all sufficiently large \(v\), uniformly in the positive
cofactor \(u\), the start \(n=2^v u-1\) has a smaller equal-time
partner at horizon \(v+k\) exactly when

\[
T^k(3^{v-d}u-1)=T^k(3^v u-1)
\quad\text{for some }1\le d\le k.
\]

Every smaller partner then has one of these lower peaks at
time \(v\). Conversely, padding the shorter odd run with \(d\)
leading halvings constructs a smaller partner with that peak.
The threshold on \(v\) depends on the prescribed suffix length.

Ternary fiber transport first puts each potential lower peak
\(y\) into a family \(y+c=3^{v-d}u\). The pairs \((d,c)\), with
\(c\) allowed to be negative, come from a finite table depending
only on \(k\). The image bound forces at most \(d\) even steps in
any smaller source reaching \(y\) at time \(v\).

The key separation lemma fixes an even-step budget \(d\) and a
nonzero integer \(C\). It gives a precision \(p\), independent of
the window length \(j\), for which

\[
3^p\nmid 2^j C-\operatorname{runA}(j,x)
\]

whenever the window has at most \(d\) even steps. Here
\(\operatorname{runA}\) is the shifted affine defect. If the last
even step is followed by \(t\) odd steps, its contribution and
all prior contributions contain \(3^t\). At a precision beyond
the valuation of \(C\), this bounds \(t\). Dividing out that
factor and removing the last even step replaces \(C\) by

\[
2^{t+1}(C/3^t)-1.
\]

This is an odd integer, so it is nonzero. Induction over the
remaining even-step budget then gives a uniform precision.
Taking \(C=1-c\) excludes every offset except \(c=1\) as the
run length grows. Lean verifies the separation argument using
integer divisibility.
