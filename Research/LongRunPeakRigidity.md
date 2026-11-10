# Rigidity of fixed-depth meetings after long odd runs

Let \(T\) be the shortcut Collatz map. Fix a suffix length \(k\).
For every \(v\ge6k+2\), uniformly in the positive
cofactor \(u\), the start \(n=2^v u-1\) has a smaller equal-time
partner at horizon \(v+k\) exactly when

\[
T^k(3^{v-d}u-1)=T^k(3^v u-1)
\quad\text{for some }1\le d\le k.
\]

Every smaller partner then has one of these lower peaks at
time \(v\). Conversely, padding the shorter odd run with \(d\)
leading halvings constructs a smaller partner with that peak.
The suffix can grow linearly with the initial odd run. If the
original shifted peak minus one has \(a\) odd steps in its suffix,
the smaller cutoff \(v\ge2k+2+4(k-a)\) suffices, and every smaller
partner has a drop \(d\le k-a\).

Write the original peak as \(A-1=2^k Q+r\) and an alternative
lower peak as \(y=2^k P+s\), with \(A=3^v u\). Their common
suffix endpoint forces the lower peak's odd count \(b\) to be
at least \(a\). Put \(d=b-a\). Dividing the affine equality by
\(3^a\) gives

\[
Q=3^dP+\left\lfloor T^k(s)/3^a\right\rfloor.
\]

The quotient on the right is below \(3^d\). Consequently
\(y+c=3^{v-d}u\) with a signed offset \(|c|\le2^k\), obtained
from the two low parts. The image bound forces at most \(d\)
even steps in any smaller source reaching \(y\) at time \(v\).

The key separation lemma fixes an even-step budget \(d\) and a
nonzero integer \(C\). Any precision \(p\) with
\(2^p3^d|C|<3^p\) gives

\[
3^p\nmid 2^j C-\operatorname{runA}(j,x)
\]

whenever the window has at most \(d\) even steps. Here
\(\operatorname{runA}\) is the shifted affine defect. If the last
even step is followed by \(t\) odd steps, its contribution and
all prior contributions contain \(3^t\). The precision bound
forces \(t<p\). Dividing out that factor and removing the last
even step replaces \(C\) by

\[
2^{t+1}(C/3^t)-1.
\]

The new integer \(C'\) is odd and satisfies
\(3^t|C'|\le3\cdot2^t|C|\). Thus \(p-t\) preserves the budget
inequality with one fewer even step. For the peak offsets,
\(C=1-c\) has \(|C|<2^{k+1}\) when \(k>0\), so precision
\(p=2k+2+3d\) suffices. The adaptive cutoff leaves at least
this many odd steps after allowing for every \(d\le k-a\).

For odd \(u\), an actual scaled-peak meeting also forces the
finite certificate at residue \(3^{v-d}u\bmod2^k\). The two
affine laws have distinct image bands whenever their slopes
differ and the common high part is positive. Equal slopes
then force equal low endpoints. The executable Lean check
tests the \(k\) candidate drops using binary modular
exponentiation. It also computes the adaptive cutoff from the
same residue, so both the applicability test and the decision
avoid evaluating an orbit through the entire initial run.
