# The first equal-time meeting after an odd run

Let \(T\) be the shortcut Collatz map and let \(L_k(n)\) be the least
nonnegative start with the same \(k\)-step image as \(n\). Write
\(n+1=2^v u\) with \(u\) odd and \(v>0\). The first \(v\) steps are odd
and the shifted peak is \(A=3^v u\).

At the end of the odd run, the all-odd image bound gives \(L_v(n)=n\).
The next state is \((A-1)/2\), which is 1 modulo 3. A target in this
residue has a unique predecessor, so \(L_{v+1}(n)=n\) as well.

Suppose \(v\ge 2\) and \(A\equiv1\pmod4\). The second halving is the
first opportunity for a smaller equal-time partner. Its minimum is exact.

\[
L_{v+2}(n)=
\begin{cases}
2^v(u/3)-1 & \text{if }3\mid u,\\
n-1 & \text{otherwise}.
\end{cases}
\]

Any smaller partner must enter the endpoint via the odd predecessor.
One step earlier that predecessor has only its even predecessor, so the
partner's \(v\)-step image must be \(3^{v-1}u-1\). The image bound forces
at least \(v-1\) odd steps in its prefix. If all \(v\) steps are odd,
the exact affine identity gives \(2^v(u/3)-1\) and requires \(3\mid u\).
With a single even step in position \(e\), numbered from zero, the
shifted affine defect is \(3^{v-1-e}2^e\). It must be divisible by
\(3^{v-1}\), so \(e=0\) and the partner is \(n-1\). Its meeting follows
by prefixing one even step to the smaller start in Hercher's Lemma 9.

If \(A\equiv3\pmod4\), an odd step follows the first halving, and the
alternative even predecessor would force a \(v\)-step image above the
all-odd cap. Thus \(L_{v+2}(n)=n\). If \(A\equiv3\pmod8\), the next
state has a unique predecessor and \(L_{v+3}(n)=n\).

The proofs are in the Lean module `Collatz.Strategy.SynchronousExcursion`.
The independent Python audit enumerates backward fibers for run lengths
up to 12 and odd cofactors below 1024.

The asynchronous meeting at the second halving appears in [Hercher,
*There are no Collatz \(m\)-cycles with \(m\le91\)*, Lemma 9](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html).
