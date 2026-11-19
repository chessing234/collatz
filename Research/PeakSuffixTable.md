# Finite suffix tables after long odd runs

Write \(n+1=2^v u\) and \(A=3^v u\). For \(v\ge7\) and
\(A\equiv3\pmod8\), the least start that meets \(n\) in \(v+7\)
shortcut steps is \(n\) itself. The proof uses two finite tests
whose sizes are independent of \(v\).

For a suffix of length \(k\), assume \(3^k\mid A\). Write
\(A=B+2^k3^kq\), where \(B\) is a positive multiple of \(3^k\)
and \(B\le2^k3^k\). The inverse fiber of the suffix endpoint at
\(A-1\) is a profile-dependent translation of the inverse fiber
at \(B-1\). A base predecessor \(w\ge B-1\) whose odd count is
at most that of \(B-1\) remains at or above \(A-1\) on every
translation. The other candidates in the seven-step table have
the form \(3^d(y+c)=A\), with \(y<A-1\), for one of eleven
explicit pairs \((d,c)\).

If a smaller start reaches \(y\) at time \(v\), the affine image
bound forces at least \(v-d\) odd steps in its prefix. Its last
\(d+p\) steps then have at least \(p\) odd steps. In the shifted
affine law, the initial-value term is divisible by \(3^p\), so
only the shifted defect from this short suffix matters. Write
that defect as \(D\). Since \(3^p\mid y+c\), it must satisfy

\[
D+2^{d+p}c\equiv 2^{d+p}\pmod{3^p}.
\]

For each of the eleven pairs, a check at \(p\le3\) excludes
this congruence for every eligible short parity word. For
example, the pair \((1,5)\) passes the test modulo \(3^2\)
for one parity word and fails it modulo \(3^3\) for all.
Lean verifies both finite tables using kernel reduction.
