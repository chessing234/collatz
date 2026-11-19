# Shortening Collatz backtraces while preserving residues

A backward shortcut path consists of runs of doubling separated
by odd inversions \(z\mapsto(2z-1)/3\). Suppose a path from source
\(x\) to target \(z\) has length \(L\) and odd count \(a\).
Fix a source modulus \(m>0\) and a time modulus \(p>0\).
There is a source \(y\le x\) with \(y\equiv x\pmod m\) that
reaches \(z\) in \(K\le L\) steps with the same odd count and
\(K\equiv L\pmod p\). The total depth satisfies

\[
K<(a+1)p\,3^a m.
\]

The state \((2^e\bmod(3^am),\,e\bmod p)\) of a doubling run
has at most \(p3^a m\) possibilities. Its first occurrence
therefore lies below that bound. Replacing a run length by
its first occurrence leaves the endpoint unchanged modulo
\(3^a m\). Each following odd inversion loses one power of
three from the retained modulus. All odd inversions remain
legal, and each replacement can only lower the source.

When \(p=1\) and a positive doubling period \(P\) modulo
\(3^a m\) is available, the depth bound improves to
\((a+1)P\). If the target is periodic with period \(p\), then
the compressed source also has the original \(L\)-step
image. In a segment whose endpoint has no earlier repeat,
a strict shortening gives a strictly smaller source.
