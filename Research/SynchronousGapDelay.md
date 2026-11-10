# Arbitrary synchronous delays with a fixed initial odd run

For \(U>0\), start at \(2^k U-2\) and take one halving followed
by \(k-1\) odd steps. At horizon \(k\), the least source in
that inverse fiber is \(2^k(U/3)-1\) if \(3\mid U\), and
\(2^k U-2\) otherwise. The image cap forces any candidate
at or below the displayed start to have at least \(k-1\)
odd steps. The shifted defect of a word with one even step
then forces that step to come first. An all-odd alternative
exists exactly when the cofactor is divisible by three.

Now start at \(n=2^v u-1\) with \(v>0\) and shifted peak
\(A=3^v u\). If \(2^k\mid A+1\), the peak is a start of the
preceding form with \(U=(A+1)/2^k\). Since \(3\mid A\),
this \(U\) is coprime to three, so the peak has no smaller
equal-time partner in \(k\) steps. The all-odd prefix image
bound transfers that conclusion back to \(n\).

For any fixed \(v>0\) and any \(k\ge3\), the congruence
\(3^v u\equiv-1\pmod{2^k}\) gives an entire progression of
odd cofactors. Consequently there are arbitrarily large
starts with exactly \(v\) initial odd steps for which the
least equal-time representative is still the start after
\(v+k\) steps.

The accompanying ancestor construction places arbitrarily
large ancestors of any target \(z\) coprime to three in
every progression with modulus \(2^a3^b\). A dyadic
prefix gives an affine image. Choosing the next step to
be odd makes its endpoint a ternary unit. Powers of two
then align this image progression with the doubling ray
of \(z\). The result recovers the corresponding case of
Monks's sufficiency theorem for arithmetic progressions.
Applied to the delay progression, it gives ancestors of
every such \(z\) with the prescribed run and delay.

The general arithmetic-progression theorem is due to
[Kenneth M. Monks](https://monks.scranton.edu/files/pubs/SufficiencyRev4.pdf).
