# Full-history excursion residues

A preceding excursion trace from $n$ to $x$ with $V$ odd shortcut steps
and $S$ total shortcut steps satisfies $2^S x=3^V n+C$. Reducing this
equality modulo $3^V$ gives the incoming residue. A candidate for the
next excursion source must also satisfy the dyadic residue
$x\equiv2^v-1\pmod{2^{v+1}}$ determined by its next odd-run length $v$.
The joint period is $2^{v+1}3^V$.

A candidate in the first joint period above a common floor bounds the
actual source below. Lean proves that a full-history candidate satisfies
the incoming congruence from the immediately preceding excursion as
well. Its floor is therefore at least the one-excursion floor. Applying
the excursion product to the full-history floors gives a descent test
that depends on the run profile and the common floor.

There is a cutoff for exact recovery. The affine offset obeys
$C\le2^S3^V$, so $n<2^S$ implies $x<2\cdot3^V$. This is below the joint
period for every next run length. The actual source is then the unique
representative in the least nonnegative joint period. Lean checks the
recovery of 103 after the first two excursions from 63 and the uniform
descent certificate for the run profile of $7\to13\to5$.

An independent audit followed the elementary shortcut map from 131,071
odd starts below $2^{18}$ and 20,000 deterministic pseudorandom odd
64-bit starts. Full history tightened 20,662 first-drop bounds and
exactly recovered 27,748 visits past the binary-size cutoff. Both
bounds certified all first excursion drops in this sample.

The ternary offset of a parity or valuation history is established
background. Tao uses it modulo powers of three in the Syracuse map.
The refinement here uses the next run's dyadic residue together with
that incoming constraint, then applies the exact excursion product.
[Tao (2022), equations (1.5) and (1.29)](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/almost-all-orbits-of-the-collatz-map-attain-almost-bounded-values/1008CC2DF91AF87F66D190C5E01C907F)
