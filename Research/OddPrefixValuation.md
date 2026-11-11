# Valuation exclusions and compression during an odd prefix

Suppose the first \(i\) shortcut steps from \(n\) are odd.
If \(m<n\) and \(T^{i+s}(m)=T^i(n)\), write \(a\) for the
odd count along the competing path. Then \(3^{a-i}\) does
not divide \(n\), with natural truncated subtraction in the
exponent. In particular, \(3^s\mid n\) excludes every smaller
partner whose meeting clock is at most \(i+s\).

The proof splits the competing path at time \(s\). Its
remaining \(i\)-step fiber has the form
\(z=3^{i-b}n+c\), where \(b\) is the last segment's odd
count and \(0\le c<3^{i-b}\). If the required ternary power
divides \(n\), subtracting its contribution preserves a valid
nonnegative preimage of \(c\). A smaller original source
would force this preimage to be zero. That leaves only initial
halvings, which give a source at least as large as \(n\).

The divisibility exclusion overlaps Theorem 6 and the all-ones
specialization of the inverse-minimum result for the odd-only
map. This formalization uses shortcut steps, admits even
meeting endpoints and competing sources, and states the
necessary power in terms of the actual odd count. [Prior
inverse-minimum result](https://rstation.ai/problems/collatz/papers/1/v2)

There is also a compression bound in terms of the competing
path's even count \(e=i+s-a\). Set \(L=3(e-1)\), using
natural truncated subtraction. If \(L\le i\), the meeting
already occurs at \(T^{s+L}(m)=T^L(n)\).

The full odd prefix makes its shifted endpoint divisible by
\(3^i\). This forces the competing defect to have the same
divisibility. Peeling off its last even step and applying
bounded-even ternary separation confines all even steps to
the first \(s+3e-3\) positions when \(e>0\). Both remaining
tails are all odd, so canceling their common affine multiplier
pulls back the equality.

## A sharp lower bound on even steps

Any smaller source joining the odd prefix of a multiple of
three has at least three even steps. With at most two even
steps, write the nonzero defect as \(3^t q\), with \(3\nmid q\).
Its leading ternary digit satisfies
\(q\equiv2^{j-t-1}\pmod3\), where \(j\) is the path length.
This follows by locating the last two even steps. If they
are consecutive, their terms contribute one extra factor of
three. Otherwise the later even step alone determines the
leading digit.

An odd-prefix meeting of a multiple of three instead requires
\(t=i\) and \(q\equiv2^{j-i}\pmod3\). These two digit
conditions are incompatible. Combining the compulsory three
even steps with the valuation exclusion shows that
\(3^t\mid n\), \(t>0\), forces overhead at least \(t+4\).

Three even steps are attained on the entire progression
\(n=1458t+273\), with smaller source \(m=1024t+191\).
The exact identity is \(T^{10}(m)=T(n)\), and the competing
path has seven odd and three even steps. Both the lower bound
and this affine family are checked by Lean.
