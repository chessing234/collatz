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
