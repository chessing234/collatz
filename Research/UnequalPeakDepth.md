# Comparing scaled peaks at different times

Let \(T\) be the shortcut Collatz map and let \(k<\ell\).
For any nonnegative exponents \(e,f\), the two images
\(T^k(3^eB-1)\) and \(T^\ell(3^fB-1)\) are distinct when
\(B>2^{2\ell-k}\).

Write \(B-1=2^\ell q+r\), with \(0\le r<2^\ell\), and let
\(s=\ell-k\). The two image values have the forms
\(2^s 3^a q+x\) and \(3^b q+y\), where the low images
satisfy \(x<2^s3^a\) and \(y<3^b\). The exponents \(a,b\)
include the corresponding peak exponent and suffix odd count.
The slopes are distinct because their dyadic valuations are
\(s\) and zero.

Remove their common factor \(g=3^{\min(a,b)}\). The smaller
reduced slope is at most \(2^s\), so \(q\ge 2^s\) makes
the gap between the leading terms at least the full width of
the smaller interval. Thus all intersections of windows of
length at most \(K\) occur at equal depths if \(B>2^{2K}\).
This applies to arbitrary exponents and to even as well as odd
cofactors.
