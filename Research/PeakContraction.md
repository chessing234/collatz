# Uniform reductions between odd-run lengths

Write \(T\) for the shortcut Collatz map. A run of \(v\) odd steps
from \(2^v u-1\) ends at \(3^v u-1\). To reduce an initial run of
length \(e+d\) to length \(e\) with the same cofactor, compare the
two peaks \(3^d B-1\) and \(B-1\), where \(B=3^e u\).

For a suffix of length \(k\), write \(B=2^k q+r\) with \(r>0\).
Let \(a\) and \(b\) count odd steps in the first \(k\) steps of
\(3^d r-1\) and \(r-1\). If their \(k\)-step images are \(x\) and
\(y\), the lifted images are \(3^{a+d}q+x\) and \(3^bq+y\).
Consequently \(b=a+d\) and \(x=y\) certify a meeting for every \(q\).
Two distinct \(q\) with meetings force these same equalities. A
residue without the certificate can give at most one meeting.

The exponent of three has period \(2^{k-2}\) modulo \(2^k\) for
\(k\ge3\). A certificate at one exponent therefore applies to an
entire progression. Prefixing \(d\) halvings to the shorter run
synchronizes it with the longer one. For \(d>0\), the synchronized
partner is smaller by \(2^d-1\). For positive starts, reaching one
is equivalent for the two exponents.

| Longer Mersenne exponent | Exponent drop | Suffix length | Smaller peak residue \(r\) |
| --- | ---: | ---: | ---: |
| \(31+64t\) | 2 | 8 | 147 |
| \(79+128t\) | 2 | 9 | 211 |
| \(111+256t\) | 2 | 10 | 595 |
| \(2047+4096t\) | 4 | 14 | 14395 |

For the first row, the two residues \(9\cdot147-1\) and \(147-1\)
both reach 47 after eight steps and have respectively two and four
odd steps. For the last row, a four-exponent drop has a certificate
at depth 14 while the two-exponent drop in the same progression
lacks one. The table gives equivalences to smaller exponents. A
proof of convergence for all Mersenne numbers would need to handle
the exponents left outside such reductions.

There is a matching delay phenomenon for drops of one or two.
Suppose \(3B=2^k q+1\) with \(k\ge2\). The peak \(3B-1\) takes
\(k\) halvings to \(q\). The peak \(B-1\) starts with a halving
and an odd step, giving \(2^{k-2}q\), and then also reaches \(q\).
The larger peak is \(9B-1=2^k(3q)+2\). Its \(k\)-step image is
strictly greater than \(q\), since the image of 2 is positive.

For \(k\ge3\), take a longer Mersenne exponent \(v>1\) with
\(v\equiv1\pmod{2^{k-2}}\), so \(B=3^{v-2}\) meets this hypothesis.
The longer peak cannot meet either of the two shorter peaks in the
first \(k\) suffix steps. Such odd \(v\) exist above any cutoff.
