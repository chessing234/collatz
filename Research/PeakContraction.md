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
