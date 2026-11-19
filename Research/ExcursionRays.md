# Excursion source classes and exact descent thresholds

For a realized nonempty excursion profile, write $S$ for its total
shortcut time, $V$ for its number of odd steps, $B=2^S$, and $A=3^V$.
The source set is a single class modulo $2B$. Reducing a source to its
least nonnegative representative preserves the entire profile. If that
base trace goes from $n$ to $e$, the source $n+2Bk$ lands at $e+2Ak$.

When $D=B-A>0$ and $e\ge n$, descent at the endpoint is equivalent to
$k>\lfloor(e-n)/(2D)\rfloor$. Lean checks the seven-excursion profile
from 165 to 167, which has $S=27$ and $V=17$. Its base endpoint exceeds
165 despite coefficient contraction. Every higher member of its class
descends at shortcut time 27. The base already descends at an earlier
time. The mixed-residue certificate from 63 extends to every source
$63+2^{55}k$, with descent at shortcut time 54.

The affine offset $C$ obeys $2^V(C+B)\le BA$. Removing the final $W$
halvings keeps $C$ fixed and gives the stronger bound
$2^V(2^W C+B)\le BA$. A non-descending shift must therefore satisfy
$2^V(2^W\cdot2Dk+1)\le A$. If $V$ and $S$ share a factor $d\ge2$,
factoring the two powers gives $2^V D\ge A$. For those contracting
profiles, every source at least one full period above the base descends.

The independent audit checked 45,055 distinct profiles and 196,608
shifted traces, including shifts of size $2^{65}$. It checked the
separation inequality on 20,802 contracting prefixes with a common
exponent factor. Source congruence and affine transport are classical
parity-vector tools. This development packages them for excursion
profiles and connects the terminal halving count to the ray cutoff.
[Terras (1976)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers)

## Values at intermediate boundaries

The source and endpoint quotients agree, $e\mathbin{//}A=n\mathbin{//}B$.
In particular, if $n<B$, the incoming residue modulo $A$ alone
determines $e$. At a boundary of a longer canonical profile, let $A_p$
be the tripling coefficient of the past and $B_f$ the denominator of the
future. The intermediate value lies below $2B_f A_p$. It is the unique
representative of its past residue modulo $A_p$ and its future source
residue modulo $2B_f$ in that interval.

Two occurrences of the same past and nonempty future profile lie in the
same joint class. If their values differ, their separation is at least
$2B_f A_p$. Translating the full source by one source period attains
that separation. Lean checks the cut values 13 and 445 for the profiles
starting at 7 and 263, with joint period 432. The independent audit
reconstructed 360,448 canonical cuts from both residues. Affine
transport and the underlying residue classes are established background.
The boundary formulation uses both directions of transport together.
[The local affine atlas of the Collatz map](https://amral.evemisslab.com/en/collatz/papers/affine-atlas/)
