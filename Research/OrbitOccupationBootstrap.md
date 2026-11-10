# Bootstrapping the occupation count of a Collatz orbit

Let $F(X)$ count the distinct values below $X$ in a single shortcut orbit
on which different values never merge under the same number of steps.
This includes injective orbits and orbits started at a periodic point.
The checked result gives $F(X)=O(X^{19/20})$, with a uniform constant.
The Lean statement uses $F(X)^{20}\le C X^{19}$.

Choose a block of $k=p+e$ steps with $e\le p$ and $3^p<2^k$.
Write $D=2^k$. At scale $2D^h$, divide starts by whether their first
$kh$ steps contain at most $ph$ odd steps.

The low-count starts have distinct images below $2(3^p)^h$. For all
sufficiently large $h$, those images lie below $2D^{h-1}$. Each image
belongs to the same orbit, so the light contribution is bounded by
$F(2D^{h-1})$. This is the recursive step in the argument.

For the remaining starts, give an odd step weight $p$ and an even
step weight $e$. The total over two residue periods is
$2(p+e)^{kh}$, and each remaining start has weight at least
$(p^p e^e)^h$. Choose an integer $W$ satisfying
$(p+e)^k\le W p^p e^e$. Then

$$
F(2D^h) \le F(2D^{h-1}) + 2W^h
$$

above the initial compression threshold. Induction gives
$F(2D^h)\le C_0 W^h$. Taking $p=94$, $e=55$ and
$W=4081199576119298850484664607591547430685275$ gives the
integer inequality $W^{20}<2^{2831}=2^{149\cdot19}$.
Monotonicity interpolates between the aligned cutoffs.

Garcia and Tal's collision-free counting argument supplies the
split by odd count. Here the low-count images use the same occupation
bound recursively. [Garcia and Tal (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf)

## Translated intervals

An input interval of width $2^{kh}$ intersects at most two dyadic
quotient classes. Fix an input quotient $b$ and an odd count $m$.
The affine formula places every image in the interval
$[3^m b, 3^m(b+1))$. Its width is $3^m$.

Group the positive low counts by $ps<m\le p(s+1)$ for $s<h$.
Above the same compression threshold, each group has at most $2p$
image intervals of width at most $D^s$. The induction hypothesis
bounds their contribution by $2p C W^s$. The small groups have
a uniform bound from their total width. Summing the larger groups
costs at most $2p C W^h/(W-1)$. When $W\ge 8p+1$, this fits
within the induction budget along with the initial groups and
exceptional words. Thus the same $19/20$ exponent holds uniformly
for intervals $[a,a+X)$.

The standard map adds the intermediate values $3x+1$ for odd shortcut
states $x$. A window in those values pulls back into a shortcut
window of at most the same width. Counting the two sets separately
gives the same exponent for the standard map.

## Multiplier occupation

For a positive injective orbit, the affine envelope bounds the
state at every time with multiplier at most $R$ by $C_1 x_0 R$.
Injectivity and the occupation theorem bound the number of such
times by $O((R+1)^{19/20})$. Consequently, for every $p/q<20/19$
and every fixed $D$, the multiplier exceeds $D(k+1)^{p/q}$
at arbitrarily late times. This constrains the growth of an
injective orbit. The conjecture still requires excluding injective
positive orbits and nontrivial positive cycles.
