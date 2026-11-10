# Bootstrapping the occupation count of a Collatz orbit

Let $F(X)$ count the distinct values below $X$ in a single shortcut orbit
on which different values never merge under the same number of steps.
This includes injective orbits and orbits started at a periodic point.
The checked result gives $F(X)=O(X^{19/20})$, with a uniform constant.
The Lean statement uses $F(X)^{20}le C X^{19}$.

Choose a block of $k=p+e$ steps with $ele p$ and $3^p<2^k$.
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
$(p+e)^kle W p^p e^e$. Then

$$
F(2D^h) le F(2D^{h-1}) + 2W^h
$$

above the initial compression threshold. Induction gives
$F(2D^h)le C_0 W^h$. Taking $p=94$, $e=55$ and
$W=4081199576119298850484664607591547430685275$ gives the
integer inequality $W^{20}<2^{2831}=2^{149cdot19}$.
Monotonicity interpolates between the aligned cutoffs.

Garcia and Tal's collision-free counting argument supplies the
low-count/high-count split. Here the low-count images use the same
occupation bound recursively. The checked statement concerns
intervals beginning at zero. Extending the recursive estimate to
translated intervals requires keeping track of the separate image
intervals for different odd counts. [Garcia and Tal (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf)
