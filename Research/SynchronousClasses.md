# Equal-time meeting classes

Two starts belong to one class if their shortcut trajectories agree
after the same number of steps. The shortcut map induces an invertible
map on these classes. One step gives the forward map, and doubling a
representative gives its inverse. Taking the least representative of
an image never increases that image. Distinct classes remain distinct.

This extends the recursive occupation argument to the set of least
representatives across all classes. Below $X$ there are at most
$O(X^{19/20})$ such representatives, even though the least
representatives need not themselves be closed under the shortcut map.
Garcia and Tal use the same class relation in equation (5).
[Garcia and Tal (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf)

## Exact finite inverse fibers

At depth $k$, put $D=2^k$. For a residue $r<D$, the affine rule is
$T^k(Du+r)=3^a u+y_r$, where $a$ is the odd count and $y_r=T^k(r)$.
The inequality $y_r<3^a$ makes the inverse test exact. A target $z$
has a preimage in this residue precisely when $z\bmod 3^a=y_r$,
and its high part is then $\lfloor z/3^a\rfloor$.

The executable fiber lists all preimages using this test. Taking
the minimum of the fiber gives the exact least equal-time partner
at depth $k$. These finite minima decrease with the horizon and
eventually equal the least representative.

Two residue profiles with odd counts $a$ and $a+d$ give an entire
meeting family when $y_s\bmod 3^a=y_r$. With
$c=\lfloor y_s/3^a\rfloor$, the lift $D(3^dv+c)+r$ meets $Dv+s$.
For $d>0$ and original high part at least two, the latter is strictly
less than two thirds of the former. The audits include the families
$384t+177$ meeting $128t+59$ and $6144t+3929$ meeting $2048t+1311$.

The last seed $c2^k-1$ in each dyadic period attains the unique
largest image among all seeds below $c2^k$. Its least partner at
horizon $k$ is therefore itself. Every fixed horizon leaves
arbitrarily large starts without a synchronous descent certificate.
The Collatz conjecture is equivalent to the existence of a smaller
equal-time partner for every start above two, with the horizon
allowed to depend on the start.
