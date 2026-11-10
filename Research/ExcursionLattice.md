# Valuation-stratified excursion products

An excursion from an odd source $x$ with $v$ odd steps and $W$ extra halvings
lands at $y$ with $2^{v+W}y=3^v x+3^v-2^v$. For a trace from $n$ to $e$
taking $S$ shortcut steps, multiplication gives the exact identity

$$
  2^S e/n=\prod_i \left(3^{v_i}+\frac{3^{v_i}-2^{v_i}}{x_i}\right).
$$

Each $x_i$ with run length $v$ satisfies $x_i\equiv2^v-1\pmod{2^{v+1}}$.
Suppose the sources are at least $m>0$ and distinct within each run length.
Let $b_v$ be the first integer at or above $m$ in that residue class.
After sorting the $k_v$ sources in the class, the source at index $j$ is
at least $b_v+j2^{v+1}$. Each factor in the exact product decreases with
its source. Replacing the sources with their grid values therefore gives
an upper bound that depends on the floor and run-length counts. If that
upper bound is strictly below $2^S$, the endpoint is below $n$.

Lean proves the product identity and the bound for any finite trace.
The caller supplies a permutation certificate that the sorted groups
contain exactly the visited sources. Products and comparisons are over
natural numbers after clearing denominators.

The audit followed the shortcut map for all 32,767 odd starts from 3
through 65,535. It checked every excursion prefix through the first
descending excursion endpoint. Replacing every source by the common
floor certified 32,765 of those endpoints. Using the exact valuation
grids certified 32,766. The additional certificate is $27\to23$ at
excursion 15, shortcut time 59. The same spacings with every grid starting
at 27 give too large an upper bound. Lean checks the certificate with
the correct class representatives. For 63 the bound still exceeds the
denominator at its first descending excursion endpoint, 61.

The use of local minima in cycle bounds and the use of distinctness to
bound products both have precedents. The specific refinement here is to
combine the exact excursion factors with the residue spacing of each
run length. The test measures the effect relative to the common-floor
excursion product. Priority for this formulation remains unverified.
[Simons and de Weger (2005)](https://doi.org/10.4064/aa117-1-3),
[Hercher (2023)](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
