# Distinct excursion sources in nested residue classes

Within one odd-run length, mixed residues have periods
$2^{v+1}3^p$ for different incoming exponents $p$. Any two such classes
are disjoint or nested. Intersecting every class with the same source
floor preserves this property.

Process the classes in order of decreasing exponent and assign the
smallest unused point in each class. This maximizes the comparison
product of the decreasing factors $3^v+(3^v-2^v)/x$ under these class
constraints and distinctness. For the exchange proof, compare a greedy
choice with the point used by another feasible assignment. If the
greedy point is unused, moving to it can only increase the product.
If a later class uses it, the earlier class lies inside that later
class. The two assignments can swap their points and leave the product
unchanged. Induction applies to the remaining classes. Lean also proves
that a greedy assignment exists whenever any feasible assignment exists,
so the comparison is attained under the stated constraints.

Lean checks the general exchange argument, the specialization to mixed
residue classes, and the descent test obtained by multiplying the
comparisons across the run lengths of a trace. One example uses the
nested classes $1\bmod12$ and $1\bmod4$ above 25. The greedy pair is
$(25,29)$ and the feasible competitor $(37,25)$ requires the exchange.
Taking each least point independently would use 25 twice and give a
strictly larger comparison product.

The independent audit checked 26,976 feasible assignments in small
finite residue problems and followed 65,535 odd Collatz starts through
their first descending excursion endpoints. Distinctness tightened
2,969 bounds. Every endpoint in the sample was already certified by
the product with independent mixed-residue floors.
