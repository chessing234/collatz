# Near-critical visits after a future minimum

Suppose the shortcut orbit from $n$ has distinct values and every
future value is at least $n$. Every injective orbit has arbitrarily
late such starting points, with starting values tending to infinity.

The occupation bound gives at most $A2^{19j}$ distinct values below
$2^{20j+1}$ for a uniform $A$. The reciprocal product proof absorbs
$A$ into a fixed shift of the lower band. For some uniform $B$, if
$n\ge 2^{20(B+q)+1}$ and $K=2^{q+1}$, the entire finite correction
from $n$ is at most $K/(K-1)$, uniformly in the segment length.

Consequently, whenever the leading multiplier $3^{a_k}/2^k$ is
at most one, the endpoint lies in the interval

$$
\left[n,\ n+\left\lfloor \frac{n}{K-1}\right\rfloor+1\right).
$$

Choose the largest admissible $q$. The width of this interval is
$O(n^{19/20})$. Distinct times have distinct endpoints, and the
translated occupation estimate gives at most
$O(n^{(19/20)^2})=O(n^{361/400})$ such times. Lean states the
last estimate as the integer inequality $N^{400}\le E n^{361}$
for any finite list of $N$ distinct qualifying times and a
uniform constant $E$.

The argument bounds the number of nonexpanding multiplier prefixes
from a large future minimum. The existence of an injective positive
orbit remains open.
