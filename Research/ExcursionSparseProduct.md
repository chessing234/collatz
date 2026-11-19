# Reciprocal corrections on sparse excursion sequences

For an excursion source $x$ with $v$ odd steps and $w$ halvings, the
endpoint is

$$
\frac{3^v}{2^{v+w}}x\left(1+\frac{3^v-2^v}{3^v x}\right).
$$

The correction factor lies between $1$ and $1+1/x$. Over a finite
sequence of excursions with totals $V$ and $S$ for the odd steps and
all shortcut steps, respectively, the corrections multiply and the
leading multiplier is $3^V/2^S$.

The Lean module proves a general product bound using dyadic source counts.
Fix a positive integer $P$, and suppose each cutoff $2^{Pj+1}$ admits
at most $2^{(P-1)j}$ distinct values. For a finite sample above the
cutoff at $j=P$, use a common denominator $D=2^{PH+1}$, where the
sample lies below the cutoff at $H+1$. Assign each source $x$ an
integer weight by summing $2^{P(H-j)}$ for the indices $P\le j\le H$
whose next cutoff exceeds $x$. The first contributing weight gives
$D\le xw(x)$. Swapping the finite sums and applying the capacity
assumption gives $2\sum_x w(x)\le D$. An integer product inequality
then bounds the product of $1+1/x$ by $2$. The finitely many sources
below the initial cutoff contribute another fixed factor.

The earlier bounded alphabet count supplies this capacity whenever the
odd-run and halving lengths are uniformly bounded. In an injective
sequence with such an alphabet, a fixed $C$ therefore gives

$$
2^{S_k} x_k \le C x_0 3^{V_k}
$$

at every excursion boundary $k$. Injectivity implies that $x_k$
eventually exceeds each fixed bound. Hence for every integer $R$ one
eventually has $R2^{S_k}<3^{V_k}$.

The bound rules out injective bounded-alphabet orbits with a multiplier
that remains bounded along any infinite subsequence. A proof of
universal descent still has to address the possible escape of the
multiplier and profiles outside the bounded alphabet. The Lean audit
checks examples and axiom dependencies. The independent Python audit
checks sparse samples and exact orbit ratios with rational arithmetic.
