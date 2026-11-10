# Reduced multiplier of the class minima

For a positive injective orbit, let $m_k$ be the least representative
of the equal-time class of $T^k(n)$. These representatives are
distinct and stay positive.

Every even step is an exact halving. A strictly rising odd step
is bounded by $(3m_k+1)/2$. A descending odd step has factor at
most one. Write $r_k$ for the number of rising steps and $h_k$ for
the number of halvings up to time $k$. These steps give the leading
multiplier $3^{r_k}/2^{r_k+h_k}$.

The $19/20$ occupation bound for least representatives gives a
uniform bound on the product of the corrections $1+1/m_i$.
Hence there is a fixed $C$ such that

$$
2^{r_k+h_k}m_k\le C m_0 3^{r_k}.
$$

The reduced multiplier tends to infinity. In particular, for any
positive integer $P$ and nonnegative integer $Q$ with
$3^P\le2^{P+Q}$, eventually $P h_k<Q r_k$. The concrete pair
$(P,Q)=(41,24)$ is checked in the Lean audit.

The spatial count of least representatives also bounds the number
of times when the reduced multiplier is at most $R$ by
$O((R+1)^{19/20})$. It follows that the reduced multiplier exceeds
every fixed power-law ceiling with exponent below $20/19$ at
arbitrarily late times. The remaining cases include trajectories
whose reduced multiplier exceeds these ceilings.
