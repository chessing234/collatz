# Ternary translations of Collatz inverse fibers

Let \(T\) be the shortcut map, \(a_k(x)\) the odd count in the
first \(k\) steps, and \(F_k(z)=\{x:T^k(x)=z\}\). For any
nonnegative \(q\), the map

\[
x\longmapsto x+2^k3^{k-a_k(x)}q
\]

is a bijection from \(F_k(z)\) to \(F_k(z+3^k q)\) and preserves
the complete depth-\(k\) parity word. For each residue \(r\) modulo
\(2^k\), the affine formula identifies admissible targets by
their remainder modulo \(3^{a_k(r)}\). A \(3^k\) translation
keeps that remainder and adds \(3^{k-a_k(r)}\) to the quotient.

For \(q>0\), all lifted sources have positive dyadic quotient.
Their order is then determined by decreasing odd count followed
by increasing dyadic residue. The entire order is the same for
all positive \(q\), so the least predecessor has the same parity
word on each target progression above \(3^k\).

The order may change between the base fiber and its positive
translates. At depth 12, both 8 and 9 map to 2, with respectively
five and six odd steps. After one ternary translation their
predecessors are 8,957,960 and 2,985,993, which reverse order.

This transport permits an exact finite analysis of inverse
suffixes when the peak varies in a mixed dyadic and ternary
progression. The Lean module also proves surjectivity, so the
transport captures every possible predecessor of a lifted target.
