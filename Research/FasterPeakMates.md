# Earlier meetings after a long odd run

Let \(n=2^v u-1\) with \(u\) odd and positive. Fix a suffix
length \(k\) and let \(a\) be the odd count in that suffix.
If \(v\ge 2k+2+4(k-a)+r\), there is a positive \(m<n\)
with \(T^{v-r+k}(m)=T^{v+k}(n)\) exactly when there is a
certified peak drop \(d>0\) with

\[
3^r < 2^r 3^d.
\]

Align the final \(k\) steps by taking only \(v-r\) steps from
\(m\) before the suffix. Its image fits below the original
peak by the affine capacity bound. The ternary separation
argument forces that image to be \(3^{v-d}u-1\) for some
\(d\le k-a\). Its shifted value is at most
\(2^r 3^{v-r}u\), which gives the stated inequality after
canceling common factors. Equality is excluded by parity
when \(r>0\), and by \(d>0\) when \(r=0\).

Conversely, for \(r\le d\), take
\(m=2^{d-r}(2^{v-d}u-1)\). This removes \(r\) of the
initial halvings from the padded shorter run. For \(r>d\),
take \(m=2^{v-r}3^{r-d}u-1\). The inequality makes this
start smaller than \(n\), and its odd prefix reaches the
required scaled peak.

For \(v=95\), \(u=1\), and \(k=8\), a drop of two permits
a lead of five, with witness \(2^{90}\cdot27-1\). The
finite test excludes a lead of six for these parameters.
The test uses the dyadic peak residues and rejects every
\(r\ge3k\) before evaluating powers of the lead.
