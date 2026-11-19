# One orbit, three arithmetic shadows

## Status and scope

The exact finite-word core of this proposal is formalized in core Lean, without
Mathlib. It proves a size bound, binary and ternary cocycle congruences, exact
endpoint recovery after a size threshold, and soundness of an executable
infinite-residue-class descent checker.

**Collatz remains unproved.** There is no assertion of digit independence,
universal certificate coverage, a Fourier inverse theorem, a power-saving
exceptional set, or a measure-rigidity result. These identities are not claimed
as new discoveries; mathematical priority has not been assessed.

## Lean modules

- `Collatz/Strategy/SyracuseData.lean`: the existing exact step predicate,
  chronological paths, and valuation sums, extracted from
  `ValuationTransition.lean` without changing their public names or types.
- `Collatz/Strategy/SyracuseShadows.lean`: exact size and cocycle theorems.
- `Collatz/Strategy/SyracuseWordSieve.lean`: exact word lifting, Boolean
  certificate checks, soundness, and kernel-checked examples.
- `scripts/audit_syracuse_shadows.py`: independent integer calculations,
  class-lift samples, theorem-axiom audits, and deliberately false controls.

The extraction avoids importing search certificates and nonconvergence theory
into elementary finite-word arithmetic. The legacy `ValuationTransition`
module now imports this shared data; its remaining statements are unchanged.

## 1. Exact chronological words

An exact step is

```
SyrStep n v e := n % 2 = 1 ∧ e % 2 = 1 ∧ 3*n+1 = 2^v*e.
```

The odd target matters: it fixes the exact valuation, rather than merely a
permitted number of halvings. For a chronological word `w = [v₁,...,vₖ]`, write
`S = valSum w` and let `Sᵢ` be its prefix sums, with `S₀ = 0`.
`SyrPath n w e` asserts that the entire word is realized.

Define the numerator cocycle by

```
cocycle [] = 0
cocycle (v :: vs) = 3^vs.length + 2^v * cocycle vs.
```

Its expanded form is `C(w) = Σᵢ 3^(k-i) 2^S_(i-1)`. The formal theorem
`SyracuseShadows.affine` proves

```
2^S * e = 3^k * n + C(w).
```

The recurrence and affine equality are formalized. The displayed summation
notation is their mathematical interpretation, not a separate Lean finite-sum
API.

For a closed path, `cycle_equation` proves the exact constraint

```
n * (2^S - 3^k) = C(w).
```

Subtraction here is natural subtraction. This equation alone does not exclude
nontrivial cycles.

## 2. Real-size shadow and the forgetting threshold

Theorems `step_growth` and `growth` prove the cleared-denominator inequalities

```
2 * (e+1) ≤ 3 * (n+1)
2^k * (e+1) ≤ 3^k * (n+1).
```

Consequently `endpoint_lt_three_pow` proves

```
n+1 ≤ 2^k  →  e < 3^k.
```

The non-strict threshold already suffices; strict `2^k > n+1` is unnecessary.
This is a bound on endpoint size, not descent below the initial value.

`seed_forgetting_log` supplies the explicit sufficient horizon
`Nat.log2 (n+1) + 1 ≤ k`. It is sufficient, not claimed minimal.

## 3. Binary shadow

If the endpoint is odd, `seed_binary_residue` proves

```
(3^k*n + C(w)) % 2^(S+1) = 2^S.
```

This records the extra bit fixing terminal oddness. It is not an assertion
that a parity itinerary is the ordinary binary expansion of the integer seed.
The parity string in the 2-adic conjugacy picture belongs to the conjugacy
coordinate. That conceptual identification is not formalized by these modules.

## 4. Ternary shadow and exact endpoint recovery

Use the finite modular inverse

```
invTwo k = (3^k+1)/2
2 * invTwo k = 3^k+1.
```

`inverse_power` and `cancel_two_power` justify inversion and cancellation
modulo `3^k`, including the empty horizon with modulus one. Define

```
tailSum k [] = 0
tailSum k (v :: vs) =
  3^vs.length * invTwo k ^ valSum (v :: vs) + tailSum k vs.
```

For a word of length `k`, its residue represents exactly

```
Σ_{i=1..k} 3^(k-i) * 2^-(vᵢ+...+vₖ)  (mod 3^k).
```

`tailSum_scaled` formally relates this recursive sum to `C(w)`.
`endpoint_residue` and `seed_forgetting` prove

```
e % 3^k = tailSum k w % 3^k
n+1 ≤ 2^k  →  e = tailSum k w % 3^k.
```

**This is not digit independence.** The realized word depends on the source.
In fact `same_word_endpoint` and `same_word_source` prove that two sources
satisfying the size threshold and realizing the same word have both the same
endpoint and the same source. Recovering the endpoint from the word does not
remove the information encoded by that word.

## 5. An infinite-class descent checker

`pathCheck r w` checks every exact step equation and every odd target.
`wordEval r w` computes the endpoint along the proposed word. `classCheck r w`
accepts precisely when this path check and all three further tests hold:

```
r < 2^(S+1)
3^k < 2^S
wordEval r w < r.
```

The exact lift theorem `path_lift` proves that a realized word from `r` to `e`
also takes

```
r + 2^(S+1)*q  →  e + 2*3^k*q
```

for every natural `q`, with exactly the same valuation word. Together with the
coefficient and representative checks, this proves strict descent for every
member of the infinite class. `descent_of_residue` applies the certificate
directly from `n % 2^(S+1) = r`.

Three examples are checked using Lean's kernel-based `decide`:

| Representative | Word | Representative path | Exact class modulus |
| --- | --- | --- | --- |
| 3 | `[1,4]` | `3 → 5 → 1` | 64 |
| 5 | `[4]` | `5 → 1` | 32 |
| 7 | `[1,1,2,3]` | `7 → 11 → 17 → 13 → 5` | 256 |

These are endpoint-descent certificates, not first-stopping-time certificates.
The checker neither checks that earlier endpoints stay above the source nor
asserts coverage of all positive odd inputs. The modulus preserves the exact
word; a broader class might descend with a different word.

## 6. Kill tests for the proposed Fourier inverse theorem

The following critique is mathematical analysis, not a formalization of complex
Fourier analysis in Lean. Its arithmetic premise is formalized by
`target_not_three`: every exact Syracuse target is nonzero modulo three.

For any `m ≥ 1`, take the order-three frequency `a = 3^(m-1)` modulo `3^m`
(nonprimitive when `m > 1`). Every positive-time term of

```
exp(2πi * a*nⱼ / 3^m)
```

is one of the two nontrivial cube roots of unity. Each has real part `-1/2`.
Thus the absolute value of their average is always at least `1/2`, irrespective
of the exponent-word structure. This automatically exceeds `3^(-εm)` for
sufficiently large `m`, for every fixed positive `ε`.

This makes raw Fourier bias, with unrestricted frequencies and moduli, a
non-discriminating premise. It is not by itself a proof that every possible
precise inverse theorem is false. An excessively large modulus gives another
trivial source of bias: finitely many fixed integer values have phases close
to one as the modulus grows.

Any empirical test or revised conjecture must specify:

- Primitive frequencies, and the effect of already known unit support.
- A modulus range tied to the sample size and orbit scale.
- Whether samples are states, endpoints, or exponent-window cocycles.
- A justified baseline, such as the image of IID geometric exponent windows,
  rather than uniformity over all residues including multiples of three.
- A finite-sample threshold and a correction for scanning many frequencies.
- A precise structural conclusion and separate near-balance hypothesis.

Periodicity alone does not imply balance. For example, the explicit finite
family `n₀ = 2^(K+1)-1` realizes `K` consecutive valuations equal to one, with
`nⱼ = 3^j*2^(K+1-j)-1`. Its discrepancy is `K*(log 2-log 3)`, not small.
This illustrative family and the logarithmic expression are not formalized
in this development. In particular, the family is not claimed to refute a
statement with an arbitrarily large constant in `K ≥ C log n₀`.

No adversarial Fourier experiment or validated inverse theorem is supplied by
the exact-shadow audit.

## 7. Entropy and rigidity: remaining research, not consequences

The previously proposed entropy deficit near `0.0500` bits per binary bit and
large-deviation cost near `0.0793` bits per odd step describe a random-word
model. Their reciprocal near `12.6` is not a universal stopping-time constant.
No entropy theorem, density improvement over Tao, or power-saving exceptional
set is proved here. The reported exhaustive search through 26 bits has not
been independently reproduced by this audit.

The proposed skew product on `Z₂ × Z₃` has a valuation-dependent branch chosen
by its 2-adic coordinate. It is not automatically an action of commuting
multiplication-by-two and multiplication-by-three maps. The 2-adic branch is
also singular at `x₂ = -1/3`. Applying a measure-rigidity theorem would require
an actual invariant measure and verification of that theorem's precise
hypotheses. No such bridge has been established here, and no literature
priority assessment has been performed.

## Verification

Run the targeted build and independent audit with

```sh
lake build Collatz.Strategy.SyracuseWordSieve
python3 -I scripts/audit_syracuse_shadows.py
```

Both commands passed on 2026-11-19. The deterministic audit reported:

- 147,579 orbit-prefix cocycle/growth/residue checks.
- 91,661 exact seed-forgetting checks.
- 147,579 checks that positive-time targets are units modulo three.
- 221 accepted finite class certificates among the tested canonical
  representatives, with 9,061 exact lifted-class samples (`q = 0,...,40`).
- 31 public Lean theorem axiom footprints checked across the three modules,
  including the five extracted data lemmas.
- Six deliberately false controls rejected by `decide`.

The independent orbit inputs include 3,000 deterministic random positive odd
seeds below `2^20`, the seeds `1,3,5,7,27,31,47,63`, and `2^b-1` for
`b = 2,...,64`. Each is tested through `max(48, bit_length(seed)+2)` odd steps.
The class search uses odd representatives from 3 through 2001 and at most
128 odd steps to find a first endpoint drop; only certificates accepted by
`classCheck` are used for the lift samples. These are finite audit parameters,
not universal stopping bounds.

The audit compares exact integer identities along deterministic random and
adversarial seeds; checks finite samples of lifted classes against actual
valuations; screens the three new Lean files for proof escapes; prints every
public theorem's axiom footprint; and requires six false statements to be
rejected specifically because `decide` proves them false. Allowed logical
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

The independent samples supplement the general Lean proofs; they do not prove
universal certificate coverage. A full repository build, including the heavy
legacy `ValuationTransition` import chain, has not been completed for this
change.
