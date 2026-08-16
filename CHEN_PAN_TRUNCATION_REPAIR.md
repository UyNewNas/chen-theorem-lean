# Chen Pan truncation: replacement interface audit

## Decision

`ChenPanTruncationSieveBound` must not be repaired by strengthening its
distribution theorem.  It is false because it takes absolute values of the
individual Möbius-expanded progression errors.  Relative to the current
all-divisor `errSum(1)` object, a tail-only bound is a logically sufficient
replacement: the Möbius correction is already disposed of by the signed
finite identity proved in `PanTruncation.lean`.

The source audit in Section 5 adds an important qualification.  The preferred
long-term repair is not to prove such an all-divisor tail at all, but to retain
the compact support of the lower-sieve coefficients in the error sum.  This is
how the classical distribution range is normally preserved.

This is a written proof-architecture audit, not a Lean certification claim.

## 1. Exact target and its class

For even `N`, put

```text
P = correctedChenSiftingProduct(N),
Δ_N(d) = panDistributionError(N-2; 1, d, N mod d),
D(N,B) = floor(sqrt(N)/(log N)^B),
w(d) = 3^ω(d).
```

The target consumed by `correctedChenPanSum_reduction` is

```text
R(N,B) + T(N,B)  <<_A  N/(log N)^A,                           (1)

R(N,B) = Σ_{d|P} w(d)|rem(d)-Δ_N(d)|,
T(N,B) = Σ_{d|P, not (2≤d≤D(N,B))} w(d)|Δ_N(d)|.
```

`R` is the Möbius-correction term; `T` is the uncovered distributional tail.
The covered range `2≤d≤D` is separately placed into the a=1 Pan/BV modulus
sum by the existing structural reduction.  Thus no theorem about
`Δ_N(lcm(d,e))` is required.

An interim replacement analytic input is precisely:

```text
ChenPanTruncationTailBound:
for every A>0 and B, there are C>0 and N0 such that
for even N≥N0,
    T(N,B) ≤ C N/(log N)^A.                                   (Tail)
```

It is an open research-level supply requirement.  Unlike the former
`ChenPanTruncationSieveBound`, it has no immediate `d=1,e=2` contradiction:
it contains no auxiliary `e` variable at all.

## 2. Proven algebraic reduction

The repository already proves the exact signed identity, for every `d|P`,

```text
rem(d)-Δ_N(d)
 = [li(N-2)-li(N)]/φ(d)
   + Σ_{1≠e|F} μ(e) base_N(lcm(d,e)),                         (2)
```

where `base_N(q)` is the relevant prime count in the residue class `N mod q`.
It also proves, after the finite Möbius sum is kept signed,

```text
Σ_{1≠e|F} μ(e) base_N(lcm(d,e))
 = -#{p<N : p prime, d|(N-p),
            some forbidden prime divides N-p}.                (3)
```

Taking the absolute value only after (3) is legitimate.  The paper proof in
`CHEN_PAN_TRUNCATION_WRITTEN_PROOF.md` establishes

```text
R(N,B) <<_A N/(log N)^A.                                      (4)
```

It does so through a bounded `li(N)-li(N-2)` difference, a Mertens divisor
sum, and the elementary `sqrt(N) log N` bound for the signed correction.  It
does not use a distribution theorem and is independent of `B`.

Combining (4) with `(Tail)` proves (1), by addition.  This is the complete
logical interface replacement:

```text
Main-term / signed correction  [proved on paper]
                +
uncovered a=1 tail             [open analytic supply]
                |
                v
CorrectedChenPanTruncationInput
                |
                v
covered a=1 Pan/BV range + Chen weighted remainder reduction.
```

## 3. Why this is the correct separation

There are two quite different phenomena.

1. The forbidden-factor expansion is a finite inclusion-exclusion device.
   Its cancellation is algebraic and must happen before absolute values.
   Equation (3) resolves it directly; treating each factor as an independent
   arithmetic-progression error destroys that cancellation.
2. The error `Δ_N(d)` for a *single* divisor `d` is a genuine prime
   distribution question.  Small divisors are exactly the portion consumed
   by the `chenPanWeightOne` Pan/BV interface.  The complement is exactly
   `(Tail)`.

Thus the prior two-supply decomposition

```text
individual lcm(d,e) distribution + main term
```

is replaced by

```text
signed finite correction + single-modulus tail distribution.
```

The first box is not a distribution theorem at all.

## 4. Falsification checks for the new interface

The replacement has a deliberately narrow, testable obligation.

- `d=1` lies in the tail.  Consequently `(Tail)` includes
  `|π(N-2)-li(N-2)|`; a proof must explicitly use the ANT prime-number
  theorem error estimate, not merely an asymptotic `π(x)~x/log x`.
- For every fixed `B`, `D(N,B)` tends to infinity, but is below the
  square-root range by a logarithmic factor.  A proposed proof must state
  which large-modulus/Titchmarsh or switching estimate controls divisors of
  `P` above this cutoff.
- Bounding every summand trivially is insufficient: the divisor weights may
  accumulate.  Any claimed tail proof must retain the `d|P` structure and
  show a final bound with arbitrary logarithmic saving.
- If a proposed estimate first expands `rem(d)` into forbidden divisors and
  then places absolute values around individual `lcm(d,e)` errors, it has
  reverted to the refuted statement and must be rejected.

These checks give a concrete stop condition for the interim route: until a
source theorem is matched to `(Tail)` with its exact modulus range, weights,
and arbitrary-`A` quantifiers, that route remains conditional.  Section 6
gives the preferred alternative which removes the all-divisor tail at the
lower-sieve interface.

## 5. Literature cross-check: Liu's correction is a warning, not a proof

Zihao Liu, *A Corrected Simplified Proof of Chen's Theorem* (2022), Section
IV, identifies the same logical hazard in the Pan-et-al. simplification.  Its
mean-value theorem is applicable to the coprime part, but the implication
`f(a) ≠ 0` ⇒ `(a,d)=1` is false.  Liu explicitly splits off the `(a,d)>1`
part as `R_1`, uses the resulting exceptional prime-count bound, and then
estimates that residual separately.

That source supports the **methodological** conclusion here: a non-coprime
or signed exceptional fibre cannot be hidden inside a coprime Pan/BV average.
It does **not** by itself prove `(Tail)`.  The objects, divisor supports,
weights, and quantifiers must be matched line by line before it can be used
as supply.

There is also an architectural mismatch worth preserving as an open audit
question.  Liu's Selberg coefficients are compactly supported, so the lcm
moduli in its displayed remainder are already below the available
distribution range.  The current Chen object has
`correctedChenBoundingSieve.weights = fun _ => 1` and its generic `errSum`
ranges over every divisor of the full sifting product.  Consequently the
tail may be a genuine deep estimate, or it may signal that the formal sieve
object is broader than the compactly-supported Selberg/Jurkat--Richert
weights used in the classical proof.  No conclusion is licensed until the
two formulations are reconciled.

Primary source: [Liu, arXiv:2203.07871, Section IV](https://arxiv.org/abs/2203.07871).

## 6. Preferred compact-support interface (deferred)

The ANT lower-sieve reduction currently derives an `errSum(1)` bound from a
lower Möbius sequence by the coarse inequality

```text
errSum(μ⁻) ≤ errSum(1).
```

That loses the support of `μ⁻`.  The classical analogue instead keeps the
error sum over the support of the lower-sieve coefficients, conventionally
`d≤D`.  The preferred replacement interface should therefore select, uniformly
in `N`, coefficients `λ⁻_{N,D}` satisfying

```text
IsLowerMoebius(λ⁻),
|λ⁻(d)| ≤ 1,
λ⁻(d) ≠ 0  =>  d ≤ D(N,B),
```

and retain `errSum(λ⁻)` in the lower-sieve conclusion.  The a=1 Pan/BV input
then controls its nontrivial moduli directly; `d=1` is handled by the
quantitative PNT error.  No all-divisor tail is created.

Accordingly there are two honest future routes:

1. prove `(Tail)` for the present broad interface, after an exact source
   match; or
2. rework the lower-sieve API so that compactly supported coefficients are
   preserved, then match the resulting supported error sum to the classical
   Pan/BV range.

Route 2 is mathematically closer to the source proof and is the recommended
one.  Neither route is a proof by axiom or a weakening of the audit.  No Lean
edit is made by this document.
