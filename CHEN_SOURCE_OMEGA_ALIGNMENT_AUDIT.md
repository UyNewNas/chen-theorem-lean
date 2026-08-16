# Source Omega alignment audit

## Decision

The repository currently contains two different objects called an Omega
quantity.  They must not be identified merely because both occur in a Chen
proof.  The classical/Liu Selberg estimate supplies an upper bound for the
first object; the corrected finite counting bridge consumes the second.  No
proved comparison is currently present.

This is a written source-and-object audit, not a claim of a new analytic
estimate.

## 1. The source object

Liu's corrected simplified proof (arXiv:2203.07871, equations (3)--(10))
uses

```text
Omega_src(N) = sum_a f_N(a) # {p_3 : a p_3 <= N,
                                N-a p_3 is prime},
```

where `a=p_1 p_2` and

```text
N^(1/10) < p_1 <= N^(1/3) < p_2 <= (N/p_1)^(1/2).              (S)
```

The legacy Lean definition `chenOmega` and its `chenF` have this intended
shape.  Its source upper-sieve stage uses Selberg coefficients supported at
`z'=N^(1/4-epsilon/2)`; after squaring, `[d_1,d_2]` lies at the supplied
distribution level.  Liu's corrected non-coprime split then concerns the
same complement primality predicate `N-a*p_3`.

## 2. The corrected consumer

The actual endpoint of the current zero-sorry finite chain is instead

```text
correctedChenOmega(N)
 = sum_{p in correctedChenCandidates(N)}
     [ primePowerSum(N-p,z,y) + tripleFactorCount(N-p,z,y) ].  (C)
```

It is the penalty in the proved finite inequality

```text
0 < # correctedChenCandidates(N) - correctedChenOmega(N)/2
  => prime + at-most-two-prime-factor representation.
```

Its triple part has the finite upper reparameterization used by
`correctedChenOmega_triple_le_switchingCount`:

```text
z <= p_1 < y,       y <= p_2,
p_1 p_2 p_3 = N-p,  p_3 prime,                                (T)
```

followed only by the effective restriction `z*p_1*p_2 <= N` coming from the
candidate sieve.  This is not the source support (S): in particular (T) has
neither `p_2 <= sqrt(N/p_1)` nor the source's exact `f_N` predicate.  It is a
deliberately coarser upper-counting construction.

The first summand in (C), `primePowerSum`, is also absent from the displayed
source Omega object.  The repository's q1 workline is intended to control
that additional repeated-prime contribution; its current all-divisor AP
expansion was independently rejected in
`CHEN_Q1_ERROR_INTERFACE_AUDIT.md`.

## 3. Consequences

The implication

```text
Liu source Selberg bound for Omega_src
    => CorrectedChenOmegaUpperBound
```

is not established and must not be treated as a documentation-only change.
It needs both of the following new comparison theorems, or a replacement
counting bridge that makes them unnecessary:

1. **Triple transport.**  Compare the corrected triple penalty in (T) with a
   source-supported switched Selberg object.  The proof must account for all
   pairs added by the coarser range, including their multiplicity; merely
   observing that both have a product `p_1 p_2` is insufficient.
2. **Repeated-prime transport.**  Bound `primePowerSum` by a source-supported
   remainder/negligible term.  q1 cannot supply this until its raw full
   Möbius expansion is replaced by supported weights and a genuine analytic
   theorem.

Thus the source-faithful Omega line and q1 are complementary, not competing:

```text
supported source Selberg pair sieve -- supplies --> source triple object
                                          |
                                          +-- needs finite transport --> corrected triple penalty

supported q1/repeated-prime argument ---- supplies --> primePowerSum penalty
                                          |
                                          +-- needs finite transport --> correctedChenOmega
```

Every arrow after “supplies” is currently open.  The existing finite
reparameterizations are useful prerequisites, but none provides this source
transport.

## 4. Next formal interfaces

Formalization should begin only after the following written statements are
fixed against the source.

1. `SourceOmegaSupport N a`: exact finite encoding of (S), with a theorem
   identifying it with the `chenF` support (including floors/strict endpoints).
2. `SourceSelbergOmegaUpperBound`: a uniform theorem for the source object,
   exposing the coefficient support, `[d1,d2]` level, the main term and Liu's
   coprime/non-coprime remainder split.
3. `CorrectedTripleTransport`: a finite inequality from the corrected triple
   penalty to the chosen source/sieved object plus an explicitly bounded
   boundary term.
4. `CorrectedPrimePowerTransport`: a separate q1 or other source-matched
   bound for the first summand of (C).
5. Only then package these as `CorrectedChenOmegaUpperBound` and feed the
   already-proved positivity/counting bridge.

Stop condition: do not instantiate `CorrectedChenOmegaUpperBound` with the
numerical constant `3.9404` until items 2--4 include every extra range and
penalty in (C).  A classical constant attached to a different Omega object is
not evidence for the corrected endpoint.

## Provenance

* Z. Liu, [*A Corrected Simplified Proof of Chen's Theorem*](https://arxiv.org/abs/2203.07871),
  Sections I, III, and IV (source object, Selberg support, and corrected
  remainder split).
* The exact repository definitions and finite consumer are in
  `MathlibNt/SieveTheory/SwitchingPrinciple.lean`.
