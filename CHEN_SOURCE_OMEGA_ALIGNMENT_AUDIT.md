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

There is a promising finite transport for the **triple** summand which is
stronger than the deliberately coarse existing theorem
`correctedChenOmega_triple_le_switchingCount`.  The definition of
`tripleFactorCount` itself retains

```text
p_1 < p_2 <= p_3,     p_1 p_2 p_3 = N-p < N.
```

Consequently

```text
p_2^2 <= N/p_1,  hence  p_2 <= sqrt(N/p_1).                   (B)
```

This is exactly the upper support condition in (S).  For all non-boundary
indices, the remaining source conditions also follow from the corrected
cutoffs:

```text
floor(N^(1/10)) < p_1 < ceil(N^(1/3)),
ceil(N^(1/3)) < p_2
```

imply the strict real inequalities in (S).  Thus the map

```text
(p, p_1, p_2, p_3) |-> (a=p_1*p_2, p_3)
```

injects these witnesses into the summands of `chenOmega(N)`, because the
candidate condition makes `p=N-a*p_3` prime.

There are only two endpoint fibres to remove before this statement is exact:

```text
p_1 = floor(N^(1/10)),       p_2 = N^(1/3) when the latter is integral.
```

For each fixed boundary prime, the crude divisor-pair count is at most
`O(N^(9/10) log N)` (and the second fibre is smaller).  This is negligible
against `N/log^2 N`; nevertheless the actual finite predicate, injectivity,
and an explicit eventual inequality must be proved before it is consumed.

Here is the needed elementary calculation.  Put
`t=floor(N^(1/10))`.  For sufficiently large `N`, `t >= N^(1/10)/2`.  If the
first boundary `p_1=t` occurs, forgetting primality and the ordering only
enlarges the number of possible pairs `(p_2,p_3)` to

```text
sum_{u <= N/t} floor(N/(t*u))
 <= (N/t) (1 + log(N/t))
 <= 2 N^(9/10) (1 + log N).                                   (E1)
```

The last inequality uses the elementary harmonic-sum bound and the lower
bound on `t`.  Each possible pair determines at most one complement prime
`p=N-t*p_2*p_3`, so (E1) bounds the corresponding penalty fibre even before
the candidate restrictions are imposed.

If `s=N^(1/3)` is integral and the second boundary `p_2=s` occurs, the same
argument, now summing `p_1*p_3 <= N/s`, gives

```text
sum_{u <= N/s} floor(N/(s*u))
 <= N^(2/3) (1 + log N).                                      (E2)
```

The overlap of the two fibres may be counted twice, which is harmless for an
upper bound.  Standard eventual growth gives both (E1) and (E2) as
`o(N/log^2 N)`.  Thus the desired written target is a concrete inequality

```text
correctedTriplePenalty(N)
 <= chenOmega(N)
    + 2*N^(9/10)*(1+log N) + N^(2/3)*(1+log N),                (CT)
```

up to harmless integer-floor ceilings and the finite small-`N` threshold.
The source-Selberg theorem may be transported only after a Lean version of
(CT), with the exact repository cutoffs, replaces this schematic display.

Accordingly, the implication

```text
Liu source Selberg bound for Omega_src
    => CorrectedChenOmegaUpperBound
```

is not yet established and must not be treated as a documentation-only
change.  It needs both of the following new comparison theorems:

1. **Triple transport.**  Preserve `p_2<=p_3` and prove the injection above,
   then bound the two explicit endpoint fibres.  The existing coarse
   reparameterization is insufficient because it has forgotten (B).
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
3. `CorrectedTripleTransport`: the source-witness injection retaining
   `p₂≤p₃`, plus an explicitly bounded `p₁=floor(N^(1/10))` / integral-cube
   endpoint term.
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
