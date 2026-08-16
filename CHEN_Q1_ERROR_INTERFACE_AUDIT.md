# q1 AP-error interface audit

## Status

This is a written audit of the q1/prime-power branch of the corrected Chen
`Omega` bound. It does not prove `q1APErrorUniformBound` and it does not
license its current source attribution.

## Findings

The current q1 definitions introduce three independent obligations.

1. For odd `m`, `q1APMainValue(N,m)` uses the ANT working expression
   `N/log N / phi(m)`. Any arbitrary-log-saving error relative to this term
   is false already for `m=1`; it must be migrated to the matching genuine
   `Li(N-2)/phi(m)` endpoint. The even-modulus exact correction remains valid
   in principle but must be checked against the migrated endpoint convention.
2. `q1CandidateAPError` takes absolute values after expanding both the
   sifting and forbidden products:
   ```text
   sum_q sum_{d|P} sum_{e|F} |mu(d)mu(e)|
     |err(lcm(q,d,e))|.
   ```
   This is not the `a=1` weighted BV sum. Its moduli can exceed the supplied
   level, and taking absolute values removes the signed cancellation before
   a distribution theorem is applied.
3. Therefore the comment claiming that generic `PanMeanValueUniform` directly
   supplies `q1APErrorUniformBound` is not a source match. A theorem must
   first be stated for the exact surviving signed/repackaged object, with a
   proved modulus cutoff.

## Why there is no MainB-style automatic cancellation

For fixed `q`, the signed expression is the inclusion--exclusion expansion of
two genuine coprimality filters.  Writing `R(m)` for `q1APError(N,m)`, it is

```text
sum_{d|P} mu(d) sum_{e|F} mu(e) R(lcm(q,d,e)).                 (1)
```

Unlike the MainB base-count term, `R(m)` is not a constant function of `m`
and has no divisor-sum identity that turns (1) into a cardinality.  Reversing
the sums simply reconstructs the original doubly sifted AP count; it does not
make the distribution error disappear.  Hence a MainB-style finite Möbius
cancellation is unavailable here without an additional analytic identity.

The source-faithful object is consequently a **dimension-two (or switching)
sieve remainder** for the pair of coprimality conditions, with its own level
and averaged distribution theorem.  It may be bounded after a source theorem
repackages the lcm multiplicities, but not by asserting a pointwise bound on
every term of (1).

## Consequence

The valid lower-sieve `a=1` route controls a compact sum of ordinary AP errors
only after coefficient support and MainB cancellation. It cannot be imported
unchanged into q1. q1 belongs to the variable-`a`/`Omega` workline (Chen #50).

## Required repair order

1. migrate `q1APMainValue` to genuine `Li(N-2)` and reprove its exact even
   modulus identity;
2. retain the signed double Möbius expression long enough to identify actual
   cancellation, or prove a new source theorem for its absolute form;
3. establish the exact level of every surviving `lcm(q,d,e)` modulus;
4. only then formulate a q1 distribution input and connect it to a cited
   Pan/BV theorem.

Stop condition: no theorem or documentation may claim q1 error control from
the `a=1` lower-sieve `WeightedBVAtOne` interface while the displayed
absolute lcm sum remains its consumer.

## Minimal replacement target

The next theorem must be stated for the **sifted pair**, rather than for a
collection of individual AP errors.  There is one further prerequisite which
the displayed legacy interface cannot hide: the exact identity in
`q1CandidateAPCount_eq_doubleSum` uses *all* divisors of
`P_sift(N)` and `F_forb(N)`.  Thus its raw modulus

```text
m(q,d,e) = lcm(q,d,e)
```

has no useful uniform level bound: a divisor of either full prime product can
be far larger than any Bombieri--Vinogradov level.  Squarefreeness does not
repair this.  Consequently even a theorem controlling the signed expression
below cannot be an ordinary AP theorem until the full-divisor identity has
been replaced by source-matched **sieve weights with explicit support**, plus
an independently bounded sieve remainder.

Write

```text
Q_N = {q prime : z(N) <= q < y(N)},
P_N = correctedChenSiftingProduct(N),
F_N = correctedChenForbiddenProduct(N),
R_N(m) = q1APBaseCount(N,m) - M_N(m).
```

Here `M_N(m)` is the exact even-modulus contribution when `m` is even and
the genuine endpoint `Li(N-2)/phi(m)` when `m` is odd.  The finite algebra
already proved in Lean identifies the legacy signed remainder as

```text
B_N(q) = sum_{d|P_N} mu(d) sum_{e|F_N} mu(e) R_N(lcm(q,d,e)).   (2)
```

It is legitimate as an identity, but it is **not** a distribution-theorem
input.  A source-matched replacement must introduce weights `lambda_N(d)`
and `rho_N(e)` (or a single combined switched weight) satisfying a stated
support condition such as

```text
lambda_N(d) != 0 and rho_N(e) != 0  =>  lcm(q,d,e) <= L(N)
```

for every surviving `q in Q_N`, together with a separately stated error for
replacing the coprimality indicators by those weights.  The exact form of
`L(N)`, the weights, and that replacement error must be copied from the
chosen Chen/Pan source; they cannot be inferred from the present raw Möbius
identity.

Only after that step may the new theorem bound the signed/repackaged remainder

```text
sum_{q in Q_N} | sum_{d,e} lambda_N(d) rho_N(e)
  R_N(lcm(q,d,e)) |
  <<_A N/log^A N,                                             (Q1-2D)
```

after (and only after) the source theorem has specified the admissible level,
the coprimality hypotheses, the exceptional-even-modulus terms, and the
sieve-weight replacement error.  A one-sided signed bound is enough for the
Chen upper bound, while the displayed absolute-in-`q` version is a stronger
and easier-to-audit target; the source must say which one it supplies.

This is a Chen-local `DimensionTwoSwitchingRemainder` target. Its eventual
formal API should expose: the three finite index sets, the supported weights,
the modulus map and proved level cutoff, the sieve-weight replacement error,
the main-term convention, a uniform threshold before `N`, and the exact final
weight. It should not conceal these data behind a generic pointwise BV name.

## Formalization boundary

The existing theorems through `q1CandidateAPCount_eq_doubleSum` are valuable
finite identities and should remain available as such.  They must not be used
as the consumer of `DimensionTwoSwitchingRemainder`.  The next Lean object is
therefore a new, explicitly supported switched/sieved count, followed by a
lemma comparing it with `correctedChenQ1Count`; only that new object may
consume the analytic remainder theorem.  This preserves the audited finite
algebra while making the analytic seam mathematically real.

## Candidate source-faithful redesign: one supported modulus, not two raw products

There is a narrower route worth separating from the rejected raw expression.
For fixed `q in Q_N`, count primes `p` with

```text
p = N (mod q),                    (N-p, P(z)) = 1.
```

Instead of expanding both coprimality predicates over all divisors, apply a
Selberg upper sieve **directly to this AP sequence**.  Its first-level
coefficients may depend on `N,q` and must satisfy

```text
lambda_{N,q}(d) != 0  =>  d | P(z),  d <= sqrt(D(N)/q).        (U0)
```

After the Selberg square is expanded, the coefficient at
`r = lcm(d1,d2)` is

```text
eta_{N,q}(r) = sum_{lcm(d1,d2)=r} lambda_{N,q}(d1)lambda_{N,q}(d2).
```

It has `r | P(z)` and `r <= D(N)/q`; this, rather than the support of a
single `lambda`, is the coefficient which multiplies an AP error.  Since
`q >= z` while every prime factor of `r` is `< z`, the surviving modulus is
the single product `m=q*r`, and (U0) gives `m <= D(N)`.  With

```text
D(N) = floor(sqrt(N)/log^B N),
```

this is exactly the level in the `a=1` weighted Bombieri--Vinogradov
specialization recorded in ANT's `A1_WEIGHTED_BV_SOURCE_MATCH.md`.

The required finite/analytic statement is consequently not Q1-2D as written
above, but the following conditional replacement target:

```text
q1Count(N)
 <= supported-main(N)
    + sum_{q in Q_N} sum_{r | P(z)}
        |eta_{N,q}(r)| |E_N(q*r)|
    + exceptional(N),                                             (Q1-1D)

E_N(m) = pi(N-2; m, N) - Li(N-2)/phi(m).
```

To consume weighted BV, a finite repackaging lemma must prove that the
coefficient of each `m=q*r` in the middle sum is bounded by a fixed multiple
of `mu(m)^2 3^omega(m)`, and that `m<=D(N)`.  In the intended strict ranges
this is especially clean: `r|P(z)` has all prime factors `<z`, while
`q>=z` is prime, so `gcd(q,r)=1`; moreover `q` is the unique prime factor of
`m` which is at least `z`.  Thus `(q,r) -> q*r` is injective on the surviving
pairs.  The standard Selberg combinatorics with `|lambda|<=1` gives
`|eta(r)| <= 3^omega(r)` (the three choices for each prime in an lcm pair),
which is at most `mu(m)^2 3^omega(m)` because `m=q*r` is squarefree.  These
elementary facts still need Lean proofs against the exact endpoint
conventions.  The resulting sum may then be bounded by the `a=1` weighted BV
theorem; this is a genuine one-modulus distribution statement, not an
invocation of pointwise BV.

There are two compulsory qualifications.

1. Start from the larger core condition
   `(N-p, correctedChenSiftingProduct(N))=1`; it contains
   `correctedChenCandidates(N)`, so is valid for an upper bound and avoids
   expanding `F_N` altogether.  Every prime factor of `r|P(z)` then does not
   divide `N` by definition of the corrected sifting product.  Hence
   `N mod (q*r)` is coprime to `q*r` unless `q|N`.  In that sole remaining
   non-coprime fibre, `q|N` and `q|N-p` force the prime `p=q`, so each such
   `q` contributes at most one.  These fixed-prime fibres need an explicit
   elementary bound, not an AP main term.
2. The upper-sieve majorant and its main term must be stated with the same
   endpoint and support as (Q1-1D).  It is not enough to assert that some
   coefficients exist: their sign/majorant property, the `Lambda²` expansion,
   its `3^omega` absolute-size bound, and support (U0) are all consumers of
   the proof.

This is a **candidate** source-matched route, not a completed deduction from
Liu.  It is preferable to Q1-2D if the required supported AP upper sieve and
coefficient repackaging can be written down, because it consumes the existing
ANT `a=1` supply without pretending that the raw `e`-sum has distributional
support.  Its falsifier is equally concrete: abandon this reduction if the
actual upper-sieve coefficients cannot satisfy (U), or if their repackaged
weight is not dominated by the available `mu²·3^omega` weight.

### Lean-facing interface sketch

The following names are schematic, but the quantifiers and the two sieve
levels are part of the required API.

```text
q1CoreCount(N,q)
 = #{p<N : p prime, 2<=N-p, q | N-p,
          gcd(N-p, correctedChenSiftingProduct(N))=1}

Q1SupportedSelbergData(N,q,D) contains lambda(d) with
  lambda(1)=1,
  lambda(d)=0 unless d | correctedChenSiftingProduct(N)
                         and d <= floor(sqrt(D/q)),
  |lambda(d)| <= 1,
  and the proved upper-majorant for q1CoreCount(N,q).

q1SelbergCoeff(N,q,r)
 = sum_{lcm(d1,d2)=r} lambda(d1)lambda(d2).
```

The first finite milestones are:

```text
correctedChenCandidates AP-count <= q1CoreCount(N,q),
q1SelbergCoeff(N,q,r) != 0 -> r | P(N) and q*r <= D,
abs(q1SelbergCoeff(N,q,r)) <= 3^omega(r),
(q,r) -> q*r injective on q in Q_N and r | P(N),
q | N -> q1CoreCount(N,q) <= 1.
```

Only after these have been kernel-checked may an analytic proposition
`Q1SupportedWeightedBV` quantify over sufficiently large even `N` and bound
the resulting supported `E_N(q*r)` sum by `N/log^A N`.  Its proof consumes
ANT's `WeightedBVAtOne` at `y=N-2`, not the legacy `q1APErrorUniformBound`.

## Source disposition: q1 is not the classical Omega remainder

The source route recorded in `PROOF_REFERENCE.md` is more specific than the
generic phrase “Pan/BV”.  In Liu's corrected proof, the switched variable is
`a = p₁ p₂`, and the Selberg upper sieve uses coefficients `λ_d` supported on
`d <= z'`.  After squaring the sieve, its only distribution moduli are
`[d₁,d₂]`; choosing `z' = N^(1/4 - ε/2)` gives

```text
[d₁,d₂] <= (z')² = N^(1/2 - ε).
```

The resulting remainder is

```text
sum_{d | Q, d <= N^(1/2-ε)} 3^ω(d)
  | sum_a f(a) Delta(N; a, d, N) |,                           (Liu-10)
```

with a separate split into `(a,d)=1` and `(a,d)>1`.  The latter is controlled
by the fact that the **complement** `N-a p` is prime and the congruence then
forces at most one `p`.  This is precisely the primitive/non-coprime
architecture recorded in `CHEN_OMEGA_PRIMALITY_OBJECT_AUDIT.md`.

It is not the q1 expression (2): q1 has a prime `q` in a different range and
two unrestricted full-product divisor sums.  Therefore Liu's Theorem 2 /
equation (10), Chen's classical Selberg stage, and the ANT a=1 Pan interface
must **not** be cited as a proof of `q1APErrorUniformBound`.

This gives an explicit fork for the theorem map:

```text
classical source-faithful Omega line:
  supported Selberg pair weights -> Liu-10 remainder -> Omega upper bound

current q1 line:
  prove a new switching/sieve comparison with supported weights
  -> source-match a theorem for Q1-2D -> q1 upper bound.
```

The first is the recommended route to an unconditional Chen chain because it
has a named source and an already audited primality object.  The second may
remain as a research interface, but has the stop condition that no theorem
from the first line can be consumed before an explicit comparison theorem is
proved.  The relevant source is Z. Liu, *A Corrected Simplified Proof of
Chen's Theorem*, arXiv:2203.07871, Sections III--IV, especially equations
(9)--(10) and (13).
