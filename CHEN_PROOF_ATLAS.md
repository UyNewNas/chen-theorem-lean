# Chen theorem proof atlas

## Target and boundary

- Target statement: an unconditional Lean proof that every sufficiently large
  even natural number is a prime plus an integer with at most two prime factors.
- Claim type: universal.  The present kernel-checked result is conditional on
  `ChenAnalyticBounds` and `ChenCountingBridge`.
- Known strongest nearby result in this repository: the conditional chain in
  `MathlibNt.ChensTheorem.chens_theorem`, with the PNT and Mertens consumers
  fully discharged by `analytic-number-theory-lean`.
- Exact obstruction: the two remaining inputs are not merely unproved.  The
  analytic input requires uniform lower/upper sieve estimates absent from the
  current pointwise interfaces, and the current concrete counting bridge is
  false.

The sieve parity barrier remains relevant: this supply line aims at
prime-plus-`P₂`, not prime-plus-prime.  It must not be described as a route
around the barrier to Goldbach.

## Architecture source

- Landmark programme: the classical Chen/Jurkat--Richert/Selberg sieve
  programme, treated here as a source of exact interfaces rather than as a
  proof imported by analogy.
- Counterexample encoding: a hypothetical even `N` with no prime-plus-`P₂`
  representation yields an empty `chenGoodRepresentations N`.
- Translation invariant: a corrected sieve candidate count must decompose into
  good candidates, a finite boundary fibre, and explicitly indexed bad
  three-factor candidates.
- Global constraints that collide: a uniform lower bound for the corrected
  candidate count and a uniform upper bound for the bad count force the good
  fibre to be nonempty.
- Source-specific prerequisites: a genuine lower-bound sieve, a correctly
  averaged Bombieri--Vinogradov/Pan error bound, Selberg quadratic-form
  estimates, and the classical numerical margin.
- Transferable mechanism: state and verify the finite counting bridge before
  attaching analytic estimates; keep an explicit error budget at the seam.

## Candidate route for the target

| Node | Statement or construction | Status | Consumer | Verification / falsifier |
| --- | --- | --- | --- | --- |
| Counterexample | `chenGoodRepresentations N` is empty for an even large `N` | conditional | Final contradiction | Its definition is kernel-checked. |
| Candidate set | Redefine the W-candidates with a named unit fibre and factor-multiplicity-aware bad fibre | hypothesis | Corrected switching bridge | Enumerate finite `N`; the old definitions fail at `N = 1000`. |
| Finite bridge | `correctedW N - correctedOmega N / m ≤ good.card + boundary N` with a proved multiplicity `m` | hypothesis | Nonemptiness from analytic positivity | Every bad candidate must map to the stated `Omega` index set with verified fibre size. |
| Error interface | `ChenPointwiseAnalyticBoundsAt N` and `chen_key_inequality_of_error_budget` | proven | Uniform analytic workline | Kernel-checked in `SwitchingPrinciple.lean`. |
| Uniform sieve bounds | A single threshold and constants closing the error budget for every even `N` above it | conditional | Key inequality | Reject any version whose constants are quantified after `N`. |
| Contradiction | Positive corrected count contradicts an empty good fibre after the finite bridge | conditional | Universal target | Requires both prior hypothesis/conditional nodes. |

## Corrected finite model

The current implementation has begun the definition seam proposed by the
red-team review:

```text
z(N) = max(2, floor(N^(1/10)))
y(N) = ceil(N^(1/3))
C(N) = {p < N : p prime, 2 ≤ N-p, no prime r < z(N) divides N-p}
G(N) = {p in C(N) : N-p is at-most-2-almost-prime}
B(N) = C(N) \ G(N)
```

`correctedChenCandidates`, `correctedChenGoodCandidates`, and
`correctedChenBadCandidates` implement these finite sets.  The proven
partition and the inclusion `G(N) ⊆ chenGoodRepresentations(N)` are only the
safe combinatorial base; they do not establish a switching estimate.

The next proposed object is a **new** weighted penalty rather than the old
`chenOmega`:

```text
penalty(q) = multiplicity of medium prime divisors of q
             + number of canonical (medium, large, large) prime triples for q
Omega*(N) = sum_{p in C(N)} penalty(N-p)
```

The required finite theorem is `p ∈ B(N) → 2 ≤ penalty(N-p)`.  Its intended
proof route is a contrapositive of the existing positive-weight-to-`P₂` lemma,
after proving that the new penalty equals the corresponding weight.  Only then
may the bridge

```text
card C(N) - Omega*(N) / 2 ≤ card G(N)
```

be stated.  The `/2` is thus justified by a lower bound on an explicit fibre,
not by an informal symmetry argument.  Any analytic estimate for `Omega*`
must be reproved; the historical `3.9404` constant cannot be reused.

The first conditional fibre theorem is now kernel-checked as
`correctedChenBad_penalty_ge_two`: it requires `z(N) < y(N)` and
`N - p < y(N)^3`. Both cutoff conditions are now discharged uniformly for
`N ≥ 9`: ceiling rounding gives `y(N)^3 ≥ N`, and the real-power/floor/ceiling
argument proves `z(N) < y(N)`.

Summing that fibre theorem is also kernel-checked as
`corrected_counting_bridge`:

```text
card C(N) - correctedChenOmega(N) / 2 ≤ card G(N)
```

under precisely the same cutoff assumptions. Since those cutoff assumptions
are now uniform at `N ≥ 9`, the only remaining work on this line is to
establish analytic bounds for the new `correctedChenCandidates` and
`correctedChenOmega` objects.

The public-facing corollary is now also kernel-checked as
`corrected_counting_bridge_public_of_nine_le`. It derives `N - p < y(N)^3`
for every candidate, embeds the corrected good fibre into
`chenGoodRepresentations N`, and discharges all cutoff arithmetic at `N ≥ 9`.
No finite counting or rounding conversion remains at that boundary.

Finally, `corrected_key_inequality_implies_chen` consumes the single target

```text
0 < card C(N) - correctedChenOmega(N) / 2
```

for all sufficiently large even `N` and extracts the public Chen
representation. The historical `ChenCountingBridge` is therefore no longer
on the active proof path.

`CorrectedChenAnalyticPositivity` names exactly this sole remaining assumption,
and `corrected_chens_theorem` is the corresponding conditional theorem.

The first analytic-side transport lemma is also kernel-checked:
`chenWCandidate_mem_corrected_of_two_le` embeds every historical lower-sieve
candidate with complementary value at least two into the corrected candidate
set.  This permits a future uniform lower bound for the old lower-sieve
candidate count to transfer with only the already-isolated unit boundary; it
does not transfer the invalid historical Omega estimate.

The next bounded analytic workline is now fixed: construct a
`BoundingSieve` whose support is the corrected complements, prove its
`siftedSum` equals `correctedChenCandidates.card`, and add the mirror-image
lower Möbius inequality

```text
totalMass * mainSum μminus - errSum μminus ≤ siftedSum.
```

The error term must remain this concrete finite `errSum`; no statement of the
form “there exists a constant after fixing N” is admissible. Only after that
finite inequality is in place should the uniform order of quantifiers be
proved for the error bound.

This generic finite inequality is now kernel-checked in `LinearSieve.lean` as
`mainSum_sub_errSum_le_siftedSum_of_lowerMoebius`. The remaining work is the
object-specific construction of `correctedChenSieve`, its exact sifted-sum
identification, and a genuinely uniform bound for that sieve's explicit error.
Its squarefree sifting product is now separately kernel-checked as
`correctedChenSiftingProduct_squarefree`.

The object-specific `BoundingSieve` record is now kernel-checked as
`correctedChenBoundingSieve`: it pairs the corrected complement support with
the sifting product, unit weights, and the Goldbach density
`ν(p) = 1/(p−1)`, proving `0 < ν(p) < 1` for every sieved prime through the
divisibility characterization `prime_dvd_correctedChenSiftingProduct`.  Its
total mass is still the exact support cardinality; replacing it with the
analytic main term and proving a uniform remainder bound remain the
`ChenAnalyticBounds` workline.

The exact sifted-sum identification is also kernel-checked:
`correctedChenBoundingSieve_siftedSum_eq_card` proves
`(correctedChenBoundingSieve N).siftedSum = correctedChenCandidates N`.card,
so the surviving sieve count is literally the corrected candidate count.  The
remaining analytic step on this line is the uniform `errSum` bound for the
corrected sieve; no further finite conversion is hidden at that boundary.

On the main-term side, the Selberg divisor sum for the corrected sieve is
factored in closed form as
`correctedChenSelbergSum_eq_prod_inv`:
`∑_{d | P} g(d) = ∏_{p | P} (1 − ν(p))⁻¹`, with prime factor
`(1 − ν(p))⁻¹ = (p−1)/(p−2)` at each sieved prime
(`correctedChenNu_inv_prime`).  The asymptotic evaluation of this product —
via the exact Mertens product formula and the singular series — is the next
main-term step on the analytic workline.

That seam is now made explicit: each sieved-prime factor splits as
`(1 − ν(p))⁻¹ = (p/(p−1)) · localFactor(p, N)⁻¹`
(`correctedChenNu_inv_prime_localFactor`), so the whole Selberg sum factors as
`∏_{p | P} p/(p−1)` times the reciprocal of the singular-series local-factor
product (`correctedChenSelbergSum_eq_mertens_mul_localFactor_inv`).

The **main-term asymptotic evaluation is now closed**.  The exact seam identity
`correctedChenSelbergSum_mul_singularSeriesTruncated` restores the excluded
`p = 2` and `p | N` factors (back into `singularSeriesTruncated`) and reduces
the sieved Selberg product to the full Mertens-type product
`∏_{p<z} p/(p−1)`:

```text
SelbergSum(N) · 𝔖(N, z−1) = 1 / primeProduct(z−1)
```

Applied to the exact Mertens product formula
(`primeProduct_asymptotic_order`), this yields the uniform main-term order
`correctedChenSelbergSum_asymptotic_order`:

```text
SelbergSum(N) = Θ(log(z−1) / 𝔖(N, z−1))
```

The only remaining main-term-adjacent work is the uniform `errSum` bound
(BV/Pan workline).

On the error side, the distribution seam is now explicit and kernel-checked.
For the corrected sieve, `correctedChenMultSum_eq_multiples_card` identifies
`multSum d` with the number of support elements divisible by `d`,
`correctedChenMultiples_card_eq_primeSupport` transfers that count to the
prime-support partners with `d ∣ N − p`, and
`correctedChenMultSum_eq_modEq_count` re-expresses it as the number of
prime-support primes congruent to `N` modulo `d`.  A Bombieri--Vinogradov/Pan
input therefore bounds `multSum` (and hence the concrete `errSum`) as an
arithmetic-progression count; no hidden finite conversion remains at that
seam.

The repackaging is closed end-to-end: `correctedChenRem_eq_modEq_count`
spells `rem d` as the congruence-count minus the density main term, and
`correctedChenErrSum_eq_modEq` writes the whole `errSum` as the sum of
absolute congruence-count errors.  The precise analytic target is stated as
`CorrectedChenDistributionCondition`: a uniform `C` bounding
`|#{p ∈ primeSupport : p ≡ N [MOD d]} − ν(d)·N/log N|` by `C·N/log^A N` for
`d ≤ N^{1/2}/log^{10} N` and every sufficiently large even `N`.  Supplying
that condition (from the classical Bombieri--Vinogradov/Pan estimates, with
the `totalMass` main term replaced by `N/log N`) is the remaining work of the
`errSum` line.

The density side of that main term is now identified in closed form:
`correctedChenNu_squarefree_eq_inv_totient` proves `ν(d) = 1/φ(d)` for
squarefree `d` (via `totient_eq_prod_primeFactors_of_squarefree`), so
`ν(d) · N/log N` is literally the standard Bombieri--Vinogradov main term
`li(N)/φ(d)`.  The BV input can therefore be applied verbatim to the
repackaged `errSum`.

## Dependency sketch

```text
empty good fibre --[hypothesis: corrected finite bridge]--> nonpositive sieve difference
                                                               ^
                                                               |
uniform JR / Selberg / BV estimates --[conditional]--> positive sieve difference
```

The old edge

```text
chenW - chenOmega / 2 <= good.card
```

is **refuted for the current definitions** by an external finite evaluation at
`N = 1000` (not yet a Lean kernel certificate):
`chenW = 153`, `chenOmega = 17`, and `good.card = 122`, so the left side is
`144.5`, larger than `122`.

## Next cycle

- Smallest testable artifact: define a corrected candidate partition and prove
  the unit fibre has cardinality at most one.  The latter is already available
  as `range_sub_eq_one_card_le_one`.
- Evidence required to retain the route: a Lean proof that every non-unit,
  non-good candidate has an `Omega` witness, together with an exact bound on
  witness multiplicity.
- Stop condition: find a finite counterexample to the proposed corrected
  bridge, or fail to establish a uniform fibre bound.  In either case revise
  the counting objects before attempting analytic work.
- Supply-line connection: `ChenPointwiseAnalyticBoundsAt` makes the remaining
  analytic requirement an explicit error-budget condition; no pointwise
  remainder theorem is allowed to masquerade as a uniform sieve estimate.
