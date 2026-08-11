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
