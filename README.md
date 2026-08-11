# Chen theorem in Lean

An auditable Lean formalization program for Chen's theorem and the sieve-theoretic
and analytic-number-theory ingredients around it.

## Project status — 2026-08-10

This repository does **not** claim an unconditional, completed formal proof of
Chen's theorem.  It is an auditable formalization program with a completed
conditional core and clearly recorded outstanding analytic and combinatorial
work.

### Phase 1 — completed and kernel-checked

The central theorem is a kernel-checked conditional derivation:

```text
ChenAnalyticBounds + ChenCountingBridge
  -> chen_key_inequality
  -> key_inequality_implies_chen
  -> chens_theorem
```

The following are complete Lean proofs in this chain:

- the numerical inequality `chen_key_inequality`, conditional on uniform
  analytic bounds;
- extraction of a prime-plus-at-most-two-almost-prime representation from a
  positive finite cardinality bound;
- the final packaging theorem `chens_theorem`, conditional on the two named
  inputs;
- the project semiprime API and its agreement with the intended “one or two
  prime factors” interpretation.

`lake build` succeeds for the full public module root. `Audit.lean` verifies
that `chens_theorem`, `key_inequality_implies_chen`, and the local
`prime_number_theorem`, and `mertens_second_theorem` depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms — not on `sorryAx`.

### Phase 2 — explicit open obligations

There is currently exactly one executable `sorry`, in
`MathlibNt/SieveTheory/MertensTheorem.lean`:

| Declaration | Work remaining |
| --- | --- |
| `mertens_product_formula` | Mertens product formula with the stated constant and error term |

The two inputs below are **not** hidden placeholders: they are named Lean
propositions deliberately exposed in the type of `chens_theorem`.

- `ChenAnalyticBounds`: the genuinely uniform Jurkat--Richert/Selberg-style
  estimates needed by Chen's argument;
- `ChenCountingBridge`: the exact finite switching/counting inequality linking
  the working definitions of `chenW`, `chenOmega`, and good representations.

Consequently, the repository proves neither an unconditional Chen theorem nor
the classical uniform sieve estimates.  It does prove exactly what follows
from the stated inputs.

### Phase 3 — imported and audited PNT route

The repository consumes
[`analytic-number-theory-lean` v0.2.0](https://github.com/UyNewNas/analytic-number-theory-lean),
whose audited public API ports the minimal PNTAnd closure to the same Lean and
mathlib versions used here. It supplies a medium-strength Chebyshev-psi error
estimate, the standard `pi_alt` asymptotic, and the natural-number interface
`NatPrimeCountingPNT`.

The local normalization bridge is complete: `primeCount_eq_primeCounting`
identifies the project count with mathlib's `Nat.primeCounting`, and
`primeCountingPNT_implies_prime_number_theorem` turns the imported
natural-number PNT into this repository's epsilon-PNT statement. Thus
`prime_number_theorem` is no longer an open obligation. Version 0.2.0 also
supplies the natural-number Mertens-II interface consumed by
`mertens_second_theorem`.

### Next milestones

1. Derive the exact Mertens product statement from an audited sufficiently
   strong analytic input.
2. Formalize `ChenAnalyticBounds` with truly uniform constants.
3. Formalize `ChenCountingBridge` for the present finite-set definitions.
4. Remove the two explicit assumptions from `chens_theorem` only after steps
   2 and 3 are complete.

Read [the chain audit](MathlibNt/SieveTheory/CHEN_CHAIN_AUDIT.md) before relying
on any headline claim.  It gives the exact theorem status, limitations of the
pointwise remainder interfaces, review commands, and completion milestones.
The external dependency audit records historical alternatives; the active,
imported PNT dependency is `analytic-number-theory-lean` v0.1.0.

## Layout

- `MathlibNt/ChensTheorem.lean`: conditional Chen theorem and the semiprime API.
- `MathlibNt/SieveTheory/`: sieve, switching, Mertens, and distribution modules.
- `MathlibNt/SieveTheory/CHEN_CHAIN_AUDIT.md`: review-oriented trust boundary.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: reproducible Lean/Lake setup.

## Build

```sh
lake build
lake env lean Audit.lean
```

The project toolchain is pinned by `lean-toolchain`. `Audit.lean` prints the
axioms used by the two conditional derivations and `prime_number_theorem`; its
output must not contain `sorryAx`.

## Continuous audit

GitHub Actions runs the same build and axiom audit on pushes to `main`, pull
requests, and manual dispatches. It requires the current inventory of exactly
two executable `sorry`s. Lake dependencies and the Lean toolchain
are cached only for speed; the job remains correct on a cache miss because it
rebuilds from `lake-manifest.json`.

CI output is the source of truth for the current commit. The PNT integration
extends the audit output with:

```text
'MathlibNt.ChensTheorem.chens_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.SwitchingPrinciple.key_inequality_implies_chen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.MertensTheorem.prime_number_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the two conditional derivations and imported-PNT consumer contain no
`sorryAx`; this record does not discharge the two explicit proposition inputs
or the two separately listed Mertens obligations.

## Verify the open obligations

```sh
rg -n '^\s*sorry\s*$' MathlibNt --glob '*.lean'
```

## Scope

This repository intentionally excludes unrelated experimental work, generated
build artifacts, vendored external PNT projects, and third-party PDFs.  External
PNT work is evaluated separately before any dependency is adopted.
