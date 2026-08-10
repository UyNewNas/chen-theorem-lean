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

`lake build` succeeds for the full public module root.  `Audit.lean` verifies
that `chens_theorem` and `key_inequality_implies_chen` depend only on Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms — not on
`sorryAx`.

### Phase 2 — explicit open obligations

There are currently exactly three executable `sorry`s, all in
`MathlibNt/SieveTheory/MertensTheorem.lean`:

| Declaration | Work remaining |
| --- | --- |
| `prime_number_theorem` | PNT for the local finite `primeCount` normalization |
| `mertens_second_theorem` | prime reciprocal-sum asymptotic with the stated error term |
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

### Phase 3 — audited external PNT route

Two external developments have been built and examined separately:

- `math-inc/strongpnt` at Lean 4.21 proves a strong PNT for Chebyshev's psi
  function; its audited main theorem has no `sorryAx`.
- `PrimeNumberTheoremAnd` v4.32.2 proves the standard prime-counting asymptotic
  `pi_alt`; its audited theorem likewise has no `sorryAx`.

The latter is the preferred import candidate because it is only one Lean
release behind this repository.  It is **not yet a dependency**: the required
v4.32.2-to-v4.33 adaptation has not been performed.

The local normalization bridge is already complete:
`primeCount_eq_primeCounting` identifies the project count with mathlib's
`Nat.primeCounting`, and `primeCountingPNT_implies_prime_number_theorem`
turns the `pi_alt` shape into this repository's epsilon-PNT statement.

### Next milestones

1. Port the dependency closure of PNTAnd's `pi_alt` to Lean 4.33 and establish
   `PrimeCountingPNT`; this discharges the local PNT interface.
2. Derive the two exact Mertens statements from an audited sufficiently strong
   analytic input.
3. Formalize `ChenAnalyticBounds` with truly uniform constants.
4. Formalize `ChenCountingBridge` for the present finite-set definitions.
5. Remove the two explicit assumptions from `chens_theorem` only after steps
   3 and 4 are complete.

Read [the chain audit](MathlibNt/SieveTheory/CHEN_CHAIN_AUDIT.md) before relying
on any headline claim.  It gives the exact theorem status, limitations of the
pointwise remainder interfaces, review commands, and completion milestones.
The separately verified status of a possible strong-PNT dependency is recorded
in [the external dependency audit](EXTERNAL_DEPENDENCY_AUDIT.md); it is not yet
an imported dependency.

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

The project toolchain is pinned by `lean-toolchain`.  `Audit.lean` prints the
axioms used by the two conditional derivations; its output must not contain
`sorryAx`.

## Continuous audit

GitHub Actions runs the same build and axiom audit on pushes to `main`, pull
requests, and manual dispatches.  It also rejects any increase above the
current three executable `sorry`s.  Lake dependencies and the Lean toolchain
are cached only for speed; the job remains correct on a cache miss because it
rebuilds from `lake-manifest.json`.

## Verify the open obligations

```sh
rg -n '^\s*sorry\s*$' MathlibNt --glob '*.lean'
```

## Scope

This repository intentionally excludes unrelated experimental work, generated
build artifacts, vendored external PNT projects, and third-party PDFs.  External
PNT work is evaluated separately before any dependency is adopted.
