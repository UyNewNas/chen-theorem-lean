# Chen theorem in Lean

An auditable Lean formalization program for Chen's theorem and the sieve-theoretic
and analytic-number-theory ingredients around it.

## Project status — 2026-08-12

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
that the conditional Chen chain and all three local PNT/Mertens interfaces
depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
axioms — not on `sorryAx`.

### Phase 2 — analytic obligations completed

There are no executable `sorry` or `admit` terms in the tracked Lean sources.
The three former analytic obligations are now discharged through the audited
`analytic-number-theory-lean` foundation:

| Declaration | Status |
| --- | --- |
| `prime_number_theorem` | Complete |
| `mertens_second_theorem` | Complete |
| `mertens_product_formula` | Complete, including the `exp (-γ)` constant and `O(log⁻² x)` error |

The weaker product-order statement `primeProduct_asymptotic_order`, namely
`primeProduct x = Θ(1 / log x)`, remains available as a separately
kernel-audited corollary.

The two inputs below are **not** hidden placeholders: they are named Lean
propositions deliberately exposed in the type of `chens_theorem`.

- `ChenAnalyticBounds`: the genuinely uniform Jurkat--Richert/Selberg-style
  estimates needed by Chen's argument;
- `ChenCountingBridge`: a historical finite switching/counting interface.  It
  is refuted by finite evaluation for the present `chenW`/`chenOmega`
  definitions, so it must be replaced rather than proved.  The replacement is
  complete: the corrected candidates, bad-fibre penalty, and finite counting
  bridge are kernel-checked, with the rounding cutoffs discharged uniformly
  for `N ≥ 9` (`corrected_counting_bridge_public_of_nine_le`).  Moreover
  `corrected_key_inequality_implies_chen` turns the new analytic positivity
  target directly into a Chen representation, without this historical input.
  `corrected_chens_theorem` exposes that active route under its one named
  input, `CorrectedChenAnalyticPositivity`.

Consequently, the repository proves neither an unconditional Chen theorem nor
the classical uniform sieve estimates.  It does prove exactly what follows
from the stated inputs.

### Phase 3 — imported and audited PNT route

The repository consumes
[`analytic-number-theory-lean` v0.3.0](https://github.com/UyNewNas/analytic-number-theory-lean),
whose audited public API ports the minimal PNTAnd closure to the same Lean and
mathlib versions used here. It supplies a medium-strength Chebyshev-psi error
estimate, the standard `pi_alt` asymptotic, and the natural-number interface
`NatPrimeCountingPNT`.

The local normalization bridge is complete: `primeCount_eq_primeCounting`
identifies the project count with mathlib's `Nat.primeCounting`, and
`primeCountingPNT_implies_prime_number_theorem` turns the imported
natural-number PNT into this repository's epsilon-PNT statement. Thus
`prime_number_theorem` is no longer an open obligation. Version 0.3.0 also
supplies the natural-number Mertens-II and exact Mertens-product interfaces
consumed by `mertens_second_theorem` and `mertens_product_formula`.

### Next milestones

1. Formalize `ChenAnalyticBounds` with truly uniform constants for the
   corrected switching objects.
2. Remove the two explicit assumptions from `chens_theorem` only after step
   1 is complete.

Read [the chain audit](MathlibNt/SieveTheory/CHEN_CHAIN_AUDIT.md) before relying
on any headline claim.  It gives the exact theorem status, limitations of the
pointwise remainder interfaces, review commands, and completion milestones.
The separate [proof atlas](CHEN_PROOF_ATLAS.md) records the finite
counterexample to the current counting bridge and the required reconstruction
workline.
The external dependency audit records historical alternatives; the active,
imported analytic dependency is `analytic-number-theory-lean` v0.3.0.

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
axioms used by the two conditional derivations and the PNT/Mertens consumers;
CI requires every report to use only the three standard axioms above.

## Continuous audit

GitHub Actions runs the same build and axiom audit on pushes to `main`, pull
requests, and manual dispatches. It requires zero executable `sorry`/`admit`
terms in tracked Lean sources. Lake dependencies and the Lean toolchain
are cached only for speed; the job remains correct on a cache miss because it
rebuilds from `lake-manifest.json`.

CI output is the source of truth for the current commit. The PNT integration
extends the audit output with:

```text
'MathlibNt.ChensTheorem.chens_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.SwitchingPrinciple.key_inequality_implies_chen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.MertensTheorem.prime_number_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.MertensTheorem.mertens_second_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.MertensTheorem.mertens_product_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete audit contains thirty-five reports: the two conditional derivations,
the three analytic consumers, `primeProduct_asymptotic_order`, the two
pointwise error-budget interfaces, and twenty-seven finite bridge-foundation lemmas.
CI rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
This record does not discharge the two explicit proposition inputs to the
conditional theorem.

## Verify the zero-placeholder invariant

```sh
rg -n '^\s*(sorry|admit)\s*$' --glob '*.lean'
```

CI additionally strips comments and strings before scanning, so it also
rejects inline forms such as `by sorry`.

## Scope

This repository intentionally excludes unrelated experimental work, generated
build artifacts, vendored external PNT projects, and third-party PDFs.  External
PNT work is evaluated separately before any dependency is adopted.
