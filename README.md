# Chen theorem in Lean

An auditable Lean formalization program for Chen's theorem and the sieve-theoretic
and analytic-number-theory ingredients around it.

## Status

This repository does **not** claim an unconditional, completed formal proof of
Chen's theorem.  The central theorem is a kernel-checked conditional derivation:

```text
ChenAnalyticBounds + ChenCountingBridge
  -> chen_key_inequality
  -> key_inequality_implies_chen
  -> chens_theorem
```

The unsupplied analytic and combinatorial ingredients are explicit Lean
propositions, not hidden placeholders.  The remaining `sorry`s are confined to
the prime number theorem and two precise Mertens statements.

Read [the chain audit](MathlibNt/SieveTheory/CHEN_CHAIN_AUDIT.md) before relying
on any headline claim.  It gives the exact theorem status, limitations of the
pointwise remainder interfaces, review commands, and completion milestones.

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

## Verify the open obligations

```sh
rg -n '^  sorry$' MathlibNt --glob '*.lean'
```

## Scope

This repository intentionally excludes unrelated experimental work, generated
build artifacts, vendored external PNT projects, and third-party PDFs.  External
PNT work is evaluated separately before any dependency is adopted.
