# Chen chain: formalization audit

This document is the review entry point for the Chen-theorem development in
`MathlibNt`.  It describes what Lean has checked, what is deliberately stated
as an explicit assumption, and what remains unformalized.

## Executive summary

The repository does **not** currently contain an unconditional formal proof of
Chen's theorem.  It contains a kernel-checked conditional derivation:

```text
ChenAnalyticBounds + ChenCountingBridge
  -> chen_key_inequality
  -> key_inequality_implies_chen
  -> chens_theorem
```

The two assumptions are named, typed Lean propositions rather than hidden
`sorry`s. The only remaining `sorry` in `MathlibNt` is the analytic
number-theory result listed below.

## Current `sorry` inventory

As of 2026-08-10, `rg -n '^\s*sorry\s*$' MathlibNt --glob '*.lean'` reports:

| File | Declaration | Status | Why it matters |
| --- | --- | --- | --- |
| `MertensTheorem.lean` | `mertens_product_formula` | `sorry` | Precise Mertens product constant |

No declaration in `ChensTheorem.lean`, `SwitchingPrinciple.lean`,
`SelbergUpperBound.lean`, or `BombieriVinogradov.lean` currently has a
`sorry`.

## Checked conditional chain

### 1. Analytic input

`SwitchingPrinciple.ChenAnalyticBounds` is a proposition asserting, for every
even `N >= 1000`, the two uniform numerical estimates needed by the classical
Chen argument:

```lean
2.6408 * chenW N >= 2.6408 * 2.6408 * N / log N ^ 2
chenOmega N <= 3.9404 * N / log N ^ 2
```

This is intentionally an external input.  The local results named
`chenW_lower_bound` and `chenOmega_upper_bound` prove only *pointwise
additive-remainder* interfaces: their constants may depend on the fixed `N`.
They must not be read as the uniform estimates above.

### 2. Numerical key inequality

Given `ChenAnalyticBounds`, `chen_key_inequality` proves

```lean
chenW N - chenOmega N / 2 > 0
```

by elementary real arithmetic.  The positivity comes from
`2.6408 - 3.9404 / 2 = 0.6706 > 0` and from the positive scale
`N / log N ^ 2`.

### 3. Combinatorial input

`SwitchingPrinciple.ChenCountingBridge` is a proposition asserting that the
positive difference above is bounded by the cardinality of
`chenGoodRepresentations N`, the finite set of primes `p < N` for which
`N - p >= 2` is at most 2-almost-prime.

This proposition is the missing precise switching/counting correspondence for
the current working definitions of `chenW` and `chenOmega`.  In particular,
`chenW` is an unweighted filter cardinal while `chenOmega` is indexed by
factor pairs `a = p1 * p2`; their relationship is not obtained merely by
unfolding definitions.

### 4. Extraction of the representation

Given `ChenCountingBridge`, `key_inequality_implies_chen` turns positivity of
the real cardinality bound into `Finset.card_pos`, extracts an element of
`chenGoodRepresentations N`, and proves `N = p + (N - p)`.

`ChensTheorem.chens_theorem` packages that result using the project's
`Semiprime q := 2 <= q /\ Nat.IsAtMostAlmostPrime 2 q` definition.

## Pointwise interfaces versus classical theorems

Several historic declarations had a constant quantified too weakly to express
the advertised uniform analytic theorem, or claimed a stronger theorem than
their definitions supported.  They were corrected rather than filled with an
opaque proof.

| Declaration | Current meaning |
| --- | --- |
| `bombieri_vinogradov` | Fixed `x, q, y, l` multiplicative-remainder interface; not the classical average-over-moduli BV theorem. |
| `pan_mean_value_theorem` | Fixed-parameter remainder interface; the previous summand did not depend on its summation variable. |
| `main_term_bound` | Fixed-`N` additive-remainder interface; `SelbergWeights` does not encode optimality. |
| `chenOmega_simple_bound` | Fixed-`N` additive-remainder interface, derived from the complete bound. |
| `chenW_lower_bound` | Fixed-`N` additive-remainder interface. |

The names are retained for API continuity, but their docstrings state these
limitations.  Reviewers should use `ChenAnalyticBounds` when they need the
genuine uniform estimates.

## Review checklist

1. Confirm the inventory with:

   ```sh
   rg -n '^\s*sorry\s*$' MathlibNt --glob '*.lean'
   ```

2. Inspect the exact types of `ChenAnalyticBounds` and `ChenCountingBridge` in
   `MathlibNt/SieveTheory/SwitchingPrinciple.lean`.
3. Compile the chain, including dependencies, with the project toolchain.
4. Do not label `chens_theorem` unconditional unless proofs of both explicit
   inputs are supplied.
5. The imported `analytic-number-theory-lean` v0.1.0 PNT already discharges
   the local `prime_number_theorem`; audit future analytic imports with
   `#print axioms` before using them for the two remaining results.

## Next completion milestones

1. Derive the two Mertens statements from the imported audited PNT foundation.
2. Replace `ChenAnalyticBounds` by a uniform Jurkat--Richert/Selberg proof.
3. Begin the switching bridge with a weak lemma: instantiate
   `chenWeight_pos_implies_semiprime` at `N - p`, with the present
   `floor (N^(1/10))` and `floor (N^(1/3))` cutoffs, and formalize the needed
   membership/positivity translation.  Then strengthen it to a precise
   switching identity matching the present finite-set definitions and prove
   `ChenCountingBridge`.
4. Re-run the inventory and strengthen `chens_theorem` by removing its two
   explicit assumptions only after steps 2 and 3 are complete.

The public repository's related documentation is `PROOF_REFERENCE.md` and
`EXTERNAL_DEPENDENCY_AUDIT.md`.  Project-wide scratch status files are
intentionally not part of this release.
