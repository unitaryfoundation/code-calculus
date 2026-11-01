# Lean development

This directory contains a partial Lean 4 mechanization of the code-calculus.
It certifies only the theorems it states; it does not establish soundness of
the whole calculus. See the repository `README.md` and `spec/GATES.md` for
what is and is not claimed.

## Building

Toolchain is pinned in `lean-toolchain`. From this directory:

```sh
lake build
```

## Layout

- `CodeCalculus.lean` — top-level module that imports everything below.
- `CodeCalculus/` — one module per concern:
  - `State.lean` — presented code state, equality, canonical mint.
  - `Term.lean` / `Eval.lean` — term language and big-step evaluation.
  - `Invariants.lean` / `WellFormedness.lean` — well-formedness (I1–I5).
  - `Soundness.lean` — annotated-judgment soundness metatheorem.
  - `Transport.lean` — judgment transport through sequences, including the
    W13 refutation shape.
  - `PricedInterval.lean` — priced interval transport.
  - `ExactDistance.lean` — exact sector distance over F₂.
  - `KernelObligations.lean` — kernel obligation lemmas (determinism,
    associativity, direct-sum laws, frame law, cross-sector permutation,
    partial-inverse clauses).
  - `RanksFit.lean` — the dimension bound behind deletion/addition k-cells.
  - `GraftWellFormedness.lean` — well-formedness for E-GRAFT.
  - `Rebase*.lean` — presentation-rebase rank preservation.
  - `Fixtures.lean` / `FixtureReplay.lean` / `FixtureEvalReplay.lean` —
    fixture transcription and replay checks.
  - `WellFormedBool.lean` — boolean well-formedness helpers.
  - `Property.lean`, `Judgment.lean`, `Interval.lean`, `Refinement.lean`,
    `MaskRank.lean`, `MixSupport.lean` — supporting definitions.
- `CodeCalculus.lean` is the entry point imported by `lake build`.

## Status

Mechanization is partial and ongoing. Modules marked with `sorry` are
incomplete; the build is expected to be green (`0 sorry` on `main`). Gate 0
(record completeness) and Gate 1 (formal syntax) are ratified; Gates 2–7 are
unchecked. See `spec/GATES.md`.
