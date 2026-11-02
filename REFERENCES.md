# References and citation keys

This note resolves the shorthand citations used throughout `spec/` and `machine/`.
None of these sources is shipped in this repository; the pointers below state
what each shorthand denotes and where (if anywhere) it can be obtained.

## Shorthand citation keys

- **proposal** — the project's internal research proposal (a planning document,
  not published). Sections cited: §3 (representation and state model), §4
  (term language and operational semantics), §5 (assertion and judgment
  language), §6 (distance opacity), §7 (property effects per operation),
  §8 (realization layer), §10 (gate structure). Where a `proposal §N`
  citation is load-bearing for a public claim, the corresponding normative
  content has been restated in `spec/` (see `SCOPE.md` and `spec/GATES.md`);
  the proposal itself is not a public artifact.
- **code-deformation** — a manuscript in preparation on CSS-code deformation
  and priced construction moves. Cited by theorem/proposition/lemma number
  (e.g. Theorem 12.1, Proposition 18.3, Theorem 28.2) and section (e.g.
  §4.1, §5.2, §9.4, §9.5). These citations name results that the calculus
  takes as inputs; where a result is reproduced in this repository it is
  recorded in `spec/OPERATIONAL_SEMANTICS.md` §4. The manuscript is not yet
  publicly available; the reproduced derivations in §4 are the
  repository's own evidence.
- **manuscript** — synonym for *code-deformation* where the citation names a
  theorem number as it appears in the manuscript (e.g. "manuscript Theorem 7").
- **an archived internal note** — an internal working note that has been
  superseded by `spec/` and `SCOPE.md`. Citations are retained as historical
  provenance only and are explicitly marked *not a normative dependency*.
  The note is not published.

## What to read instead

- For the calculus itself: `spec/` (normative), `SCOPE.md` (scope).
- For what is and is not claimed: `spec/GATES.md`, `spec/CLAIMS.md`.
- For the executable consumer: `machine/`.
- For mechanization: `lean/`.

## Why these are not in the repository

The proposal and the archived note are internal planning records; the
manuscript is a separate (in-preparation) publication. Publishing them here
would conflate planning history with normative specification. The calculus is
stated so that its normative content does not depend on reading either.

## External inputs taken (not reproduced in full)

The following results are taken as inputs from the manuscript named above.
Where a derivation is reproduced in this repository, the location is given.
None of these is a proof of a calculus claim; each enters only as a
conditional cell or as a recorded input, and the consumer never validates it.

- **Theorem 12.1** (manuscript Theorem 7), *code-deformation* §4.1 — priced
  single-check deletion: exact `d' = min(d, w_del, w_exp)` when the consumer
  supplies `w_del`, `w_exp`. Reproduced at
  `spec/OPERATIONAL_SEMANTICS.md` §4.19.
- **Proposition 18.3**, *code-deformation* §5.2 — strict improvement under
  addition: `d' ≥ d+1` with an exhaustive minimum-weight-class enumeration.
  Reproduced at `spec/OPERATIONAL_SEMANTICS.md` §4.19.
- **Lemma 18.5**, *code-deformation* §5.2 — sector-aware gauging: a supplied
  sector's lower bound is raised to `w_σ`.
- **Proposition 18.6 + Corollary 18.7**, *code-deformation* §5.2 —
  direct-sum extinction: `d' = d_B` under the stated structural side
  conditions (stack family only).
- **Theorems 27.2 / 27.5 / 27.8**, *code-deformation* §9.4 — `A-CONCAT`
  tower factorization as a deletion/exposure price provider (not a
  constructor).
- **Theorem 28.1**, *code-deformation* §9.5 — only deleted rows can expose a
  logical. Reproduced at `spec/OPERATIONAL_SEMANTICS.md` §4.19.
- **Theorem 28.2**, *code-deformation* §9.5 — sector-wise graft price.
  Reproduced (with corrections) at `spec/OPERATIONAL_SEMANTICS.md` §4.19.
- **Theorem 28.3**, *code-deformation* §9.5 — scalar monotonicity; **refuted**
  for this transition (see `spec/OPERATIONAL_SEMANTICS.md` §4.13 and §4.20).
- **Claims 15.8, 15.9, 15.10**, *code-deformation* — face-set-model
  observations about gauging-as-merge and sequencing non-commutativity.
  Recorded at `spec/OPERATIONAL_SEMANTICS.md` §2.

## Historical provenance

Shorthand citations (`proposal §N`, `code-deformation`, `manuscript`,
`an archived internal note`) are historical provenance only. The normative
content of `spec/` does not depend on reading any of them, and they are not
required to understand or use the calculus. Where a result above is reproduced,
the reproduction in `spec/OPERATIONAL_SEMANTICS.md` §4 is the authoritative
statement in this repository.