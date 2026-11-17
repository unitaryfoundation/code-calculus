# AXIOMS.md — accepted assumptions in the mechanization

This file records the Lean axioms that the repository **deliberately keeps**
rather than proving, together with the issues they gate. It is the trust-basis
counterpart of `lean/CodeCalculus/AxiomAudit.lean` (which guards
`Classical.choice` and `sorryAx` in the audited modules). Nothing here is
claimed as a theorem.

## `lean/extra/ClosedK.lean` (non-audited module)

These four axioms are the only assumptions in `extra/ClosedK.lean`. They are
rank identities of the natural check matrices of two constructors. Under the
hard rule added in PR #507, they mean that issues #497, #498, and the #424
umbrella are **closed on assumptions, not on proofs**; the corresponding
claims read `proposed (classical)` in the claim/evidence model.

| Axiom | Statement (informal) | Gates |
| --- | --- | --- |
| `hgp_rankX` | Rank of the `X`-sector natural matrix of `L-HGP` is `m1*n2 - (m1 - r1)*(n2 - r2)`. | #497 |
| `hgp_rankZ` | Rank of the `Z`-sector natural matrix of `L-HGP` is `n1*m2 - (n1 - r1)*(m2 - r2)`. | #497 |
| `product_rankX` | Rank of the `X`-sector natural matrix of `A-PRODUCT` is `nA*xB + xA*nB - xA*xB`. | #498 |
| `product_rankZ` | Rank of the `Z`-sector natural matrix of `A-PRODUCT` is `nA*zB + zA*nB - zA*zB`. | #498 |

The arithmetic that combines these ranks into the closed forms for `stateK`
(`hgp_arith`, `product_arith`) **is** proved (PR #517). Only the rank
identities above remain assumed.

### Why they are kept (not proved)

Discharging them requires three pieces the mask-rank library does not yet have:

1. An independent family inside a span is no longer than a spanning list
   (rank is monotone in the span).
2. Row rank of a matrix equals its column rank (the HGP formula is stated
   with row ranks but the argument uses the column space of `H2`).
3. The rank of a list of rows of the form `(u ⊗ e_j, e_a ⊗ v)`.

For `A-PRODUCT`, the same three are needed for the tensor product of two
three-term complexes. The discharge path is therefore: extend
`lean/CodeCalculus/MaskRank.lean` with (1)–(3), then convert the four
`axiom`s above to `theorem`s and reopen the obligations.

### Status discipline

- These are `proposed (classical)` assumptions, not `established` facts.
- They are confined to the non-audited `extra/` module and are **not** part
  of the `AxiomAudit` trust basis.
- The set of four is frozen: `scripts/lint_docs.sh` checks that
  `lean/extra/ClosedK.lean` declares exactly these four axioms. Any change
  to the set requires updating this file and the check together.
- They must not be cited as proofs of #497/#498/#424; those issues are
  closed on the explicit condition that these assumptions hold.

## Other modules

No other module in `lean/` declares an `axiom`. `Classical.choice` is
confined to the denotation, as recorded by `AxiomAudit.lean`.