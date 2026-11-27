# AXIOMS.md: accepted assumptions in the mechanization

This file records the Lean axioms that the repository deliberately keeps
in place of a proof, together with the obligations they relate to. It is
the trust-basis counterpart of `lean/CodeCalculus/AxiomAudit.lean` (which
guards `Classical.choice` and `sorryAx` in the audited modules).

## Current set

None. No module under `lean/` declares an `axiom`, and
`scripts/lint_docs.sh` fails if one appears. `Classical.choice` is confined
to the denotation, as recorded by `AxiomAudit.lean`.

A new assumption needs an entry here and a change to that check in the
same pull request, with the reason it is kept and what its discharge
requires.

## Discharged

Until 2026-11-24 the non-audited module `lean/extra/ClosedK.lean` declared
four axioms, accepted as `proposed (classical)` assumptions on 2026-11-16.
They are theorems of the audited module `lean/CodeCalculus/ClosedK.lean`
since, with the statements unchanged, and depend on `propext` and
`Quot.sound` alone.

| Statement | Content (informal) | Proved from |
| --- | --- | --- |
| `hgp_rankX` | Rank of the `X`-sector natural matrix of `L-HGP` is `m1*n2 - (m1 - r1)*(n2 - r2)`. | `rank_hgRows`, `rank_colMasks` |
| `hgp_rankZ` | Rank of the `Z`-sector natural matrix of `L-HGP` is `n1*m2 - (n1 - r1)*(m2 - r2)`. | `rank_hgRows`, `rank_colMasks` |
| `product_rankX` | Rank of the `X`-sector natural matrix of `A-PRODUCT` is `nA*xB + xA*nB - xA*xB`. | `rank_prodRows` |
| `product_rankZ` | Rank of the `Z`-sector natural matrix of `A-PRODUCT` is `nA*zB + zA*nB - zA*zB`. | `rank_prodRows` |

The three capabilities the discharge was recorded as needing are in the
audited modules:

1. The rank is monotone in the span (`rankBitmasks_le_of_span` in
   `RankNullity.lean`), with rank and nullity for an additive map
   (`rank_nullity`, `rank_kerList`).
2. Row rank equals column rank (`rank_colMasks` in `HgpRank.lean`).
3. The rank of a family of tensors is the product of the ranks
   (`rank_tens` in `TensorRank.lean`), and the rank of the family of rows
   `(u ⊗ e_j, e_a ⊗ v)` follows (`rank_hgRows` in `HgpRank.lean`). The
   tensor product of two three-term complexes is `rank_prodRows` in
   `ProductRank.lean`.

The closed forms `hgpState_k_closed` and `productState_k_closed` therefore
rest on no assumption. This file records the mechanization. It moves no
claim status in `spec/`.
