# Authority (public summary)

This is the public, sanitized summary of the repository's authority rules.
Internal exception records are omitted.

## Roles

| Role | Authority |
| --- | --- |
| Maintainer | Selects the next eligible claim; resolves scope and phase decisions; confirms promotion. |
| Claim owner | Keeps the claim record current; coordinates dependencies. |
| Independent reviewer | Reviews a nontrivial claim against its exact statement; records findings. |
| Agents and tools | May search, draft, compute, and review; never approve or promote. |

## Promotion

- Promotion requires an independent review and maintainer confirmation.
- `established` is a claim-status tag; `promoted` is a review disposition.
- Normative changes require a pull request with one approving review.

## Decision records

A maintainer decision is valid only when the record names the decider and
carries an ISO date. Phase changes and scope expansions require a dated
maintainer decision.
