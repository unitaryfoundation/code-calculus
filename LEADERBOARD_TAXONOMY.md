# Leaderboard Taxonomy

What type of code compositions and deformations are present in the qldpc challenge?

Url: https://unitaryfoundation.github.io/qldpc-challenge/

Snapshot date: September 22 (2026)

Four entries below were checked against the primary
sources; three were found wrong and one check **retracted a correction this file
had already been given**. Detail and citations in
`an internal note` §4
and `an internal note` §3:

1. **2BGA check matrices** — written as `$H_X = [L(a) | L(b)]$, $H_Z = [R(b) | R(a)]$`.
   Correct (arXiv:2306.16400 §IV.1, Eq. 16): $A = \mathrm{L}(a)$, $B = \mathrm{R}(b)$,
   $H_X = (A | B)$, $H_Z^{\,T} = [B; -A]$. The written form is recovered only in the
   abelian case, where $\mathrm{L} = \mathrm{R}$.
2. **~~Hypergraph product qubit count~~ — RETRACTED (2026-10-05).** An earlier
   dated block in this file (and correction C2 of the verification note) asserted
   that the `n = n₁m₂ + n₂m₁` entry below was wrong. **It is correct.**
   Tillich–Zémor (arXiv:0903.0566 §3) give the product hypergraph
   $|\mathcal{E}| = |\mathcal{V}_1||\mathcal{E}_2| + |\mathcal{V}_2||\mathcal{E}_1| = m_1n_2 + n_1m_2$,
   which is the entry as written; $m_i = n_i$ reduces it to $2n_1n_2$. The earlier
   claim wrongly generalised the square-case figure. The entry stands unchanged.
3. **Balanced product attribution** — written as *"introduced by Lin & Pryadko
   (2023)"*. It is Breuckmann & Eberhardt, IEEE TIT 67, 6653 (2021), arXiv:2012.09271
   (reference [4] of arXiv:2306.16400).
4. **Panteleev–Kalachev GB page** — written as *Quantum 5, 405 (2021)*; the correct
   citation is Quantum **5**, 585 (2021), arXiv:1904.02703 (reference [21] of the
   same paper).
5. **2BGA journal page** — written as *Phys. Rev. A* **109**, 022402; `refs.bib` gives
   **109**(2), **022407** (2024). arXiv:2306.16400 is correct.
6. **Provenance gaps against the challenge's own `refs.bib`,** which declares itself
   the single source of truth: neither GALA (arXiv:2608.07431) nor quantum Tanner
   codes has an entry, so those two families are cited without a bibliography
   record. Conversely `refs.bib` carries nine construction families with no row
   here (mitten codes, coset-based 2BGA, tile codes, planar nearest-neighbour,
   vine codes, self-dual bivariate bicycle, ZSZ-LP balanced products, high-girth
   affine-coset, and Kasai's orthogonality-barrier work). Details in
   `an internal note` §6.

## Composition techniques (codes formed by composing codes)

**1. Hypergraph product (HGP)** — ~13 entries
Take two classical codes with parity checks `H₁` (m₁×n₁) and `H₂` (m₂×n₂). The CSS checks are Kronecker products: X-checks `[I⊗H₂ ; H₁ᵀ⊗I]`, Z-checks `[H₂ᵀ⊗I ; I⊗H₁]`, giving n = n₁m₂ + n₂m₁ qubits. E.g. `codes/51-12-3.json` = HGP of `ham7` and `sham6`.
*Ref: Tillich & Zémor, "Quantum LDPC codes with positive rate and minimum distance proportional to √n", IEEE ISIT 2009 (arXiv:0903.0566 — the ID the board cites).*

**2. Lifted product** — ~60 entries
Generalizes the HGP: base matrices have entries in a group algebra `F₂[G]` (each entry is a permutation-like "lift"), and the Kronecker products are replaced by group-ring products. The **normal-subgroup lifted product** variant (e.g. `codes/288-24-18.json` over `Z₁₂×Z₁₂`, citing arXiv:2608.08996) builds the lift from a chain of normal subgroups.
*Ref: Panteleev & Kalachev, "Degenerate quantum LDPC codes with good finite length performance", Quantum 5, 405 (2021); asymptotic version in STOC 2022 (arXiv:2111.03654).*

**3. Balanced product** — ~3 entries
Like the lifted product but the two factors are tied by a group action acting on both, and redundant tensor copies are quotiented out, so n grows once per composition instead of twice. Board example: over `Z₃ ⋊ Z₄` (`codes/60-12-6.json`).
*Ref: introduced by Lin & Pryadko (2023); the board's entries cite arXiv:2607.27644.*

**4. Two-block group-algebra (2BGA)** — ~414 entries
`H_X = [L(a) | L(b)]`, `H_Z = [R(b) | R(a)]` where `L(·)`, `R(·)` are the left/right regular representations of a group algebra — i.e. a two-block lifted product over `G`. Covers abelian groups (`Z_m×Z_n`) and nonabelian ones (dihedral, dicyclic, metacyclic, `PSL(2,7)`, `SmallGroup(n,k)`).
*Ref: Lin & Pryadko, "Quantum two-block group algebra codes", Phys. Rev. A 109, 022407 (2024), arXiv:2306.16400. Coset-based generalization: Aydin, Tamo & Barg, "Breaking the bicycle frame: Coset-based quantum LDPC codes" (arXiv:2606.17268, in `refs.bib`).*

**5. Generalized bicycle (GB)** — ~536 entries by `family` tag
The abelian special case of 2BGA/lifted product: over `F₂[x]/(x^N−1)`, `H_X = [circ(a) | circ(b)]`, `H_Z = [Bᵀ | Aᵀ]`.
*Ref: introduced in Panteleev & Kalachev (Quantum 5, 405, 2021); distance bounds in Wang & Pryadko, "Distance bounds for generalized bicycle codes" (2022). The board's GB database entries cite arXiv:2306.16400 / the QEC-pages GB-codes repo.*

**6. Bivariate bicycle (BB)** — ~194 entries
GB over the two-variable group algebra `F₂[Z_l×Z_m]`: `H_X = [A | B]`, `H_Z = [Bᵀ | Aᵀ]` with bivariate `A, B` (the IBM [[144,12,12]] family). Includes **coprime** variants (non-dividing lattice sizes) and **open-boundary planar** versions with annulus-type boundary engines.
*Ref: Bravyi, Cross, Gambetta, Maslov, Rall, Yoder, "High-threshold and low-overhead fault-tolerant quantum memory", Nature 627, 378 (2024), arXiv:2308.07915; planar/open-boundary: Liang, Eberhardt & Chen, arXiv:2504.08887; twisted-torus variant: Liang, Liu, Song, Chen, PRX Quantum 6, 020357 (2025).*

**7. Multivariate bicycle** — 2 entries
BB generalized to ≥3 variables (e.g. trivariate over `Z₇×Z₆`); the third variable is dependent (`z = x·y`), so it reduces to a periodic BB code.
*Ref: Voss, Sim, Haug, Bharti, arXiv:2406.19151 (SM Table 2). The "quadricycle" entries (`codes/700-2-25.json`) extend GB to a rank-4 abelian torus.*

**8. Pair-partition CPM** — ~14 entries
Copy-machine product: small circulant blocks `C(e_jl)` are composed via a pair-partition array `M` with paired-difference CSS orthogonality — `H_X = (C(e_jl))`, `H_Z = (C(d_jl))` — a lifted-product-like composition with prime lift size p and controlled girth.
*Ref: Okada & Kasai, arXiv:2607.14091 (with reference implementation `kasaikenta/pair-partition-cpm-css-codes`).*

**Note (2026-09-29).** The construction's own catalogue (arXiv:2607.14091v4,
§VI) now certifies **36 exact-distance codes** (seven girth-8, distances to 24,
rates to 0.574) plus contributor-reported instances; the board count above
tracks the challenge dataset, not the catalogue. Only the independently
certified distances are certificate-grade by the paper's own accounting —
daggered contributor-reported distances (e.g. the (5,10) zero-design-rate
rows) are not. v4 also adds an APM-PP variant pairing equal relative affine
maps (see `PRIOR_ART.md` §1).

**9. Quantum Tanner codes** — ~5 entries
Compose local codes on the vertices of a left/right Cayley graph of a group: each vertex gets a copy of a small classical code, and X/Z checks are the products across the two bipartition classes.
*Ref: Leverrier & Zémor (2022) construction — what the board entries cite; foundational: Tillich & Zémor, "Quantum Tanner codes" (2014); asymptotically good version in Panteleev & Kalachev, STOC 2022.*

**10. GALA (group-action lift with active orthogonality)** — 5 entries
Two-block quasi-cyclic construction over `F₂[Z_4 × C_17]`-type group algebras where a group action enforces the orthogonality condition actively rather than by support choice.
*Ref: arXiv:2608.07431 (Table S5 instances).*

**11. Cornucopia codes** — 2 entries
Compose many blocks at once: 12 data blocks (6 L, 6 R) + 6 check blocks (3 X, 3 Z), each a small grid, stitched by block convolution `H_X = [A | B]`, `H_Z = [B̃ | Ã]`.
*Ref: Lu, Li & Deng, arXiv:2608.02773.*

**12. Multi-band dense-packed surface codes** — ~121 entries
Compose many surface-code patches ("bands") on a shared plane at raised pitch — a geometric composition of topological codes rather than an algebraic product.
*Ref: generalization of Fujiu et al., arXiv:2511.06758.*

**13. Tile codes** — 11 entries
Compose plaquette "tiles" (each a small stabilizer pattern) on a shared lattice to trade rate against distance.
*Ref: Steffan, Choe & Breuckmann, "Tile Codes: High-Efficiency Quantum Codes on a Lattice with Boundaries" (in `refs.bib`).*

**14. Concatenation** — 6 entries (added 2026-10-25, after the snapshot date above)
Replace each coordinate of an outer code by an encoded block of an inner code: the child carries the inner checks on every block plus each outer check lifted through chosen inner logical representatives, so `n = n_in * n_out` and `k = k_in * k_out`. The board carries two flavors:
- **Non-CSS inner — 3 entries, 2026-10-14:** `codes/512-54-24.json` (#3405), `codes/576-42-24.json` (#3407), `codes/672-28-30.json` (#3408): CSS outer `[[64,18,8]]` / `[[72,14,8]]` / `[[84,14,10]]` with non-CSS stabilizer inner `[[8,3,3]]` / `[[8,2,3]]` — the inner input is not a CSS code although the composite is.
- **CSS inner and outer — 3 entries, 2026-10-25:** `codes/196-100-4.json` (#4145), `codes/324-196-4.json` (#4146), `codes/400-256-4.json` (#4147): H-code inner `[[k+4,k,2]]` tree-concatenated with a sparse CSS outer chosen to keep the lifted check weight small (`196-100-4` lifts weight-8 outer checks through weight-3 inner logical representatives to max check weight 24).

*Refs:* the "concatenate … then unconcatenate" reading of Chakraborty & Albert, "Stabilizer codes over general phase spaces" (arXiv:2610.04694), and Appendix B of Sullivan, Amaro & Perlin, "Injection is all you need: parallel universal logic in high-rate concatenated self-dual codes" (arXiv:2610.30087) — neither has a `refs.bib` record, extending the provenance-gap observation above. The challenge's own `fieldnotes/2026-10-13-concatenating-onto-the-non-css-board.md` records what the first paper does and does not give a qubit board. Calculus counterpart: `A-CONCAT` (`spec/TAXONOMY.md` §2.14), `taxonomy-only`.

*Counting note:* the six entries whose `provenance.construction` states concatenation (grep for `concat` in `codes/`, challenge commit `6e1e41be3`). `codes/12-2-4-b.json` applies a CSS outer code to inner block logicals without using the word and is not counted; `codes/12-4-2-c.json`'s inter-block check products are a weaker block composition and are counted nowhere here.

Not compositions, for completeness: the topological baselines (toric/colour/hyperbolic), the SAT-discovered codes, the qecdb imports, and the Steane/Hamming/Reed–Muller self-orthogonal CSS codes (a classical code used directly, not composed with another).

## Deformation techniques

**1. Check deletion** — ~20 entries
Delete independent stabilizer rows (X and/or Z), keeping the qubit set fixed. Commutation is preserved (rows only removed), k increases by exact GF(2) rank arithmetic, and the cited theorem gives conditions under which the source's logical witnesses remain valid logicals of the child code. Used both as single moves and **greedy chains** (`700-206-28 → 700-212-28 → 700-222-28`).
*Ref: the board cites the check-deletion theorem, `github.com/MathysRennela/dem-linter` @ `1ef09d73`, CLAIMS.md claim 12.1.*

**2. Restricted r=1 lattice grafting** — the main move in ~51 reduction entries
Remove a qubit that lies in exactly one stabilizer of a given type, together with that stabilizer. CSS commutation is preserved automatically because no other same-type row touches that qubit; n decreases by 1 at unchanged k.
*Ref: Liang, Eberhardt & Chen, arXiv:2504.08887, Sec. III E.*
**(2026-10-05)** Verified against v4 (HTML): the cited move is §III.5 (*Lattice grafting*), the $r=1$ regime; v4's reorganization renumbered the lettered subsections, so "Sec. III E" is the v1/v2 pointer. Step 3 of the paper's algorithm checks distance and undoes the graft if it drops — per-instance verification, not preservation.

**3. Row-space grafting** — a few entries (`632-51-4`, `651-51-4`, `922-18-31`)
Replace one generator by a low-weight element `S` of the stabilizer *row space* (a subset sum of generators), then graft a qubit in its support. Unlike r=1 grafting this is **not distance-preserving in general** — `fieldnotes/2026-09-20-screening-traps-at-n-900.md` documents a chain where Z-distance dropped 5→4→3.
*Ref: internal move, documented in `an internal note`; no external paper.*

**4. Puncturing** — 2 entries
Delete qubits outright (columns), the classical dual of shortening.
*Ref: standard; e.g. Roffe et al., "Decoding across the quantum LDPC code landscape" (in `refs.bib`) for the general CSS move set.*

## Why I didn't mention "two-row check deletion"

Because on this board it isn't a separate technique — it's check deletion with a count. The move is defined by *deleting independent stabilizer rows*; some entries happen to delete exactly two per side (`codes/576-295-12.json`: X-rows [50, 54] and Z-rows [87, 112]; also `codes/574-254-14.json` and `codes/672-340-7.json`), but the construction string, the theorem cited, and the k-arithmetic are identical to the one-row and ten-row cases. I also searched the repo: "two-row check deletion" appears nowhere in `codes/`, `an internal note`, or `fieldnotes/` — the only "two row" hits are the unrelated phrase "the same two row spaces" in distance-certificate prose. If you've seen the term in a specific paper as a named move (e.g. a two-row deletion with a distance-preservation guarantee that single-row deletion lacks), it isn't used on the board under that name — tell me the source and I'll check whether those entries match it.

## Secondary evaluation metrics (candidate, 2026-11-12)

Operator-theory leads triaged in
`an internal note`.
Two are adopted as *reported scores*, not as properties or construction
techniques (the property inventory and the calculus are unchanged):

- **Covariance defect under a declared symmetry.** When a submission declares
  a symmetry `G`, report how far the code's encoder/decoder deviate from
  `G`-covariance (isotypic decomposition of the protected sector). Aids
  symmetry-reduced search; never a property or a cell.
- **Surplus over a random-code baseline.** Compare the submission against a
  random-subspace null model of the same `n, k` (free-probability predicted
  approximate Knill–Laflamme behaviour) and report the surplus. Baseline
  comparison only; does not alter distance or weight claims.

Both are consumer-side / leaderboard reporting quantities. They are not
validated by the calculus, do not enter the property inventory, and do not
create new obligations. Other leads (commutant dimension, SDP recovery
optimum, spectral gap, OTOC localization, transfer-operator gap, Petz
recoverability, algebraic-code dimension) remain deferred pending a scope
decision; see the triage note.
