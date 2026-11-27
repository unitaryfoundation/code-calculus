# Leaderboard Taxonomy

**What kinds of code constructions and deformations appear on the qLDPC challenge leaderboard?**

- **Source:** [Unitary Foundation qLDPC challenge](https://unitaryfoundation.github.io/qldpc-challenge/)
- **Snapshot date:** 2026-11-19 (the board changes daily; counts below are approximate)
- **How to read this page:** a *composition* builds a new code out of smaller codes; a *deformation* changes an existing code (usually to make it smaller or simpler). Counts are approximate numbers of board entries whose provenance names that technique.

This page is a human-readable survey of the code constructions and
deformations appearing on the leaderboard. It is not normative for the
calculus; where it and [`spec/`](../spec/) disagree, `spec/` wins.

---

## Composition techniques (building a code from smaller codes)

### 1. Hypergraph product (HGP) — ~13 entries
Take two classical codes with parity-check matrices $H_1$ ($m_1 \times n_1$) and $H_2$ ($m_2 \times n_2$). The CSS checks are Kronecker products: X-checks $[I \otimes H_2;\; H_1^{\mathsf T} \otimes I]$, Z-checks $[H_2^{\mathsf T} \otimes I;\; I \otimes H_1]$, giving $n = n_1 m_2 + n_2 m_1$ qubits. Example: `codes/51-12-3.json` is the HGP of `ham7` and `sham6`.

*Reference:* Tillich & Zémor, "Quantum LDPC codes with positive rate and minimum distance proportional to $\sqrt n$", IEEE ISIT 2009 (arXiv:0903.0566 — the ID the board cites).

### 2. Lifted product — ~60 entries
Generalises the HGP: base matrices have entries in a group algebra $\mathbb F_2[G]$ (each entry is a permutation-like "lift"), and the Kronecker products become group-ring products. The **normal-subgroup lifted product** variant (e.g. `codes/288-24-18.json` over $\mathbb Z_{12} \times \mathbb Z_{12}$, citing arXiv:2608.08996) builds the lift from a chain of normal subgroups.

*Reference:* Panteleev & Kalachev, "Degenerate quantum LDPC codes with good finite length performance", Quantum **5**, 585 (2021); asymptotic version STOC 2022 (arXiv:2111.03654).

### 3. Balanced product — ~3 entries
Like the lifted product, but the two factors are tied by a group action on both, and redundant tensor copies are quotiented out, so $n$ grows once per composition instead of twice. Board example: over $\mathbb Z_3 \rtimes \mathbb Z_4$ (`codes/60-12-6.json`).

*Reference:* Breuckmann & Eberhardt, IEEE TIT 67, 6653 (2021), arXiv:2012.09271; the board's entries cite arXiv:2607.27644.

### 4. Two-block group-algebra (2BGA) — ~414 entries
In the abelian case, $H_X = [L(a) \mid L(b)]$ and $H_Z = [R(b) \mid R(a)]$, where $L(\cdot)$ and $R(\cdot)$ are the left and right regular representations of a group algebra (a two-block lifted product over $G$). In the general nonabelian case, $A = \mathrm{L}(a)$, $B = \mathrm{R}(b)$, $H_X = (A \mid B)$, and $H_Z^{\mathsf{T}} = [B; -A]$. Covers abelian groups ($\mathbb Z_m \times \mathbb Z_n$) and nonabelian ones (dihedral, dicyclic, metacyclic, $\mathrm{PSL}(2,7)$, $\mathrm{SmallGroup}(n,k)$). The **coset-based** generalisation (Aydin, Tamo & Barg, arXiv:2606.17268) builds the two blocks from cosets of a non-normal subgroup.

*Reference:* Lin & Pryadko, "Quantum two-block group algebra codes", *Phys. Rev. A* **109**(2), 022407 (2024), arXiv:2306.16400. Coset generalisation: arXiv:2606.17268 (in `refs.bib`).

### 5. Generalized bicycle (GB) — ~536 entries by `family` tag
The abelian special case of 2BGA/lifted product: over $\mathbb F_2[x]/(x^N-1)$, $H_X = [\mathrm{circ}(a) \mid \mathrm{circ}(b)]$, $H_Z = [B^{\mathsf T} \mid A^{\mathsf T}]$.

*Reference:* introduced in Panteleev & Kalachev (Quantum **5**, 585, 2021); distance bounds in Wang & Pryadko, "Distance bounds for generalized bicycle codes" (2022). Board entries cite arXiv:2306.16400 / the QEC-pages GB-codes repository.

### 6. Bivariate bicycle (BB) — ~194 entries
GB over the two-variable group algebra $\mathbb F_2[\mathbb Z_l \times \mathbb Z_m]$: $H_X = [A \mid B]$, $H_Z = [B^{\mathsf T} \mid A^{\mathsf T}]$ with bivariate $A, B$ (the IBM [[144,12,12]] family). Includes **coprime** variants (non-dividing lattice sizes) and **open-boundary planar** versions with annulus-type boundary engines.

*Reference:* Bravyi, Cross, Gambetta, Maslov, Rall, Yoder, "High-threshold and low-overhead fault-tolerant quantum memory", Nature **627**, 378 (2024), arXiv:2308.07915; planar/open-boundary: Liang, Eberhardt & Chen, arXiv:2504.08887; twisted-torus variant: Liang, Liu, Song, Chen, PRX Quantum **6**, 020357 (2025).

### 7. Multivariate bicycle — 2 entries
BB generalised to $\ge 3$ variables (e.g. trivariate over $\mathbb Z_7 \times \mathbb Z_6$); the third variable is dependent ($z = x \cdot y$), so it reduces to a periodic BB code.

*Reference:* Voss, Sim, Haug, Bharti, arXiv:2406.19151 (SM Table 2). The "quadricycle" entries (`codes/700-2-25.json`) extend GB to a rank-4 abelian torus.

### 8. Pair-partition CPM — ~14 entries
Copy-machine product: small circulant blocks $C(e_{jl})$ are composed via a pair-partition array $M$ with paired-difference CSS orthogonality — $H_X = (C(e_{jl}))$, $H_Z = (C(d_{jl}))$ — a lifted-product-like composition with prime lift size $p$ and controlled girth.

*Reference:* Okada & Kasai, arXiv:2607.14091v4 (with reference implementation `kasaikenta/pair-partition-cpm-css-codes`). The construction's own catalogue (§VI) certifies 36 exact-distance codes (including seven girth-8 codes, distances up to 24, rates up to 0.574) and adds an APM-PP variant pairing equal relative affine maps ([`PRIOR_ART.md`](PRIOR_ART.md) §1).

### 9. Quantum Tanner codes — ~5 entries
Compose local codes on the vertices of a left/right Cayley graph of a group: each vertex gets a copy of a small classical code, and X/Z checks are the products across the two bipartition classes.

*Reference:* Leverrier & Zémor (2022) construction — what the board entries cite; foundational: Tillich & Zémor, "Quantum Tanner codes" (2014); asymptotically good version in Panteleev & Kalachev, STOC 2022.

### 10. GALA (group-action lift with active orthogonality) — 5 entries
Two-block quasi-cyclic construction over $\mathbb F_2[\mathbb Z_4 \times C_{17}]$-type group algebras where a group action enforces the orthogonality condition actively rather than by support choice.

*Reference:* arXiv:2608.07431 (Table S5 instances).

### 11. Cornucopia codes — 2 entries
Compose many blocks at once: 12 data blocks (6 L, 6 R) + 6 check blocks (3 X, 3 Z), each a small grid, stitched by block convolution $H_X = [A \mid B]$, $H_Z = [\tilde B \mid \tilde A]$.

*Reference:* Lu, Li & Deng, arXiv:2608.02773.

### 12. Multi-band dense-packed surface codes — ~121 entries
Compose many surface-code patches ("bands") on a shared plane at raised pitch — a geometric composition of topological codes rather than an algebraic product.

*Reference:* generalisation of Fujiu et al., arXiv:2511.06758.

### 13. Tile codes — 11 entries
Compose plaquette "tiles" (each a small stabilizer pattern) on a shared lattice to trade rate against distance.

*Reference:* Steffan, Choe & Breuckmann, "Tile Codes: High-Efficiency Quantum Codes on a Lattice with Boundaries" (in `refs.bib`).

### 14. Concatenation — 6 entries
Replace each coordinate of an outer code by an encoded block of an inner code: the child carries the inner checks on every block plus each outer check lifted through chosen inner logical representatives, so $n = n_{\mathrm{in}} \cdot n_{\mathrm{out}}$ and $k = k_{\mathrm{in}} \cdot k_{\mathrm{out}}$. Two flavours on the board:
- **Non-CSS inner — 3 entries:** `codes/512-54-24.json` (#3405), `codes/576-42-24.json` (#3407), `codes/672-28-30.json` (#3408): CSS outer `[[64,18,8]]` / `[[72,14,8]]` / `[[84,14,10]]` with non-CSS stabilizer inner `[[8,3,3]]` / `[[8,2,3]]` — neither the inner input nor the composite is a CSS code. Each composite is filed as a non-CSS stabilizer code whose stabilizer group is not generated by its X-type and Z-type elements (corrected 2026-11-24; non-CSS / symplectic inner inputs for `A-CONCAT` refused 2026-11-25).
- **CSS inner and outer — 3 entries:** `codes/196-100-4.json` (#4145), `codes/324-196-4.json` (#4146), `codes/400-256-4.json` (#4147): H-code inner `[[k+4,k,2]]` tree-concatenated with a sparse CSS outer chosen to keep the lifted check weight small (`196-100-4` lifts weight-8 outer checks through weight-3 inner logical representatives to max check weight 24).

*References:* Chakraborty & Albert, "Stabilizer codes over general phase spaces" (arXiv:2610.04694), and Appendix B of Sullivan, Amaro & Perlin, "Injection is all you need: parallel universal logic in high-rate concatenated self-dual codes" (arXiv:2610.30087). Calculus counterpart: `A-CONCAT` ([`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §2.14).

### 15. Distance amplification — ~65 entries
One or more tensor-product amplification steps (central three-term truncation of the chain-complex tensor product) applied to an existing code, trading $n$ for distance. The child keeps the base logicals tensored with a small inner code (typically `[[4,2,2]]`).

*Reference:* arXiv:2609.37231 (Eq. 1 / Eq. 12–15).

### 16. Coset-based 2BGA — ~70 entries
A variant of technique 4 where the two blocks are built from cosets of a (possibly non-normal) subgroup $H \le G$, giving codes $Q_G^H(a,b)$ with different rate/distance tradeoffs from the normal-subgroup case.

*Reference:* Aydin, Tamo & Barg, "Breaking the bicycle frame: Coset-based quantum LDPC codes" (arXiv:2606.17268, in `refs.bib`).

### 17. One-block cyclic stabilizer codes — ~100 entries
A single cyclic generator $X^a Z^b$ and its shifts; the code is determined by one polynomial pair $(a(x), b(x))$ with $a b^* + b a^* = 0$.

*Reference:* standard cyclic stabilizer construction (see the challenge entries' provenance for the specific polynomial pairs).

### 18. SAT-discovered local CSS codes — ~30 entries
Codes found by SAT search on a grid, with each check anchored at a site and acting within a bounded radius. Distance is a witness-backed upper bound.

*Reference:* challenge `research/local_sat.py` (CaDiCaL-backed); see the entries' provenance for grid size, radius, and model index.

### 19. Armillary dynamic codes — ~7 entries
Dynamic codes built from CXSWAP rounds over groups/channels/stations, with retained X/Z sectors and girth-6 Tanner graphs.

*Reference:* arXiv:2611.20410.

### 20. Symplectic halving — ~19 entries
A fold of a (possibly non-CSS) parent code by a fixed-point-free involution, producing a code that is not CSS under any local Clifford but has halved parameters.

*Reference:* arXiv:2609.30069 (the halving map $\pi$).

### 21. Mitten, affine, and algebraic constructions — small families
Lifted products over nonabelian groups with mitten structure (arXiv:2607.28795), affine-Frobenius constructions (arXiv:2609.x), ZSZ-LP balanced products, high-girth affine-coset codes, and Kasai's orthogonality-barrier work. These are recorded in the challenge's `refs.bib` and appear in small numbers on the board.

*Reference:* see the respective arXiv preprints cited in the entries' provenance.

Not compositions, for completeness: the topological baselines (toric/colour/hyperbolic), the SAT-discovered codes, the qecdb imports, and the Steane/Hamming/Reed–Muller self-orthogonal CSS codes (a classical code used directly, not composed with another).

---

## Deformation techniques (changing an existing code)

### 1. Check deletion — ~84 entries (by `family` tag; ~258 provenance hits)
Delete independent stabilizer rows (X and/or Z), keeping the qubit set fixed. Commutation is preserved (rows only removed), $k$ increases by exact GF(2) rank arithmetic, and the cited theorem gives conditions under which the source's logical witnesses remain valid logicals of the child code. Used both as single moves and **greedy chains** (`700-206-28 → 700-212-28 → 700-222-28`).

*Reference:* the check-deletion theorem. Calculus counterpart: `C-DELETE-CHECK` ([`spec/TAXONOMY.md`](../spec/TAXONOMY.md)).

### 2. Restricted r=1 lattice grafting — the main move in ~51 reduction entries
Remove a qubit that lies in exactly one stabilizer of a given type, together with that stabilizer. CSS commutation is preserved automatically because no other same-type row touches that qubit; $n$ decreases by 1 at unchanged $k$.

*Reference:* Liang, Eberhardt & Chen, arXiv:2504.08887, Sec. III.5 (*Lattice grafting*), the $r=1$ regime. Step 3 of the paper's algorithm checks distance and undoes the graft if it drops — per-instance verification, not automatic preservation.

### 3. Row-space grafting — a few entries (`632-51-4`, `651-51-4`, `922-18-31`)
Replace one generator by a low-weight element $S$ of the stabilizer *row space* (a subset sum of generators), then graft a qubit in its support. Unlike $r=1$ grafting, this is **not distance-preserving in general**: a chain of such moves has Z-distance $5 \to 4 \to 3$.

*Reference:* no external paper identified. Calculus counterpart: `E-PEEL` / `E-PUNCTURE` ([`spec/TAXONOMY.md`](../spec/TAXONOMY.md)).

### 4. Puncturing — 2 entries
Delete qubits outright (columns), the classical dual of shortening.

*Reference:* standard; e.g. Roffe et al., "Decoding across the quantum LDPC code landscape" for the general CSS move set. Calculus counterpart: `E-PUNCTURE` ([`spec/TAXONOMY.md`](../spec/TAXONOMY.md)).

### 5. Priced-calculus peeling (E-PEEL) — a growing family
Delete a qubit together with its unique stabilizer of one type and relabel surviving qubits, as a priced construction judgment. Used both as single moves and in chains; distance claims are consumer-checked against the priced rule, not proved.

*Reference:* code-calculus consumer ([`machine/priced_calculus.py`](../machine/priced_calculus.py)).

---

## Why there is no separate "two-row check deletion"

On this board, a two-row deletion is not a separate technique but an instance of check deletion with a particular count. The move is defined by *deleting independent stabilizer rows*; some entries happen to delete exactly two per side (`codes/576-295-12.json`: X-rows [50, 54] and Z-rows [87, 112]; also `codes/574-254-14.json` and `codes/672-340-7.json`). The construction string, cited theorem, and $k$-arithmetic match the one-row and ten-row cases. The board data does not identify a distinct move named "two-row check deletion"; a paper-specific source would be needed to assess any stronger distance guarantee.

---

## Secondary evaluation metrics (candidate)

The following operator-theory quantities are adopted as *reported scores*, not as properties or construction techniques (the property inventory and calculus are unchanged):

- **Covariance defect under a declared symmetry.** When a submission declares a symmetry $G$, report how far the code's encoder/decoder deviate from $G$-covariance (isotypic decomposition of the protected sector). Aids symmetry-reduced search; never a property or a cell.
- **Surplus over a random-code baseline.** Compare the submission against a random-subspace null model of the same $n, k$ (free-probability predicted approximate Knill–Laflamme behaviour) and report the surplus. Baseline comparison only; does not alter distance or weight claims.
Both are consumer-side / leaderboard reporting quantities. They are not validated by the calculus, do not enter the property inventory, and do not create new obligations. Other leads (commutant dimension, SDP recovery optimum, spectral gap, OTOC localization, transfer-operator gap, Petz recoverability, algebraic-code dimension) remain deferred pending a scope decision.

---

## Challenge family tags (as of 2026-11-19)

The challenge records a `family` tag in each code's JSON. Tags are coarse and some entries are untagged; they do not line up exactly with the techniques above, but they give a current picture of the board.

| `family` tag | Entries | Notes |
| --- | ---: | --- |
| `generalized-bicycle` | 1030 | includes cyclic and designed-divisor variants |
| *(untagged)* | 679 | mostly imports and older entries |
| `other` | 576 | mixed / not yet categorised |
| `bivariate-bicycle` | 445 | includes coprime and open-boundary planar |
| `topological` | 190 | toric / colour / hyperbolic baselines |
| `lifted-product` | 121 | includes normal-subgroup variants |
| `local-2d-single` | 101 | single-layer local layouts |
| `pair-partition-cpm` | 93 | CPM / GPM variants |
| `check-deletion` | 84 | deformation family |
| `2bga-coset` | 71 | coset-based 2BGA |
| `2bga-nonabelian` | 66 | nonabelian 2BGA |
| `distance-amplified` | 65 | tensor-product amplification |
| `tile` | 58 | plaquette tiles |
| `hypergraph-product` | 43 | HGP |
| `local-sat-css` | 29 | SAT-discovered local codes |
| `balanced-product` | 14 | |
| `quantum-tanner` | 9 | |
| `multivariate-bicycle` | 2 | |

Total board entries at this snapshot: 3676.
