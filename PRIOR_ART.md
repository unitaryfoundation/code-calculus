# Prior Art

**Role:** public design note. It constrains what the project may claim
as novel; it does not state the calculus. Where it touches the specification, that
is `spec/`, which wins.

**Status:** review input. Constrains the proposal's novelty claims and citation
obligations; does not define the calculus's scope, semantics, or proof
obligations.

Citations are tagged **[V]** (verified against the arXiv API or, for repositories,
against the repository itself) or **[C]** (from knowledge —
check before use); the ledger is at the end. Verdicts are per-claim: a work can defeat one
sentence of the proposal and be irrelevant to the rest.

---

# 1. Algebraic code constructions

The families that fix a construction *style*.

| Work | Contribution | Tag |
| --- | --- | --- |
| Tillich–Zémor, *Quantum LDPC codes with positive rate and minimum distance proportional to $n^{1/2}$*, IEEE TIT 60(2), 2014 | Hypergraph product; first positive-rate family above $\sqrt{n}$ | [V] |
| Bravyi–Hastings, *Homological Product Codes*, STOC 2014 | Homological product; good codes, low-weight stabilizers | [V] |
| Panteleev–Kalachev, *Quantum LDPC codes with almost linear minimum distance*, IEEE TIT 68(1), 2022 | Balanced product | [C] |
| Golowich–Guruswami, *…Almost Linear Distance via Homological Products*, 2024 | When products preserve distance | [V] |
| Evra–Kaufman–Zémor, *Decodable quantum LDPC codes beyond the $\sqrt{n}$ distance barrier…*, 2020 | High-dimensional expanders | [V] |
| Leverrier–Tillich–Zémor, *Quantum Expander Codes*, FOCS 2015 | Linear-time decoding | [V] |
| Bravyi–Cross–Gambetta–Maslov–Rall–Yoder, *High-threshold and low-overhead fault-tolerant quantum memory*, Nature 2024 | Bivariate bicycle codes | [C] |
| Menon et al., *Magic tricycles…*, PRX 16, 021014, 2026 | Tricycle codes | [V] |
| Wu–Li–Li–Zhai, *General Construction of QECCs from Multiple Classical Codes*, 2025 | $D$-input hypergraph-product generalization | [V] |
| Hong, *Quantum LDPC codes with design rate 1/5…*, 2026 | Finite-length balanced-product instances | [V] |
| Okada–Kasai, *Pair-Partition Constructions for CPM-Based Quantum LDPC Codes*, arXiv 2607.14091, 2026 (v4 read 2026-09-29) | CPM pair-partition CSS construction: paired-difference orthogonality over circulant-permutation lifts; v4 adds the APM-PP extension (pairing equal relative affine maps), the Kasai-construction specialization via selected block rows, a complete distance lower-bound algorithm with cyclic root reduction, the factorial distance upper bound $d \le (J+1)!$, and 36 exact-distance codes | [V] |
| Lee, *Logical spectroscopy: lifted-product codes with addressable bases*, arXiv 2607.05386, 2026 | Packet-decomposed canonical logical bases for lifted-product codes; the method behind the 19 Lee-contributed CPM-PP instances in 2607.14091v4 and the basis constructions in 2609.30069 §VII | [C] |
| Lee–Okada–Maskara–Kasai–Zhou, *Design Principles for Ultra-High-Rate Quantum Codes*, arXiv 2609.30069, 2026 | Template/degree/lift design coordinates; pair-partition template at the finite-size parameter Pareto frontier; **symplectic halving** of CSS parents with a fixed-point-free ZX duality to compact non-CSS codes; symmetry-informed low-weight canonical logical bases; subsumes arXiv 2607.14091 | [V] |
| Audoux–Couvreur, *On tensor products of CSS codes*, Ann. Inst. Henri Poincaré D 6(2), 239–287, 2019 | CSS tensor product via central truncation of the total chain complex; the logical-overlap criterion that fixes distance-multiplication factors. The construction underlying arXiv 2609.37231 below. arXiv:1512.07081, *On tensor products of CSS Codes* (title/authors/abstract verified 2026-10-04) | [V] |
| Liang–Gu–Chen–Eisert–Wang, *Ultra-high-distance quantum memories from amplified qLDPC codes*, arXiv 2609.37231, 2026 | "Distance amplifiers": recursive CSS tensor-product construction (`𝒬 ⊗ 𝒜`, central truncation) with a **circuit-level** layer — staged-joint syndrome-extraction schedule, fault-response certificates, and rigorous circuit-distance multiplication. Three amplifier families (flagged `[[4,2,2]]`, canonical HGP, rotated surface) | [V] |
| Liang–Eberhardt–Chen, *Planar quantum low-density parity-check codes with open boundaries*, arXiv 2504.08887, 2025 (v4) | Boundary anyon condensation plus "lattice grafting"; weight-1 stabilizer cleanup — **verified in the paper (v4 HTML read 2026-10-05, T11 discharged): §III.4 step 4, "Removing single-qubit stabilizers", removes boundary/corner stabilizers acting on one qubit, disentangling it and reducing $n$; the v4 structure reorganization renumbered the externally cited "§III D" to §III.4** — and the restricted $r=1$ lattice-grafting regime (§III.5, remove a qubit participating in exactly one $O$-stabilizer together with that stabilizer; step 3 *checks* distance and undoes, so distance is verified per instance, not guaranteed). The $\lvert S\rvert = 1$ regime of row-space grafting (`E-GRAFT`) is the row-space form of that cleanup | [V] |
| Yuan, *One-Shot any Code*, arXiv 2610.02137, 2026 (v1 HTML read 2026-10-05) | Any `[[n,k]]` CSS QLDPC → `[[nm,k]]` CSS QLDPC single-shot with efficient local decoder; $m$-sheet hollowed-tensor level map (Def. 111: $Y^u = K^u\otimes V + G^u\otimes R$, repetition code $R$) glued into the level map $\bar\Gamma$ (Def. 116, Eq. 249); **(T11 read applied 2026-10-05)** Def. 104 local cones $K^x,K^q,K^z$, Remark 39 seed local triviality ("it holds if the distance in the error sector exceeds the largest seed X-check weight"), Theorem 81 SS threshold, §I.2 admits only sublinear confinement. Lemma 118: $H_Q(\bar\Gamma) \cong H_Q(C)$ and $H_X, H_Z$ likewise; so $k' = k$ exactly and one tower level inflates $n$ far beyond $\times m$, hence not a frontier mover on $(n,k,d,w)$ — see the $\Phi$ analysis in `WP5_ALGEBRAIC_PRODUCT_SCOPING.md`. | [V] |
| Shalby–Bourassa–Karamlou–Martin–Morvan–Noll–Gidney–Pryadko, *Stitched surface codes: planar concatenation through GHZ corridors*, arXiv 2610.21357, 2026 (v1 HTML read 2026-10-16, **partial**: abstract, §I–§VI.1; §VI.2–VII and Appendices A–E not read) | Planar **concatenation instance**, not a new constructor: four distance-$t$ rotated surface-code patches under the $[[4,2,2]]$ outer code give $[[4t^2,2,2t]]$, $k=2$, $d=2t$, saturating the concatenation product bound (their §II.2, Eq. 1) — this instantiates `A-CONCAT` (`spec/TAXONOMY.md` §2.14) with its distance hypothesis attained, and is explicitly **without lattice surgery**: the four patches' data qubits are disjoint and the coupling rides on outer checks lifted as products of inner logicals, the GHZ corridors being measurement apparatus. The circuit layer is the residue worth recording: circuit distance $d_{\rm circ}=\min(2t,\,r_{\rm v}+3)$ (their §III.2, Eq. 8, an empirical expression) sits **below** the code distance unless $r_{\rm v}\ge 2t-3$, and single-pass MWPM decoding requires every corridor hyperedge mechanism to decompose graphlike (§IV) — an experimentally demonstrated (Willow, $d=4,6$) instance of the code/circuit distance gap driven by schedule data no code-level summary carries | [V] |
| Hsin, *Twisted Compactification, Quotient Quantum Codes and Logical Gates*, arXiv 2611.09538, 2026 (v1 HTML read 2026-11-09) | Unified construction: balanced-product, bivariate-bicycle, genon and five-qubit codes are **quotient codes** — a parent folded onto itself by identifying each check with its image under a deck transformation composed with a symmetry — and this is the lattice form of twisted compactification (theory on $X\times F$ with a symmetry background along $F$). Three construction classes: (i) **monomial quotient** (free monomial-Clifford action: qudit permutation + single-qudit Clifford) with a transfer theorem (logical qudits, logical operators and distance bounds from the parent; a Tate cohomology group counts the new logicals); (ii) **dressed quotient** for higher-form / cup-polynomial backgrounds — the twist is an entangling diagonal circuit, and when a finite cover trivializes the background the code is a dressed quotient, so abelian Pauli codes give non-abelian topological order such as $D(D_4)$ (dimension $2^2$, linear distance), with Clifford level at most one less than the twist degree; (iii) **twists as logical gates** (CCZ on $\mathbb{RP}^3$ from three toric codes on $S^3$; logical $T$ from a quarter-turn twist of the 3D fermionic toric code). Final limit: twisting abelian gauge theories reaches only quantum doubles $D(G)$ with $[G,G]$ central | [V] |

| Cross–Smith–Smolin–Zeng, *Codeword Stabilized Quantum Codes*, IEEE TIT 55(1), 433–438, 2009 (arXiv 0708.1021) | The CWS framework: a graph state $\lvert G\rangle$ plus a classical code supplies Pauli-$Z$ word operators, and a linear classical code gives a stabilizer code (Thm 5). The detection criterion is the classical-linear map $\mathrm{Cl}_S(E)$ (Thm 3), which in graph form is $\mathbf{a}B + \mathbf{b}$. **Uncited anywhere in this repository until 2026-10-15**, and the input type of the next row. | [V] |
| Aswanth–Kashyap, *Lifting an $[n,k,d]$ Binary Linear Code to an $[[n,k,d]]$ Quantum Stabilizer Code*, arXiv 2610.14192, 2026 (v1 HTML read 2026-10-15) | **Existence, not construction.** A lower bound on $\mathbb{P}(d_{\mathcal{Q}} = d)$ for $\mathrm{CWS}(\mathcal{C}, G(n,\tfrac12))$ (Thm 1); the finite GV-type condition $\sum_{j<d}\binom{n}{j}(3^j-1) < 2^{n-k}$ (Cor 1); and $R+h_2(\delta)+\delta\log_2 3 < 1$ asymptotically (Cor 2–3, identical in the limit to Feng–Ma and weaker in finite form, as the paper states). §IV leaves deterministic graph construction open. **Load-bearing for this calculus: the output is CSS only in trivial cases** — see `an internal note` §2, Proposition 1. | [V] |
**Relevance.** Complementary, as §2 says — but the §11 move-ladder protocol targets exactly
these families, so the target family (Q5) and any closure result (Gate 7) are downstream of
this literature, not parallel to it.

**Lee et al. specifics (arXiv 2609.30069v1, read 2026-09-29) — input to WP5/Gate 6.**

- The symplectic halving transformation (§IV, Def. 3) is a code-to-code
  transformation with exactly the shape the taxonomy's extended-state layer
  anticipates: input a CSS parent plus typed duality data (a fixed-point-free
  involution $\pi$ with $\pi(S_X) = S_Z$), output a general stabilizer code at
  half the blocklength with $k' = k/2$ and $\lceil d/2 \rceil \le d' \le d$.
  Recorded 2026-09-29 as the deferred pair `X-SYMPLECTIC-HALVE` /
  `X-SYMPLECTIC-DOUBLE` (`spec/TAXONOMY.md` §4.3); scoped in
  `WP5_NON_CSS_EXTENSION_SCOPING.md`.
- Its non-CSS instances ([[90,21,11]], [[140,31,15]], [[200,43,20]]) beat the
  CSS parameter frontier at matched rate and check weight — direct evidence
  that the discovery harness's Pareto frontier (§11.2) is not CSS-restricted.
- The remaining content (degree-distribution design coordinates, density
  evolution, packet-decomposed canonical logical bases) is code-design
  methodology, not code transformation; outside the calculus's object
  language, cited for frontier context only.

**Okada–Kasai v4 specifics (arXiv 2607.14091v4, read 2026-09-29) — three
calculus-relevant items beyond the CPM-PP core already recorded above.**

- **APM-PP extension (§VII, Thm 4).** The cancellation principle generalizes
  from equal CPM differences to equal *relative affine maps*
  ($\rho_{ij\ell} = d_{j\ell}^{-1} \circ e_{i\ell}$ paired across block
  columns). This strengthens the taxonomy §3.8 specialization reading: the
  general constructor is "pair equal relative permutation maps," with CPM-PP
  and APM-PP as specializations — and APM lifts escape the CPM structural
  distance ceiling ($d \le (J+1)!$, Thm 3), which is the same bound Lee et al.
  Appendix A attributes to the CPM family.
- **Kasai-construction specialization (§VII).** The selected ("active") check
  matrices of the Kasai parent are a CSS code obtained by *block-row selection*
  from a parent whose full check pair is **not** CSS-orthogonal
  ($\Psi_r \neq 0$ off $\Delta_S$): a non-CSS state whose row-selected substate
  is CSS, i.e. check deletion crossing the CSS/non-CSS boundary. Independent
  literature evidence for the two-sorted state model scoped in
  `WP5_NON_CSS_EXTENSION_SCOPING.md`.
- **Complete distance lower-bound algorithm (§V, Thm 2).** A sound and
  complete branch-and-bound over $\ker H \setminus \mathrm{rowspan} G$
  with proved pruning bounds ($b_1, b_2$) and cyclic root reduction (Prop 4,
  Cor 2, Prop 5: the enumeration bound is lift-size-independent). A completed
  `None` run is a reproducible per-state certificate that $d > W$ — exactly
  the input shape the reserved `certificate-checked` status anticipates
  (`spec/CLAIMS.md`, *Reserved future status*; per-state atomic judgments
  only). Recorded as prior art in §6 below; adopting it as a certificate
  source is a Gate 6-candidate decision, not a silent edit.

---

**Hsin specifics (arXiv 2611.09538v1, read 2026-11-09) — placement input for the
quotient/compactification family.**

- **What the paper is.** A single construction that unifies the quotient-code
  families (balanced product, bivariate bicycle, genon, five-qubit) under one
  lattice operation and its field-theory counterpart (twisted compactification).
  It is a *construction* paper with a transfer theorem and new non-CSS
  instances; it is not a transformation-soundness paper and makes no claim about
  property propagation across arbitrary terms.

- **Monomial quotient (construction class (i)).** A parent Pauli stabilizer
  code plus a free action of a finite group by qudit permutations composed with
  single-qudit Cliffords; the quotient map $\pi$ sends a Pauli on $q = hr$ to
  the corresponding Pauli on representative $r$ conjugated by $c_h^{-1}$, and
  the quotient code is $\pi(S)$. Free action is required for consistency (a
  nontrivial Clifford on a fixed point would be inconsistent). A different
  choice of representatives changes $\pi$ by single-qudit Cliffords, so the
  quotient is defined up to local Clifford equivalence. **This is the same
  state update as the existing `A-QUOTIENT` record** (`spec/TAXONOMY.md`
  §2.15) and the **balanced product** constructor (§3.4): restrict/identify
  stabilizer data under a specified linear (here, group-equivariant) map. What
  the paper adds is a distinct *parameter theorem* — the transfer theorem, with
  a Tate cohomology group counting the logical operators that are new — and a
  precisely typed quotient mechanism. Under `spec/TAXONOMY.md` §3.8
  that earns a **specialization record under `A-QUOTIENT`** ("monomial
  quotient": free monomial-Clifford action, orbit representatives, consistency
  condition), not a new primitive and not a new state update. The duality
  quotient (some $c_g$ a Hadamard-type Clifford) is the case where letters
  change and the result need not be CSS — the paper's five-qubit example — which
  is the same sector-swap phenomenon already recorded as `E-LOCAL-HADAMARD`
  (§2.12); in the CSS model it is a conditional move, and when it leaves the
  CSS model it belongs to the deferred layer (see below).

- **Dressed quotient (construction class (ii)).** Higher-form and cup-polynomial
  backgrounds: the twist is an entangling diagonal circuit (CZ-type for
  quadratic defects, CCZ-type for cubic and higher), and when a finite cover
  trivializes the background the code is a *dressed quotient* of a parent Pauli
  code — dressed Gauss laws. Outputs are commuting-projector codes, not Pauli
  stabilizer codes (e.g. $D(D_4)$, dimension $2^2$, linear distance), with
  dressings of Clifford level at most one less than the twist degree and, for
  cubic twists, code dimension equal to a count of solutions of quadratic
  equations in cup products. **This does not fit `C = (Q, X, Z, pres, used)`**
  and is not a CSS-level move; it is a new constructor whose input type is
  (parent code + background class / cup polynomial + trivializing cover) and
  whose orthogonality story is the dressed Gauss laws. It belongs in the
  **deferred extended-state layer** (`spec/TAXONOMY.md` §4),
  alongside `X-SYMPLECTIC-DOUBLE`/`HALVE` and the gauge/subsystem records, as a
  candidate constructor — not as a CSS transformation. The paper's "quotient, not
  restriction" point (§1.2.3) is worth noting here: the quotient is a map
  $\pi(S)$, not the deck-invariant subspace, which matches the calculus's
  existing distinction between quotient and restriction in `A-QUOTIENT`.

- **Twists as logical gates (construction class (iii)).** These are *logical
  operations on code spaces* (CCZ, $T$), not code transformations. The calculus
  has no term for a logical gate and is scoped to code-state transformations;
  they are out of the object language. They are relevant only as context for
  the extended-state layer's possible future "logical-action" judgments, which
  are `not yet defined` here.

- **Transfer theorem (§3.3).** Gives logical qudits, logical operators and
  distance bounds of a quotient from those of the parent. This is a
  property-propagation result of exactly the kind the judgment layer carries
  (`spec/JUDGMENT_LAYER.md`), but only as a
  conditional cell at Gate 7 / constructor level: the consumer still records
  supplied lower bounds and prices as trusted inputs and does not validate them
  (priced-hypothesis boundary). The Tate-cohomology count of new logicals is a
  candidate "does not carry / new" entry for logical operators under quotient.

- **Taxonomy placement (if ever admitted).**
  - Monomial quotient → specialization record under `A-QUOTIENT`
    (`spec/TAXONOMY.md` §2.15), with the transfer theorem as
    its conditional price/property cell; CSS-preserving instance only (permutation
    actions, or sector-preserving single-qudit Cliffords). The duality-quotient
    instance is the sector-swap case of `E-LOCAL-HADAMARD` (§2.12) and, when it
    leaves CSS, the extended-state layer.
  - Dressed quotient → new constructor candidate in §4 (deferred
    extended-state layer), input type (parent + background class / cup
    polynomial + trivializing cover), output a commuting-projector code. Distinct
    input type, distinct orthogonality proof (dressed Gauss laws), distinct
    parameter theorem (point count of cup-product solutions) — satisfies
    §3.8's criteria for a record of its own, but at the extended-state layer,
    not the CSS one.
  - "Compactification" as such is **not** a separate operation: it is the
    physical reading of the quotient (theory on $X\times F$ with a symmetry
    background along $F$). The geometry enters as the symmetry action and cover
    data — already the typed input `A-QUOTIENT`/balanced product require. No
    compactification primitive is needed.
  - Neither construction is an MVP transformation: the quotient is a constructor
    (parent → quotient), not a deformation of an existing state, and the
    dressed variant is non-CSS. Both are Gate 7 / extended-state-layer matters.

- **Relevance to the repository.** The paper is the cleanest published statement
  that balanced product, bivariate bicycle, genon and five-qubit codes are one
  construction (quotient), which supports the taxonomy's decision to treat
  balanced product as a constructor rather than a transformation and to keep
  `A-QUOTIENT` generic. Its transfer theorem is a ready-made source for a
  future conditional judgment cell for logical operators under quotient. Its
  dressed-quotient family is a concrete, worked instance of why the
  extended-state layer is a separate scope decision. It does not discharge any
  obligation, change any claim status, or justify a scope change on its own; it
  is prior art and placement input.

---

# 2. Code deformation, surgery, and logical-gate realization

The source of §8's move vocabulary.

**Two kinds of move share this section, and the distinction is the point.** The
rows above the CD discussion act *on* the code: they change which checks exist,
on which qubits, so $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$ differs before and
after. The logical-gate rows below the CD discussion leave $C$ untouched and ask
a different question — given this code, which logical operations does it admit,
and what physical circuit realises them. The second kind has no state update and
so cannot be a calculus rule; `spec/TAXONOMY.md` §1
excludes circuits from the taxonomy by design, and
[`SCOPE.md`](SCOPE.md) §4 excludes circuit realizations from scope. It is
recorded here so that a reader looking for missed *transformations* finds the
boundary stated rather than has to infer it.

| Work | Contribution | Tag |
| --- | --- | --- |
| Bombin–Martin-Delgado, *Quantum Measurements and Gates by Code Deformation*, J. Phys. A 42, 095302, 2009 | Origin of code deformation (cut-and-paste) | [V] |
| Horsman–Fowler–Devitt–Van Meter, *Surface code quantum computing by lattice surgery*, NJP 14, 123011, 2012 | Merge and split of logical patches | [C] |
| Fowler–Mariantoni–Martinis–Cleland, *Surface codes: Towards practical large-scale quantum computation*, PRA 86, 032324, 2012 | Defect movement, hole punching, grafting | [C] |
| Litinski–von Oppen, *Lattice Surgery with a Twist*, Quantum 2, 62, 2018 | Twist defects | [V] |
| Herzog–Berent–Kubica–Wille, *Lattice Surgery Compilation Beyond the Surface Code*, QCE 2025 | Code substrates; compilation as routing | [V] |
| Tan–Niu–Gidney, *A SAT Scalpel for Lattice Surgery*, ISCA 2024 | LaSsynth: SAT synthesis of surgery subroutines | [V] |
| Fujiu–Nagayama–Nishio–Kawaguchi–Satoh, *Dense packing of the surface code…*, PRA 113, 042412, 2026 | Dense packing as deformation; hook-error scheduling | [V] |
| Yin et al., *Surf-Deformer*, 2024 | Deformation as composable instructions | [V] |
| Lin et al., *Surface code logical operations on a superconducting quantum processor*, 2026 | Experimental merge/split/expansion/deformation | [V] |
| Bønnelykke–Joecker–Krogstrup–Michal–Svendsen, *Decoder- and Noise-Aware Optimization Framework for Clifford-Deformed QEC Codes*, arXiv 2610.13589, 2026 | **Clifford deformations (CDs)** — per-data-qubit stabilizer modification $S' = U S U^{\dagger}$, $U$ from the single-qubit Clifford set $\mathcal{A}_6 = \{I, H, \sqrt Z, H\sqrt Z, \sqrt ZH, H\sqrt ZH\}$; search space $\lvert\mathcal{A}_6^{n}\rvert = 6^{n}$, reduced to $\mathcal{A}_3 = \{I, H, H\sqrt ZH\}$ by the $p_X = p_Y$ symmetry (Appendix D: the reduction survives compilation under their circuit-level model); **EBBI**, a shot-efficient best-arm-ID + evolutionary search that treats circuit, noise model and decoder as a black box; new code **B-XZZX** (XZZX with a modified border), differing from XZZX on $2(d-1)$ qubits | [V] |
| Nelson–Danageozian–Cao–Economou–Barnes, *From Syndromes to Computation: A General Framework for Logical Operations in Quantum Error-Correcting Codes*, arXiv 2610.17612v1, 2026 (HTML v1 read 2026-10-15) | **Syndrome partitions** (second kind of move — see the scope note above). An exact codespace-preservation condition (Thm 1) for commuting multiqubit Pauli rotations at *arbitrary* angle, stated check-by-check through the generator syndromes, uniform over CSS and non-CSS and Clifford and non-Clifford. Equal-syndrome specialisation reduces $\pi/4$ Clifford design to stabilizer factorization with an exact sign condition (Cor 3) and gives $w_{\max}\ge\lceil d/2\rceil$ (Cor 2, saturated in §IV.5). Lifting (Thm 2) and a seven-point Fano-plane Pauli-root construction give $\pi/8$ TT-type gates; Clifford-algebra-basis (CAB) coordinates give analytic addressed CNOT/SWAP/CCZ templates on recursive hypercube codes. Searches: 291 distinct logical Cliffords on ⟦16,4,4⟧ BB, 112 on ⟦64,8,8⟧ BB, 25 on the non-CSS ⟦36,6,6⟧ Mirror; CCZ-type lifts; an addressed $T_2$ on ⟦16,4,4⟧ BB | [V] |
| Sahay–Long–Khemani, *Computing with qLDPC codes by climbing the chain map hierarchy*, arXiv 2609.02999, 2026 | Chain-map hierarchy: homological construction of Pauli, Clifford and non-Clifford logical operations, including constant-depth Clifford circuits and non-Clifford controlled phases. Positioned by 2610.17612 §I as the homological counterpart to the syndrome-partition condition, which is pitched against it. **Not read by this repository** — known from that paper's reference list and §I description only | [C] |
| Yoshioka–Seif–Groszkowski–Cross–Javadi-Abhari, *Theory and architecture of syndrome-resolved logical gates*, arXiv 2510.08290, 2025 | Weakly transversal logical gates in general CSS codes, with the logical action of physical Pauli rotations realised *probabilistically* through syndrome measurement and conditional feedforward. Positioned by 2610.17612 §I as the nearest ansatz neighbour; the claimed differentiator is directness — no measurement, no feedforward. **Not read by this repository** | [C] |
| Dua–Holmes–Gullans–Albert, *Qubit CSS codes with universal transversal gates*, arXiv 2610.06730, 2026 | CSS codes whose logical gates are depth-one layers of disjoint few-qubit gates, optionally over different physical partitions, with probabilistic logical action. Also the source 2610.17612 §V.1 cites for its partition-distance formulation (Eq. 111) — see the definitional note below. **Not read by this repository** | [C] |
| Rabeti–Shirke–Dimitrova–Mahdavifar, *Logically Augmented Quantum LDPC Codes: Construction and Hierarchical Decoding*, arXiv 2611.07062, 2026 | **LA CSS codes**: impose additional stabilizer constraints on \(n_L\) selected logical qubits of a primary CSS code via an auxiliary Logical Protection Code (LPC); physical block length and all original stabilizer generators are preserved; parameters \(\mathcal Q_A = [[n,\; k-n_L+k_L,\; d_A]]\). Hierarchical decoding (HLLD) uses the LPC syndrome to generate logical error hypotheses and condition BP. Recorded here as prior art and as an instance of `C-ADD-CHECK` — see the subsection below | [V] |

**Relevance.** §8's entries ("dense packing", "hook-error") have a 2026 paper with that
exact framing (Fujiu et al.); state the relationship. And the informal operations already
have a rigorous unifying account — next section.

**Clifford deformations are not a missing transformation here, and the
disposition already exists.** A CD is exactly *Local Hadamard (per-qubit sector
swap)*, `spec/TAXONOMY.md` §2.12 (`E-LOCAL-HADAMARD`,
`taxonomy-only`): the paper's $\mathcal{A}_6$ is the single-qubit Clifford group
modulo phases, and §2.12 already states that conjugation is the only such effect
the phase-insensitive check structure can represent, that $S$ is not
CSS-representable, and that the name is *Hadamard* rather than *local Clifford*
for exactly that reason. A second-pass red-team finding already named this paper's
headline family as the move's counterexample: "the rotated surface code with
Hadamards on alternate qubits is the XZZX code"
(the red-team note
§23). XZZX's weight-4 $Z\otimes X$ checks are the $Q=\{1,2\}$ witness of that
note at scale — a valid stabilizer code with no pure-sector presentation. The
§2.12 splitting condition rescues exactly the residual case, which that finding showed
vacuous inside CSS: a state whose row spaces split along the conjugated set is a
direct sum, and the move is then the global $T=Q$ sector swap on one summand.

Concretely, the per-qubit (or subset) Hadamard move `hadamard(T)` preserves the
standard-CSS presentation exactly when both sector row spaces split along `T`:

- for every row \(v\) of \(X\), \(v|_T \in X\);
- for every row \(w\) of \(Z\), \(w|_T \in Z\).

Without this split the image need not be CSS: a physical reading gives a valid
stabilizer code with no pure-sector presentation, and a matrix reading breaks
orthogonality under row reordering. The global instance \(T = Q\) exchanges
the two sectors' distances; the empty instance \(T = \varnothing\) is the
identity. See `spec/TAXONOMY.md` §2.12 and
`spec/OPERATIONAL_SEMANTICS.md` §4.27.

So the honest reading is the already-dispositioned one — **CDs are non-CSS
stabilizer codes**, which is `spec/TAXONOMY.md` §4's
extended-state layer, not §2. No operation ID is minted; §3.8 forbids granting
one to a family or paper without a distinct state update, and the state update
here is §2.12's.

Two further points of this work are worth stating in the record, both *not*
transformation claims:

- **The objective is decoder- and noise-model-relative, so "optimal CD" is not a
  property of the code.** Appendix H compares PyMatching, BeliefMatching, BP-OSD,
  Tesseract and CudaQ-TN over CSS / XZZX / XY / B-XZZX and reports that the
  ranking changes with the decoder (PyMatching performs particularly badly on
  XY, which §4 attributes to $H\sqrt ZH$ turning $ZZ$ errors into correlated
  $YY$ errors that matching must discard). $P_L$ under a biased circuit-level
  model is not in the property inventory ($n$, $k$, $d_X$, $d_Z$, $d$, $w$), and
  circuit-layer judgments are already `not yet defined` — see the
  `spec/TAXONOMY.md` §2.13 circuit-layer row and the
  [`SCOPE.md`](SCOPE.md) §4 exclusion of search control.
- **The $\mathcal{A}_6 \to \mathcal{A}_3$ reduction is an equivalence of states
  under a noise model**, not an operation: it is a property-preservation
  statement about compiled circuits, and $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$
  has no field for a noise model. At most a motivation for why the
  extended-state layer would need typed noise data. Recorded as prior art; not a
  candidate claim.

### Syndrome partitions (arXiv 2610.17612): prior art, four boundary statements

**Not a transformation, and no identifier is minted.** A logical gate leaves $C$
unchanged; the paper's whole object is a *function* on a fixed code. The
taxonomy already excludes circuits by design
(`spec/TAXONOMY.md` §1), `README.md` lists *no circuit
realizations* as a non-goal, and the paper is out of scope by that route rather
than by omission — so §3.8's bar is never reached. Admitting logical-gate
realization as an operation would be a Gate 6/7 admission decision, which
[`SCOPE.md`](SCOPE.md) §4 defers. Recorded so a reader does not have to
re-derive that this is a boundary rather than a gap.

**The logical-witness field is load-bearing in published work — external
support for a field this repository has twice called `not yet defined`, and it
discharges nothing.** Three things are visible in the paper's own text. Its §III.1
applies a *chosen* logical Pauli frame only *after* a search, and §IV uses a CAB
presentation in which one quartic CAB-index set yields at once the stabilizer
check, the logical qubit, its three Pauli axes, and its addressability. §IV.3.3
then states that permuting the four indices of a quartic set *"is a change of CAB
presentation, not a physical gate"* — an equivalence on the **witness**, holding
the physical operation fixed. This repository has presentation equivalence on
qubits and displayed rows (`spec/TAXONOMY.md` §1.4) and
nothing on witnesses, and the §2.10 Gate 6 prerequisite names that same missing
field. This is evidence in the same shape as the 2307.02437 row in §4; no
obligation's evidence status moves and the twelve in-scope obligations are
still twelve.

**Two candidate judgment rows this paper makes falsifiable. Neither is
scheduled, and `spec/` is untouched.** (a) *Gate survival and addressability
through `C-ADD-CHECK`.* §IV.4 builds codes by imposing one check per encoding
level — a `C-ADD-CHECK` sequence — while carrying constructed gates along;
§IV.4.3 is *promoting lower-level gates* and §IV.4.5 is *additional
addressability*. Whether a constructed gate survives a check addition, and
stays addressable, is a judgment the carry table has no row for; today that
would read `not yet defined`, which understates it, since it is derivable in
the CAB presentation and its falsifiability is exactly what makes it a
candidate. (b) *A bound that transports by weakening rather than by
substitution.* Cor 2's contrapositive says a parent of distance $d$ admits no
equal-syndrome LGA with $w_{\max}<\lceil d/2\rceil$; `C-DELETE-CHECK` only ever
lowers $d$, so a child inherits a weaker bound rather than the parent's value.
That is a carry-with-hypothesis shape the layer wants and does not yet have.
Both are Gate 6/7 admissions and are deferred with the rest.

**The retention of physically distinct realisations supports §1.2 and §2.13.**
§III.1 keeps them deliberately — *"we retain the physically distinct
realizations of the same logical action as their stabilizer syndromes can
differ, providing different building blocks for non-Clifford gates."* A search
that profits from the display is direct evidence for §1.2's *support-sensitive
predicates may change truth value* and for §2.13's disposition, where the
constructor must carry retained-presentation data of `P-REBASE` shape. **The
limit of this, recorded so a later reader does not over-claim in the other
direction:** the equal-syndrome *hypothesis* is itself invariant under
rebasing, since $\sigma_{S'}=M\sigma_S$ for invertible $M$, so the syndrome
partition of candidate generators cannot change under a basis change. What is
presentation-dependent is the frame and the witness, not the partition.

**The analytic half is bounded by the paper's own counting, and the bound sits
where the framing does not suggest.** §IV.2 requires disjoint quartic CAB-index
sets, one per independent check, so $4b\le 2n$ for $b=n-k$, hence $k\ge n/2$
— and the codes actually delivered there are its own ⟦4m,2m,2⟧ family, rate
$\tfrac12$ and distance 2 (Appendix H). The frame-based machinery is therefore
unavailable at qLDPC rates, which is where the computational results live, and
the computational results have no frame machinery: the two halves have disjoint
applicability. Theorem 1 is the general part and is used by both; §IV is not.
Recorded as a limit on the paper's reach, not as a defect in it.

**One definitional slippage, recorded as read.** §V.1 Eq. 111 minimises the
number of rotation supports that a *single* nontrivial logical touches. The
standard partition distance minimises over *pairs* of equal-size support subsets
whose union supports a logical, and the $d_{\mathrm{part}}\ge 2s+1$ correction
criterion the paper then invokes belongs to that standard definition. As written
the quantity and the criterion do not match, and §V.1's own arithmetic
reasonings are sound either way. Flagged because §2's entries keep observed
defects visible; it changes no disposition here.

**Not prior art for §10.1, and §11.1 stands.** §VI's *within their stated search
domains … they do not establish global optimality* is epistemic discipline about
a bounded search, not a design commitment about a rule system — the same
distinction §4 drew for 2307.02437's $d_2\in\mathbb{N}$. The paper has no state
model, no term language, no partiality, no judgment layer, no mechanization and
no lineage, so "none addresses a sound, mechanized, code-level transformation
calculus" is unchanged. On §11.2 the honest reading cuts both ways: its §VI
proposes AI-assisted ansatz search validated by *exactly checking* the
codespace-preservation condition, which is the shape of this repository's
claimed edge realised by someone else in the one domain where the acceptance
predicate happens to be decidable — and §11.2 precondition 1 is precisely the
firewall that prevents this repository from producing it. Precondition 2 also
stands: $n$, $k$, $d_X$, $d_Z$, $d$ transport prunes nothing in a search over
fixed codes.

---

### Logically augmented CSS codes (arXiv 2611.07062): prior art, instance of `C-ADD-CHECK`

**Read by this repository (HTML v1, 2026-11-08).** Tagged **[V]**.

**What the paper does.** Given a primary CSS code \(\mathcal Q_P=[[n,k,d]]\) and an
auxiliary CSS code \(\mathcal Q_L=[[n_L,k_L,d_L]]\) (the Logical Protection Code,
LPC), choose \(n_L\le k\) independent pairs of logical operators
\(L_X,L_Z\in\mathbb F_2^{n_L\times n}\) of \(\mathcal Q_P\) with
\(H_Z L_X^T=0\), \(H_X L_Z^T=0\), \(L_X L_Z^T=I_{n_L}\). Form the augmented code
\(\mathcal Q_A\) with
\(H_X^A=\begin{bmatrix}H_X\\ G_X L_X\end{bmatrix}\),
\(H_Z^A=\begin{bmatrix}H_Z\\ G_Z L_Z\end{bmatrix}\),
where \(G_X,G_Z\) are the LPC parity-check matrices. Then
\(\mathcal Q_A=[[n,\; k-n_L+k_L,\; d_A]]\): the physical block length and all
original stabilizer generators are preserved, and \(n_L-k_L\) independent
logical qubits are converted into stabilizer constraints. The repetition-code LPC
(\(G_X=0\), \(G_Z\) the \((r-1)\times r\) chain) is the worked case:
\(k\) drops by \(r-1\), and each LPC syndrome admits exactly two logical error
hypotheses.

**Why this is an instance of `C-ADD-CHECK`, not a new operation.** The augmented
code differs from the primary code only by the presence of the additional rows
\(G_X L_X\) and \(G_Z L_Z\). Those rows are vectors in \(\mathbb F_2^Q\) (the
\(L\)'s are physical representatives on \(Q\)), and the paper's stated conditions
are exactly the `C-ADD-CHECK` premises:

- *Commutation with the opposite sector.* For an added X-type row
  \((G_X L_X)_i\): \(H_Z (G_X L_X)_i^T = G_{X,i} (H_Z L_X^T)=0\) because
  \(H_Z L_X^T=0\); and the added Z-type rows commute with it because
  \((G_X L_X)_i (G_Z L_Z)_j^T = G_{X,i} (L_X L_Z^T) G_{Z,j}^T
  = G_{X,i} I G_{Z,j}^T = (G_X G_Z^T)_{ij}=0\) by the LPC's CSS condition.
  Symmetrically for added Z-type rows.
- *Same-sector independence.* The new rows are independent of the existing
  sector row space and of each other exactly when the LPC rows \(G_X,G_Z\) are
  independent and the selected logical operators are independent; this is the
  \(r\notin X\) (resp. \(r\notin Z\)) premise.

Hence the whole construction is a finite sequence of `C-ADD-CHECK` commands
applied to the primary state, with the added rows supplied as check data. No
qubit is added or removed, no namespace changes, and `used` grows only by the
canonically minted identifiers of the added rows. The calculus needs no new
transition to represent it; what the paper contributes is a *recipe* for choosing
the added rows (via an LPC and chosen logical representatives) so that they are
products of logical operators and carry a decoding-oriented hypothesis
structure.

**Why it does not earn a distinct operation identifier.** Under
`spec/TAXONOMY.md` §3.8, a named family deserves its own
operation only with a distinct input type, state update, CSS-orthogonality proof,
parameter theorem, or quotient/action/boundary mechanism. The state update here
is identical to `C-ADD-CHECK`; the orthogonality proof is the standard
commutation/independence argument above; and the only parameter theorem supplied
is \(k'=k-n_L+k_L\), which is the ordinary rank consequence of adding
\(n_L-k_L\) independent checks. The LPC and the logical-representative selection
are *input data* for a `C-ADD-CHECK` sequence, not a new state transformation.
So this stays prior art / a worked example of `C-ADD-CHECK` sequencing, not a
taxonomy entry and not a grammar production.

**What the calculus will and will not say about it.**

- *Carries.* The ranks, \(n\), and \(k\) consequences of adding the stated
  independent rows are ordinary `C-ADD-CHECK` consequences and are transportable
  as such.
- *Does not carry / unavailable.* The augmented distance \(d_A\) is not
  determined by the construction: it depends on the primary code, the chosen
  logical representatives, and the LPC. Any distance claim is a hypothesis to be
  supplied (lower bound, price, or minimum-weight-class enumeration); the
  consumer records and structurally checks such inputs but does not validate
  their truth. The paper's numerical distance/error-rate results are evidence
  about a construction instance, not a derivation.
- *Out of scope.* The decoding half (HLLD, BP conditioning, logical-list
  generation, complexity) is a decoding procedure; the taxonomy deliberately
  does not classify decoding procedures, and circuit/decoder judgments are
  `not yet defined` in this calculus. The paper's reported logical-error-rate
  reductions (up to 81% / 75% / 69% for mitten / lifted-product / bivariate
  bicycle based LA codes) are decoder-performance evidence and do not move any
  obligation or claim status.

**Relevance to the repository.** This is a clean, small instance of the
already-admitted `C-ADD-CHECK` move: it shows a realistic setting in which one
adds stabilizers that are products of logical operators (code expurgation at the
logical level) while preserving \(n\) and the original generators. It can serve as
a worked example for `C-ADD-CHECK` sequencing with supplied rows and for the
carry/transport of \(k\) under check addition; it does not require, and does not
justify, a scope change, a new operation ID, or a new obligation.

### Expurgation and puncturing-as-repair (arXiv 2611.08744): prior art, specialization of `C-ADD-CHECK` / `E-PUNCTURE`

**Read by this repository (abstract, 2026-11-10).** Tagged **[C]** (abstract-level
read only; full text not yet verified).

**What the paper does.** Reports 192 binary stabilizer codes improving Grassl's
tables, via two procedures: (i) *expurgation* — enumerate every logical operator
below a target distance, promote a few to stabilizers so each low-weight logical
anticommutes with at least one (random Clifford encoder followed by
expurgation); (ii) *puncturing a code from the table and repairing it* in the
same way. All distances are exact (meet-in-the-middle enumeration up to
\(4\times10^{13}\) Pauli operators for the lower bound; explicit logical operator
of weight \(d\) for the upper bound). The search was run by AI agents; codes,
certificates and an independent checker are public.

**Why this is not a new operation.** (i) Expurgation is a *specialization of
`C-ADD-CHECK`*: promoting a logical operator to a stabilizer is adding a check
that commutes with the opposite sector and is independent of its own sector,
with the surviving-logical minimum and \(k'=k-r\) consequences of §2a. The
paper's distinctive content is the *hypothesis* — an exhaustive enumeration of
low-weight logical classes and a parity hitting-set selection over them — which
is exactly the strict-improvement cell's hypothesis (Proposition 18.3 /
Corollary 18.4). (ii) Puncturing-and-repair is an instance of the already
admitted `E-PUNCTURE` conditional cell. No new state update, no new namespace
change, no new grammar production.

**What the calculus will and will not say.** Carries: ranks, \(n\), \(k\) under
the added checks are ordinary `C-ADD-CHECK` / `E-PUNCTURE` consequences.
Unavailable: the augmented distance \(d_A\) depends on the primary code, the chosen
logical representatives, and the enumeration; any distance claim is a
consumer-supplied hypothesis. The paper's reported table improvements are
evidence about construction instances, not derivations, and do not move any
obligation or claim status.

**Relevance.** Supplies a concrete, citation-backed hypothesis source for the
strict-improvement cell's minimum-weight-class enumeration, and an instance for
`E-PUNCTURE`. Record under `DERIVED_RELATIONS.md` as a `C-ADD-CHECK`
specialization requiring an externally supplied enumeration.

### Layered gauging (arXiv 2604.27363): prior art, extended-state candidate

**Read by this repository (abstract, 2026-11-10).** Tagged **[C]** (abstract-level
read only).

**What the paper does.** Proposes *layered gauging*: stack many layers of
\(k\)-dimensional systems with a symmetry and sequentially gauge a diagonal
symmetry acting on each nearest-neighbour pair of layers, generating
\((k+1)\)-dimensional (liquid or fracton) topological orders. Handles
conventional, higher-form, subsystem, anomalous, non-abelian and non-invertible
symmetries; from the subsystem symmetry of the 2D plaquette Ising model it
derives the X-cube model and an anisotropic fracton order, and from an
anomalous \(\mathbb Z_2\) symmetry in 1D a square-lattice double-semion model.
The authors note it may be viewed as a generalization of the hypergraph-product
construction beyond the standard CSS setting.

**Disposition.** A *construction* (`A-*` family), not a transformation of an
existing code, and it leaves the CSS setting (higher-form/subsystem/anomalous
symmetries). The non-CSS extended-state layer is explicitly out of scope
(`SCOPE.md` §4: `X-SYMPLECTIC-DOUBLE`/`HALVE` deferred). It does not
earn a CSS-level cell. Recorded as prior art and as a candidate constructor for
the deferred extended-state layer; if admitted, it would need a typed input
signature and a distance hypothesis, and may supply a price provider analogous to
`A-CONCAT`. No scope change, no new obligation.

# 3. Gauge fixing: the unifying operational account

The most important competing item.

| Work | Contribution | Tag |
| --- | --- | --- |
| Vuillot–Lao–Criger–García Almudéver–Bertels–Terhal, *Code Deformation and Lattice Surgery Are Gauge Fixing*, NJP 21, 033028, 2019 | Proves deformation and lattice surgery are instances of gauge fixing, with a fault-tolerance test | [V] |
| Bombin, *Single-shot fault-tolerant quantum error correction*, PRX 5, 031043, 2015 | Gauge fixing in 3D gauge color codes | [V] |
| Bombin, *Dimensional Jump in Quantum Error Correction*, NJP 18, 043038, 2016 | Dimension switched by gauge fixing | [V] |
| Higgott–Breuckmann, *Subsystem codes with high thresholds by gauge fixing…*, PRX 11, 031039, 2021 | Gauge fixing for thresholds | [V] |
| Bacon, *Operator quantum error-correcting subsystems*, PRA 73, 012340, 2006 | Subsystem-code formalism | [C] |

**Relevance.** Competes with "first to formalize merge/split/deformation." Because §7.3
defers gauge fixing, the calculus covers a strict subset of an operation with an existing
rigorous account. §7.3 must argue what the ordinary-CSS restriction buys — the defensible
answer is mechanized soundness and judgment transport, which gauge fixing does not provide.

---

# 4. Diagrammatic calculi for the same operations

| Work | Contribution | Tag |
| --- | --- | --- |
| Huang–Li–Yeh–Kissinger–Mosca–Vasmer, *Graphical CSS Code Transformation Using ZX Calculus*, arXiv 2307.02437v2, 2023 | Phase-free ZX normal form for **CSS subsystem codes** (Def. 3.1); *pushing through the encoder* as a bidirectional rewrite rule, $EL = PE$ (Prop. 3.1); **code morphing** (Def. 4.1, Proc. 4.1); **code switching** as gauge fixing of ⟦15,1,3,3⟧ (Prop. 5.2), Steane ↔ quantum Reed-Muller | [V] |
| de Beaudrap–Horsman, *The ZX calculus is a language for surface code lattice surgery*, Quantum 4, 218, 2020 | ZX spiders match rough/smooth merges and splits; rewrites derive surgery procedures | [V] |
| van de Wetering, *ZX-calculus for the working quantum computer scientist*, 2020 | Survey; completeness | [V] |
| Cowtan, *Qudit lattice surgery*, 2022 | Qudits; relation to ZX | [V] |
| Paler, *Untangling Surface Codes: Bridging Braids and Lattice Surgery*, 2025 | ZX as bridge; "unified formal language for topological QC" | [V] |
| Hanks–Estarellas–Munro–Nemoto, *…Braided Circuits Aided by ZX-Calculus*, PRX 10, 041030, 2020 | ZX as intermediate language | [V] |

**Relevance.** Competes with §2's "no single small formal language": one exists and is
complete for the Clifford fragment. The surviving gap is diagrammatic/process-level vs.
typed/state-level with code-property judgments.

**Huang et al. is the strongest instance of that verdict, because it is the one row
here that transforms *codes* rather than qubits** — every other entry in this section
is about surgery procedures, measurement-based computation, or braided circuits. It is
the closest published object to this calculus, and the gap runs in both directions: it
has no presentation, no partiality, no property judgments, and no mechanization, while
this calculus has no diagrams. Three specifics carry the weight; all three are
evidence, and none discharges anything.

- **Its headline transformation is not representable in $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ — read off the paper's own derivation rather than asserted.** Prop. 5.2 adds the three $X$-type gauge operators to $\mathcal{S}_{sub} = \langle F^X, F^Z, H^Z\rangle$ and obtains $\mathcal{S}_{ex} = \langle F^X, F^Z, H^X, H^Z\rangle$; the paper's proof then states that this intermediate diagram *"is exactly the encoder of the ⟦15,4,3⟧ stabilizer code."* The extended Steane code and that ⟦15,4,3⟧ code therefore carry **the same stabilizer group**, differing only in which of the four logical operators are logical and which are gauge (its Eq. 7, $\mathcal{L}' = \mathcal{L}_g \cup \mathcal{L}$) and in the physical gauge state $|\bar{000}\rangle$ against $|\bar{+++}\rangle$. Neither difference has a field in $C$. So the Steane ↔ Reed-Muller switch is, in this model, one of **two distinct three-step `C-ADD-CHECK` sequences** — add $H^X$ or add $J^Z$, $n' = 15$, $k: 4 \to 1$ — after which the switching step itself **has no expression**. This is external support for the §2.10 Gate 6 prerequisite (the `not yet defined` logical-witness field) and for §4.2's bare/dressed requirement: a published transformation needs a field this calculus has not defined.
- **It supports §4.1's refusal to model gauge fixing as ordinary `addStab`.** The reduction to *"equivalent to adding $L_g^X$ to $\mathcal{S}_{sub}$"* (Prop. 5.2, concluding paragraph) is available in that paper only **after** Def. 3.1 has already changed the object — gauge operators are Z-spiders fed a joint density operator $\rho$ in step (e), with no input wire to push anything through. The reduction follows from having built the extended state, not from the stabilizer-group bookkeeping. §4.1's sentence is thereby externally supported rather than only asserted.
- **Its distance discipline is the shape of the `unavailable` refusal.** Def. 4.1 and Proc. 4.1 write the post-morphing distances as $d_1, d_2 \in \mathbb{N}$ — declined, not forgotten — and reason per instance instead (Ex. 4.1: the ⟦6,1,1⟧ result, because qubit $\bar{3}$ is unprotected by any $X$-type stabilizer). That is the shape of the $d'_X \le d_X$ proved / exact value `unavailable` split in `JUDGMENT_LAYER.md` §2. **The limit of the analogy is load-bearing:** the paper's version attaches to no rule system and no outcome vocabulary, so it is not the design commitment `unavailable` is. §10.1 records what this does and does not do to that row.

**Do not import its completeness.** ZX completeness is completeness for equality of
*linear maps*, not for property propagation. It is not an argument for
`OBL-JUDGMENT-SOUNDNESS`, and citing it that way would repeat in the opposite
direction the error the README's *Status* section forbids.

---

# 5. Mechanized QEC verification (circuits and codes)

| Work | Contribution | Tag |
| --- | --- | --- |
| Huang–Zhou–Fang–Zhao–Ying, *Efficient Formal Verification of Quantum Error Correcting Programs*, PLDI 2025 | Coq assertion + program logic for QEC programs; sound proof system; Veri-QEC; 14-code benchmark | [V] |
| Hietala–Rand–Hung–Wu–Hicks, *A Verified Optimizer for Quantum Circuits* (VOQC/SQIR), POPL 2021 | Verified circuit optimizer in Coq | [V] |
| Rand–Paykin–Zdancewic, *QWIRE Practice: Formal Verification of Quantum Circuits in Coq*, EPTCS 266 (QPL 2017) | Circuit language embedded in Coq | [V] |
| Bordg–Paulson et al., quantum Hoare logic in Isabelle/HOL | Program-logic mechanization | [C] |
| Jain, *QECLean* — Lean 4 formalization of QEC (2025–, UW–Madison), with companion repo `qec-lab` | Sorry-free stabilizer/CSS/symplectic library; toric code `[[2L²,2,L]]` and gross code `[[144,12,12]]` with distance proved exactly; CSS concatenation `[[n₁n₂,k₂,≥d₁d₂]]`; BB doubling framework; long-term goal of a generic QLDPC framework with proven distance; 267-code zoo catalog in `qec-lab` | [V] |
| Ehatamm–Lee–Wu–Tao, *End-to-End Formalization of Quantum Error Correction*, arXiv 2605.16523, 2026 (repo `VerifiedQC/Lean-QEC`) | Lean 4 stabilizer/CSS formalization with a **verified SAT translation** of the distance condition; machine-checked distance lower bounds incl. `[[90,8,10]]`, `[[70,6,9]]` BB codes; scales to 144 qubits outside the Lean kernel | [V] |
| He–Chen–Xiong–Ni–Zhang–Wang, *QECert: Formal Foundations for Quantum Error-Correction Theory in Lean*, arXiv 2611.05047, 2026 (repo `QudeLeap/Lean-QECert`) | Lean 4 library for asymptotic properties and fundamental limits of QEC: stabilizer and CSS codes as chain complexes, distance via homology, hypergraph/lifted/balanced-product and quantum Tanner constructions with parameter theorems, asymptotically-good qLDPC family predicates, plus locality, distillation and energy-barrier results. Research focus is code families and asymptotic theorems rather than transformation soundness | [V] |
| Schlesinger et al., *cslib-frontier* (cslib-community, 2026) — Lean 4 general-CS formalization atop CSLib + Mathlib | Broad formalization of theoretical CS: classical coding theory (linear codes, Hamming/Reed–Solomon/concatenation bounds, list/locally-decodable and expander codes), quantum foundations (Pauli `X`/`Z`, Hadamard, density matrices), complexity classes, Turing machines, PCP. **No CSS/stabilizer code formalization** (no stabilizer codes, chain complexes, or homology), so it is not a QEC substrate; its classical-code theorems are the nearest overlap with CSS distance hypotheses | [V] |
| Adal, *Quantumlib.lean* (inQWIRE LeanQuantum, 2025) | Lean 4 quantum-computing library; `StabilizerCode` structure with bit-flip and Shor-9 codes verified; Steane/surface/CSS listed as planned | [V] |
| *Project_qec_lean* (Ruizsolveall, 2026) | CSS ↔ length-3 chain complex over $\mathbb F_2$; logicals as homology; distance as min-weight nontrivial class; `[[4,2,2]]` and repetition instances | [V] |
| Unitary Foundation QEC Challenge, certificates schema (`schema/cert.schema.json`; issue #2511/#2728; PR #2522/#2753/#2754 — red-team T1/T3, 2026-10-04), 2026 | Operational three-tier evidence stack: `solver` / `proof_log` / `formal`, with `artifact`/`checker` fields on `main` (`verification.replay` is the formal-tier recipe; the `cnf_sha256` regeneration-recipe design for `proof_log` is proposed in the open PR #2754). #2753 rules that what makes a certificate formal is the verified reduction in the development (Lean-QEC), not the emitted query or refutation — external prior art for the Gate 5 semantics distinction. See `EPISTEMIC_LAYERS_CROSSWALK_2026-10-04.md` | [V] |

**Relevance.** Different object, now confirmed to exist in Lean 4 — this discharges the
former "Lean 4 QEC formalization — confirm whether any exists" [C] item. The circuit-logic
works mechanize *programs under error models*; the Lean code works mechanize *properties
of individual codes* (parameters, exact distances, homology) — static certification of a
fixed code. The calculus mechanizes *transformations between code states* with per-move
soundness and judgment transport. QECLean's concatenation theorem and BB doubling framework
are the nearest mechanized precedent for parameter-judgment transport across a
construction — family/instance theorems over fixed codes, not a typed term language;
cite and distinguish (§11.1). Lean-QEC's verified SAT bridge is the natural future route
for discharging the MVP's `unavailable` deletion-distance judgment without a trusted
solver. For Gate 5 and WP0 this makes a mathlib-native, sorry-free substrate available
instead of a from-scratch formalization, and the Lean-4-vs-Coq choice §12 requires can
now be stated affirmatively. Presentational fix retained: §12's "machine-checked proof
that every derivable annotation is true" invites the Huang et al. comparison and should
name the object.

**QECert (arXiv 2611.05047) — third candidate substrate, recorded 2026-11-04.** Adds
a Lean 4 library whose research focus is asymptotic properties and fundamental limits
rather than distance certification (Lean-QEC) or code structures/logicals (QECLean). Its
formalized content overlaps the calculus's object model at the code level — CSS codes as
chain complexes, distance as minimum-weight nontrivial homology class, and parameter
theorems for the hypergraph, lifted, balanced (cyclic) and quantum Tanner constructions
the move ladder already targets — plus asymptotically-good qLDPC family predicates,
locality bounds, distillation and energy barriers. It is therefore a candidate source of
verified construction theorems for conditional judgment cells, and a third substrate to
evaluate for Gate 5 / WP0 alongside Lean-QEC and QECLean. It does not change the calculus's
scope or obligations: it formalizes codes and families, not transformations between code
states, and it supplies no state model, term language, judgment transport, or `unavailable`
discipline. Adoption (dependency in `lean/lakefile.toml`, toolchain compatibility check)
is a maintainer decision and is not made here.

**cslib-frontier (Schlesinger et al., cslib-community, 2026) — general-CS library,
recorded 2026-11-09.** Adds a Lean 4 library whose scope is theoretical computer
science generally rather than QEC: it formalizes classical linear codes and their
distance bounds (including concatenation — `le_minDist_image_concat`, minimum
distance at least the product of the inner and outer minimum distances),
locally/locally-list decodable and expander codes, and quantum foundations (Pauli
`X`/`Z`, Hadamard, density matrices). It is atop CSLib + Mathlib, so its
build/dependency profile matches the `mathlib alone` mitigation rather than a
single-maintainer fork. It is **not** a QEC substrate: it contains no
stabilizer/CSS code formalization, no chain complexes, and no homology, so it
supplies no distance certification for CSS codes and no state model. Its realistic
use for this calculus is narrow and optional — as a source of classical-code
distance theorems (concatenation product bounds, Hamming/Singleton/Plotkin bounds)
that a future discharge of conditional CSS distance/parameter cells could consume
as hypotheses, and as mathlib-aligned infrastructure if the Lean layer ever needs
finite-type/linear-algebra lemmas beyond Std. It does not change the calculus's
scope, obligations, or `unavailable` discipline. Adoption (dependency in
`lean/lakefile.toml`, toolchain alignment from `v4.35.0` to `v4.36.0-rc2`) is a
maintainer decision and is not made here.

---

# 6. Distance: computation, bounds, hardness

| Work | Contribution | Tag |
| --- | --- | --- |
| Vardy, *The intractability of computing the minimum distance of a code*, IEEE TIT 43(6), 1997 | NP-hardness of exact distance | [C] |
| Berlekamp, McEliece, and van Tilborg, *On the inherent intractability of certain coding problems*, IEEE TIT 24(3), 1978 | NP-completeness of syndrome decoding (the coset-weights problem); the root of Theorem 24.1's exposure-price reduction and of the column-weight-three reduction in `DERIVED_RELATIONS.md` §3a | [C] |
| Prange / Stern / Leon, information-set decoding | Classical ISD; ancestor of RIS | [C] |
| Webster–Jacob–Higgott, *Distance-Finding Algorithms for Quantum Codes and Circuits*, 2026 | Exact (Brouwer–Zimmermann, SAT, MIP) and heuristic (RIS, Stim) methods; QDistEvol; `codeDistance` | [V] |
| Okada–Kasai, arXiv 2607.14091v4 §V | Complete branch-and-bound distance lower-bound certificate for CSS lifts: proved pruning, cyclic root reduction, lift-size-independent enumeration bound; completed `None` run certifies $d > W$ | [V] |
| Liang et al., arXiv 2609.37231v1 App. B.2 | Exact fault-response-certificate computation: stabilizer-reduced response catalog, then Dijkstra (BFS when unit costs) over a $2^{n-\mathrm{rank} H_P}$-state quotient graph; returns a per-circuit circuit-distance lower bound. App. G adds BP+LSD circuit-level simulation | [V] |
| Ye–Palsberg, *Parametric Proof-Carrying Compilation for Quantum Error-Correction*, arXiv 2611.12985v1, 2026 | PC-QEC: parametric proof-carrying compilation from a CodeML family through a QStab syndrome-extraction program to a QClifford circuit; finite symbolic certificate whose size is independent of code distance; circuit-level code distance $d^{\mathrm{circ}}\geq d$ for every legal size of Surface, unrotated Surface (HGP), Toric, triangular color and Cartesian LP code families under declared single-wire Pauli fault and readout contracts; four extraction schemes (Standard/Flag/Shor/Knill); OCaml consumer checker; Lean 4 mechanization of metatheory and exact distances for canonical Surface, HGP and Toric programs | [V] |
| QDistRnd (GAP package) | Randomized distance estimation | [C] |
| Roffe et al., BP/OSD decoding | Decoders for frontier evaluation | [C] |
| Egorov–Bondesan–Welling, *The END: An Equivariant Neural Decoder*, 2023 | Learned decoders for evaluation | [V] |
| Unitary Foundation QEC Challenge dataset | §11 testbed (566 CSS codes) | [C] |
| Krishnamoorthy et al., *Certified decoding of quantum LDPC codes*, arXiv 2608.25545, 2026 | Degenerate ML as partition-function inference; AIS decoder attaching optimality certificates to every decision (bootstrap test, or exact proof composed with WISH); region-based decoder reproducing exact ML on tested surface-code instances and feasible exact degenerate ML on `[[72,12,6]]`; certificates flag the syndromes where fast decoders should be distrusted | [V] |
| Rowshan, *Metachecks in Bivariate Bicycle Codes: Syndrome Distance, Measurement Faults, and Repair Limits*, arXiv 2609.39121, 2026 | Exact characterization of leading single-measurement-fault ambiguity in BB codes; `[[144,12,12]]` merges 72 syndrome locations into 36 indistinguishable pairs while the 72-qubit BB code distinguishes all single measurement faults. Boundary entry: measurement/DEM-level structure is outside this calculus's state model, so such judgments are `not yet defined`, not `unavailable` | [V] |

**Relevance.** The §11 discipline is right; this is where exact algorithms and their cost
live. Check the §7.2 deletion-distance formula against known deformation bounds before
present it as an obligation, and fix the definition of $d_X, d_Z$ (finite minimum vs.
$\inf$) — it determines how much of WP0/WP2 is real work.

**Distance amplifiers specifics (arXiv 2609.37231v1, HTML read 2026-09-30) — prior
art for the §2.13 algebraic branch and this section's certificate machinery; not a
new operation.** Recorded 2026-09-30. Filed here rather than in §1 because the
load-bearing calculus-facing content is the certificate-based *circuit*-distance
bound; the construction itself is catalogued in §1.

- **Not new algebra.** The construction is the Audoux–Couvreur CSS tensor product:
  two CSS codes as length-two chain complexes, the total complex truncated to its
  central three terms, data `T₂ = (Q₁⊗A₁) ⊕ (Q₂⊗A₀) ⊕ (Q₀⊗A₂)`. This is an
  instance of `spec/TAXONOMY.md` §2.13 (*Algebraic product of code-level objects*,
  Status: Later extension), whose warning — "a naive tensor product of Hilbert
  spaces is not by itself a CSS-code operation" — is precisely the distinction the
  chain-complex truncation supplies. The paper confirms §2.13's stated conditions
  rather than opening a new taxonomy slot.
- **Explicitly not `C-DIRECT-SUM`.** The premise fails: the output qubit set
  overlaps both inputs' qubits, and $\tilde n = n\,n_A + m_Z m_X^A + m_X m_Z^A$,
  $\tilde k = k\,k_A$, with a distance *gain* $\lceil \alpha_P d_P \rceil \le \tilde d_P$
  rather than a `min`. Namespace disjointness (`OPERATIONAL_SEMANTICS.md` §2) and used-set
  disjointness (I3) are unavailable premises here, so the constructor cannot be
  expressed through the MVP expression language.
- **Presentation dependence is a `P-REBASE`-shaped datum.** $\tilde n$ and the
  retained row counts depend on the *displayed row counts* $m_X, m_Z$ of the chosen
  presentation, not on ranks; the recursion is a $3\times 3$ integer matrix on
  $(n, m_X, m_Z)$. The constructor's type therefore has to carry the retained
  presentation as data. `TERM_LANGUAGE.md` §2 records that `P-REBASE` is
  neither command nor quotient in the MVP.
- **Sharpest calculus-facing item: dependent displayed rows.** The construction
  deliberately retains *dependent* displayed rows ("the base-code checks need not be
  independent"). Its own published bookkeeping gives, for the first flagged
  `[[4,2,2]]` step on the `[[18,4,4]]` seed: $n' = 90$, $k' = 8$, and $m_X' + m_Z' =
  108$ retained check rows. The last figure follows from the source's two count
  formulas alone — $n' = n_A n + z_A m_X + x_A m_Z = 72 + (m_X + m_Z)$ fixes
  $m_X + m_Z = 18$, and $m_X' + m_Z' = (x_A + z_A) n + n_A (m_X + m_Z) = 36 + 72 =
  108$ — and agrees with its Table 3 syndrome-auxiliary count. Since
  $\mathrm{rank} H_X + \mathrm{rank} H_Z = 90 - 8 = 82$, **26 of the 108
  displayed rows are dependent**. Under I2/I5 that state is not well-formed as
  displayed; it is reachable only after row reduction
  (`OBL-ROW-REPLACEMENT-FACTOR`). This is a concrete instance where the §2.13
  constructor's output falls outside the MVP well-formedness class.
- **Circuit layer is outside the object language.** Staged-joint extraction
schedules, gate orderings, flag placement, fault-response certificates, and
circuit distance $d_{\mathrm{circ}}$ have no representation in
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$; the certificate-multiplication
theorem is judgment transport over circuit fields that do not exist yet. Those
judgments are `not yet defined` at the calculus level. Paper Appendix H is the
sharp witness: code distance doubles to 4 while the certificate reaches only 2 —
code-level and circuit-level judgments are separate claims.
- **Consequence for the ledger.** Probed as `W20` in
`WORKED_EXAMPLES.md`. No scope, obligation, or
claim-status change follows from this entry; §12 citation added.

**PC-QEC specifics (arXiv 2611.12985v1, HTML read 2026-11-14) — prior art for
circuit-level distance certificates and parametric family proofs; not a new
operation.** Recorded 2026-11-14. Filed here rather than in §1 because the
load-bearing calculus-facing content is the certificate-based *circuit*-distance
bound and the parametric family proof; the code families themselves are catalogued
in §1.

- **Not a code transformation.** PC-QEC compiles a code family and its
  syndrome-extraction schedule into a circuit and checks a Hoare derivation
  against it. It does not add, delete, or rebase checks in
  $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$; qubits, namespaces and
  `used` are untouched. Syndrome-extraction circuits, gate orderings, fault
  sites and readout contracts have no representation in the state model, so
  circuit-level distance judgments are `not yet defined` at the calculus level
  rather than `unavailable` — the same boundary as the Liang et al. circuit layer.
- **What it supplies.** A finite symbolic certificate whose size is independent
  of code distance, proving $d^{\mathrm{circ}} \geq d$ for every legal size of
  the Surface, unrotated Surface (HGP), Toric, triangular color and Cartesian LP
  families under a single-wire Pauli fault model and declared record contracts,
  across all four extraction schemes (Standard/Flag/Shor/Knill), plus a matching
  silent execution for the Standard Scheme Surface case. This is an externally
  certified *circuit-level* hypothesis source for exactly the families the
  calculus references (§1), and a worked instance of a parametric family proof
  without enumerating instances.
- **Mechanization.** Lean 4 mechanizes the metatheory and exact circuit-level
  distances for canonical Surface, HGP and Toric programs; the OCaml verifier is
  the trusted checker for symbolic and finite certificates. This is adjacent to
  the §5 substrate candidates (QECLean, Lean-QEC, QECert) but is a verification
  artifact, not a substrate: it mechanizes programs and circuits under fault
  models, not code-state transformations or judgment transport.
- **Boundary preserved.** The paper's circuit-level distance is a different
  claim from the calculus's code-level $d_X, d_Z, d$: its §7.3 matching silent
  failure establishes equality only under the declared record contract, and its
  Table 2 shows extraction-scheme dependence (e.g. interleaved vs. block Shor
  order). This is consistent with the repository's stated non-goals (no circuit
  realizations, no DEM-level distance equality) and with the priced-hypothesis
  boundary (supplied lower bounds are trusted inputs, not validated).
- **Consequence for the ledger.** No scope, obligation, or claim-status change.
  If ever adopted, it would enter as a consumer-side certificate source for
  family distance hypotheses, which is outside the current stopping point
  (certificates are `not yet defined`/deferred per `SCOPE.md` §4). No
  operation ID is minted; no `spec/` artifact is touched.

---

# 7. Agentic and LLM code discovery

| Work | Contribution | Tag |
| --- | --- | --- |
| Yan–Li–Ma–Zhang–Ma–Wang–Hsieh–Du, *OmniQEC: discovering practical quantum error-correcting codes by an AI scientist*, 2026 | LLM orchestrator; slow–fast loop (code-level proxies / circuit-level evaluation); four qLDPC families; beats BB references at smaller qubit budgets | [V] |
| Qian–Li, *Multi-agent discovery of practical quantum LDPC codes*, 2026 | Proposal/review agents, persistent memory, closed-loop evaluation | [V] |
| Romera-Paredes et al., *Mathematical discoveries from program search with large language models* (FunSearch), Nature 625, 2024 | LLM program search with an evaluator | [C] |
| Novikov et al., *AlphaEvolve: A coding agent for scientific and algorithmic discovery*, 2025 | Evolutionary coding agent (white paper) | [V] |
| Lu et al., *The AI Scientist*, 2024 | End-to-end automated research loop | [C] |
| Campbell–Chen–Luk–Fan, *Enhancing LLM-based Quantum Code Generation…*, DAC 2025 | Multi-agent quantum code generation | [V] |
| Jain, `qec-lab` (companion to QECLean, 2026) | Catalog-driven formalization pipeline: 267-code Error-Correction-Zoo catalog with priority scores, dashboard, and four agent operating specs (prioritizer, skeleton-drafter, formalization-runner, moonshot), with failure write-ups as first-class outputs | [V] |
| Bastounis–Circelli–Hansen, *Navier–Stokes lost in translation — why Lean verification of AI autoformalisation does not guarantee correct natural language proofs*, arXiv 2610.08144v1, 2026 | Separates proof-formalisation from faithful semantic translation; documents mistranslations in a Lean-verified proof; DPRM/SCI lower bound on resolving NL presuppositions | [V] |

**Relevance.** OmniQEC already implements the harness proposal's thesis (propose → verify →
allocate → close the loop) in the QEC domain; Qian–Li covers the multi-agent variant;
`qec-lab` demonstrates the formalization-pipeline variant (catalog-driven, agent-operated,
Lean-emitting). So "adaptive agentic QEC discovery" is taken. What none of them has is a
search whose *move language and pruning judgments come from a sound calculus* — see §11.2.

**OmniQEC specifics (arXiv 2607.25865v1, read 2026-09-26) — ammunition for §11.2.**

- **Proxy rank reversal.** Fast loop scores $\Phi_{\rm code}=kd^2/n$; slow loop ranks by
  circuit-level $p_{\rm LER}$ (per round, per logical qubit; BP+OSD, depolarizing $p=0.005$).
  At $N=144$ the best discovered codes score $\Phi_{\rm code}=2.25$ (DeepSeek), $5.56$
  (Claude), $3.36$ (GPT), yet all beat BB $[[72,12,6]]$ ($\Phi=6$) at circuit level; only
  one discovered code exceeds BB $[[144,12,12]]$ ($\Phi=12$) on the proxy. Empirical proof
  that a cheap code-level proxy mis-ranks operational performance.
- **Advantage persists off the search point.** Sweeps over $p\in[0.002,0.01]$ fit
  $p_{\rm LER}\propto p^{\Gamma}$ with $\Gamma=5.20$–$5.60$ vs. $\Gamma=3.79$ for the BB
  reference; the strongest candidate is $29.23\times$ lower LER at $p=0.002$ ($1.66\times$
  at $p=0.01$). Crossover on BB $[[72,12,6]]$ first at budget $N=98$; Claude/GPT surpass
  BB $[[144,12,12]]$ at $N=240$; DeepSeek does not within the explored range.
- **Feedback is the active ingredient.** Ablation, top-five mean $-\log_{10}p_{\rm LER}$ at
  the final iteration (Claude / GPT / DeepSeek): full workflow $4.61\pm0.54$ /
  $5.17\pm0.09$ / $4.07\pm0.28$; fast-loop-only $2.14\pm0.10$ / $3.20\pm0.40$ /
  $0.84\pm0.16$; no feedback $3.86\pm0.66$ / $4.25\pm0.19$ / $2.83\pm1.50$. Overall mean
  suppression $4.27$ with variance $0.79$; removing feedback raises variance to
  $1.24$–$1.26$.
- **Scale.** $T=60$ iterations $\times$ 24 programs $\times$ 20 seeds $\approx 480$
  candidates/iteration screened in the fast loop; 14 budgets $N=20$–$288$; three LLM
  backends (Claude Opus 4.8, GPT-5.5, DeepSeek-V4-Pro).
- **Double-edged for §11.2.** The result indicts *proxies*, but its logic reaches any
  code-level ranking, including the calculus's cheap judgments ($k$, sector distances).
  Two mitigations already latent in the paper: even OmniQEC estimates $d$ decoder-assisted
  (BP+LSD, OSD) rather than exactly, and its ablation shows the value comes from
  ground-truth feedback loops — so the edge must rest on judgments that are expensive or
  sequence-level (§7.2 deletion distance, §4 judgment transport), as §11.2.2 concedes.

**Autoformalisation fidelity (arXiv 2610.08144v1, HTML full text read 2026-10-08;
partial read, scope below) — external precedent for the conformance rule, and one
gap it does not close.**

*Read scope, stated because §12 intake requires it.* Abstract, §1–§3.2, §5, and
Appendix A read in full; §3.3 and §4 read only in summary. The `[V]` tag covers
Examples 2.1, 2.2, 3.1, Remark 3.2, the §5 Meta case, and Theorems A.3/A.4 with
Corollary A.5. It does **not** cover the body of Example 3.3 or the constructions
of §4.1–§4.3; those remain unread and are not relied on below.

- **The distinction the repo already draws, externally sourced.** The paper
  separates translating a proof whose statement is already trusted (success =
  the kernel accepts it) from faithfully translating a whole mathematical text
  (success = the kernel accepts it *and* the meaning is preserved), and argues a
  kernel-clean build certifies only the first. This is external precedent for
  `METHOD.md` claim-work-loop
  step 7 and for `CONFORMANCE.md` §4, both of
  which already state it. Different object (§11.1): the paper's subject is
  prose↔formal for research mathematics; the calculus mechanizes
  code-state↔code-state.
- **The gap it exposes is premise drift, and the conformance rule misses it.**
  In Example 3.1 the natural-language estimate needs $m{+}4$ input derivatives
  while the Lean hypotheses assume $m{+}5$; Remark 3.2 records the same $m{+}4$
  versus $m{+}5$ split recurring across declarations, and `inverse_finiteJets`
  uses mixed rather than torus-only derivatives, making that claim incomparable
  with the source rather than merely weaker. `CONFORMANCE_CONTRACT.md` §2
  diffs **outcomes**. A mechanized layer with strictly stronger hypotheses, or a
  strictly weaker conclusion, reproduces every `W0`–`W16` record exactly, because
  each fixture satisfying the weaker spec hypothesis also satisfies the stronger
  one. Outcome-diff cannot see it. This is a different defect from the
  `used`-disjointness coverage gap closed by `W21`, which was a premise with no
  negative fixture; here every fixture passes and the layer is still wrong. Any
  premise-level or conclusion-level conformance requirement is a schema change
  plus a dated maintainer disposition, not an edit — see §12.
- **Not prior art for the refuse-to-derive row (§10.1), and must not be cited
  there.** The paper's argument concerns *underdetermined* NL input, where
  meaning must be reconstructed. The repository's `unavailable` commitments
  concern a *fully specified* calculus whose downstream consumer would reward
  closing the gap. Different hazard and different structure; recording this as
  prior art would move §10.1's verdict for the wrong reason. It also does not
  support the calculus being unable to close its own gaps: the repo's canonical
  mint (invariant I3), its rule that there is no fresh-name choice anywhere, and
  the FD7 ruling that `steps` is semantically inert remove the name-choice and
  hidden-presupposition sources the paper's lower bound runs on. Cite it as
  external precedent for the *rule*, never as an obstruction to the plan.
- **Overclaim to avoid importing.** `Σ⁰₂`-completeness is a correct DPRM
  encoding and establishes the *existence* of hard instances; it is not a
  statement about translating research mathematics, which the paper does not
  show to be adversarially encoded. The abstract's "harder than any
  computational problem" is therefore a property of the encoding. Importing it
  as a headline limitation of this repository's mechanization path would repeat
  in the opposite direction the error `README` *Status* forbids. Likewise
  Example 3.1 is consistent with the Lean simply not yet encoding a sharper true
  estimate; the authors claim no misstatement of the mathematics, and neither
  should any citation of them here.

---

# 8. Search control and resource allocation

| Work | Contribution | Tag |
| --- | --- | --- |
| Li et al., Hyperband / ASHA; Falkner et al., BOHB | Successive-halving allocation | [C] |
| Shahriari et al., *Taking the Human Out of the Loop: A Review of Bayesian Optimization* | Bayesian optimization / acquisition | [C] |
| Aglietti et al., *FunBO: Discovering Acquisition Functions with FunSearch*, 2024 | LLM-discovered acquisition functions | [V] |
| Multi-armed bandits / best-arm identification | Stopping and allocation theory | [C] |
| Guo et al., *On Calibration of Modern Neural Networks* | ECE; threshold reliability | [C] |
| Okada–Kasai, arXiv 2607.14091v4 §IV-C | Distance-guided forbidden-pattern bank: stored low-weight logical supports normalized under cyclic translation, tested by parity tables before full binary search | [V] |
| Bønnelykke et al., arXiv 2610.13589 §III | **EBBI**: hybrid best-arm identification (beta posteriors on $P_L$ per candidate, credible-interval pruning at $\gamma = 2.5\%$) plus mutation of the current best CD; $\sim 1100\times$ fewer shots than random search at distance 3, and the first CD search reported to be decoder- *and* noise-model-aware | [V] |
| Zhuang–Chen–Wu, *Quantum CSS codes: Decoder-aware multiobjective design and bound-certified selection*, arXiv 2611.14923v1, 2026 (HTML v1, read 2026-11-14) | Fixed-resource CSS design with two objectives (DML failure probability $P_D$ and basis-invariant check weight $B_*$), distance floor $d\geq 3$, component constraint $k_c\geq 1$, two-sided truncation bounds, certified threshold/dominance decisions, and paired equal-budget search comparison. Consumer-side analogue of the certify/prune/re-measure loop; its interval-dominance rule (§III.5) is `B_*'\leq B_*$, $U'\leq L$. | [V] |

**Relevance.** `qldpc-laya` is specialization against these baselines, not a new idea. Name
the baselines (successive halving, a calibrated bandit, BO), not just "fixed vs. LLM-only."
The forbidden-pattern bank is a smaller-scale instance of the same screening problem the
harness faces: reuse observed failure mechanisms to prune later candidates. It is
within-construction (one family, cyclic symmetry), not a cross-family allocation policy.
EBBI is the same shape of machinery pointed at a different space: it too is a
bandit over an exponentially large candidate set that treats the evaluator as a
black box, and its pruning statistic is a confidence interval over a noisy
per-candidate score. It is downstream of the calculus (discovery architecture and
search control are excluded by [`SCOPE.md`](SCOPE.md) §4), so it is named
as a baseline, not a competitor.

---

# 9. Author's own lineage

| Work | Contribution | Tag |
| --- | --- | --- |
| Rennela–Staton, *Classical Control, Quantum Circuits and Linear Logic in Enriched Category Theory*, LMCS 16(1), 2020 | Categorical semantics for quantum circuit languages | [V] |
| Rennela, forthcoming on distance-safe code deformation and composition | Referenced in §1, WP3 | [C] |
| Fujiu–Nagayama–…–Satoh, *Dense packing…*, PRA 113, 042412, 2026 | Dense packing + hook-error | [V] |

**Relevance.** The throughline (categorical semantics → code-level calculus) is the
strongest argument that the calculus is not a re-derivation of gauge fixing; make it
explicit. Import the forthcoming results only as theorems with explicit hypotheses (WP3
already says this). Confirm the Fujiu et al. relationship.

---

# 10. Gap analysis

| Proposal claim | Nearest prior art | Verdict |
| --- | --- | --- |
| "No single small formal language" (§2) | de Beaudrap–Horsman; Paler 2025 | **Withdraw**; restate as state-level/judgment-level. |
| Merge/split/deformation as the operations (§7–8) | Vuillot et al. 2019; Bombin–Martin-Delgado 2009 | **Justify the ordinary-CSS restriction** against gauge fixing. |
| Mechanized soundness (Gate 5, §12) | Huang et al., PLDI 2025 | **Related, different object**; cite and distinguish. |
| Direct sum; $k\pm1$; `addStab` monotonicity (§7.1–7.3) | Elementary stabilizer algebra | **Refinement, not theorem.** |
| Two-sector deletion distance (§7.2) | Deformation distance bounds (§2–3) | **Check against prior art**; may be derivable. |
| Presentation-sensitive state, context $\Pi$ (§3.1) | Not evident | **Candidate novelty**; justify against over-engineering. |
| Judgment transport / conditional permutation (§4) | No direct analog found | **Candidate novelty**; most defensible technical contribution. |
| Family boundary / closure (Q5, Gate 7) | Product/lift/bicycle families (§1) | **Downstream of prior art.** |
| Adaptive search harness | OmniQEC 2026; Qian–Li 2026 | **Architecture overlap**; re-scope. |
| `qldpc-laya` decision model | Allocation literature (§8) | **Reposition** as specialization. |
| Discovery guided by the calculus | OmniQEC/Qian–Li (empirical evaluation only) | **Candidate novelty**; see §11.2. |
| Deliberately underivable judgment (discipline D2, `unavailable` outcomes) | Not evident **in this object**; the *pattern* is standard practice | **Candidate novelty**, conditional — **check performed 2026-10-10, verdict stands for the interaction; two narrower claims now prior art. See §10.1.** |

### 10.1 On the refuse-to-derive row

Added 2026-10-07 (maintainer decision; PR #9 review). This row did not exist,
which had forced the co-author briefing to call the discipline "not a novelty
tier" — the honest reading of the table, but one that under-sold a feature the
project treats as distinctive. The row is now here, so the briefing can call it a
candidate novelty without the briefing overriding this table.

**The verdict is conditional, and the condition is unmet.** Two separate things
are being claimed and they have different standing:

- *The pattern* — sound but deliberately incomplete, with some judgments recorded
  `unavailable` — is unremarkable in its own right. Type systems and static
  analyses routinely under-approximate. No novelty is claimed for the pattern.
- *This instance* — refusing to derive deletion-distance lower bounds and
  equalities in a calculus whose downstream consumer is a submission leaderboard
  — is not evident elsewhere. No direct analog was found.

So the candidate novelty is in the *interaction*, not in the
under-approximation. Stated in one direction only, because two drafts of this
section stated it in opposite ones: the withheld class is lower bounds and
equalities, and the *submitter* is the party with an incentive to overstate them
— the challenge's verifier requires an exhibited logical operator for an upper
bound, and an inflated lower bound is what a submission would gain from. So the
discipline **refuses the claim class the submitter has an incentive to
overstate**. (An earlier draft said the consumer "wants upper bounds while lower
bounds are withheld", which is no tension at all — that is scope, not novelty.)

**Qualification (challenge-rules read, 2026-10-10 — dispositioned: not
load-bearing).** The challenge's rules (`unitaryfoundation/qldpc-challenge`,
clone at `8406d0a`) were read on 2026-10-10. They confirm the witness
requirement and the upper-bound currency, but there is **no lower-bound claim
type in the challenge at all** — its own `research/AUTORESEARCH.md` names the
*upper* bound as "the one that inflates" — so the overstatement gloss above is
**not supported by the consumer's rules**.

**Disposition (2026-10-10, maintainer): this framing is not load-bearing and is
not pursued.** The challenge has its own reasons for how it treats upper and
lower bounds; they are not this repository's claim to make. What the calculus
claims is **a sound calculus and judgment transformations over it** — and the
refusal of deletion-distance lower bounds is *propagational*: an upper bound
survives deletion ($d'\le d$), a lower bound does not, because the child can be
arbitrarily worse. That justification needs no consumer and no incentive story,
and it stands regardless of how any external project scores its submissions.
The gloss above is left in place, superseded by this note rather than edited
away, per `AGENTS.md`; **no artifact should repeat the incentive framing.** The
D-12 verdict is unaffected — it asked whether *prior work* combines a restricted
class with a consumer, and the answer is no.

**Enforcement is currently procedural, not mechanical.** Proposal §6 protects the
registry by *admission discipline*: a card review that checks the `Underivability`
field. The mechanical check is Phase 3's gate, which does not exist yet. Do not
describe the discipline as enforced mechanically until it is.

**The exit condition is the prior-art check owed below**; until it is done this
row is a claim, not a finding, and no artifact may describe the discipline as
established novelty.

**Check performed (2026-10-10, agent; maintainer decision "do the check now").**
Recorded in
`D12_PRIOR_ART_CHECK_2026-10-10.md`.
**Finding: partial — adjacent work exists, the interaction does not.** No work
was found doing *both* legs: refusing a class of judgments by design commitment
*and* motivating that refusal by a downstream party's incentive to overstate the
same class. Leg (a) is essentially unoccupied; leg (b) is well populated
(SV-COMP solves the incentive problem by scoring and witness validation, not by
refusal). **The candidate-novelty verdict stands for the interaction**, in the
narrow wording this row already carries.

**Qualifier (2026-10-15, agent): "leg (a) is essentially unoccupied" above is
narrowed, not reversed.** A QEC-domain instance of the pattern has since been
found and is recorded two paragraphs below; it declines to state a
post-transformation distance in a way that does not reach this row's meaning of
leg (a). The finding above is kept as the 2026-10-10 record of what the search
then returned, per `AGENTS.md`.

**Both nominated analogs tested and cleared** (the row predicted the verdict
might land on prior art via *partial correctness*; it does not — partial vs. total
correctness distinguishes which property is claimed, not a labelled outcome
meaning "intentionally unprovable here"; *soundiness* is disclosure, not
restriction, as §10.1 called it).

**Two narrower claims are now prior art** and are recorded on the check's §4, to
be read before this row is quoted in any wider form: two-sector distance bounds
with an explicit not-delivered register and kernel-checked certificates
(An & Yang, arXiv:2610.03214); and a leaderboard judgment vocabulary with
independently validated witnesses plus scoring that makes overstatement
expensive (SV-COMP rules). Neither displaces *this* row as worded.

**One QEC-domain instance of the pattern now exists, and it does not move the
verdict.** Huang et al., arXiv 2307.02437v2 (read 2026-10-15; §4 above), write
the post-morphing distance of a code transformation as $d_2 \in \mathbb{N}$ —
declined, not forgotten — and then reason about distance per instance. That is
the shape of leg (a)'s refusal, in this literature. What it is not: the refusal
attaches to no rule system and no outcome vocabulary, so it is a per-paper
presentational choice rather than the *commitment about a calculus* that
`unavailable` is — exactly the distinction
`JUDGMENT_LAYER.md` §1 draws between an evaluation
outcome and a claim status. The row's narrow wording — refusing a class **by
design commitment**, in a specified rule system — is untouched, and leg (b) is
unaffected. Recorded here because a reader who meets this paper elsewhere would
otherwise have no way to tell that §10.1 had considered it.

**Limits of the finding, on the record:** a negative literature result. Paywalled
venues were not full-text searched, non-English venues were not searched, and one
crypto item (Bellare–Ong–Schneider *Tighten-and-Proof*) is unverified and not
counted. Read as *no prior art found*, not *no prior art exists*. Separately,
**this row's consumer is named, but its incentive rules were not read in this
check** *(corrected 2026-10-10, after an overbroad first draft said the consumer
was unnamed)*: `unitaryfoundation/qldpc-challenge` is identified in four
artifacts, including `EPISTEMIC_LAYERS_CROSSWALK_2026-10-04.md`,
which maps this repository's claim vocabulary onto the challenge's own
certificate schema. Leg (b) was therefore assessed against *this repository's*
description of the incentive rather than against the challenge's published
submission rules — the likeliest place a same-domain interaction could hide, and
a one-repository read to close.

**Prior-art check owed.** What to look for: QEC verification frameworks that
restrict a judgment class by design; conservativity and refinement arguments in
program verification that exclude a property class rather than fail to prove it;
audited-soundness or ‘no false claims’ frameworks in static analysis; and any
formalization of a physics or coding literature that publishes a *deliberate*
gap list alongside its results. If a prior work combines a restricted judgment
class with a downstream consumer that would reward closing the gap, the verdict
moves to **Prior art** and the discipline reverts to a design practice.

**Two close analogs to check first**:

1. ***Partial correctness*** in Hoare logic, which withholds termination by
   design in a setting where essentially every party wants termination. This is
   structurally very close — a sound system refusing a judgment class that its
   consumer has an incentive to assume. **Expect the verdict may land on prior
   art on this row**, which the row above already allows for.
2. ***The soundiness manifesto*** (Livshits et al., CACM 2015), which asks
   analyses to publish their deliberate gaps rather than let silence imply
   completeness. This is about *disclosure* rather than *restriction*, so it is a
   weaker analog — but it is the nearest precedent for publishing an
   under-approximation as a feature, which is half of what this row claims.

**Already-stated limits, not to be dropped when the check is done.** The
repository limits the claim itself, independent of prior art: it is a *registry*
commitment, not a property of the logic (disposition §3.2, where D2 becomes a
registry check rather than a semantic theorem); it attaches to an *evaluation*,
not to a state ; and underivability is declared per-claim in the
`spec/CLAIMS.md` schema, so a claim marked `unavailable` is a recorded
decision rather than a missing derivation.

---

# 11. Competing prior art and the edge

## 11.1 Competing (same object)

1. Gauge fixing unifies the operations (Vuillot et al. 2019) — vs. "first to formalize
   merge/split/deformation."
2. A diagrammatic calculus exists (de Beaudrap–Horsman 2020) — vs. "no language exists."
3. Agentic QEC discovery exists (OmniQEC 2026; Qian–Li 2026) — vs. the harness architecture
   claim.
4. Mechanized code-property certification in Lean 4 exists (QECLean; Lean-QEC, arXiv
   2605.16523) — vs. "mechanized soundness for code transformations." They certify
   parameters of fixed codes; QECLean's concatenation and doubling theorems are the
   nearest mechanized instances of judgment transport — single-constructor, not a term
   language over states.

None addresses a sound, mechanized, code-level transformation calculus.

## 11.2 The edge

An agentic discovery loop whose **move language** is the calculus's typed terms and whose
**guidance signal** is its *sound* derived judgments — not an empirical proxy (empirical
case in point: §7's OmniQEC proxy rank reversal). Versus §7's
systems this gives validity by construction, guaranteed intermediate facts ($k$, sector
distances) that prune without re-verification, and sound composition via judgment transport
(§4). The exchange rate is compute.

Two preconditions, both internal:

1. **The documents firewall it.** The design plan lists "a calculus-to-harness API", "AI or
   Jev integration", and "candidate prioritization" as non-goals and requires the calculus
   to stand alone; `qldpc-laya` trains on search outcomes, not judgments. If the edge is the
   coupling, the firewall must become a specified interface.
2. **The first slice is too thin.** $k\pm1$ and `addStab` monotonicity are microseconds of
   rank arithmetic; soundness buys nothing there. The edge bites only when judgments are
   expensive to compute (the §7.2 deletion distance) or give sequence-level guarantees —
   i.e. contingent on §7.2 and §4.

## 11.3 Internal risks

1. The first slice is folklore; standalone value rests on §4 and §7.2.
2. The edge is firewalled by the project's own documents (§11.2.1) — cheapest to fix.
3. The edge depends on judgments not yet produced (§11.2.2).
4. `qldpc-laya` competes with a mature allocation literature.
5. **Substrate dependency (WP0/Gate 5).** The candidate Lean 4 substrates
   (QECLean; Lean-QEC) are ~1-year-old, single-maintainer repositories. Mitigations:
   pin toolchain and commit (both currently pin `leanprover/lean4:v4.30.0-rc2`);
   prefer kernel-checked results over `native_decide` leaves (QECLean's own
   discipline — its parked branches still carry `native_decide` leaves); and keep
   the calculus's core obligations provable against mathlib alone, so a substrate
   fork or abandonment never blocks Gate 5. The WP0 substrate evaluation owns
   this risk (see `SCOPE.md`, WP0).

---

# 12. Required citations

- [ ] **Vuillot et al., NJP 2019** — deformation = gauge fixing. *Answer: what the
      ordinary-CSS restriction buys.*
- [ ] **de Beaudrap–Horsman, Quantum 2020** — ZX as a surgery language. *Answer:
      process-level vs. state-level with code judgments.*
- [ ] **Huang et al., arXiv 2307.02437** — graphical CSS code transformation in ZX:
      morphing, gauge fixing, code switching. *Answer: diagrammatic/process-level
      vs. state-level with code-property judgments (§4); cite its ⟦15,4,3⟧
      intermediate at `spec/TAXONOMY.md` §4.1–§4.2 as
      external support for the extended-state layer and the logical-witness
      prerequisite, and its $d_2 \in \mathbb{N}$ refusal at §10.1 as a pattern
      precedent that does **not** move that row.*
- [ ] **Huang et al., PLDI 2025** — Coq QEC *program* logic. *Cite as a different object;
      state Lean-4-vs-Coq.*
- [ ] **Lean-QEC (Ehatamm–Lee–Wu–Tao, arXiv 2605.16523)** — verified SAT distance
      certificates in Lean 4. *Cite as different object: parameters of fixed codes vs.
      transformation-soundness; future route for discharging `unavailable` distance
      judgments.*
- [ ] **QECLean (Jain, UW–Madison)** — sorry-free Lean 4 stabilizer/CSS library; toric and
      gross-code distance proofs; CSS concatenation. *Cite as construction-instance
      theorems; candidate mechanization substrate for WP0/Gate 5.*
- [ ] **Bombin–Martin-Delgado 2009** — origin of code deformation.
- [ ] **Bønnelykke et al., arXiv 2610.13589** — Clifford deformations and EBBI.
      *Answer: `E-LOCAL-HADAMARD` (`spec/TAXONOMY.md` §2.12)
      already covers the deformation, and a second-pass red-team finding already named
      XZZX as its non-CSS counterexample — cite to say so, not to mint an
      operation.* Note in the same breath that the objective is
      noise-model- and decoder-relative, so it is not a property judgment this
      calculus makes.
- [ ] **Nelson et al., arXiv 2610.17612** — syndrome partitions for logical-gate
      design. *Cite at the boundary stated in §2: logical-gate realization is
      outside the taxonomy by design and outside scope, and this is the paper
      that fixes the boundary concretely. Cite its logical-Pauli-frame and CAB
      presentation as external support for the `not yet defined`
      logical-witness field (the same field as the §2.10 Gate 6 prerequisite),
      and its §IV.4 check-per-level construction as the candidate source for a
      gate-survival/addressability judgment row. Do **not** cite its Thm 1
      decision procedure as an argument for `OBL-JUDGMENT-SOUNDNESS`; it is a
      decidable predicate about fixed instances, not a soundness theorem about
      a rule system — the same prohibition the 2307.02437 entry carries.*
- [ ] **Sahay–Long–Khemani, arXiv 2609.02999** — chain-map hierarchy. *Cite as
      the homological counterpart to the syndrome-partition condition, when a
      logical-gate admission is ever on the table. `[C]` — unread.*
- [ ] **Yoshioka et al., arXiv 2510.08290** — syndrome-resolved logical gates.
      *Cite as the nearest ansatz neighbour and state the differentiator
      (measurement + conditional feedforward vs. direct preservation).
      `[C]` — unread.*
- [ ] **Dua et al., arXiv 2610.06730** — universal transversal gates for CSS
      codes. *Cite as the partition-distance source behind the §2 definitional
      note. `[C]` — unread.*
- [ ] **OmniQEC 2026; Qian–Li 2026** — agentic qLDPC discovery. *Answer: controller +
      guidance signal (§11.2).*
- [ ] **Tillich–Zémor; Bravyi–Hastings; Panteleev–Kalachev** — add finite-length instances
      (Hong 2026; Menon et al. 2026).
- [ ] **Webster–Jacob–Higgott 2026** — distance algorithms; §11 protocol's ground truth.
- [ ] **Rennela–Staton, LMCS 2020** — author's lineage.
- [ ] **Fujiu et al., PRA 2026** — dense packing / hook-error; state the relationship.
- [ ] **Lee–Okada–Maskara–Kasai–Zhou, arXiv 2609.30069** — ultra-high-rate design
      principles; symplectic halving. *Cite at the extension boundary (taxonomy §4.3,
      WP5 scoping note): non-CSS frontier evidence and the halving/doubling pair.*
- [ ] **Okada–Kasai, arXiv 2607.14091 (v4)** — pair-partition CPM/APM constructions;
      complete distance-verification algorithm. *Cite at taxonomy §3.8 (APM-PP
      specialization note) and the certificate-status discussion (`spec/CLAIMS.md`
      reserved future status); the APM-PP generalization and the Kasai specialization
      are the load-bearing items.*
- [ ] **Liang–Gu–Chen–Eisert–Wang, arXiv 2609.37231** — distance amplifiers;
      fault-response certificates and circuit-distance multiplication. *Cite at
      taxonomy §2.13 (algebraic product of code-level objects) as a worked instance,
      and in §6 for the certificate computation. Cite alongside Audoux–Couvreur,
      *On tensor products of CSS codes* (Ann. Inst. Henri Poincaré D 6(2), 2019) —
      the underlying tensor construction, currently uncited in this repository.*
      State explicitly that the circuit-level layer (extraction schedules, flags,
      $d_{\mathrm{circ}}$) has no representation in the calculus's state model, so
      those judgments are `not yet defined` rather than `unavailable`.
- [ ] **Liang–Eberhardt–Chen, arXiv 2504.08887** — planar qLDPC codes with
      open boundaries; weight-1 stabilizer cleanup (cited as "§III D step 4";
      verified in v4 2026-10-05 as §III.4 step 4 — the v4 reorganization
      renumbered the lettered subsections — plus the §III.5 $r=1$ grafting
      regime). *Cite at
      taxonomy §2.7 (`E-GRAFT`): the $\lvert S\rvert = 1$ row-space-graft
      regime is the row-space form of that cleanup; novelty constraint on the
      Stage A reduction.* **(T11 discharged 2026-10-05: this row's internal
      details verified against v1--v4 latest HTML; the §12 citation obligation
      itself remains open.)**
- [ ] **Yuan, arXiv 2610.02137** — One-Shot any Code. *Cite at taxonomy §2.13
      and the WP5 product scoping note: the $k_A = d_A = 1$ amplifier corner
      preserves distance exactly and cannot move a frontier (Lemma 118: read
      in the paper, verified 2026-10-05 — $H_Q(\bar\Gamma) \cong H_Q(C)$, stated
      as an isomorphism; the T11 qualifier on the §1 row is discharged for this
      paper); the frontier-moving instances need $d_A \ge 2$ — see the $\Phi$
      no-go in `WP5_ALGEBRAIC_PRODUCT_SCOPING.md`
      and the qldpc-challenge fieldnote (PR #2749). The single-shot/decoder
      capability claims have no judgment type in this calculus (`not yet
      defined`, per `an internal note`).*
      **(T11 partially discharged 2026-10-05: this paper; the 2504.08887
      qualifier stands.)** **(Superseded same day, 2026-10-05: the
      2504.08887 half was verified later the same day — v4 HTML §III.4 step 4
      and §III.5 — and T11 is now fully discharged; see
      `REDTEAM_WP5_ROUND1_2026-10-04.md`
      T11.)
- [ ] **qldpc-challenge certificates schema + PR #2753** — three-tier evidence
      stack (`solver` / `proof_log` / `formal`) and the formal-tier ruling.
      *Cite at `spec/CLAIMS.md` reserved `certificate-checked` and Gate
      5; the #2273 caveat (a satisfiable-checkable CNF that asked the wrong
      thing) is the external statement of the encoding-faithfulness gap.*
- [ ] **Krishnamoorthy et al., arXiv 2608.25545** — certified decoding with
      decision certificates. *Cite in §6: external precedent for evidence-
      tiered decisions; evaluation-side, not transformation-side.*
- [ ] **Sound-but-incomplete frameworks** — **new 2026-10-07**, owed as the exit
      condition for the §10 refuse-to-derive row. *Answer: whether any prior work
      combines a deliberately restricted judgment class with a downstream consumer
      that would reward closing the gap. Search QEC verification frameworks that
      restrict a judgment class by design; conservativity and refinement arguments
      that exclude a property class rather than fail to prove it; audited-soundness
      or ‘no false claims’ frameworks in static analysis; formalizations that
      publish a deliberate gap list alongside their results. Outcome moves the
      §10 verdict between **Candidate novelty** and **Prior art**.*
- [ ] **Bastounis–Circelli–Hansen, arXiv 2610.08144** — AI autoformalisation
      mistranslation; `Σ⁰₂` presupposition-resolution lower bound. *Cite in
      `CONFORMANCE.md` as external precedent
      for §4 only, and as the external trigger for its §9 diagnoses CC-G-1 (outcome
      diff is blind to premise and conclusion drift) and CC-G-2 (no outcome label
      for incomparable claims), both **awaiting maintainer disposition** as of
      2026-10-08 (renumbered from `G-1`/`G-2` 2026-10-08, PR #9 review round 4 —
      note-local `G-` prefix, see `AGENTS.md`). Its Example 3.1 is the load-bearing item. Explicitly not cited
      for the §10 refuse-to-derive row above, whose hazard is different in kind;
      see the §7 addendum for that exclusion and its reason.*
- [ ] **Aswanth–Kashyap, arXiv 2610.14192** — CWS lifting of an `[n,k,d]` classical code
      to an `[[n,k,d]]` stabilizer code by random graph choice; an existence
      result with no construction. *Answer: cite at
      `spec/TAXONOMY.md` §3.6/§3.7 as the first concrete
      instance of the §5 `graphs / cellulations` input branch, and at §4 as
      extended-state evidence — the output is not representable as CSS unless
      $k=0$ or $d=1$ (`CWS_NON_CSS_FEASIBILITY_2026-10-15.md`
      §2). Cite its Lemma 1 as a **per-instance** distance check, the pattern of
      the 2504.08887 §III.5 row above — not as a parameter effect. Do not cite
      its GV inequality as an operation precondition: the bound is over the
      existence of a witness the calculus cannot construct.*
- [ ] **Cross–Smith–Smolin–Zeng, arXiv 0708.1021** — the CWS framework the row
      above instantiates. *Answer: cite as the source of the $\mathrm{Cl}_G$
      detection criterion and of “linear classical code $\Rightarrow$ stabilizer
      code.” Uncited until 2026-10-15. The non-CSS finding recorded in that
      note is independent of this paper and rests on no claim of it.*
- [ ] **Leverrier–Zémor, arXiv 2202.13641** — quantum Tanner codes. *Answer:
      cite as the CSS-layer relative of the CWS construction (graph plus
      classical code, CSS output), per
      `Q7_OPEN_FAMILY_READS_2026-10-05.md`
      §2 ($r$-block; closes into the 2-block family only at local length 2).
      **Not read** — this line is opened from the Q7 survey's characterization,
      not from the paper, and the [V] ledger is not to gain an entry for it
      until it is.*
- [ ] **Internal:** reconcile the calculus↔harness firewall with §11.2.

---

# Verification ledger

## Verified [V]

| arXiv ID | Work |
| --- | --- |
| 0903.0566 | Tillich–Zémor, IEEE TIT 60(2), 2014 |
| 1311.0885 | Bravyi–Hastings, STOC 2014 |
| 2411.03646 | Golowich–Guruswami, 2024 |
| 2004.07935 | Evra–Kaufman–Zémor, 2020 |
| 1504.00822 | Leverrier–Tillich–Zémor, FOCS 2015 |
| 2508.10714 | Menon et al., PRX 16, 021014, 2026 |
| 2512.22116 | Wu–Li–Li–Zhai, 2025 |
| 2607.27644 | Hong, 2026 |
| 0704.2540 | Bombin–Martin-Delgado, J. Phys. A 42, 095302, 2009 |
| 1709.02318 | Litinski–von Oppen, Quantum 2, 62, 2018 |
| 2504.10591 | Herzog–Berent–Kubica–Wille, QCE 2025 |
| 2404.18369 | Tan–Niu–Gidney, ISCA 2024 |
| 2511.06758 | Fujiu et al., PRA 113, 042412, 2026 |
| 2405.06941 | Yin et al., 2024 |
| 2607.01473 | Lin et al., 2026 |
| 1810.10037 | Vuillot et al., NJP 21, 033028, 2019 |
| 1404.5504 | Bombin, PRX 5, 031043, 2015 |
| 1412.5079 | Bombin, NJP 18, 043038, 2016 |
| 2010.09626 | Higgott–Breuckmann, PRX 11, 031039, 2021 |
| 1704.08670 | de Beaudrap–Horsman, Quantum 4, 218, 2020 |
| 2012.13966 | van de Wetering, 2020 |
| 2204.13228 | Cowtan, 2022 |
| 2511.22290 | Paler, 2025 |
| 1912.11503 | Hanks et al., PRX 10, 041030, 2020 |
| 2504.07732 | Huang et al., PLDI 2025 |
| 1912.02250 | Hietala et al., POPL 2021 |
| 1803.00699 | Rand–Paykin–Zdancewic, EPTCS 266, 2018 |
| 2605.16523 | Lean-QEC: Ehatamm–Lee–Wu–Tao, 2026; repo `VerifiedQC/Lean-QEC` |
| — (repo) | QECLean, `Stavan-Jain/QECLean` + `qec-lab`; gross `[[144,12,12]]` d=12, toric `[[2L²,2,L]]`, CSS concatenation |
| — (repo) | inQWIRE/LeanQuantum; bit-flip and Shor-9 stabilizer codes |
| — (repo) | Ruizsolveall/Project_qec_lean; CSS ↔ chain complex over F₂ |
| 1711.05159 | Rennela–Staton, LMCS 16(1), 2020 |
| 2603.22532 | Webster–Jacob–Higgott, 2026 |
| 2607.25865 | Yan et al., OmniQEC, 2026 |
| 2608.08996 | Qian–Li, 2026 |
| 2506.13131 | Novikov et al., AlphaEvolve, 2025 |
| 2504.14557 | Campbell et al., DAC 2025 |
| 2611.12985 | Ye–Palsberg, PC-QEC, 2026 |
| 2406.04824 | Aglietti et al., FunBO, 2024 |
| 2304.07362 | Egorov–Bondesan–Welling, 2023 |
| 2607.14091 | Okada–Kasai, pair-partition CPM, 2026 (v4 read 2026-09-29: APM-PP, Kasai specialization, complete distance algorithm, factorial bound) |
| 2609.30069 | Lee–Okada–Maskara–Kasai–Zhou, design principles + symplectic halving, 2026 (HTML v1, read 2026-09-29) |
| 2609.37231 | Liang–Gu–Chen–Eisert–Wang, distance amplifiers + fault-response certificates, 2026 (HTML v1, read 2026-09-30) |
| 2504.08887 | Liang–Eberhardt–Chen, planar qLDPC open boundaries + weight-1 cleanup, 2025 (v4 abstract read 2026-10-04; **v4 HTML full text read 2026-10-05** — §III.4 step 4 weight-1 cleanup and §III.5 lattice grafting/$r=1$ regime verified; T11 fully discharged) |
| 2610.02137 | Yuan, One-Shot any Code, 2026 (v1 abstract read 2026-10-04; **v1 HTML full text read 2026-10-05** — Def. 104/111/116, Eq. 249, Lemma 118, Thm. 81, Remark 39 verified against arXiv HTML v1; count formulas cross-checked against the qldpc-challenge fieldnote PR #2749, which this repo reads as an external secondary source, not repository evidence) |
| 2608.25545 | Krishnamoorthy et al., certified decoding of qLDPC codes, 2026 (v1 abstract read 2026-10-04) |
| 2609.39121 | Rowshan, metachecks in BB codes, 2026 (v2 abstract read 2026-10-04) |
| 1512.07081 | Audoux–Couvreur, On tensor products of CSS Codes, 2018 (v3 abstract read 2026-10-04; resolves the former [C] entry) |
| 2610.08144 | Bastounis–Circelli–Hansen, Navier–Stokes lost in translation, 2026 (HTML v1, read 2026-10-08, **partial**: abstract, §1–§3.2, §5, Appendix A in full; §3.3 and §4 in summary only — the [V] tag does not cover them) |
| 2307.02437 | Huang–Li–Yeh–Kissinger–Mosca–Vasmer, *Graphical CSS Code Transformation Using ZX Calculus*, 2023 (HTML v2, read 2026-10-15 — §2.2 Eq. 3/5/7, §3.1 Def. 3.1, §3.2 Prop. 3.1, §4 Def. 4.1/Proc. 4.1/Ex. 4.1, §5 Prop. 5.2 and Lem. 5.1 verified against the arXiv HTML; the [V] tag does not cover the proof figures, which were read as rendered images and captions only) |
| 2610.13589 | Bønnelykke–Joecker–Krogstrup–Michal–Svendsen, decoder- and noise-aware CD optimization (EBBI), 2026 (HTML v1, read 2026-10-12, **partial**: abstract, §I–§IV.3 in full; Appendices A–H in summary/listings only — the [V] tag covers the §II deformation-set claims, §III EBBI, §IV results and Table 3/4 readings, and **does not** cover the Appendix D 6→3 reduction proof, which is cited from its section title and statement only) |
| 2610.17612 | Nelson–Danageozian–Cao–Economou–Barnes, syndrome partitions for logical-gate design, 2026 (HTML v1, read 2026-10-15, **partial**: abstract, §I–§VI in full, including Thm 1, Cor 1–3, Thm 2, the §III search tables, §IV.1–§IV.5 and the reference list; **Appendices A–K read as table-of-contents entries and section titles only** — so the [V] tag does not cover the proofs in App. A (arbitrary-angle preservation, equal-syndrome consequences, higher-level phases, lifting), the search domains in App. B–E, the CAB algebra in App. F–G, the ⟦4m,2m,2⟧ family in App. H, or the Reed–Muller argument in App. K; the §2 rows cite those only from their main-text statements. The Cor 2 bound is taken from its main-text §II.2 argument, which is stated in full there) |

| 0708.1021 | Cross–Smith–Smolin–Zeng, *Codeword Stabilized Quantum Codes*, IEEE TIT 55(1), 2009 (arXiv HTML rendering read 2026-10-15, **partial**: Thm 1 (standard form), Thm 3 (detection criterion), Thm 5 (abelian word operators $\Rightarrow$ stabilizer code), Lemma 2, and the $\mathrm{Cl}_S$ definition, in full; the §IV ring/double-ring constructions, Table 1, and the encoding circuits were **not** read) |
| 2610.14192 | Aswanth–Kashyap, CWS lifting of an `[n,k,d]` classical code to an `[[n,k,d]]` stabilizer code by random graph choice, 2026 (HTML v1, read 2026-10-15, **in full**: §I–§IV, Definitions 1–4, Lemmas 1–3, Thm 1, Cor. 1–3, all with proofs — the [V] tag covers the paper as read) |
| 2610.21357 | Shalby–Bourassa–Karamlou–Martin–Morvan–Noll–Gidney–Pryadko, stitched surface codes (planar concatenation via GHZ corridors), 2026 (HTML v1, read 2026-10-16, **partial**: abstract, §I–§VI.1 in full — the [V] tag covers the §II.2–II.3 concatenation parameters and Eq. 1, the §III.2 Eq. 8 circuit-distance expression, and the §IV graphlike-decomposition requirement; §VI.2–VII and Appendices A–E not read) |
## 7. Recent scan (2026-11-09) — candidate transformations and constructions

Recorded from a web scan (arXiv quant-ph, 2026; GitHub). Full triage in
`an internal note`. None of these discharges
an obligation or changes a claim status; they are prior art and placement input.

| Work | Contribution | Tag |
| --- | --- | --- |
| Wang–Krastanov, *Local Clifford equivalence to CSS codes: Polynomial-time classification and conversion*, arXiv 2610.28737, 2026 | Deterministic polynomial-time algorithm deciding whether an arbitrary stabilizer code is locally Clifford-equivalent to a CSS code, constructing the single-qubit Clifford and CSS checks when it is; preserves parameters and check sparsity for qLDPC codes; graph-state bipartite criterion in the local-complementation orbit. **CSS-recovery instance of `X-LOCAL-CLIFFORD` (taxonomy §4.4)** — supplies the missing decision procedure and construction. | [V] |
| Yuan–Baspin, *Non-CSS Quantum Code Embedding*, arXiv 2608.16995, 2026 (builds on Yuan, Phys. Rev. A 113, 022438, 2026) | Generalises the mapping-cone embedding framework from CSS to arbitrary stabilizer codes; enables non-CSS logical measurements, weight reduction and Euclidean embedding for non-CSS inputs. | [V] |
| Yuan–Baspin–Williamson, *Quantum Weight Reduction with Layer Codes*, arXiv 2603.04883, 2026 (with Hastings, arXiv 2102.10030; arXiv 2410.10194) | Maps any stabilizer code to a 3-local subsystem code via layer codes and a typed Tanner-graph embedding. **Candidate extended-state operation `X-WEIGHT-REDUCTION` (taxonomy §4.6).** | [V] |
| Wang et al., *Decoupling 2D translation-invariant topological CSS codes*, arXiv 2608.09915, 2026 | Local-unitary decoupling of every 2D translation-invariant topological CSS code into toric codes + product states, via the maximal anyon-preserving superlattice; efficient algorithm for the decoupling map. Inverse direction of gluing/merge; sibling of `C-DIRECT-SUM`. | [V] |
| Chang et al., *Magic Quantum Code Surgery*, arXiv 2610.03920, 2026 | Deforms a qLDPC code across ancillary qubits to measure a transversal Clifford logical; the deformed code stays LDPC and its distance is preserved up to a constant factor. Code deformation / surgery (already tracked); adds LDPC- and distance-preservation property claims. | [V] |
| Zhang–Wei–Tantivasadakarn, *Coupled-Layer Codes: Beyond Quantum Product Constructions*, arXiv 2608.10069, 2026; and *Coupled-Layer Construction of Quantum Product Codes*, arXiv 2603.08711, 2026 | Unifies tensor and balanced product codes with coupled-layer/topological-phase constructions via excitation condensation specified by an excitation algebra + algebra-preserving map; generalises balanced product by allowing unitary (ZX-duality) balancing, yielding non-CSS codes (fermionic toric code, 3-fermion Walker-Wang); reproduces X-cube and Chamon models. Candidate extension of the balanced-product constructor (`L-BALANCED`, taxonomy §3.4). | [V] |

**Relevance.** C1 is the most directly useful: it gives the `X-LOCAL-CLIFFORD` record an algorithmic witness for its single-qubit CSS-recovery case without promoting the extended-state layer. C3 and C4 are new candidate records (`X-WEIGHT-REDUCTION` added to taxonomy §4.6; `E-SPLIT`/decoupling noted at taxonomy §2.11). C2 and C6 extend existing records (mapping cone §2.13; balanced product §3.4) with non-CSS/generalised variants. C5 is prior art for surgery only. None of these discharges an obligation or changes a claim status; the priced-hypothesis and extended-state-layer boundaries stand.

## Check before use [C]

Panteleev–Kalachev (title/venue/ID) ·
Audoux–Couvreur — **resolved 2026-10-04**: arXiv:1512.07081, *On tensor products of CSS Codes* (v3), title/authors/abstract verified on arXiv; moved to the [V] ledger (was: arXiv ID quoted from the reference list of 2609.37231v1, not independently verified) ·
Horsman–Fowler–Devitt–Van Meter (journal/year) ·
Fowler et al. (journal/year) · Bravyi–Cross–Gambetta–Maslov–Rall–Yoder (title/volume) ·
Bacon (volume/page) · Vardy (volume/page) · Prange/Stern/Leon · QDistRnd · Roffe et al. ·
Romera-Paredes et al. (volume/page) · Lu et al. (arXiv ID) · Li et al. Hyperband; Falkner
et al. BOHB · Shahriari et al. · Guo et al. · Bordg–Paulson · Rennela forthcoming ·
Lee, Logical spectroscopy (arXiv 2607.05386 — known only through citing papers) ·
Sahay–Long–Khemani (arXiv 2609.02999 — title/authors and a one-line §I
description taken from 2610.17612's reference list and text; never read here) ·
Yoshioka–Seif–Groszkowski–Cross–Javadi-Abhari (arXiv 2510.08290 — as above) ·
Dua–Holmes–Gullans–Albert (arXiv 2610.06730 — as above). The last three are
tagged `[C]` on that basis deliberately: all three are the nearest-neighbour set
for a future logical-gate admission, and an unread nearest neighbour recorded as
`[V]` is worse than one recorded as `[C]`.
