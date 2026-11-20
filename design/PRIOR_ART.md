# Prior Art

**Role:** non-normative literature survey. This document positions
`code-calculus` relative to existing work in algebraic code constructions,
code deformation, gauge fixing, diagrammatic calculi, mechanized QEC
verification, distance certification, and search-guided code discovery. Where
this survey touches the specification, [`spec/`](../spec/) is authoritative.

---

## 1. Algebraic code constructions

| Work | Contribution |
| --- | --- |
| Tillich–Zémor, *Quantum LDPC codes with positive rate and minimum distance proportional to $n^{1/2}$*, IEEE TIT 60(2), 2014 (arXiv:0903.0566) | Hypergraph product (`L-HGP`); first positive-rate family above $\sqrt{n}$. |
| Bravyi–Hastings, *Homological Product Codes*, STOC 2014 (arXiv:1311.0885) | Homological product; good codes, low-weight stabilizers. |
| Panteleev–Kalachev, *Quantum LDPC codes with almost linear minimum distance*, IEEE TIT 68(1), 2022 (arXiv:2012.04068) | Balanced / lifted product (`L-LIFTED`, `L-BALANCED`). |
| Golowich–Guruswami, *…Almost Linear Distance via Homological Products*, 2024 (arXiv:2411.03646) | Conditions under which products preserve distance. |
| Evra–Kaufman–Zémor, *Decodable quantum LDPC codes beyond the $\sqrt{n}$ distance barrier…*, 2020 (arXiv:2004.07935) | High-dimensional expanders. |
| Leverrier–Tillich–Zémor, *Quantum Expander Codes*, FOCS 2015 (arXiv:1504.00822) | Linear-time decoding. |
| Bravyi–Cross–Gambetta–Maslov–Rall–Yoder, *High-threshold and low-overhead fault-tolerant quantum memory*, Nature 627, 2024 (arXiv:2308.07915) | Bivariate bicycle (BB) codes. |
| Menon et al., *Magic tricycles…*, PRX 16, 021014, 2026 (arXiv:2508.10714) | Tricycle codes. |
| Wu–Li–Li–Zhai, *General Construction of QECCs from Multiple Classical Codes*, 2025 (arXiv:2512.22116) | $D$-input hypergraph-product generalization. |
| Hong, *Quantum LDPC codes with design rate 1/5…*, 2026 (arXiv:2607.27644) | Finite-length balanced-product instances. |
| Okada–Kasai, *Pair-Partition Constructions for CPM-Based Quantum LDPC Codes*, arXiv:2607.14091v4, 2026 | CPM pair-partition CSS construction (and APM-PP affine-map extension, Kasai block-row specialization, complete branch-and-bound distance algorithm, factorial bound $d \le (J+1)!$, and 36 exact-distance codes). |
| Lee, *Logical spectroscopy: lifted-product codes with addressable bases*, arXiv:2607.05386, 2026 | Packet-decomposed canonical logical bases for lifted-product codes. |
| Lee–Okada–Maskara–Kasai–Zhou, *Design Principles for Ultra-High-Rate Quantum Codes*, arXiv:2609.30069, 2026 | Template/degree/lift design coordinates, **symplectic halving** of CSS parents with a fixed-point-free ZX duality (`X-SYMPLECTIC-HALVE`), and low-weight canonical logical bases. |
| Audoux–Couvreur, *On tensor products of CSS codes*, Ann. Inst. Henri Poincaré D 6(2), 239–287, 2019 (arXiv:1512.07081) | CSS tensor product (`A-PRODUCT`) via central truncation of the total chain complex and logical-overlap criteria. |
| Liang–Gu–Chen–Eisert–Wang, *Ultra-high-distance quantum memories from amplified qLDPC codes*, arXiv:2609.37231, 2026 | Recursive CSS tensor-product "distance amplifiers" (`Q ⊗ A`) with staged-joint syndrome-extraction schedules and fault-response certificates. |
| Liang–Eberhardt–Chen, *Planar quantum low-density parity-check codes with open boundaries*, arXiv:2504.08887v4, 2025 | Boundary anyon condensation plus lattice grafting (§III.4 step 4 single-qubit stabilizer cleanup and §III.5 $r=1$ grafting with per-instance distance checking). |
| Yuan, *One-Shot any Code*, arXiv:2610.02137, 2026 | $m$-sheet hollowed-tensor level map (`spec/JUDGMENT_LAYER.md` §2j) giving single-shot codes with $k' = k$ (Lemma 118) and $n$ inflated beyond $m \cdot n$. |
| Shalby–Bourassa–Karamlou–Martin–Morvan–Noll–Gidney–Pryadko, *Stitched surface codes: planar concatenation through GHZ corridors*, arXiv:2610.21357, 2026 | Planar concatenation (`A-CONCAT`) of four rotated surface-code patches under $[[4,2,2]]$, showing circuit distance $d_{\mathrm{circ}} = \min(2t, r_v + 3)$ can sit below code distance. |
| Hsin, *Twisted Compactification, Quotient Quantum Codes and Logical Gates*, arXiv:2611.09538, 2026 | Unifies balanced-product, BB, genon, and five-qubit codes as **monomial quotients** (`A-QUOTIENT` specialization, [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2i) alongside non-Pauli **dressed quotients** (`X-DRESSED-QUOTIENT`). |
| Cross–Smith–Smolin–Zeng, *Codeword Stabilized Quantum Codes*, IEEE TIT 55(1), 433–438, 2009 (arXiv:0708.1021) | The CWS framework: a graph state plus a classical code supplies Pauli-$Z$ word operators and a linear detection criterion $\mathrm{Cl}_S(E)$. |
| Aswanth–Kashyap, *Lifting an $[n,k,d]$ Binary Linear Code to an $[[n,k,d]]$ Quantum Stabilizer Code*, arXiv:2610.14192, 2026 | Existence lower bound for random-graph CWS lifting; outputs are generally non-CSS. |
| Zhang–Wei–Tantivasadakarn, *Coupled-Layer Codes: Beyond Quantum Product Constructions*, arXiv:2608.10069 / arXiv:2603.08711, 2026 | Unifies tensor and balanced products with coupled-layer excitation condensation, including unitary (ZX-duality) balancing yielding non-CSS codes. |

### Key structural takeaways for the calculus

- **Symplectic halving (`arXiv:2609.30069`) and Kasai block-row selection (`arXiv:2607.14091v4`):** Symplectic halving maps a CSS parent with a fixed-point-free duality $\pi$ ($\pi(S_X) = S_Z$) to a compact non-CSS stabilizer code ($n' = n/2$, $k' = k/2$, $\lceil d/2 \rceil \le d' \le d$), motivating the deferred extended-state pair `X-SYMPLECTIC-HALVE` / `X-SYMPLECTIC-DOUBLE`. Similarly, Kasai block-row selection extracts a CSS substate from a non-CSS parent check pair.
- **Quotient vs. dressed quotient (`arXiv:2611.09538`):** Monomial quotients act by free qudit-permutation and single-qudit Clifford actions, matching the state update of `A-QUOTIENT` (with a Tate-cohomology transfer theorem in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2i). Dressed quotients apply entangling diagonal circuits over higher-form backgrounds and produce non-Pauli commuting-projector codes (`X-DRESSED-QUOTIENT`), placing them in the deferred extended-state layer.
- **Distance amplifiers (`arXiv:2609.37231`):** Instantiate the Audoux–Couvreur central-truncation CSS tensor product (`A-PRODUCT`). Because their output retains dependent check rows and depends on displayed row counts $(m_X, m_Z)$, the calculus models `A-PRODUCT` with explicit independent-display retention and does not represent circuit-level extraction schedules or $d_{\mathrm{circ}}$.

---

## 2. Code deformation, surgery, and logical-gate realization

Two distinct kinds of operation appear in this literature:

1. **State-changing deformations** modify the checks or qubits of $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$.
2. **Logical-gate realizations** leave $C$ unchanged and ask which logical unitaries preserve the codespace and what physical circuits implement them. Because [`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §1 and [`SCOPE.md`](SCOPE.md) §4 exclude circuit realizations from the state-transition language, logical gates enter only through codespace-preservation predicates ($\mathsf{preserves}_U$) rather than state transitions.

| Work | Contribution |
| --- | --- |
| Bombin–Martin-Delgado, *Quantum Measurements and Gates by Code Deformation*, J. Phys. A 42, 095302, 2009 (arXiv:0704.2540) | Origin of code deformation (cut-and-paste). |
| Horsman–Fowler–Devitt–Van Meter, *Surface code quantum computing by lattice surgery*, NJP 14, 123011, 2012 | Merge and split of logical patches. |
| Fowler–Mariantoni–Martinis–Cleland, *Surface codes: Towards practical large-scale quantum computation*, PRA 86, 032324, 2012 | Defect movement, hole punching, and grafting. |
| Litinski–von Oppen, *Lattice Surgery with a Twist*, Quantum 2, 62, 2018 (arXiv:1709.02318) | Twist defects in lattice surgery. |
| Herzog–Berent–Kubica–Wille, *Lattice Surgery Compilation Beyond the Surface Code*, QCE 2025 (arXiv:2504.10591) | Code substrates and compilation as routing. |
| Tan–Niu–Gidney, *A SAT Scalpel for Lattice Surgery*, ISCA 2024 (arXiv:2404.18369) | LaSsynth: SAT synthesis of surgery subroutines. |
| Fujiu–Nagayama–Nishio–Kawaguchi–Satoh, *Dense packing of the surface code…*, PRA 113, 042412, 2026 (arXiv:2511.06758) | Dense packing as deformation and hook-error scheduling. |
| Yin et al., *Surf-Deformer*, 2024 (arXiv:2405.06941) | Deformation as composable instructions. |
| Lin et al., *Surface code logical operations on a superconducting quantum processor*, 2026 (arXiv:2607.01473) | Experimental merge, split, expansion, and deformation. |
| Chang et al., *Magic Quantum Code Surgery*, arXiv:2610.03920, 2026 | Deforms a qLDPC code across ancillas to measure a transversal Clifford logical while preserving LDPC structure and distance up to a constant factor. |
| Wang et al., *Decoupling 2D translation-invariant topological CSS codes*, arXiv:2608.09915, 2026 | Local-unitary decoupling of 2D translation-invariant topological CSS codes into toric codes and product states. |
| He–Wang–Song–Gu, *Toric codes all the way down: decoupling translation-invariant topological CSS codes in higher dimensions*, arXiv:2610.40592, 2026 | Explicit SUM/SWAP decoupling circuit and obstruction characterization for higher-dimensional translation-invariant CSS codes ([`DECOUPLING_CONSTRUCTOR.md`](DECOUPLING_CONSTRUCTOR.md)). |
| Bønnelykke–Joecker–Krogstrup–Michal–Svendsen, *Decoder- and Noise-Aware Optimization Framework for Clifford-Deformed QEC Codes*, arXiv:2610.13589, 2026 | Per-qubit Clifford deformations $\mathcal{A}_6$ (reduced to $\mathcal{A}_3 = \{I, H, H\sqrt{Z}H\}$ under $p_X=p_Y$ symmetry) and black-box EBBI search. |
| Wang–Krastanov, *Local Clifford equivalence to CSS codes: Polynomial-time classification and conversion*, arXiv:2610.28737, 2026 | Deterministic polynomial-time algorithm deciding whether a stabilizer code is locally Clifford-equivalent to a CSS code (`X-LOCAL-CLIFFORD` recovery witness). |
| Nelson–Danageozian–Cao–Economou–Barnes, *From Syndromes to Computation: A General Framework for Logical Operations in Quantum Error-Correcting Codes*, arXiv:2610.17612, 2026 | Decidable syndrome-partition condition (Thm 1, Cor 2–3) for codespace preservation of commuting multiqubit Pauli rotations ([`GATE_REALIZATION_ROWS.md`](GATE_REALIZATION_ROWS.md)). |
| Sahay–Long–Khemani, *Computing with qLDPC codes by climbing the chain map hierarchy*, arXiv:2609.02999, 2026 | Homological chain-map hierarchy for Pauli, Clifford, and non-Clifford logical operations. |
| Yoshioka–Seif–Groszkowski–Cross–Javadi-Abhari, *Theory and architecture of syndrome-resolved logical gates*, arXiv:2510.08290, 2025 | Weakly transversal logical gates realized probabilistically via syndrome measurement and feedforward. |
| Dua–Holmes–Gullans–Albert, *Qubit CSS codes with universal transversal gates*, arXiv:2610.06730, 2026 | Depth-one disjoint few-qubit logical gate layers and partition-distance formulation. |
| Rabeti–Shirke–Dimitrova–Mahdavifar, *Logically Augmented Quantum LDPC Codes: Construction and Hierarchical Decoding*, arXiv:2611.07062, 2026 | Imposes additional stabilizer constraints on $n_L$ logical qubits of a primary CSS code via an auxiliary Logical Protection Code, giving $[[n, k - n_L + k_L, d_A]]$ (`C-ADD-CHECK` instance). |
| Su–Gidney–et al., *Expurgation and puncturing-as-repair*, arXiv:2611.08744, 2026 | Expurgation (`C-ADD-CHECK`) and puncturing (`E-PUNCTURE`) to repair defective qLDPC stabilizer checks. |

### Relation to specific calculus operations

- **Clifford deformations (`arXiv:2610.13589`):** Modulo phase, the single-qubit Clifford group is $\mathcal{A}_6$. Because the CSS state model is phase-insensitive and pure-sector, the only single-qubit Clifford deformation representable inside CSS is the sector swap `E-LOCAL-HADAMARD`. General non-CSS deformations (such as alternating Hadamards producing XZZX checks) belong to `X-LOCAL-CLIFFORD` in the deferred extended-state layer.
- **Syndrome partitions (`arXiv:2610.17612`):** Motivates the admitted `preserves_U(C)` predicate and equal-syndrome weight floor $\omega(C) \ge \lceil d(C)/2 \rceil$ ([`GATE_REALIZATION_ROWS.md`](GATE_REALIZATION_ROWS.md)). Because CSS displays determine the phase $(-i)^m$ of any product of $X$- and $Z$-rows sharing $m$ qubits, CSS phase-insensitivity does not obstruct CSS gate preservation.
- **Logically augmented CSS codes (`arXiv:2611.07062`):** Directly instantiates `C-ADD-CHECK` with exact $k$-bookkeeping ($k' = k - n_L + k_L$) and non-decreasing distance ($d_A \ge d$).

---

## 3. Gauge fixing

| Work | Contribution |
| --- | --- |
| Vuillot–Lao–Criger–García Almudéver–Bertels–Terhal, *Code Deformation and Lattice Surgery Are Gauge Fixing*, NJP 21, 033028, 2019 (arXiv:1810.10037) | Proves code deformation and lattice surgery are instances of gauge fixing, with a fault-tolerance test. |
| Bombin, *Single-shot fault-tolerant quantum error correction*, PRX 5, 031043, 2015 (arXiv:1404.5504) | Gauge fixing in 3D gauge color codes. |
| Bombin, *Dimensional Jump in Quantum Error Correction*, NJP 18, 043038, 2016 (arXiv:1412.5079) | Dimension switching by gauge fixing. |
| Higgott–Breuckmann, *Subsystem codes with high thresholds by gauge fixing…*, PRX 11, 031039, 2021 (arXiv:2010.09626) | Gauge fixing for thresholds. |
| Bacon, *Operator quantum error-correcting subsystems*, PRA 73, 012340, 2006 | Subsystem-code formalism. |

Gauge fixing provides the unifying operational account for subsystem code
transformations. Because `code-calculus` restricts its core state model to
ordinary CSS codes (`C = (Q, X, Z, pres, used)`) and defers subsystem and
gauge-fixing moves (`X-SUBSYSTEM`, `X-GAUGE-FIX`), it covers a strict subset of
gauge fixing—trading generality for typed presentation tracking, partial
operational semantics, and judgment transport.

---

## 4. Diagrammatic calculi

| Work | Contribution |
| --- | --- |
| Huang–Li–Yeh–Kissinger–Mosca–Vasmer, *Graphical CSS Code Transformation Using ZX Calculus*, arXiv:2307.02437v2, 2023 | Phase-free ZX normal form for CSS subsystem codes, encoder push-through ($EL = PE$), code morphing, and code switching (Steane $\leftrightarrow$ quantum Reed–Muller). |
| de Beaudrap–Horsman, *The ZX calculus is a language for surface code lattice surgery*, Quantum 4, 218, 2020 (arXiv:1704.08670) | ZX spiders match rough/smooth merges and splits; rewrites derive surgery procedures. |
| van de Wetering, *ZX-calculus for the working quantum computer scientist*, 2020 (arXiv:2012.13966) | Survey and completeness of ZX calculus. |
| Cowtan, *Qudit lattice surgery*, 2022 (arXiv:2204.13228) | Qudit lattice surgery and relation to ZX. |
| Paler, *Untangling Surface Codes: Bridging Braids and Lattice Surgery*, 2025 (arXiv:2511.22290) | ZX as a bridge between braids and lattice surgery. |
| Hanks–Estarellas–Munro–Nemoto, *…Braided Circuits Aided by ZX-Calculus*, PRX 10, 041030, 2020 (arXiv:1912.11503) | ZX as an intermediate language for braided circuits. |

ZX-based frameworks provide complete diagrammatic rewrite rules for **linear
maps and circuits**. By contrast, `code-calculus` is a **typed, state-level
term language with code-property judgments**:

- Huang et al. (`arXiv:2307.02437v2`) is the closest code-transforming
  counterpart. However, its code-switching intermediate (e.g. `[[15,4,3]]`
  with explicit gauge/logical partition and physical gauge state) relies on
  logical-witness data outside $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$,
  and ZX completeness for linear maps does not imply soundness of code-property
  transport.
- Notably, Huang et al.'s Def. 4.1 and Proc. 4.1 leave post-morphing distance
  unspecified ($d_2 \in \mathbb{N}$) and verify distance per instance—a
  per-paper analogue of withholding unpriced distance bounds, though without a
  formal outcome vocabulary like `unavailable`.

---

## 5. Mechanized QEC verification

| Work | Contribution |
| --- | --- |
| Huang–Zhou–Fang–Zhao–Ying, *Efficient Formal Verification of Quantum Error Correcting Programs*, PLDI 2025 (arXiv:2504.07732) | Coq assertion and program logic for QEC programs (Veri-QEC; 14-code benchmark). |
| Hietala–Rand–Hung–Wu–Hicks, *A Verified Optimizer for Quantum Circuits* (VOQC/SQIR), POPL 2021 (arXiv:1912.02250) | Verified quantum circuit optimizer in Coq. |
| Rand–Paykin–Zdancewic, *QWIRE Practice: Formal Verification of Quantum Circuits in Coq*, EPTCS 266, 2018 (arXiv:1803.00699) | Quantum circuit language embedded in Coq. |
| Bordg–Paulson et al. | Quantum Hoare logic in Isabelle/HOL. |
| Jain, *QECLean* and `qec-lab` (UW–Madison, 2025–) | Sorry-free Lean 4 stabilizer/CSS/symplectic library; exact distances for toric `[[2L²,2,L]]` and gross `[[144,12,12]]` codes; CSS concatenation and BB doubling; 267-code catalog in `qec-lab`. |
| Ehatamm–Lee–Wu–Tao, *End-to-End Formalization of Quantum Error Correction*, arXiv:2605.16523, 2026 (`VerifiedQC/Lean-QEC`) | Lean 4 stabilizer/CSS formalization with a verified SAT translation for machine-checked distance lower bounds (including `[[90,8,10]]` and `[[70,6,9]]` BB codes). |
| He–Chen–Xiong–Ni–Zhang–Wang, *QECert: Formal Foundations for Quantum Error-Correction Theory in Lean*, arXiv:2611.05047, 2026 (`QudeLeap/Lean-QECert`) | Lean 4 library for asymptotic QEC theory: stabilizer/CSS codes as chain complexes, homology distance, HGP/lifted/balanced/Tanner parameter theorems, and energy barriers. |
| Ye–Palsberg, *Parametric Proof-Carrying Compilation for Quantum Error-Correction*, arXiv:2611.12985, 2026 | PC-QEC: parametric proof-carrying compilation from `CodeML` to `QClifford` with finite symbolic certificates proving $d^{\mathrm{circ}} \ge d$ across Surface, HGP, Toric, and color-code families (Lean 4 metatheory + OCaml checker). |
| Schlesinger et al., *cslib-frontier* (cslib-community, 2026) | Lean 4 library for classical linear codes (including concatenation bounds) and quantum foundations atop Mathlib (no CSS/stabilizer formalization). |
| Adal, *Quantumlib.lean* (inQWIRE LeanQuantum, 2025) | Lean 4 quantum library with `StabilizerCode` structure and bit-flip / Shor-9 verification. |
| *Project_qec_lean* (Ruizsolveall, 2026) | Lean 4 CSS $\leftrightarrow$ length-3 chain complex over $\mathbb{F}_2$ and homology distance. |

Existing mechanized QEC work certifies **programs under error models** (Veri-QEC,
PC-QEC) or **properties of fixed codes and code families** (QECLean, Lean-QEC,
QECert). `code-calculus` instead mechanizes **transformations between code
states** with per-move soundness and judgment transport. Verified SAT distance
certificates (Lean-QEC) and parametric family theorems (QECert, `cslib-frontier`)
are complementary sources of trusted or machine-checked distance hypotheses for
the calculus's conditional cells.

---

## 6. Distance computation, bounds, and hardness

| Work | Contribution |
| --- | --- |
| Vardy, *The intractability of computing the minimum distance of a code*, IEEE TIT 43(6), 1997 | NP-hardness of exact minimum distance. |
| Berlekamp–McEliece–van Tilborg, *On the inherent intractability of certain coding problems*, IEEE TIT 24(3), 1978 | NP-completeness of syndrome decoding (root of the column-weight-three hardness reduction in [`DERIVED_RELATIONS.md`](DERIVED_RELATIONS.md) §3a). |
| Prange / Stern / Leon | Classical information-set decoding (ISD), ancestor of randomized impulse search (RIS). |
| Webster–Jacob–Higgott, *Distance-Finding Algorithms for Quantum Codes and Circuits*, 2026 (arXiv:2603.22532) | Exact (Brouwer–Zimmermann, SAT, MIP) and heuristic (RIS, Stim) distance-finding methods (`QDistEvol`, `codeDistance`). |
| Okada–Kasai, arXiv:2607.14091v4 §V, 2026 | Complete branch-and-bound distance lower-bound certificate for CSS lifts; a completed `None` run certifies $d > W$. |
| Liang et al., arXiv:2609.37231 App. B.2, 2026 | Exact fault-response-certificate computation via shortest-path search over a reduced quotient graph. |
| QDistRnd (GAP package) | Randomized distance estimation. |
| Roffe et al. | BP/OSD decoding for qLDPC evaluation. |
| Egorov–Bondesan–Welling, *The END: An Equivariant Neural Decoder*, 2023 (arXiv:2304.07362) | Learned decoders for evaluation. |
| Krishnamoorthy et al., *Certified decoding of quantum LDPC codes*, arXiv:2608.25545, 2026 | Certified ML decoding with optimality certificates flagging syndromes where fast decoders should be distrusted. |
| Rowshan, *Metachecks in Bivariate Bicycle Codes: Syndrome Distance, Measurement Faults, and Repair Limits*, arXiv:2609.39121, 2026 | Measurement-fault ambiguity characterization in BB codes (outside the code-level state model, so `not yet defined` in the calculus). |
| Unitary Foundation QEC Challenge (`schema/cert.schema.json`) | Three-tier evidence stack (`solver` / `proof_log` / `formal`) for submitted code distances. |

Exact distance computation is intractable in general, and circuit/measurement
fault distances (`d_circ`) live outside the code-level state model. The
calculus's interval consumer ([`machine/intervals.py`](../machine/intervals.py))
propagates supplied lower bounds and witnessed upper bounds through construction
steps, calling on external distance finders only when transported intervals
cannot decide a target.

---

## 7. Agentic discovery and autoformalisation

| Work | Contribution |
| --- | --- |
| Yan–Li–Ma–Zhang–Ma–Wang–Hsieh–Du, *OmniQEC: discovering practical quantum error-correcting codes by an AI scientist*, 2026 (arXiv:2607.25865) | LLM orchestrator with slow–fast loop (code-level proxy $\Phi_{\mathrm{code}} = kd^2/n$ vs. circuit-level $p_{\mathrm{LER}}$), showing proxy rank reversal on BB targets. |
| Qian–Li, *Multi-agent discovery of practical quantum LDPC codes*, 2026 (arXiv:2608.08996) | Multi-agent proposal/review loop with persistent memory and closed-loop evaluation. |
| Romera-Paredes et al., *FunSearch*, Nature 625, 2024 | LLM program search paired with an evaluator. |
| Novikov et al., *AlphaEvolve: A coding agent for scientific and algorithmic discovery*, 2025 (arXiv:2506.13131) | Evolutionary coding agent for scientific and algorithmic discovery. |
| Lu et al., *The AI Scientist*, 2024 | End-to-end automated research loop. |
| Campbell–Chen–Luk–Fan, *Enhancing LLM-based Quantum Code Generation…*, DAC 2025 (arXiv:2504.14557) | Multi-agent quantum code generation. |
| Jain, `qec-lab` (companion to QECLean, 2026) | Catalog-driven Lean formalization pipeline with prioritized code queue and failure write-ups. |
| Bastounis–Circelli–Hansen, *Navier–Stokes lost in translation*, arXiv:2610.08144, 2026 | Distinguishes kernel-checked proof formalization from faithful semantic translation, highlighting premise drift where stronger hypotheses pass outcome-only checks. |

OmniQEC and Qian–Li establish closed-loop agentic QEC discovery, while
Bastounis et al. highlight the gap between kernel acceptance and semantic
faithfulness (premise/conclusion drift). `code-calculus` complements discovery
loops by providing a typed move language and sound interval transport for
sequence-level pruning without re-running expensive distance searches at every
step.

---

## 8. Search control and resource allocation

| Work | Contribution |
| --- | --- |
| Li et al. (Hyperband / ASHA); Falkner et al. (BOHB) | Successive-halving resource allocation. |
| Shahriari et al., *Taking the Human Out of the Loop: A Review of Bayesian Optimization* | Bayesian optimization and acquisition functions. |
| Aglietti et al., *FunBO: Discovering Acquisition Functions with FunSearch*, 2024 (arXiv:2406.04824) | LLM-discovered acquisition functions. |
| Multi-armed bandits / best-arm identification | Stopping and allocation theory. |
| Guo et al., *On Calibration of Modern Neural Networks* | Expected calibration error and threshold reliability. |
| Zhuang–Chen–Wu, *Quantum CSS codes: Decoder-aware multiobjective design and bound-certified selection*, arXiv:2611.14923, 2026 | Fixed-resource multiobjective CSS design with two-sided truncation bounds and interval dominance (`B_*' ≤ B_*`, `U' ≤ L`). |

Search control and budget allocation are downstream of the calculus
([`SCOPE.md`](SCOPE.md) §4). Notably, Zhuang et al.'s interval-dominance rule
is a consumer-side analogue of the certify/prune/re-measure loop.

---

## 9. Positioning and deliberate incompleteness

Across these areas, no prior system combines:

1. a **typed, presentation-sensitive state model** $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$,
2. a **partial operational semantics** for code transformations,
3. **judgment transport** with explicit non-transport (`W13`) across deleted
   generators, and
4. a **four-outcome vocabulary** (`false`, `not derivable`, `unavailable`,
   `not yet defined`) separating refutation from deliberate design exclusion.

### Rationale for `unavailable` and formal-methods analogs

The calculus withholds unpriced deletion-distance lower bounds and equalities as
`unavailable` for a purely propagational reason: an upper bound survives check
deletion ($d' \le d$), whereas a lower bound does not without external pricing
because removing a check can make the child code arbitrarily worse.

In formal methods, the closest precedents for publishing deliberate gaps as
first-class semantics are:

- **Partial correctness in Hoare logic**, which withholds termination by design;
- **The soundiness manifesto** (Livshits et al., CACM 2015), which advocates
  explicitly publishing deliberate under-approximations rather than letting
  silence imply completeness; and
- **Per-instance distance withholding** in Huang et al. (`arXiv:2307.02437v2`),
  which declines to state a general post-morphing distance rule while checking
  distances per instance (without a formal outcome vocabulary).
