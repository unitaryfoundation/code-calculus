# Gate-realization candidate rows

**Status:** non-normative design note. It states the two
gate-realization judgment rows of [`ROADMAP.md`](ROADMAP.md),
*Gate-realization verification*, and derives each from the CSS display. The
normative cells and dated hand derivations are in
`spec/JUDGMENT_LAYER.md` §2, §2h, §7.1–§7.4,
`spec/CLAIMS.md`, and
`spec/OPERATIONAL_SEMANTICS.md` §4.37;
where this note and `spec/` touch the same ground, `spec/` wins. The
derivations remain hand derivations (not machine-checked).

**Source.** Nelson, Danageozian, Cao, Economou, and Barnes, *From Syndromes to
Computation: A General Framework for Logical Operations in Quantum
Error-Correcting Codes*, arXiv 2610.17612v1 (13 October 2026). The statements
used are its Theorem 1 and Corollaries 2 and 3, re-read from the HTML version
on 2026-11-13. This note re-derives what it uses for a CSS display, so no
cell below rests on the source's appendix proofs, which
[`PRIOR_ART.md`](PRIOR_ART.md) records as unread.

## 1. Setting

Let $C$ be a well-formed state on $n$ qubits. Each displayed row is a sector
and a support, and it stands for the Pauli operator that applies the sector's
letter on the support. Write $\mathcal{S}(C)$ for the group these operators
generate and $\mathcal{V}(C)$ for the codespace, the common $+1$ eigenspace of
the rows.

For bit vectors $a$ and $b$ of length $n$, write $X(a)$ for the product of
Pauli $X$ over the support of $a$ and $Z(b)$ for the product of Pauli $Z$ over
the support of $b$. Every Pauli operator with a phase is $i^{t}X(a)Z(b)$ for
one triple $(t,a,b)$ with $t\in\{0,1,2,3\}$.

**Lemma 1 (membership).** The operator $i^{t}X(a)Z(b)$ lies in
$\mathcal{S}(C)$ iff $t=0$, the vector $a$ is in the span of the $X$-row
supports, and the vector $b$ is in the span of the $Z$-row supports.

*Derivation.* The rows commute pairwise by I1, so any product of rows can be
ordered with the $X$-rows first. The $X$-rows multiply to $X(a)$ with $a$ the
sum of their supports, the $Z$-rows to $Z(b)$ likewise, and no phase arises.
Conversely each such $X(a)Z(b)$ is a product of rows. $\square$

In particular $-I\notin\mathcal{S}(C)$, so $\mathcal{V}(C)\neq 0$. This is the
sign lemma of ROADMAP (*FD1 is safe here*) in the form the checks below use.

**Lemma 2 (fixing the codespace).** A Pauli operator $P$ with a phase satisfies
$P\psi=\psi$ for every $\psi\in\mathcal{V}(C)$ iff $P\in\mathcal{S}(C)$.

*Derivation.* Elements of $\mathcal{S}(C)$ fix $\mathcal{V}(C)$ by definition.
Conversely, let $\Pi$ be the projector onto $\mathcal{V}(C)$, which is the
average of the elements of $\mathcal{S}(C)$. From $P\Pi=\Pi$ the trace of
$P\Pi$ is positive, so the trace of $Ps$ is nonzero for some
$s\in\mathcal{S}(C)$. A Pauli operator with nonzero trace is a multiple of the
identity, so $P=cs^{-1}$ for a scalar $c$, and $c=1$ because both $P$ and
$s^{-1}$ fix a nonzero vector. $\square$

**Gates.** A *gate* is a list of pairwise commuting Hermitian Pauli operators
$G_1,\dots,G_q$ (the *generators*), signs $\epsilon_j\in\{+1,-1\}$, and angles
$\theta_j\ge 0$. It denotes the unitary

$$
 U=\prod_{j=1}^{q}\exp(i\epsilon_j\theta_j G_j),
$$

which is the source's ansatz with its sign and angle convention. A gate is
not state data and no command produces one: it is a parameter of the
predicate below. The gate *preserves* $C$ when $U$ maps $\mathcal{V}(C)$ into
itself.

**Lemma 3 (preservation at $\pi/4$).** Let every angle be $\pi/4$. For a
displayed row $g$, let $J(g)$ be the set of indices $j$ such that $G_j$
anticommutes with $g$, and let

$$
 V_g=\prod_{j\in J(g)} i\epsilon_j G_j .
$$

Then $U^{\dagger}gU=gV_g$, and the gate preserves $C$ iff
$V_g\in\mathcal{S}(C)$ for every displayed row $g$.

*Derivation.*

1. *One rotation.* Let $R=\exp(i\epsilon(\pi/4)G)$. If $G$ commutes with $g$
 then $R^{\dagger}gR=g$. If $G$ anticommutes with $g$ then
 $gR=R^{\dagger}g$, so $R^{\dagger}gR=gR^{2}=g\exp(i\epsilon(\pi/2)G)
 =g(i\epsilon G)$.
2. *The family.* The generators commute, so each rotation commutes with every
 factor $i\epsilon_jG_j$. Conjugating $g$ by the rotations one at a time
 and applying step 1 at each gives $U^{\dagger}gU=gV_g$.
3. *Preservation.* The gate preserves $C$ iff $gU\psi=U\psi$ for every row
 $g$ and every $\psi\in\mathcal{V}(C)$, that is iff $gV_g\psi=\psi$ by step
 2. Since $g\psi=\psi$ and $g^{2}=I$, this says $V_g\psi=\psi$. The operator
 $V_g$ is a Pauli operator with a phase, so Lemma 2 gives the claim.
 $\square$

Step 2 and the first equivalence of step 3 are the source's Theorem 1 at
angle $\pi/4$, where its check-conditioned unitary is the Pauli operator
$V_g$. When all generators have one common nonzero syndrome, every $J(g)$ is
empty or everything, and the condition is the stabilizer-factorization
condition of its Corollary 3. By Lemma 1 the condition is decidable from the
display: two span-membership tests and one phase per row.

## 2. Candidate row A: gate survival

**Property.** For a fixed gate $U$, the predicate *$U$ preserves the state*.
Its carrier would be the span, since it depends on $\mathcal{S}(C)$ only. It
is a predicate with a parameter that is not state data, which the assertion
language does not have today.

**Candidate cells.** Evidence in brackets refers to this note only.

| Transition | Candidate verdict | Condition |
| --- | --- | --- |
| `C-SKIP` | carries | none |
| `C-ADD-CHECK`, adding the row $s$, every generator commuting with $s$ | carries, at every angle `[derived, §2.1]` | none beyond the stated commutation |
| `C-ADD-CHECK`, adding the row $s$, all angles $\pi/4$ | carries iff $V_s\in\mathcal{S}(C')$ for the child $C'$ `[derived, §2.1]` | one membership test at the added row |
| `C-ADD-CHECK`, a generator anticommuting with $s$, some angle not $\pi/4$ | `not yet defined` | the condition reads eigenvalues of logical operators, which needs the logical-witness field |
| `C-DELETE-CHECK` | does not carry `[counterexample, §2.2]` | the child's own test of Lemma 3 over its remaining rows decides it at $\pi/4$ |
| `C-DIRECT-SUM`, gate supported on one summand | carries `[derived, §2.3]` | none |
| `C-SEQUENCE` | by composition of the cells above | as the steps |

Addressability is `not yet defined` and this note proposes no cell for it.
The source uses the word for a gate that acts on chosen logical qubits, which
is a statement about a logical frame, and the parts of the source read for
this note do not define it (its §IV.3.3 and §IV.4.3 in full, §IV.4.5 in
summary only). It depends on the logical-witness field.

### 2.1 Addition

Let $C'$ be the child of `C-ADD-CHECK` with added row $s$, and let the gate
preserve $C$. The codespace $\mathcal{V}(C')$ is the set of
$\psi\in\mathcal{V}(C)$ with $s\psi=\psi$.

*Commuting generators, any angle.* If every $G_j$ commutes with $s$ then $U$
commutes with $s$. For $\psi\in\mathcal{V}(C')$ the vector $U\psi$ is in
$\mathcal{V}(C)$, and $sU\psi=Us\psi=U\psi$, so $U\psi\in\mathcal{V}(C')$.

*Angle $\pi/4$.* By Lemma 3 for $C'$, the gate preserves $C'$ iff
$V_g\in\mathcal{S}(C')$ for every row $g$ of $C'$. The rows of $C'$ are the
rows of $C$ and $s$. For a row $g$ of $C$, Lemma 3 for $C$ gives
$V_g\in\mathcal{S}(C)\subseteq\mathcal{S}(C')$. So the gate preserves $C'$
iff $V_s\in\mathcal{S}(C')$. $\square$

The second case contains the first at $\pi/4$, since $J(s)$ is then empty and
$V_s=I$. The source's §IV.4.3 promotes a gate through an outer code by
checking that it preserves the outer stabilizers. That is an instance of the
question this cell answers. This note has not checked the source's instances.

### 2.2 Deletion

On two qubits with rows $X_0X_1$ and $Z_0Z_1$, take generators $X_0$ and
$X_1$ with signs $+1$ and $-1$ at angle $\pi/4$. The row $Z_0Z_1$
anticommutes with both, so $V=(iX_0)(-iX_1)=X_0X_1$, which is in the group,
and the row $X_0X_1$ commutes with both. The gate preserves the state. After
deleting $X_0X_1$ the operator $X_0X_1$ is no longer in the group, and the
gate does not preserve the child. Deletion enlarges the codespace, so
preservation on the parent says nothing about the new vectors.

### 2.3 Direct sum

Let the gate preserve $A$ and act as the identity on the qubits of $B$. The
codespace of $A\oplus B$ is $\mathcal{V}(A)\otimes\mathcal{V}(B)$, and
$U\otimes I$ maps it into itself. $\square$

## 3. Candidate row B: a weight floor that transports by weakening

**Definitions.** The *syndrome* of a Pauli operator $P$ on $C$ is the set of
displayed rows that anticommute with $P$. A family of generators
$G_1,\dots,G_q$ with $q\ge 2$ is *equal-syndrome* on $C$ when all its members
have one common nonempty syndrome. It is *nontrivial* on $C$ when some
product $G_1G_j$ is not in $\mathcal{S}(C)$ up to sign. Write
$w_{\max}$ for the largest weight of a generator of the family, and
$d(C)=\min(d_X(C),d_Z(C))$.

**Lemma 4 (weight floor).** A nontrivial equal-syndrome family on $C$ has
$w_{\max}\ge\lceil d(C)/2\rceil$.

*Derivation.* Take $j$ with $L=G_1G_j$ not in $\mathcal{S}(C)$ up to sign,
and write $L=i^{t}X(a)Z(b)$. The two generators have the same syndrome, so
$L$ commutes with every row: $a$ has even overlap with every $Z$-row support
and $b$ with every $X$-row support. By Lemma 1, $a$ is outside the span of
the $X$-row supports or $b$ is outside the span of the $Z$-row supports. In
the first case $X(a)$ is a logical of the $X$ sector and $|a|\ge d_X(C)$. In
the second $|b|\ge d_Z(C)$. The weight of $L$ is at least $\max(|a|,|b|)$,
hence at least $d(C)$, and it is at most the sum of the weights of $G_1$ and
$G_j$, hence at most $2w_{\max}$. $\square$

This is the source's Corollary 2 for a CSS display. The hypothesis here is
the one its main-text argument uses, and Lemma 4 does not need the gate to
preserve the codespace.

**Property.** Let $\omega(C)$ be the least $w_{\max}$ over the nontrivial
equal-syndrome families on $C$, and $+\infty$ when there is none. Its carrier
would be the span. Lemma 4 says $\omega(C)\ge\lceil d(C)/2\rceil$ at every
state.

**Candidate cell and its transport.** The cell is a lower bound on $\omega$
computed from the ledger interval of $d$: if the interval of $d$ at a state
has lower endpoint $\ell$, the state carries
$\omega\ge\lceil \ell/2\rceil$. The map $\ell\mapsto\lceil\ell/2\rceil$ is
nondecreasing, so the bound is sound at every state where the interval of
$d$ is, with no cell of its own per transition:

| Transition | Effect on the carried floor |
| --- | --- |
| `C-SKIP` | unchanged |
| `C-ADD-CHECK` | does not decrease, since the lower endpoint of $d$ is carried |
| `C-DELETE-CHECK` | recomputed from the child's lower endpoint, which may be smaller: the floor weakens |
| `C-DIRECT-SUM` | recomputed from $\min(d^A,d^B)$ |
| `C-SEQUENCE` | recomputed at each state |

What does not transport is the parent's value. On the nine-qubit Shor code,
$d=3$ and the floor is $2$. Delete the $X$-row on the first six qubits. In
the child, $Z_3$ and $Z_6$ (qubits numbered from $0$) both anticommute with
the remaining $X$-row and with no other row, and $Z_3Z_6$ is not in the
group, so the pair is a nontrivial equal-syndrome family with $w_{\max}=1$.
The child has $d=1$ and its own floor $1$ holds with equality. At angle
$\pi/2$ the pair is the logical operator $-Z_3Z_6$, so it is also a gate
that preserves the child.

This is the shape ROADMAP calls transport by weakening: a claim about one
property whose only content is the image of another property's bound under
a monotone map, re-read at each state, never substituted from the parent.
Whether that is an instance of the monotonicity schema of
`spec/JUDGMENT_LAYER.md` §7.2 or needs a schema
of its own is a question for the decision.

## 4. Evidence

`machine/experiments/gate_realization_rows.py` implements Lemma 1, the test of
Lemma 3, the addition cell of §2.1, and the hypothesis of Lemma 4, and
compares them with an oracle that applies the rotations to state vectors and
uses no Pauli-group reasoning. `machine/test_gate_realization_rows.py` pins
the instances of §2.2 and §3 and a sweep. At seed 452 with 400 random
displays on two to four qubits the sweep compares 400 preservation verdicts
(181 preserving), 161 addition verdicts (92 surviving), 61 commuting
additions at random angles, and 40 nontrivial equal-syndrome families, with
no disagreement, and finds 16 deletions that do not carry the gate out of
236. Agreement is evidence that the derivations are transcribed as stated.
It is not a proof and it confirms no cell (AGENTS.md).

## 5. What the admission settles

1. **A parametrised predicate.** Row A is the operator-indexed predicate
 $\mathsf{preserves}_U(C)$ on CSS displays, admitted as an axis-3
 assertion-language extension (`stdCSS-3` / `v0.3.0`) with its `C-ADD-CHECK`
 carry cell and kernel rows in
 `spec/JUDGMENT_LAYER.md` §2 and §2h
 (derivations in
 `spec/OPERATIONAL_SEMANTICS.md`
 §4.37).
2. **The logical witness.** The cell for an anticommuting generator at an
 angle other than $\pi/4$, the logical action of an accepted gate, and
 addressability all need a logical-frame reading of the logical-witness
 field (`spec/STATE_MODEL.md` §1a)
 and remain `not yet defined`. Row A admits the part that depends on the CSS
 display alone.
3. **The inventory and weakening transport.** Row B adds the equal-syndrome
 generator weight floor $\omega(C) \ge \lceil d(C)/2 \rceil$ to the property
 inventory (`spec/CLAIMS.md`) and carry table
 (`spec/JUDGMENT_LAYER.md` §2, §2h), and
 records transport by weakening as structural schema 6
 (`spec/JUDGMENT_LAYER.md` §7.2): the bound
 $\omega \ge \lceil L_d/2 \rceil$ is the monotone image of the full-distance
 lower endpoint $L_d$, re-read at each state and never substituted from the
 parent.
4. **Scope.** Both rows are stated for a CSS display across the kernel
 primitives. A mixed row needs a sign bit per row (ROADMAP, *Per-row sign*;
 refused for `v0.3.0` under ), and Lemma 1 is false without it.
 The Gate 6 commands and `E-GRAFT` are not covered.

Neither row mints an operation identifier, since a gate leaves the state
unchanged (`spec/TAXONOMY.md` §3.8).

## 6. Completion note

Both rows are stated with their cells and derivations for a CSS display (§2,
§3; `spec/OPERATIONAL_SEMANTICS.md`
§4.37) and recorded in
`spec/JUDGMENT_LAYER.md` §2, §2h, §7.1–§7.4
and `spec/CLAIMS.md`, with
consumer support in `machine/intervals.py`
(`DistanceLedger.equal_syndrome_weight_floor`), transcription in
`machine/consumer.json`, and the falsification harness in
`machine/experiments/gate_realization_rows.py`
(`machine/test_gate_realization_rows.py`). Addressability, logical action, and
the non-$\pi/4$ anticommuting `C-ADD-CHECK` branch remain `not yet defined`.
No operation identifier is minted for a logical gate.

---

## Completion note

The four done-when items of the gate-realization row admission are settled and
recorded in `spec/` and `machine/`:

1. **Row A — Gate survival** (`preserves_U`, assertion-language extension, axis 3)
 and the `C-ADD-CHECK` carry-table row. For a fixed commuting Pauli-rotation
 gate \(U = \prod_{j=1}^q \exp(i\epsilon_j\theta_j G_j)\) on \(Q\), the
 operator-indexed predicate \(\mathsf{preserves}_U(C)\) ("\(U\) maps the
 codespace \(\mathcal{V}(C)\) into itself", carrier `span`, CSS displays only)
 is admitted to the `stdCSS-3` / `v0.3.0` assertion language and carry table
 (`spec/JUDGMENT_LAYER.md` §2, §2h, §7.1–§7.4; `spec/CLAIMS.md`; dated hand
 derivations at `spec/OPERATIONAL_SEMANTICS.md` §4.37):
 - across `C-ADD-CHECK` adding row \(s\) with child \(C'\): carries at every
 angle \(\theta_j \ge 0\) when every generator \(G_j\) commutes with \(s\);
 at all angles \(\theta_j = \pi/4\), carries iff \(V_s \in \mathcal{S}(C')\)
 (one stabilizer-membership check at \(s\)); when some \(G_j\) anticommutes
 with \(s\) and some angle is not \(\pi/4\), stays `not yet defined`
 (depends on eigenvalues of zero-syndrome logical operators in a chosen frame);
 - across the remaining kernel primitives: carries across `C-SKIP`, across
 `C-DIRECT-SUM` when \(U\) is supported on one summand, and across
 `C-SEQUENCE` by composition; does not carry across `C-DELETE-CHECK`
 (`false`, two-qubit counterexample in §4.37; at \(\pi/4\) the child's own
 Lemma 3 test over its remaining rows decides it);
 - addressability and the logical action of an accepted gate remain
 `not yet defined` pending a logical-frame reading of the logical-witness
 field (`spec/STATE_MODEL.md` §1a).
2. **Row B — Equal-syndrome generator weight floor** (\(\omega\)) and transport by
 weakening (axis 3). The property \(\omega(C)\) (the least \(w_{\max}\) over
 nontrivial equal-syndrome generator families on \(C\), \(+\infty\) if none;
 carrier `span`) enters the property inventory (`spec/CLAIMS.md`) and carry
 table (`spec/JUDGMENT_LAYER.md` §2, §2h) with the state-wise lower bound
 \(\omega(C) \ge \lceil d(C)/2 \rceil\) (Lemma 4,
 `spec/OPERATIONAL_SEMANTICS.md` §4.37). Transport by weakening — carrying the
 monotone image \(\lceil L_d/2 \rceil\) of the full-distance lower endpoint
 \(L_d\), re-read at each state and never substituted from the parent (refuted
 by the nine-qubit Shor-code deletion counterexample in §4.37) — is recorded
 as a claim shape in `spec/CLAIMS.md` and as structural schema 6 in
 `spec/JUDGMENT_LAYER.md` §7.2, and is implemented on the consumer ledger as
 `DistanceLedger.equal_syndrome_weight_floor` (`machine/intervals.py`).
3. **No operation identifier is minted for a logical gate.** A logical gate
 leaves \(C = (Q, X, Z, \mathsf{pres}, \mathsf{used})\) unchanged and has no
 state update, so it never reaches `spec/TAXONOMY.md` §3.8's bar for a
 taxonomy operation identifier (`spec/TAXONOMY.md` §3.8;
 `spec/JUDGMENT_LAYER.md` §2h).
4. **Consumer transcription and tests.** `machine/consumer.json` transcribes both
 rows under `gate_realization` (`source: spec/JUDGMENT_LAYER.md §2h`).
 `machine/experiments/gate_realization_rows.py` adds `Display.from_code_state`
 and `addition_survival_verdict` for the three-branch `C-ADD-CHECK` cell, with
 unit tests for all three branches and for ledger weakening transport in
 `machine/test_gate_realization_rows.py`.

Addressability, logical action, and the non-\(\pi/4\) anticommuting `C-ADD-CHECK`
branch remain `not yet defined` until a rule reading the logical-witness frame
is admitted.
