# CSS Code Calculus

Glossary for the formal calculus of CSS-code constructions and transformations.

## Operation origins

**Code-level transformation**:
An operation whose input is one or more already-formed CSS-code states and whose output is another CSS-code state. Composition and deformation are code-level transformations.
_Avoid_: code operation when the level is ambiguous.

**Lower-level constructor**:
An operation that forms a CSS code from ingredients below the CSS-code level, such as classical codes, matrices, group algebras, graphs, or cellulations. Lower-level constructors are part of the taxonomy but are a later calculus layer.
_Avoid_: composition when the inputs are not already CSS codes.

**Composition**:
A code-level transformation that combines two or more code states, or a later lower-level constructor that combines structured ingredients, to form a new CSS code without being primarily a reduction of one existing code.
_Avoid_: construction as an undifferentiated synonym for every operation.

**Deformation**:
An operation that modifies an existing CSS code's stabilizers, qubits, interfaces, or related structure to form a new CSS code. Its defining input is an existing code state.
_Avoid_: layout change when the stabilizer code itself is unchanged.

**Standard CSS state**:
A finite qubit namespace together with binary X- and Z-type stabilizer row spaces satisfying X orthogonal to Z. The calculus does not impose X intersection Z equals zero; valid CSS-generated stabilizer groups may contain Y-type products.

**Phase-insensitive CSS check structure**:
The MVP representation of a standard CSS state. It records supports, row spaces, displayed independent generators, and stable generator identifiers, but quotients out stabilizer signs and phases. It is not a full codespace-with-phase representation.

**Presented state**:
A CSS check structure together with its displayed generator presentation. Presentation data is semantic for presentation-sensitive operations such as selecting a check to delete.

**MVP**:
The planning target consisting of skip, direct sum, single-check deletion, single-check addition, and conventional left-to-right sequencing. Deletion-distance lower bounds and equalities are unavailable in the MVP rather than silently inferred; distance non-increase under deletion is an included upper-bound claim, covering $d_X$, $d_Z$ and the full distance $d$.

**Contract lifecycle**:
The distinction between taxonomy-only, syntax-candidate, transition-defined, state-sound, contract-stated, contract-proved, and mechanized. A draft contract or planned transition is not an admitted or mechanized rule.

**Opaque distance term**:
A distance predicate $d_X$ or $d_Z$ appearing in an assertion. It is not a function of the row space: no rule or procedure may compute a distance from the exact state update, and an assertion equating a distance to an expression over the row space is not well-formed (the research proposal (see REFERENCES.md) *Distance opacity*; ratified.
_Avoid_: any phrasing implying the calculus evaluates a distance, and any future claim of the form "$d$ is a function of the row space", which is unstatable in this language without a release bump.

**Unavailable judgment**:
A property that is deliberately represented as not derivable by the current calculus. It is distinct from a false proposition, an unproved claim, and an implementation failure. Unavailability attaches to evaluations, not to states: a fact about an output state that some other evaluation derives stays admissible.

**Underivability field**:
The card row that states, for one operation, what it deliberately withholds — as a named list with reason and scope, or the explicit word *none*. It is a **positive assertion**, not an omission, and it is what makes unavailability auditable by card review rather than aspirational (required by `spec/CLAIMS.md` §9, added 2026-10-05).
_Avoid_: treating an absent row, or a deferred item, as an underivability claim — deferred is not unavailable.

## State and judgment vocabulary

**Layout**:
A geometric placement of a state's qubits: one coordinate per qubit, a layer count, and optionally a module id per qubit. Ledger data — supplied per code, held beside the state, not part of it. Two states differing only in their layout are the same state.
_Avoid_: geometry as a synonym for the layout, and do not read a layout as a presentation of the code — the layout is a parameter of the code, not a way of writing it down.

**Interaction radius**:
Given a layout, the largest Euclidean diameter of any displayed row's support in that layout. A derived property of the display relative to the layout, in the same sense that max stabilizer weight is a derived property of the display: computed, never stored, never a search. A function of the pair (state, layout), so a state with no layout has no radius.
_Avoid_: radius of the code — the quantity is not a property of the code alone.

**Locality class**:
A verdict computed from the interaction radius against consumer-supplied caps. Not a calculus property: the caps are the consumer's constants, and the class follows from the radius's transport rather than from a cell of its own.
_Avoid_: locality as a property of the code, and do not carry the class as a state field or an inventory property.

**Tanner connectivity**:
The number of connected components of the combined X+Z Tanner graph built from a presented state's displayed rows. A derived, display-relative quantity (like max stabilizer weight): computed by finite traversal, never stored, no hypothesis. Carried exactly under every primitive; not part of $\equiv$.
_Avoid_: connectivity of the code — the predicate is a property of the presentation. The strictly stronger stabilizer-group predicate (the gate's second check) is named separately, not as "full" or "true" connectivity.

**Stabilizer-group connectivity**:
The statement that the stabilizer row space does not split into blocks on disjoint qubit sets, computed by reducing $H_X$ and $H_Z$ separately and unioning the two reduced row sets' supports. Strictly stronger than Tanner connectivity: a direct sum padded with a redundant cross-block check passes the Tanner check and fails this one.
_Avoid_: reducing the combined X+Z mask matrix and calling the result "the" block count — the combined reduction XORs X rows into Z rows and can report a false split.

## Versioned development

**Release**:
A named pin of the calculus over its four version axes: state model, operation set, assertion language, and obligation set. Named `<line>-<ordinal>`.
_Avoid_: version when the pinned axes are meant.

**Line**:
The calculus lineage identified by its state model. A new state model starts a new line rather than superseding an existing one.
_Avoid_: branch, track.

**Conservative extension**:
A change within a line that adds operations, assertions, or proofs without altering any existing derivation.
_Avoid_: backward-compatible change — this guarantees less.

**Re-discharge obligation**:
The obligation, created by every release bump, to re-establish the release's metatheorems against its expanded operation set.
_Avoid_: regression test.
