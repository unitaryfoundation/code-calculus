# Red-team findings adopted into the calculus

This note records red-team findings that changed how a claim must be read, in
public form. Internal finding identifiers are generalized per the sanitization
rules; the normative consequences live in `spec/`.

## Split-subset `E-LOCAL-HADAMARD`

The per-qubit (or subset) Hadamard move `hadamard(T)` preserves the standard-CSS
presentation exactly when both sector row spaces split along `T`:

- for every row \(v\) of \(X\), \(v|_T \in X\);
- for every row \(w\) of \(Z\), \(w|_T \in Z\).

Without this split the image need not be CSS (a physical reading gives a valid
stabilizer code with no pure-sector presentation; a matrix reading breaks
orthogonality under row reordering). The global instance \(T = Q\) exchanges the
two sectors' distances; the empty instance is the identity. See
`spec/TAXONOMY.md` §2.12 and `spec/OPERATIONAL_SEMANTICS.md` §4.27.
