# Admissible seams as a regular family

**Status:** non-normative design note. This note explains how the Lean
mechanization of glued-code distances connects to the admissible-seam
certificate in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2e.
Where this note and `spec/` touch the same ground, `spec/` is authoritative.

---

## 1. Admissible seams in the specification

Under [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2e, an admissible
seam certificate for `E-GLUE` (given as identical planar move words over
$\{U, D, L, R\}^*$) certifies that the seam is admissible and that the glued
$Z$-sector distance satisfies

$$
d_Z(Q) = \min(d_A, d_B),
$$

realized by the embedded factor representative.

## 2. Mechanized family-level guarantees

The Lean development under [`lean/CodeCalculus/`](../lean/CodeCalculus/)
mechanizes the algebraic and witness-field structure of this guarantee across
three modules:

### Witness-field characterization (`LogicalWitness.lean`)

For an arbitrary family $F : \mathsf{GlueInstance} \to \mathsf{Prop}$ of
regular instances—where regularity (`GlueInstance.Regular`) requires well-formed
factors and glued state, disjoint qubit namespaces, and sound, complete, and
tight factor witness fields—[`LogicalWitness.lean`](../lean/CodeCalculus/LogicalWitness.lean)
proves:

- `family_glueExact_iff`: on $F$, `GlueExact` holds on every member if and only
  if the transported witness field `CarriesMin` holds on every member (combining
  `glueExact_of_carriesMin` and `glueLog_carries_min_of_logical`).
- `family_exactDistance_eq_min`: if `CarriesMin` holds on every member, then
  $\mathsf{exactDistance}\,\sigma\,(\mathsf{glueState}\dots) = \min(\mathsf{exactDistance}\,\sigma\,a,\; \mathsf{exactDistance}\,\sigma\,b)$
  on every member.

In the $Z$ sector, an admissible seam provides `GlueExact` via the certified
bound, and the transported field carries the surviving embedded factor
representative as a minimum-weight entry (`CarriesMin`).

### Decidable admissibility (`AdmissibleSeamFamily.lean`)

[`AdmissibleSeamFamily.lean`](../lean/CodeCalculus/AdmissibleSeamFamily.lean)
isolates the decidable content that an admissible-seam certificate provides:

- `AdmissibleSeam`: every minimum-weight factor logical survives the seam.
- `admissible_carriesMin`: at the instance level, an admissible seam with
  sound, complete, and tight factor fields yields `CarriesMin`.
- `admissible_family_exactDistance_eq_min`: at the family level, on any family
  of regular instances with admissible seams, the glued distance equals the
  minimum of the factor distances on every member.

### Extraction and `Gate6Exact` bridge (`GlueExtraction.lean`)

[`GlueExtraction.lean`](../lean/CodeCalculus/GlueExtraction.lean) completes
the algebraic side of [`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
§4.31 and §4.33:

- **Equivalence and well-formedness:**
  `evalExpr_glue_iff_evalTerm_glueCommand`, `wf_glueState_of_eval_glueCommand`,
  and `stateK_glueState_add_seams` establish the equivalence of
  `EvalExpr.glue` and `⟨glueCommand seams, directSum (base a) (base b)⟩`,
  deriving output well-formedness from step-by-step seam admissibility.
- **Re-exposure and lower bounds:**
  `reExposedVectors_eq_nil`, `wRe?_eq_none`, `glue_exactDistance?_ge_min`, and
  `glue_theorem4_lower_bound` mechanize $w_{\mathrm{re},\sigma} = +\infty$ and
  the lower bound in `Option Nat`.
- **Class-pair algebra and refutation:**
  `phiSeam_congr`, `phiSeam_linear`, `glue_exactDistance?_ge_add_of_no_pure_survivor`,
  and `glue_universal_min_equality_false` mechanize the linear-algebraic
  class-pair decomposition and the counterexample refuting universal minimum
  equality.
- **Direct `Option Nat` equality and judgment soundness:**
  `admissibleSeam_exactDistance?_eq_min`,
  `admissible_family_exactDistance?_eq_min`, `admissible_carriesMin_glueField`,
  `admissible_family_glueField_exact`, `glue_expr_sound_exact_of_admissible`, and
  `glue_term_sound_exact_of_admissible` derive exact distance equality directly
  from `AdmissibleSeam` (without requiring `HasMinLogical` or `LogField`),
  bridge to `glueField` in [`WitnessFields.lean`](../lean/CodeCalculus/WitnessFields.lean),
  and discharge the certificate premise `hcert` in [`Gate6Exact.lean`](../lean/CodeCalculus/Gate6Exact.lean).

## 3. Remaining mechanization gap

One geometric step remains outside the Lean substrate: deriving
`AdmissibleSeam` (that every minimum-weight factor logical survives) from
identical planar move words $w(c_A) = w(c_B)$ over $\{U, D, L, R\}^*$.
Formalizing that step requires a Lean model of the planar grid and move words
(currently seams are represented as `List (Sector × List Nat)`). Separately,
shared-interface gluing with overlapping qubits lies outside disjoint-namespace
`E-GLUE`.
