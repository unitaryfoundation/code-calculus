import CodeCalculus.CertificateChecker

/-!
# External code ingestion: binding a state to a matrix presentation

A matrix presentation of a CSS code is a qubit count `n` and two lists of
check supports, one per sector, as an external source writes them
(`spec/REPRESENTATION.md` §9). A presentation may list dependent checks. A
`CodeState` may not, so the ingested state retains an independent subset of
the presented rows.

`presentationBinds s p c` is the computable statement that the state `s` is
an ingestion of the presentation `p`. It holds when the qubit list of `s`
is `0, …, n - 1`, every presented support lies in that range, every row of
`s` is a presented row of its sector, and every presented row is the
combination of the rows of `s` in its sector that the coefficients `c`
name. The three theorems below read these facts off an accepted check.
Together they say that the row space of `s` in each sector is the row
space of the presented matrix of that sector.

The generated instances (`IngestedInstances.lean`) discharge
`presentationBinds` by kernel `decide`. The coefficients are supplied by an
untrusted generator and are checked, not trusted. No hash is computed here.
The binding hash of `spec/REPRESENTATION.md` §9 is computed outside Lean
over the `Presentation` literal of the generated module.
-/

namespace CodeCalculus

/-- A matrix presentation: a qubit count and the check supports of each
    sector. -/
structure Presentation where
  n : Nat
  X : List (List Nat)
  Z : List (List Nat)
  deriving Repr, BEq, DecidableEq

/-- The presented supports of one sector. -/
def Presentation.side (p : Presentation) : Sector → List (List Nat)
  | Sector.X => p.X
  | Sector.Z => p.Z

/-- For each presented row of each sector, the coefficients of a combination
    of the retained rows of that sector. -/
structure SpanCoefficients where
  X : List (List Bool)
  Z : List (List Bool)
  deriving Repr, BEq, DecidableEq

/-- The coefficient lists of one sector. -/
def SpanCoefficients.side (c : SpanCoefficients) : Sector → List (List Bool)
  | Sector.X => c.X
  | Sector.Z => c.Z

/-- The presented row `row` is the combination of the σ-rows of `s` that
    `coeffs` names. -/
def rowSpanCheck (s : CodeState) (σ : Sector) (row : List Nat) (coeffs : List Bool) : Bool :=
  coeffs.length == (sectorRows s σ).length &&
    combineRows s.Q.length ((sectorRows s σ).map (rowVector s.Q)) coeffs ==
      supportVector s.Q row

/-- Every presented row has a coefficient list, and each passes
    `rowSpanCheck`. -/
def spanChecks (s : CodeState) (σ : Sector) : List (List Nat) → List (List Bool) → Bool
  | [], [] => true
  | row :: rows, c :: cs => rowSpanCheck s σ row c && spanChecks s σ rows cs
  | _, _ => false

/-- Every σ-row of `s` is a presented row. -/
def retainedCheck (s : CodeState) (σ : Sector) (src : List (List Nat)) : Bool :=
  (sectorRows s σ).all (fun r => src.contains r.support)

/-- The state `s` is an ingestion of the presentation `p`, with span
    coefficients `c`. -/
def presentationBinds (s : CodeState) (p : Presentation) (c : SpanCoefficients) : Bool :=
  s.Q == List.range p.n &&
    (p.X ++ p.Z).all (fun row => row.all (fun q => decide (q < p.n))) &&
    retainedCheck s Sector.X p.X && retainedCheck s Sector.Z p.Z &&
    spanChecks s Sector.X p.X c.X && spanChecks s Sector.Z p.Z c.Z

theorem spanChecks_sound (s : CodeState) (σ : Sector) :
    ∀ (src : List (List Nat)) (cs : List (List Bool)), spanChecks s σ src cs = true →
      ∀ row, row ∈ src → inSpanRows s.Q (sectorRows s σ) (supportVector s.Q row)
  | [], _, _, row, hmem => nomatch hmem
  | r :: rs, [], h, _, _ => by simp [spanChecks] at h
  | r :: rs, c :: cs, h, row, hmem => by
      simp only [spanChecks, Bool.and_eq_true] at h
      cases hmem with
      | head =>
          have hrow := h.1
          simp only [rowSpanCheck, Bool.and_eq_true, beq_iff_eq] at hrow
          exact ⟨c, hrow.1, hrow.2⟩
      | tail _ hrest => exact spanChecks_sound s σ rs cs h.2 row hrest

theorem presentationBinds_parts {s : CodeState} {p : Presentation} {c : SpanCoefficients}
    (h : presentationBinds s p c = true) (σ : Sector) :
    retainedCheck s σ (p.side σ) = true ∧ spanChecks s σ (p.side σ) (c.side σ) = true := by
  simp only [presentationBinds, Bool.and_eq_true] at h
  cases σ with
  | X => exact ⟨h.1.1.1.2, h.1.2⟩
  | Z => exact ⟨h.1.1.2, h.2⟩

/-- The qubit list of an ingested state is `0, …, n - 1`. -/
theorem presentationBinds_Q {s : CodeState} {p : Presentation} {c : SpanCoefficients}
    (h : presentationBinds s p c = true) : s.Q = List.range p.n := by
  simp only [presentationBinds, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1

/-- Every row of an ingested state is a presented row of its sector. -/
theorem presentationBinds_retained {s : CodeState} {p : Presentation} {c : SpanCoefficients}
    (h : presentationBinds s p c = true) (σ : Sector) (r : Row)
    (hr : r ∈ sectorRows s σ) : r.support ∈ p.side σ := by
  have hret := (presentationBinds_parts h σ).1
  simp only [retainedCheck, List.all_eq_true] at hret
  exact List.contains_iff_mem.mp (hret r hr)

/-- Every presented row lies in the span of the rows the ingested state
    retains in that sector. -/
theorem presentationBinds_span {s : CodeState} {p : Presentation} {c : SpanCoefficients}
    (h : presentationBinds s p c = true) (σ : Sector) (row : List Nat)
    (hrow : row ∈ p.side σ) :
    inSpanRows s.Q (sectorRows s σ) (supportVector s.Q row) :=
  spanChecks_sound s σ (p.side σ) (c.side σ) (presentationBinds_parts h σ).2 row hrow

end CodeCalculus
