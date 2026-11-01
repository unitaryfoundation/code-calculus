import CodeCalculus.State

namespace CodeCalculus

/-- I3 — identifier discipline: live row identifiers are injective, and every
    live row's identifier is in `used`. Canonical mint freshness is the
    separate theorem `canonicalMint_fresh`. -/
def I3 (s : CodeState) : Prop :=
  (s.rows.map Row.id).Nodup ∧
  s.rows.all (fun r => s.used.contains r.id) = true

/-- I4 — sector typing: every displayed row carries exactly one sector label.
    This is structural in the `Row` type, which has a single `sector` field. -/
def I4 (s : CodeState) : Prop :=
  s.rows.all (fun r => r.sector == Sector.X || r.sector == Sector.Z) = true

/-- I5 — valid provenance. Provenance is not a field of the MVP state
    (`steps` is semantically inert), so the invariant is vacuous at this
    layer. -/
def I5 (s : CodeState) : Prop := True

theorem i3_of_list_level {s : CodeState}
    (hIds : (s.rows.map Row.id).Nodup)
    (hUsed : s.rows.all (fun r => s.used.contains r.id) = true) :
    I3 s := by
  exact (And.intro hIds hUsed : I3 s)

theorem i4_trivial (s : CodeState) : I4 s := by
  unfold I4
  induction s.rows with
  | nil => rfl
  | cons r rs ih => simp [List.all, ih]; cases r.sector <;> decide

theorem i5_trivial (s : CodeState) : I5 s := by
  unfold I5
  trivial

end CodeCalculus
