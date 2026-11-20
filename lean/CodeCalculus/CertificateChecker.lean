import CodeCalculus.ExactDistance
import CodeCalculus.ExactPeel

/-!
# The mechanized certificate checker

`spec/CLAIMS.md` admits the evidence status `certificate-checked` for
per-state atomic judgments, attached only through a checker in the proof
assistant whose acceptance is proved to imply the certified fact. This module
is that checker for the kill-certificate format of `machine/certificates.py`.

The certified fact. For a state `s`, a sector `σ`, and a bound `L`, the fact
is `L ≤ d_σ(s)` for the exact sector distance of `ExactDistance.lean`: every
σ-logical of `s` has weight at least `L`. A certificate lists kills. A kill
names a support over `s.Q` and a reason the vector of that support is not a
σ-logical:

* `oddOverlap row`: the vector has odd overlap with the displayed
  opposite-sector row whose support is `row`; or
* `inSpan coeffs`: the vector is the `F₂` combination `coeffs` of the
  displayed σ-rows.

`checkCertificate s c` enumerates the vectors of length `|s.Q|` and weight
below `c.bound` (`ballVectors`) and accepts when each has a kill in `c` whose
reason it validates. It searches for no logical operator and no minimum.

What is proved. `checkCertificate_sound`: acceptance implies that every
σ-logical has weight at least the bound. `certificate_lower_bound`,
`certificate_lower_bound_ext`, and `certificate_lower_bound_nat` restate it
for the three readings of the exact distance. `certificate_equality` adds a
checked witness of weight exactly the bound and concludes
`exactDistance? σ s = some L`.

Scope (a second review pass, `spec/OPERATIONAL_SEMANTICS.md` §4.24). A theorem
obtained from these is keyed to one state, one property (the σ-distance), and
one sector. It is a statement about the Lean term `s`; nothing here relates
that term to a state written elsewhere, and nothing here concerns an operation
contract. The checker does not test well-formedness: the exact distance is
defined for every `CodeState`, and the theorems hold for every one.

Differences from the Python prototype. `check_sector_lower_bound_certificate`
also rejects a non-CSS display, a kill that covers no vector of the ball, and
an invalid kill next to a valid one for the same support. Soundness needs
none of the three, so this checker accepts a superset of what the prototype
accepts on the same state.
-/

namespace CodeCalculus

/-- The reason a vector is not a σ-logical. -/
inductive KillReason where
  | oddOverlap (row : List Nat)
  | inSpan (coeffs : List Bool)
  deriving Repr, BEq, DecidableEq

/-- One kill: a support over the state's qubits and its reason. -/
structure Kill where
  support : List Nat
  reason : KillReason
  deriving Repr, BEq, DecidableEq

/-- A certificate for `bound ≤ d_sector`. -/
structure SectorCertificate where
  sector : Sector
  bound : Nat
  kills : List Kill
  deriving Repr, BEq, DecidableEq

/-- The vector of a support over the qubit list `Q`. -/
def supportVector (Q sup : List Nat) : List Bool :=
  Q.map (fun q => sup.contains q)

/-- The vectors of length `n` and weight below `L`. -/
def ballVectors : Nat → Nat → List (List Bool)
  | _, 0 => []
  | 0, _ + 1 => [[]]
  | n + 1, L + 1 =>
      (ballVectors n (L + 1)).map (fun v => false :: v) ++
        (ballVectors n L).map (fun v => true :: v)

/-- A reason is valid for `v` when it shows `v` is not a σ-logical of `s`. -/
def killReasonValid (s : CodeState) (σ : Sector) (v : List Bool) : KillReason → Bool
  | KillReason.oddOverlap row =>
      (sectorRows s (oppositeSector σ)).any
        (fun r => r.support == row && dotPar v (rowVector s.Q r) % 2 == 1)
  | KillReason.inSpan coeffs =>
      coeffs.length == (sectorRows s σ).length &&
        combineRows s.Q.length ((sectorRows s σ).map (rowVector s.Q)) coeffs == v

/-- The kill names the vector `v` and carries a valid reason for it. -/
def killCovers (s : CodeState) (σ : Sector) (v : List Bool) (k : Kill) : Bool :=
  supportVector s.Q k.support == v && killReasonValid s σ v k.reason

/-- The checker: every vector of weight below the bound has a covering kill. -/
def checkCertificate (s : CodeState) (c : SectorCertificate) : Bool :=
  (ballVectors s.Q.length c.bound).all (fun v => c.kills.any (killCovers s c.sector v))

/-- A witness for the upper endpoint: a σ-logical of length `|Q|` and weight `L`. -/
def witnessValid (s : CodeState) (σ : Sector) (L : Nat) (w : List Bool) : Bool :=
  w.length == s.Q.length && isLogicalBool s σ w && weight w == L

/-! ## The ball is complete -/

theorem mem_ballVectors : ∀ (n L : Nat) (v : List Bool),
    v.length = n → weight v < L → v ∈ ballVectors n L
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, v, hlen, _ => by
      have hv : v = [] := List.length_eq_zero_iff.mp hlen
      subst hv
      exact List.mem_singleton.mpr rfl
  | n + 1, L + 1, v, hlen, hw => by
      cases v with
      | nil => cases hlen
      | cons b bs =>
          have hbs : bs.length = n := Nat.succ.inj hlen
          rw [weight_cons] at hw
          show b :: bs ∈ (ballVectors n (L + 1)).map (fun v => false :: v) ++
            (ballVectors n L).map (fun v => true :: v)
          rw [List.mem_append]
          cases b with
          | false =>
              exact Or.inl (List.mem_map.mpr
                ⟨bs, mem_ballVectors n (L + 1) bs hbs (by simpa using hw), rfl⟩)
          | true =>
              have hw' : weight bs < L := by
                have : weight bs + 1 < L + 1 := by simpa using hw
                omega
              exact Or.inr (List.mem_map.mpr ⟨bs, mem_ballVectors n L bs hbs hw', rfl⟩)

/-! ## A valid reason excludes the vector -/

theorem not_logical_of_killReasonValid (s : CodeState) (σ : Sector) (v : List Bool)
    (reason : KillReason) (h : killReasonValid s σ v reason = true) :
    isLogicalBool s σ v = false := by
  cases reason with
  | oddOverlap row =>
      unfold killReasonValid at h
      rw [List.any_eq_true] at h
      obtain ⟨r, hr, hodd⟩ := h
      rw [Bool.and_eq_true] at hodd
      have h1 : dotPar v (rowVector s.Q r) % 2 = 1 := Nat.eq_of_beq_eq_true hodd.2
      cases hlog : isLogicalBool s σ v with
      | false => rfl
      | true =>
          exfalso
          unfold isLogicalBool at hlog
          rw [Bool.and_eq_true, List.all_eq_true] at hlog
          have h0 : dotPar v (rowVector s.Q r) % 2 = 0 := Nat.eq_of_beq_eq_true (hlog.1 r hr)
          omega
  | inSpan coeffs =>
      unfold killReasonValid at h
      rw [Bool.and_eq_true] at h
      have hlen : coeffs.length = (sectorRows s σ).length := Nat.eq_of_beq_eq_true h.1
      have hcomb : combineRows s.Q.length ((sectorRows s σ).map (rowVector s.Q)) coeffs = v :=
        eq_of_beq h.2
      have hspan : inSpanRowsBool s.Q (sectorRows s σ) v = true :=
        (exact_inSpanRowsBool_iff _ _ _).mpr ⟨coeffs, hlen, hcomb⟩
      unfold isLogicalBool
      rw [hspan]
      exact Bool.and_false _

/-! ## Soundness -/

/-- Acceptance implies that every σ-logical has weight at least the bound. -/
theorem checkCertificate_sound (s : CodeState) (c : SectorCertificate)
    (h : checkCertificate s c = true) (v : List Bool)
    (hv : v ∈ logicalVectors s c.sector) : c.bound ≤ weight v := by
  rcases Nat.lt_or_ge (weight v) c.bound with hlt | hge
  · exfalso
    have hball := mem_ballVectors s.Q.length c.bound v (length_of_mem_logicalVectors hv) hlt
    unfold checkCertificate at h
    rw [List.all_eq_true] at h
    have hany := h v hball
    rw [List.any_eq_true] at hany
    obtain ⟨k, _, hk⟩ := hany
    unfold killCovers at hk
    rw [Bool.and_eq_true] at hk
    have hnot := not_logical_of_killReasonValid s c.sector v k.reason hk.2
    unfold logicalVectors at hv
    have hlog := (List.mem_filter.mp hv).2
    rw [hnot] at hlog
    exact Bool.false_ne_true hlog
  · exact hge

/-- The certified fact in `Option Nat`: a finite exact distance is at least
    the bound. A `none` value is `+∞` and needs no bound. -/
theorem certificate_lower_bound (s : CodeState) (c : SectorCertificate)
    (h : checkCertificate s c = true) (d : Nat)
    (hd : exactDistance? c.sector s = some d) : c.bound ≤ d := by
  obtain ⟨v, hv, hw⟩ := minWeight?_attained _ _ hd
  rw [← hw]
  exact checkCertificate_sound s c h v hv

/-- The certified fact in the S2 concrete domain `ℕ ∪ {+∞}`. -/
theorem certificate_lower_bound_ext (s : CodeState) (c : SectorCertificate)
    (h : checkCertificate s c = true) :
    ExtNat.finite c.bound ≤ exactDistanceExt c.sector s := by
  unfold exactDistanceExt
  cases hd : exactDistance? c.sector s with
  | none => exact trivial
  | some d => exact certificate_lower_bound s c h d hd

/-- The certified fact for the `Nat` reading, whose `+∞` is the sentinel
    `|Q| + 1`; the bound must not exceed the sentinel. -/
theorem certificate_lower_bound_nat (s : CodeState) (c : SectorCertificate)
    (h : checkCertificate s c = true) (hb : c.bound ≤ s.Q.length + 1) :
    c.bound ≤ exactDistance c.sector s := by
  rw [exactDistance_eq_getD]
  cases hd : exactDistance? c.sector s with
  | none => exact hb
  | some d => exact certificate_lower_bound s c h d hd

/-- A checked lower bound and a checked witness of the same weight give the
    exact distance. -/
theorem certificate_equality (s : CodeState) (c : SectorCertificate)
    (h : checkCertificate s c = true) (w : List Bool)
    (hw : witnessValid s c.sector c.bound w = true) :
    exactDistance? c.sector s = some c.bound := by
  unfold witnessValid at hw
  rw [Bool.and_eq_true, Bool.and_eq_true] at hw
  have hlen : w.length = s.Q.length := Nat.eq_of_beq_eq_true hw.1.1
  have hwt : weight w = c.bound := Nat.eq_of_beq_eq_true hw.2
  have hmem : w ∈ logicalVectors s c.sector := by
    unfold logicalVectors
    exact List.mem_filter.mpr ⟨(exact_mem_allBoolLists _ _).mpr hlen, hw.1.2⟩
  obtain ⟨m, hm, hle⟩ := exactDistance?_le_of_mem hmem
  have hge := certificate_lower_bound s c h m hm
  rw [hm]
  have : m = c.bound := by omega
  rw [this]

end CodeCalculus
