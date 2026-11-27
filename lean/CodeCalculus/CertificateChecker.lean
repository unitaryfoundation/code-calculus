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

A second format, the pruning tree, is checked by `checkPruneCertificate`
and described in its own section below. It covers the vectors of weight
below the bound by classes, so the checker walks a tree and enumerates no
ball.

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

/-! ## Pruning-tree certificates

The kill-list checker visits every vector of weight below the bound, so its
cost is the size of the ball. A pruning tree covers the same vectors by
classes. A class is given by two masks over the positions of `s.Q`: `u`
marks positions fixed to `true` and `z` positions fixed to `false`. A vector
`v` is in the class when `subVec u v` and `disjVec z v` hold. The root class
has both masks empty and contains every vector.

A leaf closes its class with a reason no σ-logical of weight below the bound
is in it:

* `bound`: the positions fixed to `true` already number at least the bound;
* `needMore r`: the opposite-sector row `r` has odd overlap with `u`, so a
  vector commuting with it has a further `true` position, and one more
  reaches the bound;
* `conflict r`: the opposite-sector row `r` has odd overlap with `u` and
  every position of its support is fixed, so every vector of the class has
  odd overlap with it;
* `inSpan coeffs`: every position is fixed, so the class is the single
  vector `u`, and `u` is the stated combination of the σ-rows.

`branch q one zero` splits a class on position `q`. Rows are named by their
index among the displayed rows of the sector, in display order.

`checkPrune` reads the two row matrices as arguments, so the soundness
theorem `checkPrune_sound` is a statement about lists of vectors.
`checkPruneCertificate` supplies the matrices of a state, after checking
that the literal matrices the certificate carries are the state's. -/

/-- A pruning tree over the positions of a qubit list. -/
inductive PruneTree where
  | bound : PruneTree
  | needMore (row : Nat) : PruneTree
  | conflict (row : Nat) : PruneTree
  | inSpan (coeffs : List Bool) : PruneTree
  | branch (q : Nat) (one zero : PruneTree) : PruneTree

/-- Set position `q` of a mask. A position outside the mask changes nothing. -/
def vecSet : List Bool → Nat → List Bool
  | [], _ => []
  | _ :: bs, 0 => true :: bs
  | b :: bs, q + 1 => b :: vecSet bs q

/-- Position `q` of a vector, `false` outside it. -/
def vecBit : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, q + 1 => vecBit bs q

/-- Every `true` position of `u` is a `true` position of `v`; equal lengths. -/
def subVec : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => (!a || b) && subVec as bs
  | _, _ => false

/-- No `true` position of `z` is a `true` position of `v`; equal lengths. -/
def disjVec : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => !(a && b) && disjVec as bs
  | _, _ => false

/-- Every `true` position of `ρ` is fixed by `u` or by `z`. -/
def coveredBy : List Bool → List Bool → List Bool → Bool
  | [], [], [] => true
  | r :: rs, a :: as, b :: bs => (!r || a || b) && coveredBy rs as bs
  | _, _, _ => false

/-- Every position is fixed by `u` or by `z`. -/
def fullyFixed : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => (a || b) && fullyFixed as bs
  | _, _ => false

/-- The tree closes the class `(u, z)` for the bound `L`, the opposite-sector
    vectors `opp`, and the same-sector vectors `same` of length `n`. -/
def checkPrune (n L : Nat) (opp same : List (List Bool)) :
    List Bool → List Bool → PruneTree → Bool
  | u, _, PruneTree.bound => decide (L ≤ weight u)
  | u, _, PruneTree.needMore r =>
      match opp[r]? with
      | some ρ => dotPar u ρ % 2 == 1 && decide (L ≤ weight u + 1)
      | none => false
  | u, z, PruneTree.conflict r =>
      match opp[r]? with
      | some ρ => dotPar u ρ % 2 == 1 && coveredBy ρ u z
      | none => false
  | u, z, PruneTree.inSpan coeffs =>
      fullyFixed u z && coeffs.length == same.length && combineRows n same coeffs == u
  | u, z, PruneTree.branch q one zero =>
      checkPrune n L opp same (vecSet u q) z one &&
        checkPrune n L opp same u (vecSet z q) zero

theorem weight_le_of_subVec : ∀ (u v : List Bool), subVec u v = true → weight u ≤ weight v
  | [], [], _ => Nat.le_refl _
  | [], _ :: _, h => by simp [subVec] at h
  | _ :: _, [], h => by simp [subVec] at h
  | a :: as, b :: bs, h => by
      simp only [subVec, Bool.and_eq_true] at h
      have ih := weight_le_of_subVec as bs h.2
      rw [weight_cons, weight_cons]
      cases a <;> cases b <;> simp at h ⊢ <;> omega

theorem eq_of_subVec_of_weight_le : ∀ (u v : List Bool), subVec u v = true →
    weight v ≤ weight u → u = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [subVec] at h
  | _ :: _, [], h, _ => by simp [subVec] at h
  | a :: as, b :: bs, h, hw => by
      simp only [subVec, Bool.and_eq_true] at h
      have hle := weight_le_of_subVec as bs h.2
      rw [weight_cons, weight_cons] at hw
      cases a <;> cases b <;> simp at h hw
      · rw [eq_of_subVec_of_weight_le as bs h hw]
      · omega
      · rw [eq_of_subVec_of_weight_le as bs h hw]

theorem dotPar_eq_of_coveredBy : ∀ (ρ u z v : List Bool), coveredBy ρ u z = true →
    subVec u v = true → disjVec z v = true → dotPar v ρ = dotPar u ρ
  | [], _, _, v, _, _, _ => by rw [dotPar_nil_right, dotPar_nil_right]
  | _ :: _, [], _, _, h, _, _ => by simp [coveredBy] at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp [coveredBy] at h
  | _ :: _, _ :: _, _ :: _, [], _, hs, _ => by simp [subVec] at hs
  | r :: rs, a :: as, b :: bs, c :: cs, h, hs, hd => by
      simp only [coveredBy, Bool.and_eq_true] at h
      simp only [subVec, Bool.and_eq_true] at hs
      simp only [disjVec, Bool.and_eq_true] at hd
      have ih := dotPar_eq_of_coveredBy rs as bs cs h.2 hs.2 hd.2
      rw [dotPar_cons, dotPar_cons, ih]
      have h1 := h.1
      have h2 := hs.1
      have h3 := hd.1
      cases r <;> cases a <;> cases b <;> cases c <;> simp at h1 h2 h3 ⊢

theorem eq_of_fullyFixed : ∀ (u z v : List Bool), fullyFixed u z = true →
    subVec u v = true → disjVec z v = true → v = u
  | [], [], [], _, _, _ => rfl
  | [], [], _ :: _, _, hs, _ => by simp [subVec] at hs
  | [], _ :: _, _, h, _, _ => by simp [fullyFixed] at h
  | _ :: _, [], _, h, _, _ => by simp [fullyFixed] at h
  | _ :: _, _ :: _, [], _, hs, _ => by simp [subVec] at hs
  | a :: as, b :: bs, c :: cs, h, hs, hd => by
      simp only [fullyFixed, Bool.and_eq_true] at h
      simp only [subVec, Bool.and_eq_true] at hs
      simp only [disjVec, Bool.and_eq_true] at hd
      rw [eq_of_fullyFixed as bs cs h.2 hs.2 hd.2]
      have h1 := h.1
      have h2 := hs.1
      have h3 := hd.1
      cases a <;> cases b <;> cases c <;> simp at h1 h2 h3 ⊢

theorem subVec_vecSet : ∀ (u v : List Bool) (q : Nat), subVec u v = true →
    vecBit v q = true → subVec (vecSet u q) v = true
  | [], [], _, _, hb => by simp [vecBit] at hb
  | [], _ :: _, _, h, _ => by simp [subVec] at h
  | _ :: _, [], _, h, _ => by simp [subVec] at h
  | a :: as, b :: bs, 0, h, hb => by
      simp only [subVec, Bool.and_eq_true] at h
      simp only [vecBit] at hb
      simp [vecSet, subVec, hb, h.2]
  | a :: as, b :: bs, q + 1, h, hb => by
      simp only [subVec, Bool.and_eq_true] at h
      simp only [vecBit] at hb
      simp only [vecSet, subVec, Bool.and_eq_true]
      exact ⟨h.1, subVec_vecSet as bs q h.2 hb⟩

theorem disjVec_vecSet : ∀ (z v : List Bool) (q : Nat), disjVec z v = true →
    vecBit v q = false → disjVec (vecSet z q) v = true
  | [], [], _, _, _ => by simp [vecSet, disjVec]
  | [], _ :: _, _, h, _ => by simp [disjVec] at h
  | _ :: _, [], _, h, _ => by simp [disjVec] at h
  | a :: as, b :: bs, 0, h, hb => by
      simp only [disjVec, Bool.and_eq_true] at h
      simp only [vecBit] at hb
      simp [vecSet, disjVec, hb, h.2]
  | a :: as, b :: bs, q + 1, h, hb => by
      simp only [disjVec, Bool.and_eq_true] at h
      simp only [vecBit] at hb
      simp only [vecSet, disjVec, Bool.and_eq_true]
      exact ⟨h.1, disjVec_vecSet as bs q h.2 hb⟩

/-- An accepted tree closes its class: a vector of the class that has even
    overlap with every opposite-sector vector and is no combination of the
    same-sector vectors has weight at least the bound. -/
theorem checkPrune_sound (n L : Nat) (opp same : List (List Bool)) :
    ∀ (t : PruneTree) (u z : List Bool), checkPrune n L opp same u z t = true →
      ∀ v : List Bool, subVec u v = true → disjVec z v = true →
        (∀ ρ, ρ ∈ opp → dotPar v ρ % 2 = 0) →
        (∀ coeffs : List Bool, coeffs.length = same.length →
          combineRows n same coeffs ≠ v) →
        L ≤ weight v
  | PruneTree.bound, u, z, h, v, hs, _, _, _ => by
      simp only [checkPrune, decide_eq_true_eq] at h
      exact Nat.le_trans h (weight_le_of_subVec u v hs)
  | PruneTree.needMore r, u, z, h, v, hs, _, hopp, _ => by
      simp only [checkPrune] at h
      cases hr : opp[r]? with
      | none => rw [hr] at h; exact absurd h Bool.false_ne_true
      | some ρ =>
          rw [hr] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          have hodd : dotPar u ρ % 2 = 1 := Nat.eq_of_beq_eq_true h.1
          have heven := hopp ρ (List.mem_of_getElem? hr)
          have hle := weight_le_of_subVec u v hs
          rcases Nat.lt_or_ge (weight u) (weight v) with hlt | hge
          · omega
          · have heq := eq_of_subVec_of_weight_le u v hs hge
            rw [heq] at hodd
            omega
  | PruneTree.conflict r, u, z, h, v, hs, hd, hopp, _ => by
      simp only [checkPrune] at h
      cases hr : opp[r]? with
      | none => rw [hr] at h; exact absurd h Bool.false_ne_true
      | some ρ =>
          rw [hr] at h
          simp only [Bool.and_eq_true] at h
          have hodd : dotPar u ρ % 2 = 1 := Nat.eq_of_beq_eq_true h.1
          have heven := hopp ρ (List.mem_of_getElem? hr)
          rw [dotPar_eq_of_coveredBy ρ u z v h.2 hs hd] at heven
          omega
  | PruneTree.inSpan coeffs, u, z, h, v, hs, hd, _, hspan => by
      simp only [checkPrune, Bool.and_eq_true] at h
      have hv := eq_of_fullyFixed u z v h.1.1 hs hd
      have hlen : coeffs.length = same.length := Nat.eq_of_beq_eq_true h.1.2
      have hcomb : combineRows n same coeffs = u := eq_of_beq h.2
      exact absurd (hcomb.trans hv.symm) (hspan coeffs hlen)
  | PruneTree.branch q one zero, u, z, h, v, hs, hd, hopp, hspan => by
      simp only [checkPrune, Bool.and_eq_true] at h
      cases hb : vecBit v q with
      | true =>
          exact checkPrune_sound n L opp same one (vecSet u q) z h.1 v
            (subVec_vecSet u v q hs hb) hd hopp hspan
      | false =>
          exact checkPrune_sound n L opp same zero u (vecSet z q) h.2 v hs
            (disjVec_vecSet z v q hd hb) hopp hspan

theorem subVec_replicate_false : ∀ v : List Bool,
    subVec (List.replicate v.length false) v = true
  | [] => rfl
  | _ :: bs => by
      simp only [List.length_cons, List.replicate_succ, subVec, Bool.not_false, Bool.true_or,
        Bool.true_and]
      exact subVec_replicate_false bs

theorem disjVec_replicate_false : ∀ v : List Bool,
    disjVec (List.replicate v.length false) v = true
  | [] => rfl
  | _ :: bs => by
      simp only [List.length_cons, List.replicate_succ, disjVec, Bool.false_and, Bool.not_false,
        Bool.true_and]
      exact disjVec_replicate_false bs

/-- A pruning-tree certificate. `opp` and `same` are the vectors of the
    opposite-sector and same-sector rows, carried as literals so the tree is
    checked against them and not against a recomputation at every leaf. The
    sector and the bound are arguments of the checker, so the theorems below
    state the bound for the sector and the number written at the call. -/
structure PruneCertificate where
  opp : List (List Bool)
  same : List (List Bool)
  tree : PruneTree

/-- The checker for `L ≤ d_σ(s)`: the carried matrices are those of the
    state, and the tree closes the class of every vector. -/
def checkPruneCertificate (s : CodeState) (σ : Sector) (L : Nat) (c : PruneCertificate) :
    Bool :=
  c.opp == (sectorRows s (oppositeSector σ)).map (rowVector s.Q) &&
    c.same == (sectorRows s σ).map (rowVector s.Q) &&
    checkPrune s.Q.length L c.opp c.same
      (List.replicate s.Q.length false) (List.replicate s.Q.length false) c.tree

/-- Acceptance implies that every σ-logical has weight at least the bound. -/
theorem checkPruneCertificate_sound (s : CodeState) (σ : Sector) (L : Nat)
    (c : PruneCertificate) (h : checkPruneCertificate s σ L c = true) (v : List Bool)
    (hv : v ∈ logicalVectors s σ) : L ≤ weight v := by
  unfold checkPruneCertificate at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have hopp : c.opp = (sectorRows s (oppositeSector σ)).map (rowVector s.Q) :=
    eq_of_beq h.1.1
  have hsame : c.same = (sectorRows s σ).map (rowVector s.Q) := eq_of_beq h.1.2
  have hlen : v.length = s.Q.length := length_of_mem_logicalVectors hv
  have hlog : isLogicalBool s σ v = true := by
    unfold logicalVectors at hv
    exact (List.mem_filter.mp hv).2
  unfold isLogicalBool at hlog
  rw [Bool.and_eq_true, List.all_eq_true] at hlog
  have htree := h.2
  rw [← hlen] at htree
  refine checkPrune_sound v.length L c.opp c.same c.tree _ _ htree v
    (subVec_replicate_false v) (disjVec_replicate_false v) ?_ ?_
  · intro ρ hρ
    rw [hopp] at hρ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hρ
    exact Nat.eq_of_beq_eq_true (hlog.1 r hr)
  · intro coeffs hc hcomb
    rw [hsame, List.length_map] at hc
    rw [hsame, hlen] at hcomb
    have hspan : inSpanRowsBool s.Q (sectorRows s σ) v = true :=
      (exact_inSpanRowsBool_iff _ _ _).mpr ⟨coeffs, hc, hcomb⟩
    rw [hspan] at hlog
    exact Bool.false_ne_true hlog.2

/-- The certified fact in `Option Nat`. -/
theorem pruneCertificate_lower_bound (s : CodeState) (σ : Sector) (L : Nat)
    (c : PruneCertificate) (h : checkPruneCertificate s σ L c = true) (d : Nat)
    (hd : exactDistance? σ s = some d) : L ≤ d := by
  obtain ⟨v, hv, hw⟩ := minWeight?_attained _ _ hd
  rw [← hw]
  exact checkPruneCertificate_sound s σ L c h v hv

/-- The certified fact in the S2 concrete domain `ℕ ∪ {+∞}`. -/
theorem pruneCertificate_lower_bound_ext (s : CodeState) (σ : Sector) (L : Nat)
    (c : PruneCertificate) (h : checkPruneCertificate s σ L c = true) :
    ExtNat.finite L ≤ exactDistanceExt σ s := by
  unfold exactDistanceExt
  cases hd : exactDistance? σ s with
  | none => exact trivial
  | some d => exact pruneCertificate_lower_bound s σ L c h d hd

/-- The certified fact for the `Nat` reading, whose `+∞` is the sentinel
    `|Q| + 1`; the bound must not exceed the sentinel. -/
theorem pruneCertificate_lower_bound_nat (s : CodeState) (σ : Sector) (L : Nat)
    (c : PruneCertificate) (h : checkPruneCertificate s σ L c = true)
    (hb : L ≤ s.Q.length + 1) : L ≤ exactDistance σ s := by
  rw [exactDistance_eq_getD]
  cases hd : exactDistance? σ s with
  | none => exact hb
  | some d => exact pruneCertificate_lower_bound s σ L c h d hd

/-- A checked lower bound and a validated logical of the same weight give
    the exact distance. The witness is checked as a logical by
    `isLogicalBool`, whose span test enumerates every combination of the
    σ-rows, so this theorem is for states with few σ-rows. -/
theorem pruneCertificate_equality (s : CodeState) (σ : Sector) (L : Nat)
    (c : PruneCertificate) (h : checkPruneCertificate s σ L c = true) (w : List Bool)
    (hw : witnessValid s σ L w = true) : exactDistance? σ s = some L := by
  unfold witnessValid at hw
  rw [Bool.and_eq_true, Bool.and_eq_true] at hw
  have hwt : weight w = L := Nat.eq_of_beq_eq_true hw.2
  have hmem : w ∈ logicalVectors s σ := by
    unfold logicalVectors
    exact List.mem_filter.mpr
      ⟨(exact_mem_allBoolLists _ _).mpr (Nat.eq_of_beq_eq_true hw.1.1), hw.1.2⟩
  obtain ⟨m, hm, hle⟩ := exactDistance?_le_of_mem hmem
  have hge := pruneCertificate_lower_bound s σ L c h m hm
  rw [hm]
  have : m = L := by omega
  rw [this]

end CodeCalculus
