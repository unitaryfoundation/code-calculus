import CodeCalculus.ExactPermute

/-!
# The §4.13 graft relations for the exact distance (issue #367)

`E-GRAFT` at a qubit `q` in the sector `τ` along the chain of the `τ`-rows
through `q` removes `q`, replaces the chain by its adjacent sums, and
shortens the opposite-sector rows at `q`. The two unpriced relations of
`spec/OPERATIONAL_SEMANTICS.md` §4.13 hold for the exact distance
(`exactDist_graft_relations`):

* the spliced sector does not fall: a `τ`-logical of the output, with a
  zero inserted at `q`, is a `τ`-logical of the input of the same weight
  (`GraftCtx.logical_insert`);
* the opposite sector does not rise: an opposite-sector logical of the
  input, with its entry at `q` dropped, is an opposite-sector logical of
  the output (`GraftCtx.logical_drop`).

For the first, the `τ`-rows of the input lie in the span of the first chain
row and the output's `τ`-rows (each chain row is the previous one plus an
adjacent sum), and only the first chain row has an entry at `q` there, so a
combination with a zero at `q` does not use it. For the second, a
combination of the shortened rows that equals the dropped vector lifts to a
combination of the input's rows that agrees with the vector off `q`, and
the overlap parity with a chain row forces agreement at `q` too.
-/

namespace CodeCalculus

/-! ## Row vectors and the removed position -/

theorem rowVector_dropAt (Q1 Q2 : List Nat) (q : Nat) (w : Row) :
    rowVector (Q1 ++ Q2) w = dropAt Q1.length (rowVector (Q1 ++ q :: Q2) w) := by
  unfold rowVector
  exact (dropAt_append_length _ Q1 q Q2).symm

theorem entryAt_rowVector_mid (Q1 Q2 : List Nat) (q : Nat) (w : Row) :
    entryAt Q1.length (rowVector (Q1 ++ q :: Q2) w) = w.support.contains q := by
  unfold rowVector
  exact entryAt_append_length _ Q1 q Q2

theorem rowVector_graftShorten (Q : List Nat) (q : Nat) (τ : Sector) (w : Row) (hq : q ∉ Q) :
    rowVector Q (graftShorten q τ w) = rowVector Q w := by
  unfold rowVector
  apply List.map_congr_left
  intro x hx
  have hxq : x ≠ q := fun h => hq (by rw [← h]; exact hx)
  unfold graftShorten
  split
  · exact shortenRow_contains q x w hxq
  · rfl

/-- If the head of a list of rows and every adjacent sum lie in a span, so
    does every row of the list. -/
theorem span_of_adjacent (Q : List Nat) (rows : List Row) : ∀ (L : List Row),
    (∀ a, L.head? = some a → inSpanRows Q rows (rowVector Q a)) →
    (∀ p ∈ L.zip (L.drop 1), inSpanRows Q rows (xorVec (rowVector Q p.1) (rowVector Q p.2))) →
    ∀ r ∈ L, inSpanRows Q rows (rowVector Q r)
  | [], _, _, _, h => nomatch h
  | [a], hh, _, r, h => by
      rw [List.mem_singleton.mp h]
      exact hh a rfl
  | a :: b :: L, hh, hp, r, h => by
      have ha := hh a rfl
      have hab := hp (a, b) (List.mem_cons_self ..)
      have hb : inSpanRows Q rows (rowVector Q b) := by
        have hx := inSpanRows_xor Q rows ha hab
        rwa [xorVec_cancel_left _ _ (by rw [rowVector_length, rowVector_length])] at hx
      rcases List.mem_cons.mp h with rfl | h'
      · exact ha
      · exact span_of_adjacent Q rows (b :: L)
          (fun x hx => by
            have : b = x := Option.some.inj hx
            rw [← this]
            exact hb)
          (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) r h'

theorem exists_zip_snd {α β : Type} : ∀ (xs : List α) (ys : List β) (x : α), x ∈ xs →
    xs.length ≤ ys.length → ∃ y, (x, y) ∈ xs.zip ys
  | [], _, _, h, _ => nomatch h
  | _ :: _, [], _, _, hl => absurd hl (by rw [List.length_cons, List.length_nil]; omega)
  | a :: xs, b :: ys, x, h, hl => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨b, List.mem_cons_self ..⟩
      · obtain ⟨y, hy⟩ := exists_zip_snd xs ys x h' (Nat.le_of_succ_le_succ hl)
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-! ## One graft, as a context -/

/-- The data of one admitted graft: the command's list names exactly the
    `τ`-rows through `q`, and `q` sits at position `|Q1|` of the namespace. -/
structure GraftCtx (s : CodeState) (q : Nat) (τ : Sector) (ids Q1 Q2 : List Nat) : Prop where
  wf : EncodingWellFormed s
  htouch : touchingRows s τ q ≠ []
  hlen : ids.length = (touchingRows s τ q).length
  hnodup : ids.Nodup
  hids : ∀ id ∈ ids, id ∈ (touchingRows s τ q).map Row.id
  heq : s.Q = Q1 ++ q :: Q2
  h1 : q ∉ Q1
  h2 : q ∉ Q2

namespace GraftCtx

variable {s : CodeState} {q : Nat} {τ : Sector} {ids Q1 Q2 : List Nat}

theorem graft_Q (G : GraftCtx s q τ ids Q1 Q2) : (graftState s q τ ids).Q = Q1 ++ Q2 := by
  rw [graftState_Q', G.heq]
  exact filter_ne_split Q1 Q2 q G.h1 G.h2

theorem Q_length (G : GraftCtx s q τ ids Q1 Q2) : s.Q.length = Q1.length + Q2.length + 1 := by
  rw [G.heq, List.length_append, List.length_cons]
  omega

theorem qnot (G : GraftCtx s q τ ids Q1 Q2) : q ∉ Q1 ++ Q2 := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact G.h1 h
  · exact G.h2 h

theorem ids_iff (G : GraftCtx s q τ ids Q1 Q2) :
    ∀ r ∈ s.rows, (r.id ∈ ids ↔ (r.sector = τ ∧ r.support.contains q = true)) :=
  graft_ids_iff s q τ ids G.wf.2.1 G.hlen G.hnodup G.hids

theorem chain_mem (G : GraftCtx s q τ ids Q1 Q2) {L : Row} (hL : L ∈ graftChain s ids) :
    L ∈ s.rows ∧ L.sector = τ ∧ L.support.contains q = true :=
  ⟨(mem_graftChain hL).1, (G.ids_iff L (mem_graftChain hL).1).mp (mem_graftChain hL).2⟩

theorem mem_chain_of_touching (G : GraftCtx s q τ ids Q1 Q2) {r : Row} (hr : r ∈ s.rows)
    (hτ : r.sector = τ) (hq : r.support.contains q = true) : r ∈ graftChain s ids := by
  unfold graftChain
  exact List.mem_filterMap.mpr
    ⟨r.id, (G.ids_iff r hr).mpr ⟨hτ, hq⟩, rowById_of_mem s G.wf.2.1 r hr⟩

theorem chain_ne_nil (G : GraftCtx s q τ ids Q1 Q2) : graftChain s ids ≠ [] := by
  intro hnil
  cases ht : touchingRows s τ q with
  | nil => exact G.htouch ht
  | cons r rest =>
      have hr : r ∈ touchingRows s τ q := by
        rw [ht]
        exact List.mem_cons_self ..
      have hr' := List.mem_filter.mp hr
      have hcond := of_decide_eq_true hr'.2
      have hmem := G.mem_chain_of_touching hr'.1 hcond.1 hcond.2
      rw [hnil] at hmem
      cases hmem

/-- A minted row does not contain the grafted qubit. -/
theorem minted_q (L R : Row) (id : Nat) :
    (graftMintedRow s q τ ((L, R), id)).support.contains q = false := by
  cases hc : (graftMintedRow s q τ ((L, R), id)).support.contains q with
  | false => rfl
  | true =>
      exfalso
      rw [graftMintedRow_support] at hc
      have h1 := (sortNat_perm _).mem_iff.mp (List.contains_iff_mem.mp hc)
      have h2 := (List.mem_filter.mp (List.mem_filter.mp h1).1).2
      exact absurd rfl (of_decide_eq_true h2)

/-- Over the input namespace, a minted row's vector is the sum of the two
    chain rows it is minted from. -/
theorem rowVector_minted (G : GraftCtx s q τ ids Q1 Q2) {L R : Row}
    (hL : L ∈ graftChain s ids) (hR : R ∈ graftChain s ids) (id : Nat) :
    rowVector s.Q (graftMintedRow s q τ ((L, R), id)) =
      xorVec (rowVector s.Q L) (rowVector s.Q R) := by
  unfold rowVector
  rw [xorVec_map_map]
  apply List.map_congr_left
  intro x hx
  show (graftMintedRow s q τ ((L, R), id)).support.contains x =
    (L.support.contains x != R.support.contains x)
  rcases Decidable.em (x = q) with hxq | hxq
  · rw [hxq, minted_q, (G.chain_mem hL).2.2, (G.chain_mem hR).2.2]
    rfl
  · rw [graftMintedRow_support, Bool.eq_iff_iff, List.contains_iff_mem,
      (sortNat_perm _).mem_iff, List.mem_filter, List.mem_filter]
    constructor
    · intro h
      have hne := of_decide_eq_true h.2
      cases hl : L.support.contains x <;> cases hr : R.support.contains x
      · exact absurd (hl.trans hr.symm) hne
      · rfl
      · rfl
      · exact absurd (hl.trans hr.symm) hne
    · intro h
      refine ⟨⟨hx, decide_eq_true hxq⟩, decide_eq_true ?_⟩
      intro heq
      rw [heq] at h
      cases hr : R.support.contains x <;> rw [hr] at h <;> exact absurd h (by decide)

/-- The output's `τ`-rows: the input's `τ`-rows off `q`, then the minted rows. -/
theorem sectorRows_same (G : GraftCtx s q τ ids Q1 Q2) :
    sectorRows (graftState s q τ ids) τ = graftUntouched s q τ ++ graftMintedRows s q τ ids := by
  rw [graft_sectorRows_same s q τ ids G.wf.2.1 G.hlen G.hnodup G.hids]
  congr 1
  have h : (graftUntouched s q τ).map (graftShorten q τ) = (graftUntouched s q τ).map id := by
    apply List.map_congr_left
    intro w hw
    have hsec : w.sector = τ := by
      have h := (List.mem_filter.mp hw).2
      rw [Bool.and_eq_true] at h
      exact of_decide_eq_true h.1
    exact graftShorten_eq_of_same q τ w hsec
  rw [h, List.map_id]

theorem sectorRows_opp (G : GraftCtx s q τ ids Q1 Q2) :
    sectorRows (graftState s q τ ids) (oppositeSector τ) =
      (sectorRows s (oppositeSector τ)).map (graftShorten q τ) :=
  graft_sectorRows_opp s q τ ids G.wf.2.1 G.hlen G.hnodup G.hids

theorem untouched_mem (_G : GraftCtx s q τ ids Q1 Q2) {w : Row} (hw : w ∈ graftUntouched s q τ) :
    w ∈ sectorRows s τ ∧ w.support.contains q = false := by
  have h := List.mem_filter.mp hw
  have h2 := h.2
  rw [Bool.and_eq_true] at h2
  refine ⟨List.mem_filter.mpr ⟨h.1, decide_eq_true (of_decide_eq_true h2.1)⟩, ?_⟩
  cases hc : w.support.contains q with
  | false => rfl
  | true =>
      rw [hc] at h2
      exact absurd h2.2 (by decide)

/-- No `τ`-row of the output contains the grafted qubit. -/
theorem same_q (G : GraftCtx s q τ ids Q1 Q2) {g : Row}
    (hg : g ∈ graftUntouched s q τ ++ graftMintedRows s q τ ids) :
    g.support.contains q = false := by
  rcases List.mem_append.mp hg with h | h
  · exact (G.untouched_mem h).2
  · obtain ⟨L, R, id, _, _, _, rfl⟩ := mem_graftMintedRows h
    exact minted_q L R id

/-- The input's `τ`-rows lie in the span of the first chain row and the
    output's `τ`-rows, over the input namespace. -/
theorem spanLE_chain (G : GraftCtx s q τ ids Q1 Q2) {r1 : Row} {rest : List Row}
    (hchain : graftChain s ids = r1 :: rest) :
    SpanLE s.Q (sectorRows s τ)
      (r1 :: (graftUntouched s q τ ++ graftMintedRows s q τ ids)) := by
  apply spanLE_of_forall_mem
  intro r hr
  have hr' := List.mem_filter.mp hr
  have hrτ : r.sector = τ := of_decide_eq_true hr'.2
  cases hc : r.support.contains q with
  | false =>
      apply inSpanRows_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      apply List.mem_filter.mpr
      refine ⟨hr'.1, ?_⟩
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hrτ, by rw [hc]; rfl⟩
  | true =>
      have hmem := G.mem_chain_of_touching hr'.1 hrτ hc
      apply span_of_adjacent s.Q _ (graftChain s ids) _ _ r hmem
      · intro a ha
        rw [hchain] at ha
        have : r1 = a := Option.some.inj ha
        rw [← this]
        exact inSpanRows_of_mem s.Q (List.mem_cons_self ..)
      · intro p hp
        have hlenle : ((graftChain s ids).zip ((graftChain s ids).drop 1)).length ≤
            (mintFresh s.used (ids.length - 1)).length := by
          rw [List.length_zip, List.length_drop, mintFresh_length]
          have hle : (graftChain s ids).length ≤ ids.length := by
            unfold graftChain
            exact List.length_filterMap_le _ _
          omega
        obtain ⟨id, hid⟩ := exists_zip_snd _ _ p hp hlenle
        have hpL := (List.of_mem_zip hp).1
        have hpR := (List.drop_sublist 1 _).subset (List.of_mem_zip hp).2
        have hrow : graftMintedRow s q τ (p, id) ∈ graftMintedRows s q τ ids := by
          unfold graftMintedRows
          exact List.mem_map.mpr ⟨(p, id), hid, rfl⟩
        have hvec := G.rowVector_minted hpL hpR id
        rw [← hvec]
        exact inSpanRows_of_mem s.Q
          (List.mem_cons_of_mem _ (List.mem_append_right _ hrow))

/-! ## The two maps on logicals -/

/-- A `τ`-logical of the output, with a zero inserted at `q`, is a
    `τ`-logical of the input. -/
theorem logical_insert (G : GraftCtx s q τ ids Q1 Q2) {v' : List Bool}
    (hv' : v' ∈ logicalVectors (graftState s q τ ids) τ) :
    insertAt Q1.length false v' ∈ logicalVectors s τ := by
  obtain ⟨hlen', hlog'⟩ := (mem_logicalVectors_iff _ _ _).mp hv'
  obtain ⟨horth', hspan'⟩ := (isLogicalBool_iff_prop _ _ _).mp hlog'
  rw [G.graft_Q, List.length_append] at hlen'
  have hi : Q1.length ≤ v'.length := by rw [hlen']; exact Nat.le_add_right _ _
  rw [mem_logicalVectors_iff]
  refine ⟨by rw [length_insertAt _ _ _ hi, hlen', G.Q_length], ?_⟩
  rw [isLogicalBool_iff_prop]
  refine ⟨?_, ?_⟩
  · intro w hw
    have hc : Q1.length < (rowVector s.Q w).length := by
      rw [rowVector_length, G.Q_length]
      omega
    rw [dotPar_insertAt_false _ _ _ hi hc]
    have hvec : dropAt Q1.length (rowVector s.Q w) =
        rowVector (graftState s q τ ids).Q (graftShorten q τ w) := by
      rw [G.graft_Q, rowVector_graftShorten _ _ _ _ G.qnot, G.heq]
      exact (rowVector_dropAt Q1 Q2 q w).symm
    rw [hvec]
    exact horth' _ (by rw [G.sectorRows_opp]; exact List.mem_map.mpr ⟨w, hw, rfl⟩)
  · intro hin
    cases hchain : graftChain s ids with
    | nil => exact G.chain_ne_nil hchain
    | cons r1 rest =>
        have hr1 : r1 ∈ graftChain s ids := by
          rw [hchain]
          exact List.mem_cons_self ..
        obtain ⟨cs, hcs, hcomb⟩ := G.spanLE_chain hchain _ hin
        have hvlen : ∀ v ∈ (graftUntouched s q τ ++ graftMintedRows s q τ ids).map
            (rowVector s.Q), v.length = Q1.length + Q2.length + 1 := by
          intro v hv
          rw [← G.Q_length]
          exact rowVectors_length s.Q _ v hv
        have hventry : ∀ v ∈ (graftUntouched s q τ ++ graftMintedRows s q τ ids).map
            (rowVector s.Q), entryAt Q1.length v = false := by
          intro v hv
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
          rw [G.heq, entryAt_rowVector_mid]
          exact G.same_q hg
        cases cs with
        | nil => cases hcs
        | cons c cs' =>
            rw [List.map_cons, G.Q_length] at hcomb
            cases c with
            | true =>
                exfalso
                have h := congrArg (entryAt Q1.length) hcomb
                change entryAt Q1.length (xorVec (rowVector s.Q r1)
                  (combineRows (Q1.length + Q2.length + 1) _ cs')) = _ at h
                rw [entryAt_xorVec _ _ _ (by
                    rw [rowVector_length, combineRows_length _ _ _ hvlen, G.Q_length]),
                  entryAt_combineRows_false _ _ _ _ hvlen hventry,
                  entryAt_insertAt _ _ _ hi, G.heq, entryAt_rowVector_mid,
                  (G.chain_mem hr1).2.2] at h
                exact absurd h (by decide)
            | false =>
                change combineRows (Q1.length + Q2.length + 1) _ cs' = _ at hcomb
                apply hspan'
                rw [G.sectorRows_same, G.graft_Q]
                refine ⟨cs', Nat.succ.inj hcs, ?_⟩
                have hmap : (graftUntouched s q τ ++ graftMintedRows s q τ ids).map
                    (rowVector (Q1 ++ Q2)) =
                    ((graftUntouched s q τ ++ graftMintedRows s q τ ids).map
                      (rowVector s.Q)).map (dropAt Q1.length) := by
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro g _
                  show rowVector (Q1 ++ Q2) g = dropAt Q1.length (rowVector s.Q g)
                  rw [G.heq]
                  exact rowVector_dropAt Q1 Q2 q g
                rw [hmap, List.length_append,
                  ← combineRows_dropAt Q1.length (Q1.length + Q2.length)
                    (Nat.le_add_right _ _) _ cs' hvlen,
                  hcomb, dropAt_insertAt _ _ _ hi]

/-- An opposite-sector logical of the input, with its entry at `q` dropped,
    is an opposite-sector logical of the output. -/
theorem logical_drop (G : GraftCtx s q τ ids Q1 Q2) {u : List Bool}
    (hu : u ∈ logicalVectors s (oppositeSector τ)) :
    dropAt Q1.length u ∈ logicalVectors (graftState s q τ ids) (oppositeSector τ) := by
  obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hu
  obtain ⟨horth, hspan⟩ := (isLogicalBool_iff_prop _ _ _).mp hlog
  rw [oppositeSector_involutive] at horth
  have hlt : Q1.length < u.length := by
    rw [hlen, G.Q_length]
    omega
  rw [mem_logicalVectors_iff]
  refine ⟨by rw [length_dropAt _ _ hlt, hlen, G.Q_length, G.graft_Q, List.length_append]; omega,
    ?_⟩
  rw [isLogicalBool_iff_prop, oppositeSector_involutive, G.sectorRows_same, G.sectorRows_opp,
    G.graft_Q]
  refine ⟨?_, ?_⟩
  · intro g hg
    have hglen : Q1.length < (rowVector (Q1 ++ q :: Q2) g).length := by
      rw [rowVector_length, ← G.heq, G.Q_length]
      omega
    rw [rowVector_dropAt Q1 Q2 q g,
      dotPar_dropAt_of_entry_false _ _ _ hlt hglen
        (by rw [entryAt_rowVector_mid]; exact G.same_q hg),
      ← G.heq]
    rcases List.mem_append.mp hg with hun | hmint
    · exact horth g (G.untouched_mem hun).1
    · obtain ⟨L, R, id, hL, hR, _, rfl⟩ := mem_graftMintedRows hmint
      have hLτ : L ∈ sectorRows s τ :=
        List.mem_filter.mpr ⟨(G.chain_mem hL).1, decide_eq_true (G.chain_mem hL).2.1⟩
      have hRτ : R ∈ sectorRows s τ :=
        List.mem_filter.mpr ⟨(G.chain_mem hR).1, decide_eq_true (G.chain_mem hR).2.1⟩
      rw [G.rowVector_minted hL hR id,
        dotPar_xorVec u _ _ (by rw [rowVector_length, rowVector_length])]
      have h1 := horth L hLτ
      have h2 := horth R hRτ
      omega
  · intro hin
    obtain ⟨cs, hcs, hcomb⟩ := hin
    cases hchain : graftChain s ids with
    | nil => exact G.chain_ne_nil hchain
    | cons r1 rest =>
        have hr1 : r1 ∈ graftChain s ids := by
          rw [hchain]
          exact List.mem_cons_self ..
        obtain ⟨hr1mem, hr1τ, hr1q⟩ := G.chain_mem hr1
        have hvlen : ∀ v ∈ (sectorRows s (oppositeSector τ)).map (rowVector s.Q),
            v.length = Q1.length + Q2.length + 1 := by
          intro v hv
          rw [← G.Q_length]
          exact rowVectors_length s.Q _ v hv
        have hy_span : inSpanRows s.Q (sectorRows s (oppositeSector τ))
            (combineRows s.Q.length ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs) :=
          ⟨cs, by rw [hcs, List.length_map], rfl⟩
        have hylen : (combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs).length = s.Q.length :=
          combineRows_length _ _ _ (rowVectors_length s.Q _)
        have hmap : ((sectorRows s (oppositeSector τ)).map (graftShorten q τ)).map
            (rowVector (Q1 ++ Q2)) =
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)).map (dropAt Q1.length) := by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro w _
          show rowVector (Q1 ++ Q2) (graftShorten q τ w) = dropAt Q1.length (rowVector s.Q w)
          rw [rowVector_graftShorten _ _ _ _ G.qnot, G.heq]
          exact rowVector_dropAt Q1 Q2 q w
        have hdrop : dropAt Q1.length (combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs) = dropAt Q1.length u := by
          rw [← hcomb, hmap, List.length_append, G.Q_length]
          exact combineRows_dropAt Q1.length (Q1.length + Q2.length) (Nat.le_add_right _ _)
            _ cs hvlen
        have hx1len : Q1.length < (rowVector s.Q r1).length := by
          rw [rowVector_length, G.Q_length]
          omega
        have hx1q : entryAt Q1.length (rowVector s.Q r1) = true := by
          rw [G.heq, entryAt_rowVector_mid]
          exact hr1q
        have hu1 : dotPar u (rowVector s.Q r1) % 2 = 0 :=
          horth r1 (List.mem_filter.mpr ⟨hr1mem, decide_eq_true hr1τ⟩)
        have hy1 : dotPar (combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs)
            (rowVector s.Q r1) % 2 = 0 := by
          rw [dotPar_comm]
          apply dotPar_even_of_inSpanRows s.Q _ _ _ hy_span
          intro r hr
          have hr' := List.mem_filter.mp hr
          exact dotPar_rowVector_even_of_wf G.wf hr1mem hr'.1
            (by rw [hr1τ]; exact of_decide_eq_true hr'.2)
        have eu := dotPar_dropAt_dropAt Q1.length u (rowVector s.Q r1) hlt hx1len
        have ey := dotPar_dropAt_dropAt Q1.length _ (rowVector s.Q r1)
          (by rw [hylen, G.Q_length]; omega) hx1len
        rw [hx1q, Bool.and_true] at eu ey
        rw [hdrop] at ey
        have hentry : entryAt Q1.length (combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs) = entryAt Q1.length u := by
          cases hyq : entryAt Q1.length (combineRows s.Q.length
              ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs) <;>
            cases huq : entryAt Q1.length u
          · rfl
          · exfalso
            rw [hyq] at ey
            rw [huq] at eu
            simp at eu ey
            omega
          · exfalso
            rw [hyq] at ey
            rw [huq] at eu
            simp at eu ey
            omega
          · rfl
        have hyu : combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs = u := by
          have e1 := insertAt_entryAt_dropAt Q1.length (combineRows s.Q.length
            ((sectorRows s (oppositeSector τ)).map (rowVector s.Q)) cs)
            (by rw [hylen, G.Q_length]; omega)
          have e2 := insertAt_entryAt_dropAt Q1.length u hlt
          rw [hdrop, hentry] at e1
          exact e1.symm.trans e2
        rw [hyu] at hy_span
        exact hspan hy_span

end GraftCtx

/-! ## The §4.13 relations for `exactDist` -/

/-- The two unpriced §4.13 relations of `E-GRAFT` for the exact distance, in
    the shape of the hypothesis `hgraft` of `gate6_interval_soundness`: the
    spliced sector does not fall and the opposite sector does not rise. -/
theorem exactDist_graft_relations {q : Nat} {τ : Sector} {ids : List Nat} {s s' : CodeState}
    (hwf : EncodingWellFormed s) (hEval : Eval (Command.graft q τ ids) s s') :
    (if τ = Sector.X then leOpt (exactDist s).x (exactDist s').x
      else leOpt (exactDist s).z (exactDist s').z) ∧
    (if τ = Sector.X then leOpt (exactDist s').z (exactDist s).z
      else leOpt (exactDist s').x (exactDist s).x) := by
  have hpre : q ∈ s.Q ∧ touchingRows s τ q ≠ [] ∧
      ids.length = (touchingRows s τ q).length ∧ ids.Nodup ∧
      (∀ id ∈ ids, id ∈ (touchingRows s τ q).map Row.id) ∧ s' = graftState s q τ ids := by
    cases hEval with
    | graft hq _ htouch hlen hnodup hids _ _ hs' _ => exact ⟨hq, htouch, hlen, hnodup, hids, hs'⟩
  obtain ⟨hq, htouch, hlen, hnodup, hids, hs'⟩ := hpre
  subst hs'
  obtain ⟨Q1, Q2, heq, h1, h2⟩ := split_of_mem_nodup hq hwf.1
  have G : GraftCtx s q τ ids Q1 Q2 := ⟨hwf, htouch, hlen, hnodup, hids, heq, h1, h2⟩
  have hsel : leOpt (exactDistOpt τ s) (exactDistOpt τ (graftState s q τ ids)) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    apply leOpt_exactDistance?_of_map
    intro v' hv'
    have hlen' := ((mem_logicalVectors_iff _ _ _).mp hv').1
    rw [G.graft_Q, List.length_append] at hlen'
    refine ⟨insertAt Q1.length false v', G.logical_insert hv', ?_⟩
    rw [weight_insertAt _ _ _ (by rw [hlen']; exact Nat.le_add_right _ _)]
    show weight v' + 0 ≤ weight v'
    omega
  have hopp : leOpt (exactDistOpt (oppositeSector τ) (graftState s q τ ids))
      (exactDistOpt (oppositeSector τ) s) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    apply leOpt_exactDistance?_of_map
    intro u hu
    exact ⟨dropAt Q1.length u, G.logical_drop hu, weight_dropAt_le _ _⟩
  cases τ with
  | X =>
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨hsel, hopp⟩
  | Z =>
      have hne : ¬ (Sector.Z = Sector.X) := by decide
      rw [ite_eq_right hne, ite_eq_right hne]
      exact ⟨hsel, hopp⟩

end CodeCalculus
