import CodeCalculus.CayleyGroups

/-!
# Finite groups by multiplication table

The raw-data presentation of a finite group that the term language carries
(issue #631): an `ℓ × ℓ` multiplication table on `{0, ..., ℓ - 1}`, as
`spec/OPERATIONAL_SEMANTICS.md` §2 admits for `L-LIFTED`, `L-GROUP-ALGEBRA`,
and `L-BALANCED` since 2026-11-22. `StateExpr` derives decidable equality, so
a production cannot carry a `FiniteGroup` (a structure of functions and
proofs). It carries the table, and this file turns a table that passes the
Boolean typing check `tableGroupTyped` into a `FiniteGroup`.

`tableGroupTyped` checks what `machine/constructors.py`
`_validate_cayley_table` checks: a nonempty square table with entries in
range, a two-sided identity, a two-sided inverse for every element, and
associativity. The Python check also asks that the identity and each inverse
be unique. In an associative table with a two-sided identity both are unique
whenever they exist, so the two checks accept the same tables.

`tableGroup` is total: on a table that fails the check it is the trivial
group. No evaluation rule reads it there, since every rule carries the typing
check as a premise.

The balanced product reads its actions as one permutation per group element,
in the element order of the table. The permutation-generator presentation of
a group has no production here.
-/

namespace CodeCalculus

/-! ## Search and range lemmas -/

/-- The first element of `l` satisfying `p`, `0` when there is none. -/
def firstWhere (p : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: xs => if p x = true then x else firstWhere p xs

theorem firstWhere_spec (p : Nat → Bool) :
    ∀ l : List Nat, l.any p = true → firstWhere p l ∈ l ∧ p (firstWhere p l) = true
  | [], h => absurd (show false = true from h) Bool.false_ne_true
  | x :: xs, h => by
    cases hx : p x with
    | true =>
      have hfw : firstWhere p (x :: xs) = x := by
        show (if p x = true then x else firstWhere p xs) = x
        rw [ite_eq_left hx]
      rw [hfw]
      exact ⟨List.mem_cons_self, hx⟩
    | false =>
      have hfw : firstWhere p (x :: xs) = firstWhere p xs := by
        show (if p x = true then x else firstWhere p xs) = firstWhere p xs
        rw [ite_eq_right (by rw [hx]; exact Bool.false_ne_true)]
      rw [List.any_cons, hx, Bool.false_or] at h
      obtain ⟨h1, h2⟩ := firstWhere_spec p xs h
      rw [hfw]
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem all_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true)
    {a : Nat} (ha : a < n) : p a = true :=
  List.all_eq_true.mp h a (List.mem_range.mpr ha)

theorem firstWhere_range {n : Nat} {p : Nat → Bool}
    (h : (List.range n).any p = true) :
    firstWhere p (List.range n) < n ∧ p (firstWhere p (List.range n)) = true :=
  ⟨List.mem_range.mp (firstWhere_spec p _ h).1, (firstWhere_spec p _ h).2⟩

/-! ## Tables -/

/-- The product of `a` and `b` read off the table, `0` outside it. -/
def tableMul (t : List (List Nat)) (a b : Nat) : Nat := (t.getD a []).getD b 0

/-- Whether `e` is a two-sided identity of the table. -/
def tableIsIdentity (t : List (List Nat)) (e : Nat) : Bool :=
  (List.range t.length).all (fun g => tableMul t e g == g && tableMul t g e == g)

/-- The identity of the table: its first two-sided identity. -/
def tableE (t : List (List Nat)) : Nat :=
  firstWhere (tableIsIdentity t) (List.range t.length)

/-- Whether `h` is a two-sided inverse of `g`. -/
def tableIsInverse (t : List (List Nat)) (g h : Nat) : Bool :=
  tableMul t g h == tableE t && tableMul t h g == tableE t

/-- The inverse of `g`: its first two-sided inverse. -/
def tableInv (t : List (List Nat)) (g : Nat) : Nat :=
  firstWhere (tableIsInverse t g) (List.range t.length)

/-- A nonempty square table with entries in range. -/
def tableClosed (t : List (List Nat)) : Bool :=
  decide (1 ≤ t.length) &&
    t.all (fun r => r.length == t.length && r.all (fun v => decide (v < t.length)))

/-- Associativity of the table. -/
def tableAssoc (t : List (List Nat)) : Bool :=
  (List.range t.length).all (fun a => (List.range t.length).all (fun b =>
    (List.range t.length).all (fun c =>
      tableMul t (tableMul t a b) c == tableMul t a (tableMul t b c))))

/-- The typing check of a group given by its multiplication table. -/
def tableGroupTyped (t : List (List Nat)) : Bool :=
  tableClosed t &&
    (List.range t.length).any (tableIsIdentity t) &&
    (List.range t.length).all (fun g =>
      (List.range t.length).any (tableIsInverse t g)) &&
    tableAssoc t

theorem tableGroupTyped_parts {t : List (List Nat)} (h : tableGroupTyped t = true) :
    tableClosed t = true ∧
    (List.range t.length).any (tableIsIdentity t) = true ∧
    (List.range t.length).all (fun g =>
      (List.range t.length).any (tableIsInverse t g)) = true ∧
    tableAssoc t = true := by
  unfold tableGroupTyped at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem tableMul_lt {t : List (List Nat)} (h : tableClosed t = true) {a b : Nat}
    (ha : a < t.length) (hb : b < t.length) : tableMul t a b < t.length := by
  unfold tableClosed at h
  rw [Bool.and_eq_true] at h
  have hrow := List.all_eq_true.mp h.2 t[a] (List.getElem_mem ha)
  rw [Bool.and_eq_true] at hrow
  have hlen : t[a].length = t.length := eq_of_beq hrow.1
  have hb' : b < t[a].length := by rw [hlen]; exact hb
  have hentry := List.all_eq_true.mp hrow.2 t[a][b] (List.getElem_mem hb')
  unfold tableMul
  have h1 : t.getD a [] = t[a] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
  have h2 : t[a].getD b 0 = t[a][b] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb', Option.getD_some]
  rw [h1, h2]
  exact of_decide_eq_true hentry

theorem tableE_lt {t : List (List Nat)} (h : tableGroupTyped t = true) :
    tableE t < t.length :=
  (firstWhere_range (tableGroupTyped_parts h).2.1).1

theorem tableE_identity {t : List (List Nat)} (h : tableGroupTyped t = true)
    {g : Nat} (hg : g < t.length) :
    tableMul t (tableE t) g = g ∧ tableMul t g (tableE t) = g := by
  have hid := all_range (firstWhere_range (tableGroupTyped_parts h).2.1).2 hg
  rw [Bool.and_eq_true] at hid
  exact ⟨eq_of_beq hid.1, eq_of_beq hid.2⟩

theorem tableInv_spec {t : List (List Nat)} (h : tableGroupTyped t = true)
    {g : Nat} (hg : g < t.length) :
    tableInv t g < t.length ∧ tableMul t g (tableInv t g) = tableE t ∧
      tableMul t (tableInv t g) g = tableE t := by
  have hany := all_range (tableGroupTyped_parts h).2.2.1 hg
  have hfw := firstWhere_range hany
  have hinv := hfw.2
  unfold tableIsInverse at hinv
  rw [Bool.and_eq_true] at hinv
  exact ⟨hfw.1, eq_of_beq hinv.1, eq_of_beq hinv.2⟩

theorem tableMul_assoc {t : List (List Nat)} (h : tableGroupTyped t = true)
    {a b c : Nat} (ha : a < t.length) (hb : b < t.length) (hc : c < t.length) :
    tableMul t (tableMul t a b) c = tableMul t a (tableMul t b c) := by
  have hassoc := (tableGroupTyped_parts h).2.2.2
  unfold tableAssoc at hassoc
  exact eq_of_beq (all_range (all_range (all_range hassoc ha) hb) hc)

/-! ## The group of a table -/

/-- The trivial group. -/
def trivialGroup : FiniteGroup where
  order := 1
  mul := fun _ _ => 0
  inv := fun _ => 0
  e := 0
  h_e := Nat.zero_lt_one
  h_mul_lt := fun _ _ _ _ => Nat.zero_lt_one
  h_inv_lt := fun _ _ => Nat.zero_lt_one
  h_assoc := fun _ _ _ _ _ _ => rfl
  h_mul_e := fun _ ha => (Nat.lt_one_iff.mp ha).symm
  h_e_mul := fun _ ha => (Nat.lt_one_iff.mp ha).symm
  h_mul_inv := fun _ _ => rfl
  h_inv_mul := fun _ _ => rfl

/-- The group of a table that passes the typing check. -/
def tableGroupOf (t : List (List Nat)) (h : tableGroupTyped t = true) : FiniteGroup where
  order := t.length
  mul := tableMul t
  inv := tableInv t
  e := tableE t
  h_e := tableE_lt h
  h_mul_lt := fun _ _ ha hb => tableMul_lt (tableGroupTyped_parts h).1 ha hb
  h_inv_lt := fun _ ha => (tableInv_spec h ha).1
  h_assoc := fun _ _ _ ha hb hc => tableMul_assoc h ha hb hc
  h_mul_e := fun _ ha => (tableE_identity h ha).2
  h_e_mul := fun _ ha => (tableE_identity h ha).1
  h_mul_inv := fun _ ha => (tableInv_spec h ha).2.1
  h_inv_mul := fun _ ha => (tableInv_spec h ha).2.2

/-- The group of a table, the trivial group when the table fails the typing
    check. -/
def tableGroup (t : List (List Nat)) : FiniteGroup :=
  if h : tableGroupTyped t = true then tableGroupOf t h else trivialGroup

theorem tableGroup_eq {t : List (List Nat)} (h : tableGroupTyped t = true) :
    tableGroup t = tableGroupOf t h := by
  unfold tableGroup
  rw [dite_eq_left h]

theorem tableGroup_order {t : List (List Nat)} (h : tableGroupTyped t = true) :
    (tableGroup t).order = t.length := by
  rw [tableGroup_eq h]; rfl

theorem tableGroup_mul {t : List (List Nat)} (h : tableGroupTyped t = true) :
    (tableGroup t).mul = tableMul t := by
  rw [tableGroup_eq h]; rfl

theorem tableGroup_inv {t : List (List Nat)} (h : tableGroupTyped t = true) :
    (tableGroup t).inv = tableInv t := by
  rw [tableGroup_eq h]; rfl

theorem tableGroup_e {t : List (List Nat)} (h : tableGroupTyped t = true) :
    (tableGroup t).e = tableE t := by
  rw [tableGroup_eq h]; rfl

/-! ## Group-algebra inputs -/

/-- An element of `𝔽₂[G]`: a list of group elements, each in range. -/
def tableElementTyped (t : List (List Nat)) (x : List Nat) : Bool :=
  x.all (fun g => decide (g < t.length))

/-- A nonempty matrix over `𝔽₂[G]` with rows of one positive length. -/
def tableMatrixTyped (t : List (List Nat)) : List (List (List Nat)) → Bool
  | [] => false
  | r :: rs =>
      decide (1 ≤ r.length) && rs.all (fun r' => r'.length == r.length) &&
        (r :: rs).all (fun r' => r'.all (tableElementTyped t))

/-- The state of `twoblock_G(a, b)` for `G` given by its table. -/
def tableTwoblockState (t : List (List Nat)) (a b : List Nat) : CodeState :=
  cayleyTwoblockState (tableGroup t) a b

/-- The state of `lift_G(A, B)` for `G` given by its table. -/
def tableLiftState (t : List (List Nat)) (A B : List (List (List Nat))) : CodeState :=
  cayleyLiftState (tableGroup t) A B

/-! ## Actions, one permutation per group element -/

/-- The image of `x` under the permutation listed for the group element `g`,
    `0` outside the listing. -/
def permAt (perms : List (List Nat)) (g x : Nat) : Nat := (perms.getD g []).getD x 0

/-- One list of length `size` per group element, mapping `{0, ..., size - 1}`
    into itself, the identity element acting trivially. -/
def tableActionShape (t : List (List Nat)) (size : Nat) (perms : List (List Nat)) : Bool :=
  perms.length == t.length && perms.all (fun p => p.length == size) &&
    (List.range t.length).all (fun g =>
      (List.range size).all (fun x => decide (permAt perms g x < size))) &&
    (List.range size).all (fun x => permAt perms (tableE t) x == x)

/-- A right action: `perms[g h] = perms[h] ∘ perms[g]`. -/
def tableRightActionTyped (t : List (List Nat)) (size : Nat)
    (perms : List (List Nat)) : Bool :=
  tableActionShape t size perms &&
    (List.range t.length).all (fun g => (List.range t.length).all (fun h =>
      (List.range size).all (fun x =>
        permAt perms (tableMul t g h) x == permAt perms h (permAt perms g x))))

/-- A left action: `perms[g h] = perms[g] ∘ perms[h]`. -/
def tableLeftActionTyped (t : List (List Nat)) (size : Nat)
    (perms : List (List Nat)) : Bool :=
  tableActionShape t size perms &&
    (List.range t.length).all (fun g => (List.range t.length).all (fun h =>
      (List.range size).all (fun x =>
        permAt perms (tableMul t g h) x == permAt perms g (permAt perms h x))))

theorem tableActionShape_lt {t : List (List Nat)} {size : Nat} {perms : List (List Nat)}
    (h : tableActionShape t size perms = true) {g x : Nat}
    (hg : g < t.length) (hx : x < size) : permAt perms g x < size := by
  unfold tableActionShape at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true (all_range (all_range h.1.2 hg) hx)

theorem tableActionShape_e {t : List (List Nat)} {size : Nat} {perms : List (List Nat)}
    (h : tableActionShape t size perms = true) {x : Nat} (hx : x < size) :
    permAt perms (tableE t) x = x := by
  unfold tableActionShape at h
  rw [Bool.and_eq_true] at h
  exact eq_of_beq (all_range h.2 hx)

/-- The trivial right action. -/
def trivialRightAction (G : FiniteGroup) (size : Nat) : FiniteRightAction G size where
  act := fun _ x => x
  h_lt := fun _ _ _ hx => hx
  h_e := fun _ _ => rfl
  h_mul := fun _ _ _ _ _ _ => rfl

/-- The trivial left action. -/
def trivialLeftAction (G : FiniteGroup) (size : Nat) : FiniteLeftAction G size where
  act := fun _ x => x
  h_lt := fun _ _ _ hx => hx
  h_e := fun _ _ => rfl
  h_mul := fun _ _ _ _ _ _ => rfl

/-- The right action listed by `perms`, the trivial action when the table or
    the listing fails its typing check. -/
def tableRightAction (t : List (List Nat)) (size : Nat) (perms : List (List Nat)) :
    FiniteRightAction (tableGroup t) size :=
  if h : tableGroupTyped t = true ∧ tableRightActionTyped t size perms = true then
    { act := permAt perms
      h_lt := fun g x hg hx => by
        rw [tableGroup_order h.1] at hg
        have hty := h.2
        unfold tableRightActionTyped at hty
        rw [Bool.and_eq_true] at hty
        exact tableActionShape_lt hty.1 hg hx
      h_e := fun x hx => by
        have hty := h.2
        unfold tableRightActionTyped at hty
        rw [Bool.and_eq_true] at hty
        rw [tableGroup_e h.1]
        exact tableActionShape_e hty.1 hx
      h_mul := fun g k x hg hk hx => by
        rw [tableGroup_order h.1] at hg hk
        have hty := h.2
        unfold tableRightActionTyped at hty
        rw [Bool.and_eq_true] at hty
        rw [tableGroup_mul h.1]
        exact eq_of_beq (all_range (all_range (all_range hty.2 hg) hk) hx) }
  else trivialRightAction _ _

/-- The left action listed by `perms`, the trivial action when the table or
    the listing fails its typing check. -/
def tableLeftAction (t : List (List Nat)) (size : Nat) (perms : List (List Nat)) :
    FiniteLeftAction (tableGroup t) size :=
  if h : tableGroupTyped t = true ∧ tableLeftActionTyped t size perms = true then
    { act := permAt perms
      h_lt := fun g x hg hx => by
        rw [tableGroup_order h.1] at hg
        have hty := h.2
        unfold tableLeftActionTyped at hty
        rw [Bool.and_eq_true] at hty
        exact tableActionShape_lt hty.1 hg hx
      h_e := fun x hx => by
        have hty := h.2
        unfold tableLeftActionTyped at hty
        rw [Bool.and_eq_true] at hty
        rw [tableGroup_e h.1]
        exact tableActionShape_e hty.1 hx
      h_mul := fun g k x hg hk hx => by
        rw [tableGroup_order h.1] at hg hk
        have hty := h.2
        unfold tableLeftActionTyped at hty
        rw [Bool.and_eq_true] at hty
        rw [tableGroup_mul h.1]
        exact eq_of_beq (all_range (all_range (all_range hty.2 hg) hk) hx) }
  else trivialLeftAction _ _

theorem tableRightAction_act {t : List (List Nat)} {size : Nat} {perms : List (List Nat)}
    (hG : tableGroupTyped t = true) (hA : tableRightActionTyped t size perms = true) :
    (tableRightAction t size perms).act = permAt perms := by
  unfold tableRightAction
  rw [dite_eq_left ⟨hG, hA⟩]

theorem tableLeftAction_act {t : List (List Nat)} {size : Nat} {perms : List (List Nat)}
    (hG : tableGroupTyped t = true) (hA : tableLeftActionTyped t size perms = true) :
    (tableLeftAction t size perms).act = permAt perms := by
  unfold tableLeftAction
  rw [dite_eq_left ⟨hG, hA⟩]

/-- Equivariance of `H` under the listed row and column permutations:
    `H[rows[g](a), cols[g](i)] = H[a, i]`. -/
def tableEquivariantTyped (t : List (List Nat)) (H : List (List Bool))
    (rows cols : List (List Nat)) : Bool :=
  (List.range t.length).all (fun g => (List.range H.length).all (fun a =>
    (List.range (matCols H)).all (fun i =>
      matEntry H (permAt rows g a) (permAt cols g i) == matEntry H a i)))

/-- The typing check of `balanced_G(H₁, α₁; H₂, α₂)` for `G` given by its
    table: a group, two binary matrices, a right action on the rows and on
    the columns of `H₁`, a left action on the rows and on the columns of
    `H₂`, and both matrices equivariant. -/
def tableBalancedTyped (t : List (List Nat)) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : Bool :=
  tableGroupTyped t && binaryMatrixTyped H1 && binaryMatrixTyped H2 &&
    tableRightActionTyped t H1.length rows1 &&
    tableRightActionTyped t (matCols H1) cols1 &&
    tableLeftActionTyped t H2.length rows2 &&
    tableLeftActionTyped t (matCols H2) cols2 &&
    tableEquivariantTyped t H1 rows1 cols1 && tableEquivariantTyped t H2 rows2 cols2

/-- The qubit count of `balanced_G(H₁, α₁; H₂, α₂)` for `G` given by its
    table: the orbits of the pairs of column indices plus the orbits of the
    pairs of row indices. -/
def tableBalancedQubits (t : List (List Nat)) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : Nat :=
  cayleyBalancedQubits (tableGroup t) H1 H2
    (tableRightAction t H1.length rows1) (tableRightAction t (matCols H1) cols1)
    (tableLeftAction t H2.length rows2) (tableLeftAction t (matCols H2) cols2)

/-- The state of `balanced_G(H₁, α₁; H₂, α₂)` for `G` given by its table. -/
def tableBalancedState (t : List (List Nat)) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : CodeState :=
  cayleyBalancedState (tableGroup t) H1 H2
    (tableRightAction t H1.length rows1) (tableRightAction t (matCols H1) cols1)
    (tableLeftAction t H2.length rows2) (tableLeftAction t (matCols H2) cols2)

/-! ## Groups by permutation generators

The third presentation of §4.44: permutations of `{0, ..., d - 1}` that
generate a group, its elements listed in lexicographic order. It has no
production of its own. A group given by generators is the table
`gensTable d gens`, and the table productions carry it. `gensTable` is `[]`
on a malformed generator list, which `tableGroupTyped` rejects. -/

/-- A positive degree and a list of permutations of `{0, ..., d - 1}`. -/
def gensTyped (d : Nat) (gens : List (List Nat)) : Bool :=
  decide (1 ≤ d) && gens.all (fun g =>
    g.length == d && (List.range d).all (fun x => g.contains x))

/-- The composite `p ∘ q` on `{0, ..., d - 1}`. -/
def permCompose (d : Nat) (p q : List Nat) : List Nat :=
  (List.range d).map (fun x => p.getD (q.getD x 0) 0)

/-- One round of the closure: every `p ∘ g`, for `p` listed and `g` a
    generator, that is not yet listed. -/
def gensStep (d : Nat) (gens seen : List (List Nat)) : List (List Nat) :=
  (seen.flatMap (fun p => gens.map (permCompose d p))).foldl
    (fun acc p => if acc.contains p then acc else acc ++ [p]) seen

/-- Rounds of the closure until one adds nothing, at most `fuel` of them. -/
def gensClosure (d : Nat) (gens : List (List Nat)) :
    Nat → List (List Nat) → List (List Nat)
  | 0, seen => seen
  | fuel + 1, seen =>
      if (gensStep d gens seen).length == seen.length then seen
      else gensClosure d gens fuel (gensStep d gens seen)

/-- Lexicographic `≤` on lists of naturals. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else lexLe as bs

/-- Insertion into a lexicographically sorted list. -/
def insertLex (p : List Nat) : List (List Nat) → List (List Nat)
  | [] => [p]
  | q :: qs => if lexLe p q = true then p :: q :: qs else q :: insertLex p qs

/-- The elements of the generated group in lexicographic order. A round adds
    at least one element until the closure is reached, and there are at most
    `d ^ d` maps, so `d ^ d` rounds are enough. -/
def gensElements (d : Nat) (gens : List (List Nat)) : List (List Nat) :=
  (gensClosure d gens (d ^ d) [List.range d]).foldr insertLex []

/-- The multiplication table of the group generated by `gens`, `[]` on a
    malformed generator list. -/
def gensTable (d : Nat) (gens : List (List Nat)) : List (List Nat) :=
  if gensTyped d gens = true then
    (gensElements d gens).map (fun p => (gensElements d gens).map (fun q =>
      (gensElements d gens).idxOf (permCompose d p q)))
  else []

end CodeCalculus
