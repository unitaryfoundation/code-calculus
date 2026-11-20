import CodeCalculus.ConstructorRankTyped
import CodeCalculus.ConstructorAssembly

/-!
# `L-BALANCED`: the natural rows have pairwise even overlap

`balanced_naturalOrthogonal` proves, for every typed input, the overlap
hypothesis of `evalExpr_balanced_wf`, so every evaluation of `L-BALANCED`
yields a well-formed state (`evalExpr_balanced_wf'`). It follows the hand
derivation of `spec/OPERATIONAL_SEMANTICS.md` §4.35.

* Iterates of a map of `[size]` to itself, and lists of such maps that
  commute and have prescribed orders (`ActTyped`), with the action `actF` of
  an exponent tuple. The action composes (`actF_gadd`) and inverts
  (`actF_gneg`).
* The row and column permutations of a typed action, and their inverses,
  are such lists (`actTyped_fwd`, `actTyped_inv`), and an equivariant matrix
  is invariant under the action of every exponent tuple (`matEntry_actF`).
* The least pair of an orbit (`orbitRep`) lies in the orbit and is the same
  for every pair of the orbit (`pairRep_mem`, `pairRep_act`).
* The overlap of the natural `X`-row of an orbit `c` with the natural
  `Z`-row of a pair `(i, b)` has the parity of twice the number of pairs
  `(a, j)` in the orbit `c` with `H₁[a, i]` and `H₂[b, j]`
  (`balanced_overlap`): the left qubits contribute that number, the right
  qubits contribute it again.
-/

namespace CodeCalculus

/-! ## Iterates -/

/-- `f` maps `0, …, size - 1` to itself. -/
def MapsBelow (size : Nat) (f : Nat → Nat) : Prop := ∀ x, x < size → f x < size

theorem repeat_lt {size : Nat} {f : Nat → Nat} (hf : MapsBelow size f) :
    ∀ (e x : Nat), x < size → Nat.repeat f e x < size
  | 0, _, h => h
  | e + 1, x, h => hf _ (repeat_lt hf e x h)

theorem repeat_add (f : Nat → Nat) : ∀ (d e x : Nat),
    Nat.repeat f (d + e) x = Nat.repeat f d (Nat.repeat f e x)
  | 0, e, x => by
      rw [Nat.zero_add]
      rfl
  | d + 1, e, x => by
      rw [Nat.succ_add]
      show f (Nat.repeat f (d + e) x) = f (Nat.repeat f d (Nat.repeat f e x))
      rw [repeat_add f d e x]

theorem repeat_comm_one {size : Nat} {f g : Nat → Nat} (hg : MapsBelow size g)
    (hc : ∀ x, x < size → f (g x) = g (f x)) :
    ∀ (e x : Nat), x < size → f (Nat.repeat g e x) = Nat.repeat g e (f x)
  | 0, _, _ => rfl
  | e + 1, x, h => by
      show f (g (Nat.repeat g e x)) = g (Nat.repeat g e (f x))
      rw [hc _ (repeat_lt hg e x h), repeat_comm_one hg hc e x h]

theorem repeat_mul_order {size : Nat} {f : Nat → Nat} {o : Nat}
    (ho : ∀ x, x < size → Nat.repeat f o x = x) :
    ∀ (q x : Nat), x < size → Nat.repeat f (q * o) x = x
  | 0, x, _ => by
      rw [Nat.zero_mul]
      rfl
  | q + 1, x, h => by
      rw [Nat.succ_mul, repeat_add, ho x h, repeat_mul_order ho q x h]

theorem repeat_mod {size : Nat} {f : Nat → Nat} {o : Nat}
    (ho : ∀ x, x < size → Nat.repeat f o x = x) (n x : Nat) (hx : x < size) :
    Nat.repeat f (n % o) x = Nat.repeat f n x := by
  have h := Nat.mod_add_div n o
  have e : Nat.repeat f n x = Nat.repeat f (n % o + (n / o) * o) x := by
    rw [Nat.mul_comm (n / o) o, h]
  rw [e, repeat_add, repeat_mul_order ho (n / o) x hx]

theorem repeat_negm {size : Nat} {f : Nat → Nat} {o e : Nat}
    (ho : ∀ x, x < size → Nat.repeat f o x = x) (he : e < o) (x : Nat) (hx : x < size) :
    Nat.repeat f (negm o e + e) x = x := by
  rw [negm_eq he]
  split
  · rename_i h0
    rw [h0]
    rfl
  · have h : o - e + e = o := by omega
    rw [h]
    exact ho x hx

/-! ## Commuting maps of prescribed orders -/

/-- A list of maps of `[size]` to itself that commute pairwise there, the
    `i`-th of order dividing the `i`-th of `os`. -/
def ActTyped (size : Nat) : List (Nat → Nat) → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | f :: fs, o :: os => MapsBelow size f ∧ (∀ x, x < size → Nat.repeat f o x = x) ∧
      (∀ f' ∈ fs, ∀ x, x < size → f (f' x) = f' (f x)) ∧ ActTyped size fs os

/-- The action of an exponent tuple: the `i`-th map iterated `g_i` times. -/
def actF : List (Nat → Nat) → List Nat → Nat → Nat
  | [], _, x => x
  | _ :: _, [], x => x
  | f :: fs, e :: g, x => actF fs g (Nat.repeat f e x)

theorem actF_lt {size : Nat} : ∀ (fs : List (Nat → Nat)) (os g : List Nat),
    ActTyped size fs os → ∀ x, x < size → actF fs g x < size
  | [], _, _, _, _, h => h
  | _ :: _, _, [], _, _, h => h
  | _ :: _, [], _ :: _, ht, _, _ => nomatch ht
  | _ :: fs, _ :: os, e :: g, ht, x, h =>
      actF_lt fs os g ht.2.2.2 _ (repeat_lt ht.1 e x h)

theorem actF_comm {size : Nat} {f : Nat → Nat} : ∀ (fs : List (Nat → Nat)) (os g : List Nat),
    ActTyped size fs os → (∀ f' ∈ fs, ∀ x, x < size → f (f' x) = f' (f x)) →
    ∀ x, x < size → f (actF fs g x) = actF fs g (f x)
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, _, [], _, _, _, _ => rfl
  | _ :: _, [], _ :: _, ht, _, _, _ => nomatch ht
  | f' :: fs, _ :: os, e :: g, ht, hc, x, h => by
      show f (actF fs g (Nat.repeat f' e x)) = actF fs g (Nat.repeat f' e (f x))
      rw [actF_comm fs os g ht.2.2.2 (fun f'' hf'' => hc f'' (List.mem_cons_of_mem _ hf'')) _
        (repeat_lt ht.1 e x h), repeat_comm_one ht.1 (hc f' (List.mem_cons_self ..)) e x h]

theorem repeat_actF_comm {size : Nat} {f : Nat → Nat} (fs : List (Nat → Nat))
    (os g : List Nat) (ht : ActTyped size fs os)
    (hc : ∀ f' ∈ fs, ∀ x, x < size → f (f' x) = f' (f x)) (hf : MapsBelow size f) :
    ∀ (d x : Nat), x < size → Nat.repeat f d (actF fs g x) = actF fs g (Nat.repeat f d x)
  | 0, _, _ => rfl
  | d + 1, x, h => by
      show f (Nat.repeat f d (actF fs g x)) = actF fs g (f (Nat.repeat f d x))
      rw [repeat_actF_comm fs os g ht hc hf d x h,
        actF_comm fs os g ht hc _ (repeat_lt hf d x h)]

/-- The sum of two group elements. -/
def gadd : List Nat → List Nat → List Nat → List Nat
  | o :: os, x :: xs, y :: ys => ((x + y) % o) :: gadd os xs ys
  | _, _, _ => []

theorem inGroup_gadd : ∀ (os g h : List Nat), InGroup os g → InGroup os h →
    InGroup os (gadd os g h)
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, hh => nomatch hh
  | [], _ :: _, _, hg, _ => nomatch hg
  | _ :: _, [], _, hg, _ => nomatch hg
  | _ :: _, _ :: _, [], _, hh => nomatch hh
  | _ :: os, x :: xs, _ :: ys, hg, hh =>
      ⟨Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le x) hg.1), inGroup_gadd os xs ys hg.2 hh.2⟩

/-- The action composes: acting by `g` and then by `h` is acting by their
    sum. -/
theorem actF_gadd {size : Nat} : ∀ (fs : List (Nat → Nat)) (os g h : List Nat),
    ActTyped size fs os → InGroup os g → InGroup os h →
    ∀ x, x < size → actF fs h (actF fs g x) = actF fs (gadd os h g) x
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, ht, _, _, _, _ => nomatch ht
  | _ :: _, _ :: _, [], _, _, hg, _, _, _ => nomatch hg
  | _ :: _, _ :: _, _ :: _, [], _, _, hh, _, _ => nomatch hh
  | f :: fs, o :: os, e :: g, d :: h, ht, hg, hh, x, hx => by
      show actF fs h (Nat.repeat f d (actF fs g (Nat.repeat f e x))) =
        actF fs (gadd os h g) (Nat.repeat f ((d + e) % o) x)
      rw [repeat_actF_comm fs os g ht.2.2.2 ht.2.2.1 ht.1 d _ (repeat_lt ht.1 e x hx),
        ← repeat_add, actF_gadd fs os g h ht.2.2.2 hg.2 hh.2 _ (repeat_lt ht.1 (d + e) x hx),
        repeat_mod ht.2.1 (d + e) x hx]

/-- Acting by `g` and then by its inverse is the identity. -/
theorem actF_gneg {size : Nat} : ∀ (fs : List (Nat → Nat)) (os g : List Nat),
    ActTyped size fs os → InGroup os g →
    ∀ x, x < size → actF fs (gneg os g) (actF fs g x) = x
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, ht, _, _, _ => nomatch ht
  | _ :: _, _ :: _, [], _, hg, _, _ => nomatch hg
  | f :: fs, o :: os, e :: g, ht, hg, x, hx => by
      rw [gneg_cons]
      show actF fs (gneg os g) (Nat.repeat f (negm o e) (actF fs g (Nat.repeat f e x))) = x
      rw [repeat_actF_comm fs os g ht.2.2.2 ht.2.2.1 ht.1 (negm o e) _
        (repeat_lt ht.1 e x hx), ← repeat_add, repeat_negm ht.2.1 hg.1 x hx,
        actF_gneg fs os g ht.2.2.2 hg.2 x hx]

/-- Acting by the inverse of `g` and then by `g` is the identity. -/
theorem actF_gneg' {size : Nat} (fs : List (Nat → Nat)) (os g : List Nat)
    (ht : ActTyped size fs os) (hg : InGroup os g) (x : Nat) (hx : x < size) :
    actF fs g (actF fs (gneg os g) x) = x := by
  have h := actF_gneg fs os (gneg os g) ht (inGroup_gneg os g hg) x hx
  rw [gneg_gneg os g hg] at h
  exact h

theorem actF_inj {size : Nat} (fs : List (Nat → Nat)) (os g : List Nat)
    (ht : ActTyped size fs os) (hg : InGroup os g) (x y : Nat) (hx : x < size)
    (hy : y < size) (h : actF fs g x = actF fs g y) : x = y := by
  rw [← actF_gneg fs os g ht hg x hx, ← actF_gneg fs os g ht hg y hy, h]

theorem actTyped_maps {size : Nat} : ∀ (fs : List (Nat → Nat)) (os : List Nat),
    ActTyped size fs os → ∀ f ∈ fs, MapsBelow size f
  | [], _, _, _, hf => nomatch hf
  | _ :: _, [], ht, _, _ => nomatch ht
  | f :: fs, _ :: os, ht, f', hf' => by
      rcases List.mem_cons.mp hf' with rfl | h
      · exact ht.1
      · exact actTyped_maps fs os ht.2.2.2 f' h

theorem actTyped_length {size : Nat} : ∀ (fs : List (Nat → Nat)) (os : List Nat),
    ActTyped size fs os → fs.length = os.length
  | [], [], _ => rfl
  | [], _ :: _, ht => nomatch ht
  | _ :: _, [], ht => nomatch ht
  | _ :: fs, _ :: os, ht => congrArg Nat.succ (actTyped_length fs os ht.2.2.2)

/-! ## Permutations -/

theorem permTyped_unpack {size : Nat} {p : List Nat} (h : permTyped size p = true) :
    p.length = size ∧ p.Nodup ∧ ∀ x ∈ p, x < size := by
  unfold permTyped at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, of_decide_eq_true h.1.2,
    fun x hx => of_decide_eq_true (List.all_eq_true.mp h.2 x hx)⟩

/-- A permutation of `[size]` takes every value below `size`. -/
theorem mem_of_permTyped {size : Nat} {p : List Nat} (h : permTyped size p = true) (y : Nat)
    (hy : y < size) : y ∈ p := by
  obtain ⟨hlen, hnd, hlt⟩ := permTyped_unpack h
  rcases Decidable.em (y ∈ p) with hm | hm
  · exact hm
  · exfalso
    have hsub : ∀ x ∈ p, x ∈ (List.range size).filter (fun x => decide (x ≠ y)) :=
      fun x hx => List.mem_filter.mpr ⟨List.mem_range.mpr (hlt x hx),
        decide_eq_true (fun e => hm (e ▸ hx))⟩
    have h1 := length_le_of_nodup_subset_gen p _ hnd
      (nodup_filter_cf _ _ (nodup_range_cf size)) hsub
    have h2 := length_filter_ne_gen y (List.range size) (nodup_range_cf size)
      (List.mem_range.mpr hy)
    rw [List.length_range] at h2
    omega

theorem permApply_lt {size : Nat} {p : List Nat} (h : permTyped size p = true) :
    MapsBelow size (permApply p) := by
  intro x hx
  obtain ⟨hlen, _, hlt⟩ := permTyped_unpack h
  exact hlt _ (getD_mem 0 p x (by rw [hlen]; exact hx))

theorem idxOf_lt_of_mem : ∀ (l : List Nat) (y : Nat), y ∈ l → l.idxOf y < l.length
  | [], _, h => nomatch h
  | x :: l, y, h => by
      rw [List.idxOf_cons]
      rcases Decidable.em (x = y) with e | e
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr e))]
        exact Nat.zero_lt_succ _
      · have hm : y ∈ l := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm e
          · exact h'
        rw [ite_eq_right_of_eq_false _ _ (eq_false (fun hb => e (beq_iff_eq.mp hb)))]
        exact Nat.succ_lt_succ (idxOf_lt_of_mem l y hm)

theorem getD_idxOf_of_mem : ∀ (l : List Nat) (y : Nat), y ∈ l → l.getD (l.idxOf y) 0 = y
  | [], _, h => nomatch h
  | x :: l, y, h => by
      rw [List.idxOf_cons]
      rcases Decidable.em (x = y) with e | e
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr e))]
        exact e
      · have hm : y ∈ l := by
          rcases List.mem_cons.mp h with h' | h'
          · exact absurd h'.symm e
          · exact h'
        rw [ite_eq_right_of_eq_false _ _ (eq_false (fun hb => e (beq_iff_eq.mp hb)))]
        exact getD_idxOf_of_mem l y hm

theorem permInv_lt {size : Nat} {p : List Nat} (h : permTyped size p = true) :
    MapsBelow size (permInv p) := by
  intro y hy
  obtain ⟨hlen, _, _⟩ := permTyped_unpack h
  have hm := idxOf_lt_of_mem p y (mem_of_permTyped h y hy)
  rw [hlen] at hm
  exact hm

theorem permApply_permInv {size : Nat} {p : List Nat} (h : permTyped size p = true) (y : Nat)
    (hy : y < size) : permApply p (permInv p y) = y :=
  getD_idxOf_of_mem p y (mem_of_permTyped h y hy)

theorem permInv_permApply {size : Nat} {p : List Nat} (h : permTyped size p = true) (x : Nat)
    (hx : x < size) : permInv p (permApply p x) = x := by
  obtain ⟨hlen, hnd, _⟩ := permTyped_unpack h
  have hx' : x < p.length := by rw [hlen]; exact hx
  unfold permApply permInv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx']
  exact hnd.idxOf_getElem x hx'

/-- The inverses of two commuting permutations commute. -/
theorem permInv_comm {size : Nat} {p p' : List Nat} (h : permTyped size p = true)
    (h' : permTyped size p' = true)
    (hc : ∀ x, x < size → permApply p (permApply p' x) = permApply p' (permApply p x))
    (y : Nat) (hy : y < size) :
    permInv p (permInv p' y) = permInv p' (permInv p y) := by
  have hv : permInv p' (permInv p y) < size := permInv_lt h' _ (permInv_lt h y hy)
  have e : permApply p' (permApply p (permInv p' (permInv p y))) = y := by
    rw [← hc _ hv, permApply_permInv h' _ (permInv_lt h y hy), permApply_permInv h y hy]
  rw [← e, permInv_permApply h' _ (permApply_lt h _ hv), permInv_permApply h _ hv, e]

theorem repeat_permInv_cancel {size : Nat} {p : List Nat} (h : permTyped size p = true) :
    ∀ (e y : Nat), y < size →
      Nat.repeat (permInv p) e (Nat.repeat (permApply p) e y) = y
  | 0, _, _ => rfl
  | e + 1, y, hy => by
      have h1 : Nat.repeat (permInv p) (e + 1) (Nat.repeat (permApply p) (e + 1) y) =
          Nat.repeat (permInv p) e (permInv p (Nat.repeat (permApply p) (e + 1) y)) :=
        repeat_add (permInv p) e 1 _
      rw [h1]
      show Nat.repeat (permInv p) e
        (permInv p (permApply p (Nat.repeat (permApply p) e y))) = y
      rw [permInv_permApply h _ (repeat_lt (permApply_lt h) e y hy),
        repeat_permInv_cancel h e y hy]

theorem repeat_permInv_order {size : Nat} {p : List Nat} (h : permTyped size p = true)
    {o : Nat} (ho : ∀ x, x < size → Nat.repeat (permApply p) o x = x) (y : Nat)
    (hy : y < size) : Nat.repeat (permInv p) o y = y := by
  have h1 := repeat_permInv_cancel h o y hy
  rw [ho y hy] at h1
  exact h1

/-! ## Typed actions -/

theorem actionTyped_unpack {orders : List Nat} {size : Nat} {perms : List (List Nat)}
    (h : actionTyped orders size perms = true) :
    perms.length = orders.length ∧ (∀ p ∈ perms, permTyped size p = true) ∧
    (∀ po ∈ perms.zip orders, ∀ x, x < size → Nat.repeat (permApply po.1) po.2 x = x) ∧
    (∀ p ∈ perms, ∀ p' ∈ perms, ∀ x, x < size →
      permApply p (permApply p' x) = permApply p' (permApply p x)) := by
  unfold actionTyped at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun p hp => List.all_eq_true.mp h2 p hp, ?_, ?_⟩
  · intro po hpo x hx
    exact Nat.eq_of_beq_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp h3 po hpo) x (List.mem_range.mpr hx))
  · intro p hp p' hp' x hx
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp h4 p hp) p' hp') x (List.mem_range.mpr hx))

theorem actTyped_of {size : Nat} (φ : List Nat → Nat → Nat) :
    ∀ (perms : List (List Nat)) (orders : List Nat), perms.length = orders.length →
    (∀ p ∈ perms, MapsBelow size (φ p)) →
    (∀ po ∈ perms.zip orders, ∀ x, x < size → Nat.repeat (φ po.1) po.2 x = x) →
    (∀ p ∈ perms, ∀ p' ∈ perms, ∀ x, x < size → φ p (φ p' x) = φ p' (φ p x)) →
    ActTyped size (perms.map φ) orders
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | p :: perms, o :: orders, hlen, hmap, hord, hcomm => by
      show MapsBelow size (φ p) ∧ (∀ x, x < size → Nat.repeat (φ p) o x = x) ∧
        (∀ f' ∈ perms.map φ, ∀ x, x < size → φ p (f' x) = f' (φ p x)) ∧
        ActTyped size (perms.map φ) orders
      refine ⟨hmap p (List.mem_cons_self ..), hord (p, o) (List.mem_cons_self ..), ?_,
        actTyped_of φ perms orders (Nat.succ.inj hlen)
          (fun q hq => hmap q (List.mem_cons_of_mem _ hq))
          (fun po hpo => hord po (List.mem_cons_of_mem _ hpo))
          (fun q hq q' hq' => hcomm q (List.mem_cons_of_mem _ hq) q'
            (List.mem_cons_of_mem _ hq'))⟩
      intro f' hf' x hx
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hf'
      exact hcomm p (List.mem_cons_self ..) p' (List.mem_cons_of_mem _ hp') x hx

/-- The permutations of a typed action commute and have the group's
    orders. -/
theorem actTyped_fwd {orders : List Nat} {size : Nat} {perms : List (List Nat)}
    (h : actionTyped orders size perms = true) :
    ActTyped size (perms.map permApply) orders := by
  obtain ⟨hlen, hperm, hord, hcomm⟩ := actionTyped_unpack h
  exact actTyped_of permApply perms orders hlen (fun p hp => permApply_lt (hperm p hp))
    hord hcomm

/-- So do their inverses. -/
theorem actTyped_inv {orders : List Nat} {size : Nat} {perms : List (List Nat)}
    (h : actionTyped orders size perms = true) :
    ActTyped size (perms.map permInv) orders := by
  obtain ⟨hlen, hperm, hord, hcomm⟩ := actionTyped_unpack h
  apply actTyped_of permInv perms orders hlen (fun p hp => permInv_lt (hperm p hp))
  · intro po hpo x hx
    exact repeat_permInv_order (hperm po.1 (List.of_mem_zip hpo).1) (hord po hpo) x hx
  · intro p hp p' hp' x hx
    exact permInv_comm (hperm p hp) (hperm p' hp') (hcomm p hp p' hp') x hx

theorem actFwd_eq : ∀ (perms : List (List Nat)) (g : List Nat) (x : Nat),
    actFwd perms g x = actF (perms.map permApply) g x
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: perms, e :: g, x => actFwd_eq perms g (Nat.repeat (permApply p) e x)

theorem actInv_eq : ∀ (perms : List (List Nat)) (g : List Nat) (x : Nat),
    actInv perms g x = actF (perms.map permInv) g x
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: perms, e :: g, x => actInv_eq perms g (Nat.repeat (permInv p) e x)

/-! ## Equivariant matrices -/

/-- `H[f a, f' i] = H[a, i]` for the maps of two lists taken in step. -/
def EquivF (H : List (List Bool)) (m n : Nat) : List (Nat → Nat) → List (Nat → Nat) → Prop
  | [], _ => True
  | _ :: _, [] => True
  | f :: fs, f' :: fs' =>
      (∀ a, a < m → ∀ i, i < n → matEntry H (f a) (f' i) = matEntry H a i) ∧
        EquivF H m n fs fs'

theorem equivF_of (H : List (List Bool)) (m n : Nat) (φ : List Nat → Nat → Nat) :
    ∀ (rows cols : List (List Nat)),
    (∀ rc ∈ rows.zip cols, ∀ a, a < m → ∀ i, i < n →
      matEntry H (φ rc.1 a) (φ rc.2 i) = matEntry H a i) →
    EquivF H m n (rows.map φ) (cols.map φ)
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | r :: rows, c :: cols, h => by
      show (∀ a, a < m → ∀ i, i < n → matEntry H (φ r a) (φ c i) = matEntry H a i) ∧
        EquivF H m n (rows.map φ) (cols.map φ)
      exact ⟨h (r, c) (List.mem_cons_self ..),
        equivF_of H m n φ rows cols (fun rc hrc => h rc (List.mem_cons_of_mem _ hrc))⟩

theorem matEntry_repeat {H : List (List Bool)} {m n : Nat} {f f' : Nat → Nat}
    (hf : MapsBelow m f) (hf' : MapsBelow n f')
    (h : ∀ a, a < m → ∀ i, i < n → matEntry H (f a) (f' i) = matEntry H a i) :
    ∀ (e a i : Nat), a < m → i < n →
      matEntry H (Nat.repeat f e a) (Nat.repeat f' e i) = matEntry H a i
  | 0, _, _, _, _ => rfl
  | e + 1, a, i, ha, hi => by
      show matEntry H (f (Nat.repeat f e a)) (f' (Nat.repeat f' e i)) = matEntry H a i
      rw [h _ (repeat_lt hf e a ha) _ (repeat_lt hf' e i hi), matEntry_repeat hf hf' h e a i ha hi]

/-- An equivariant matrix is invariant under the action of every exponent
    tuple. -/
theorem matEntry_actF {H : List (List Bool)} {m n : Nat} :
    ∀ (fs fs' : List (Nat → Nat)) (g : List Nat), fs.length = fs'.length →
    EquivF H m n fs fs' → (∀ f ∈ fs, MapsBelow m f) → (∀ f ∈ fs', MapsBelow n f) →
    ∀ a i, a < m → i < n → matEntry H (actF fs g a) (actF fs' g i) = matEntry H a i
  | [], [], _, _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, h, _, _, _, _, _, _, _ => nomatch h
  | _ :: _, [], _, h, _, _, _, _, _, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _ => rfl
  | f :: fs, f' :: fs', e :: g, hlen, hE, hm, hn, a, i, ha, hi => by
      have hf := hm f (List.mem_cons_self ..)
      have hf' := hn f' (List.mem_cons_self ..)
      show matEntry H (actF fs g (Nat.repeat f e a)) (actF fs' g (Nat.repeat f' e i)) =
        matEntry H a i
      rw [matEntry_actF fs fs' g (Nat.succ.inj hlen) hE.2
        (fun q hq => hm q (List.mem_cons_of_mem _ hq))
        (fun q hq => hn q (List.mem_cons_of_mem _ hq)) _ _ (repeat_lt hf e a ha)
        (repeat_lt hf' e i hi), matEntry_repeat hf hf' hE.1 e a i ha hi]

theorem equivariantTyped_unpack {H : List (List Bool)} {rows cols : List (List Nat)}
    (h : equivariantTyped H rows cols = true) :
    ∀ rc ∈ rows.zip cols, ∀ a, a < H.length → ∀ i, i < matCols H →
      matEntry H (permApply rc.1 a) (permApply rc.2 i) = matEntry H a i := by
  intro rc hrc a ha i hi
  unfold equivariantTyped at h
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h rc hrc) a
    (List.mem_range.mpr ha)) i (List.mem_range.mpr hi))

/-- An equivariant matrix under the permutations of a typed action. -/
theorem equivF_fwd {H : List (List Bool)} {rows cols : List (List Nat)}
    (h : equivariantTyped H rows cols = true) :
    EquivF H H.length (matCols H) (rows.map permApply) (cols.map permApply) :=
  equivF_of H _ _ permApply rows cols (equivariantTyped_unpack h)

/-- An equivariant matrix under the inverse permutations. -/
theorem equivF_inv {orders : List Nat} {H : List (List Bool)} {rows cols : List (List Nat)}
    (hr : actionTyped orders H.length rows = true)
    (hc : actionTyped orders (matCols H) cols = true)
    (h : equivariantTyped H rows cols = true) :
    EquivF H H.length (matCols H) (rows.map permInv) (cols.map permInv) := by
  apply equivF_of H _ _ permInv rows cols
  intro rc hrc a ha i hi
  have hpr := (actionTyped_unpack hr).2.1 rc.1 (List.of_mem_zip hrc).1
  have hpc := (actionTyped_unpack hc).2.1 rc.2 (List.of_mem_zip hrc).2
  have e := equivariantTyped_unpack h rc hrc _ (permInv_lt hpr a ha) _ (permInv_lt hpc i hi)
  rw [permApply_permInv hpr a ha, permApply_permInv hpc i hi] at e
  exact e.symm

/-! ## The least pair of an orbit -/

/-- The lexicographic order on pairs. -/
def pairLe (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance (a b : Nat × Nat) : Decidable (pairLe a b) := by
  unfold pairLe
  exact inferInstance

theorem pairLe_refl (a : Nat × Nat) : pairLe a a := Or.inr ⟨rfl, Nat.le_refl _⟩

theorem pairLe_total (a b : Nat × Nat) : pairLe a b ∨ pairLe b a := by
  rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.le_total a.2 b.2 with h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
  · exact Or.inr (Or.inl h)

theorem pairLe_trans {a b c : Nat × Nat} (h1 : pairLe a b) (h2 : pairLe b c) : pairLe a c := by
  rcases h1 with h1 | ⟨e1, l1⟩
  · rcases h2 with h2 | ⟨e2, _⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl (by rw [← e2]; exact h1)
  · rcases h2 with h2 | ⟨e2, l2⟩
    · exact Or.inl (by rw [e1]; exact h2)
    · exact Or.inr ⟨e1.trans e2, Nat.le_trans l1 l2⟩

theorem pairLe_antisymm {a b : Nat × Nat} (h1 : pairLe a b) (h2 : pairLe b a) : a = b := by
  rcases h1 with h1 | ⟨e1, l1⟩
  · rcases h2 with h2 | ⟨e2, _⟩
    · exact absurd h2 (Nat.lt_asymm h1)
    · exact absurd h1 (by rw [e2]; exact Nat.lt_irrefl _)
  · rcases h2 with h2 | ⟨_, l2⟩
    · exact absurd h2 (by rw [e1]; exact Nat.lt_irrefl _)
    · exact Prod.ext e1 (Nat.le_antisymm l1 l2)

theorem pairMin_of_le {a b : Nat × Nat} (h : pairLe a b) : pairMin a b = a :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

theorem pairMin_of_not_le {a b : Nat × Nat} (h : ¬ pairLe a b) : pairMin a b = b :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

theorem pairMin_le_left (a b : Nat × Nat) : pairLe (pairMin a b) a := by
  rcases Decidable.em (pairLe a b) with h | h
  · rw [pairMin_of_le h]
    exact pairLe_refl a
  · rw [pairMin_of_not_le h]
    rcases pairLe_total a b with h' | h'
    · exact absurd h' h
    · exact h'

theorem pairMin_le_right (a b : Nat × Nat) : pairLe (pairMin a b) b := by
  rcases Decidable.em (pairLe a b) with h | h
  · rw [pairMin_of_le h]
    exact h
  · rw [pairMin_of_not_le h]
    exact pairLe_refl b

theorem pairMin_mem (a b : Nat × Nat) : pairMin a b = a ∨ pairMin a b = b := by
  rcases Decidable.em (pairLe a b) with h | h
  · exact Or.inl (pairMin_of_le h)
  · exact Or.inr (pairMin_of_not_le h)

theorem foldl_pairMin_mem : ∀ (L : List (Nat × Nat)) (p : Nat × Nat),
    L.foldl pairMin p = p ∨ L.foldl pairMin p ∈ L
  | [], _ => Or.inl rfl
  | x :: L, p => by
      show L.foldl pairMin (pairMin p x) = p ∨ L.foldl pairMin (pairMin p x) ∈ x :: L
      rcases foldl_pairMin_mem L (pairMin p x) with h | h
      · rcases pairMin_mem p x with h' | h'
        · exact Or.inl (h.trans h')
        · exact Or.inr (by rw [h, h']; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem foldl_pairMin_le_init : ∀ (L : List (Nat × Nat)) (p : Nat × Nat),
    pairLe (L.foldl pairMin p) p
  | [], p => pairLe_refl p
  | x :: L, p => pairLe_trans (foldl_pairMin_le_init L (pairMin p x)) (pairMin_le_left p x)

theorem foldl_pairMin_le_mem : ∀ (L : List (Nat × Nat)) (p x : Nat × Nat), x ∈ L →
    pairLe (L.foldl pairMin p) x
  | [], _, _, h => nomatch h
  | y :: L, p, x, h => by
      show pairLe (L.foldl pairMin (pairMin p y)) x
      rcases List.mem_cons.mp h with rfl | h'
      · exact pairLe_trans (foldl_pairMin_le_init L _) (pairMin_le_right p x)
      · exact foldl_pairMin_le_mem L _ x h'

/-- The action of an exponent tuple on a pair, by one list of maps on each
    component. -/
def pairAct (fs1 fs2 : List (Nat → Nat)) (g : List Nat) (p : Nat × Nat) : Nat × Nat :=
  (actF fs1 g p.1, actF fs2 g p.2)

/-- The least pair of the orbit of `p`. -/
def pairRep (os : List Nat) (fs1 fs2 : List (Nat → Nat)) (p : Nat × Nat) : Nat × Nat :=
  ((groupElements os).map (fun g => pairAct fs1 fs2 g p)).foldl pairMin p

theorem orbitRep_eq (orders : List Nat) (first second : List (List Nat)) (p : Nat × Nat) :
    orbitRep orders first second p =
      pairRep orders (first.map permApply) (second.map permInv) p := by
  have e : (groupElements orders).map
        (fun g => (actFwd first g p.1, actInv second g p.2)) =
      (groupElements orders).map
        (fun g => pairAct (first.map permApply) (second.map permInv) g p) :=
    List.map_congr_left (fun g _ => by
      show (actFwd first g p.1, actInv second g p.2) =
        (actF (first.map permApply) g p.1, actF (second.map permInv) g p.2)
      rw [actFwd_eq, actInv_eq])
  unfold orbitRep pairRep
  rw [e]

theorem inGroup_zeros : ∀ os : List Nat, groupTyped os = true →
    InGroup os (os.map (fun _ => 0))
  | [], _ => trivial
  | o :: os, h => by
      unfold groupTyped at h
      rw [List.all_cons, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, inGroup_zeros os h.2⟩

section Orbits

variable {os : List Nat} {m n : Nat} {fs1 fs2 : List (Nat → Nat)}

theorem pairAct_lt (h1 : ActTyped m fs1 os) (h2 : ActTyped n fs2 os) (g : List Nat)
    (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    (pairAct fs1 fs2 g p).1 < m ∧ (pairAct fs1 fs2 g p).2 < n :=
  ⟨actF_lt fs1 os g h1 _ hp1, actF_lt fs2 os g h2 _ hp2⟩

theorem pairAct_gadd (h1 : ActTyped m fs1 os) (h2 : ActTyped n fs2 os) (g h : List Nat)
    (hg : InGroup os g) (hh : InGroup os h) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    pairAct fs1 fs2 h (pairAct fs1 fs2 g p) = pairAct fs1 fs2 (gadd os h g) p := by
  show (actF fs1 h (actF fs1 g p.1), actF fs2 h (actF fs2 g p.2)) =
    (actF fs1 (gadd os h g) p.1, actF fs2 (gadd os h g) p.2)
  rw [actF_gadd fs1 os g h h1 hg hh _ hp1, actF_gadd fs2 os g h h2 hg hh _ hp2]

theorem pairAct_gneg (h1 : ActTyped m fs1 os) (h2 : ActTyped n fs2 os) (g : List Nat)
    (hg : InGroup os g) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    pairAct fs1 fs2 (gneg os g) (pairAct fs1 fs2 g p) = p := by
  show (actF fs1 (gneg os g) (actF fs1 g p.1), actF fs2 (gneg os g) (actF fs2 g p.2)) = p
  rw [actF_gneg fs1 os g h1 hg _ hp1, actF_gneg fs2 os g h2 hg _ hp2]

theorem pairAct_gneg' (h1 : ActTyped m fs1 os) (h2 : ActTyped n fs2 os) (g : List Nat)
    (hg : InGroup os g) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    pairAct fs1 fs2 g (pairAct fs1 fs2 (gneg os g) p) = p := by
  show (actF fs1 g (actF fs1 (gneg os g) p.1), actF fs2 g (actF fs2 (gneg os g) p.2)) = p
  rw [actF_gneg' fs1 os g h1 hg _ hp1, actF_gneg' fs2 os g h2 hg _ hp2]

/-- The least pair of an orbit is a pair of the orbit. -/
theorem pairRep_mem (hos : groupTyped os = true) (h1 : ActTyped m fs1 os)
    (h2 : ActTyped n fs2 os) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    ∃ g, InGroup os g ∧ pairRep os fs1 fs2 p = pairAct fs1 fs2 g p := by
  rcases foldl_pairMin_mem ((groupElements os).map (fun g => pairAct fs1 fs2 g p)) p with h | h
  · have hz := inGroup_zeros os hos
    refine ⟨gadd os (gneg os (os.map (fun _ => 0))) (os.map (fun _ => 0)),
      inGroup_gadd os _ _ (inGroup_gneg os _ hz) hz, ?_⟩
    rw [← pairAct_gadd h1 h2 _ _ hz (inGroup_gneg os _ hz) p hp1 hp2,
      pairAct_gneg h1 h2 _ hz p hp1 hp2]
    exact h
  · obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp h
    exact ⟨g, (mem_groupElements os g).mp hg, hgeq.symm⟩

theorem pairRep_le (g : List Nat) (hg : InGroup os g) (p : Nat × Nat) :
    pairLe (pairRep os fs1 fs2 p) (pairAct fs1 fs2 g p) :=
  foldl_pairMin_le_mem _ _ _ (List.mem_map.mpr ⟨g, (mem_groupElements os g).mpr hg, rfl⟩)

/-- Every pair of an orbit has the same least pair. -/
theorem pairRep_act (hos : groupTyped os = true) (h1 : ActTyped m fs1 os)
    (h2 : ActTyped n fs2 os) (g : List Nat) (hg : InGroup os g) (p : Nat × Nat)
    (hp1 : p.1 < m) (hp2 : p.2 < n) :
    pairRep os fs1 fs2 (pairAct fs1 fs2 g p) = pairRep os fs1 fs2 p := by
  have hq := pairAct_lt h1 h2 g p hp1 hp2
  apply pairLe_antisymm
  · obtain ⟨h, hh, hrep⟩ := pairRep_mem hos h1 h2 p hp1 hp2
    have e : pairAct fs1 fs2 h p =
        pairAct fs1 fs2 (gadd os h (gneg os g)) (pairAct fs1 fs2 g p) := by
      rw [← pairAct_gadd h1 h2 (gneg os g) h (inGroup_gneg os g hg) hh _ hq.1 hq.2,
        pairAct_gneg h1 h2 g hg p hp1 hp2]
    rw [hrep, e]
    exact pairRep_le _ (inGroup_gadd os _ _ hh (inGroup_gneg os g hg)) _
  · obtain ⟨h, hh, hrep⟩ := pairRep_mem hos h1 h2 _ hq.1 hq.2
    rw [hrep, pairAct_gadd h1 h2 g h hg hh p hp1 hp2]
    exact pairRep_le _ (inGroup_gadd os _ _ hh hg) _

theorem pairRep_idem (hos : groupTyped os = true) (h1 : ActTyped m fs1 os)
    (h2 : ActTyped n fs2 os) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    pairRep os fs1 fs2 (pairRep os fs1 fs2 p) = pairRep os fs1 fs2 p := by
  obtain ⟨g, hg, hrep⟩ := pairRep_mem hos h1 h2 p hp1 hp2
  rw [hrep, pairRep_act hos h1 h2 g hg p hp1 hp2]
  exact hrep

theorem pairRep_lt (hos : groupTyped os = true) (h1 : ActTyped m fs1 os)
    (h2 : ActTyped n fs2 os) (p : Nat × Nat) (hp1 : p.1 < m) (hp2 : p.2 < n) :
    (pairRep os fs1 fs2 p).1 < m ∧ (pairRep os fs1 fs2 p).2 < n := by
  obtain ⟨g, _, hrep⟩ := pairRep_mem hos h1 h2 p hp1 hp2
  rw [hrep]
  exact pairAct_lt h1 h2 g p hp1 hp2

end Orbits

/-! ## Counting -/

/-- The number of entries where two parity vectors are both odd has the
    parity of the sum of the products of the counts. -/
theorem filter_odd_and_odd {α : Type} (f g : α → Nat) : ∀ L : List α,
    (L.filter (fun o => (f o % 2 == 1) && (g o % 2 == 1))).length % 2 =
      (L.map (fun o => f o * g o)).sum % 2
  | [] => rfl
  | o :: L => by
      have ih := filter_odd_and_odd f g L
      have hm : (f o * g o) % 2 = (f o % 2) * (g o % 2) % 2 := Nat.mul_mod _ _ _
      rw [List.map_cons, List.sum_cons]
      rcases Nat.mod_two_eq_zero_or_one (f o) with hf | hf
      · rw [hf, Nat.zero_mul] at hm
        rw [List.filter_cons_of_neg (by rw [hf]; exact Bool.false_ne_true)]
        omega
      · rcases Nat.mod_two_eq_zero_or_one (g o) with hg | hg
        · rw [hg, Nat.mul_zero] at hm
          rw [List.filter_cons_of_neg (by rw [hf, hg]; exact Bool.false_ne_true)]
          omega
        · rw [hf, hg] at hm
          rw [List.filter_cons_of_pos (by rw [hf, hg]; rfl), List.length_cons]
          omega

theorem length_filter_cons {α : Type} (q : α → Bool) (x : α) (X : List α) :
    ((x :: X).filter q).length = (if q x then 1 else 0) + (X.filter q).length := by
  cases h : q x with
  | true =>
      rw [List.filter_cons_of_pos h, List.length_cons]
      exact Nat.add_comm _ _
  | false =>
      rw [List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true)]
      exact (Nat.zero_add _).symm

theorem sum_map_add {α : Type} (a b : α → Nat) : ∀ L : List α,
    (L.map (fun o => a o + b o)).sum = (L.map a).sum + (L.map b).sum
  | [] => rfl
  | o :: L => by
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, sum_map_add a b L]
      omega

/-- Summing a weight over the fibers of a map: the points of `X` that
    satisfy `P`, grouped by their image in the repeat-free list `L`. -/
theorem sum_fiber {α β : Type} [BEq β] [LawfulBEq β] [DecidableEq β] (F : β → Nat)
    (P : α → Bool) (r : α → β) (L : List β) (hnd : L.Nodup) :
    ∀ X : List α, (∀ x ∈ X, r x ∈ L) →
    (L.map (fun o => F o * (X.filter (fun x => P x && (r x == o))).length)).sum =
      (X.map (fun x => if P x then F (r x) else 0)).sum
  | [], _ => by
      rw [List.map_nil, List.sum_nil]
      exact sum_map_zero _ L (fun o _ => Nat.mul_zero _)
  | x :: X, h => by
      have ih := sum_fiber F P r L hnd X (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have e : L.map (fun o => F o * ((x :: X).filter (fun x => P x && (r x == o))).length) =
          L.map (fun o => F o * (if P x && (r x == o) then 1 else 0) +
            F o * (X.filter (fun x => P x && (r x == o))).length) :=
        List.map_congr_left (fun o _ => by rw [length_filter_cons, Nat.mul_add])
      have hx : (L.map (fun o => F o * (if P x && (r x == o) then 1 else 0))).sum =
          if P x then F (r x) else 0 := by
        cases hP : P x with
        | false => exact sum_map_zero _ L (fun o _ => Nat.mul_zero _)
        | true =>
            apply sum_map_point (r x) (F (r x)) _ L hnd (h x (List.mem_cons_self ..))
            intro o _
            show F o * (if (true && (r x == o)) = true then 1 else 0) =
              if o = r x then F (r x) else 0
            rcases Decidable.em (o = r x) with e | e
            · have hb : (r x == o) = true := beq_iff_eq.mpr e.symm
              rw [hb, ite_eq_left_of_eq_true _ _ (eq_true e), e]
              exact Nat.mul_one _
            · have hb : (r x == o) = false := beq_eq_false_iff_ne.mpr (fun h => e h.symm)
              rw [hb, ite_eq_right_of_eq_false _ _ (eq_false e)]
              exact Nat.mul_zero _
      rw [e, sum_map_add, ih, hx, List.map_cons, List.sum_cons]

theorem filter_length_le_of_inj {α : Type} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (φ ψ : α → α) (hφ : ∀ x ∈ L, φ x ∈ L) (hψφ : ∀ x ∈ L, ψ (φ x) = x) (F : α → Bool) :
    (L.filter (fun x => F (φ x))).length ≤ (L.filter F).length := by
  have h1 : ((L.filter (fun x => F (φ x))).map φ).Nodup := by
    apply nodup_map_of_inj_on φ _ (nodup_filter_cf _ L hnd)
    intro x hx y hy hxy
    have hx' := (List.mem_filter.mp hx).1
    have hy' := (List.mem_filter.mp hy).1
    rw [← hψφ x hx', ← hψφ y hy', hxy]
  have h2 : ∀ z ∈ (L.filter (fun x => F (φ x))).map φ, z ∈ L.filter F := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    have hx' := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨hφ x hx'.1, hx'.2⟩
  have h3 := length_le_of_nodup_subset_gen _ _ h1 (nodup_filter_cf _ L hnd) h2
  rw [List.length_map] at h3
  exact h3

/-- Counting over a repeat-free list is invariant under a bijection of
    it. -/
theorem filter_length_bij {α : Type} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (φ ψ : α → α) (hφ : ∀ x ∈ L, φ x ∈ L) (hψ : ∀ x ∈ L, ψ x ∈ L)
    (hψφ : ∀ x ∈ L, ψ (φ x) = x) (hφψ : ∀ x ∈ L, φ (ψ x) = x) (F : α → Bool) :
    (L.filter (fun x => F (φ x))).length = (L.filter F).length := by
  apply Nat.le_antisymm (filter_length_le_of_inj L hnd φ ψ hφ hψφ F)
  have h := filter_length_le_of_inj L hnd ψ φ hψ hφψ (fun x => F (φ x))
  have hc : L.filter (fun x => F (φ (ψ x))) = L.filter F :=
    List.filter_congr (fun x hx => by rw [hφψ x hx])
  rw [hc] at h
  exact h

/-! ## The overlap -/

/-- The number of pairs `(a, j)` of the orbit `c` with `j = o.2` and
    `H₁[a, o.1]`: the entry of the `X`-row of `c` at the left qubit `o`,
    before reduction modulo 2. -/
def cntXL (repX : Nat × Nat → Nat × Nat) (H1 : List (List Bool)) (m1 n2 : Nat)
    (c o : Nat × Nat) : Nat :=
  ((indexPairs m1 n2).filter (fun p =>
    repX p == c && p.2 == o.2 && matEntry H1 p.1 o.1)).length

/-- The number of pairs `(a, j)` of the orbit `c` with `a = o.1` and
    `H₂[o.2, j]`: the entry of the `X`-row of `c` at the right qubit `o`. -/
def cntXR (repX : Nat × Nat → Nat × Nat) (H2 : List (List Bool)) (m1 n2 : Nat)
    (c o : Nat × Nat) : Nat :=
  ((indexPairs m1 n2).filter (fun p =>
    repX p == c && p.1 == o.1 && matEntry H2 o.2 p.2)).length

section Overlap

variable {os : List Nat} {m1 n1 m2 n2 : Nat} {R1 C1 R2 C2 : List (Nat → Nat)}
  {H1 H2 : List (List Bool)}

theorem pairAct_mem_indexPairs {m n : Nat} {fs1 fs2 : List (Nat → Nat)}
    (h1 : ActTyped m fs1 os) (h2 : ActTyped n fs2 os) (g : List Nat) (p : Nat × Nat)
    (hp : p ∈ indexPairs m n) : pairAct fs1 fs2 g p ∈ indexPairs m n := by
  obtain ⟨a, j⟩ := p
  have hp' := mem_indexPairs.mp hp
  exact mem_indexPairs.mpr ⟨actF_lt fs1 os g h1 a hp'.1, actF_lt fs2 os g h2 j hp'.2⟩

/-- The left entry of an `X`-row does not depend on the pair that names the
    left qubit. -/
theorem cntXL_rep (hos : groupTyped os = true) (hR1 : ActTyped m1 R1 os)
    (hC1 : ActTyped n1 C1 os) (hC2 : ActTyped n2 C2 os)
    (hE1 : ∀ g a i, a < m1 → i < n1 → matEntry H1 (actF R1 g a) (actF C1 g i) = matEntry H1 a i)
    (c : Nat × Nat) (i j : Nat) (hi : i < n1) (hj : j < n2) :
    cntXL (pairRep os R1 C2) H1 m1 n2 c (pairRep os C1 C2 (i, j)) =
      cntXL (pairRep os R1 C2) H1 m1 n2 c (i, j) := by
  obtain ⟨g, hg, hrep⟩ := pairRep_mem hos hC1 hC2 (i, j) hi hj
  rw [hrep]
  have hbij := filter_length_bij (indexPairs m1 n2) (nodup_indexPairs m1 n2)
    (pairAct R1 C2 g) (pairAct R1 C2 (gneg os g))
    (fun p hp => pairAct_mem_indexPairs hR1 hC2 g p hp)
    (fun p hp => pairAct_mem_indexPairs hR1 hC2 (gneg os g) p hp)
    (fun p hp => by
      obtain ⟨a, j'⟩ := p
      have hp' := mem_indexPairs.mp hp
      exact pairAct_gneg hR1 hC2 g hg (a, j') hp'.1 hp'.2)
    (fun p hp => by
      obtain ⟨a, j'⟩ := p
      have hp' := mem_indexPairs.mp hp
      exact pairAct_gneg' hR1 hC2 g hg (a, j') hp'.1 hp'.2)
    (fun p => pairRep os R1 C2 p == c && p.2 == actF C2 g j && matEntry H1 p.1 (actF C1 g i))
  refine hbij.symm.trans (congrArg List.length (List.filter_congr (fun p hp => ?_)))
  obtain ⟨a, j'⟩ := p
  have hp' := mem_indexPairs.mp hp
  show (pairRep os R1 C2 (pairAct R1 C2 g (a, j')) == c && actF C2 g j' == actF C2 g j &&
      matEntry H1 (actF R1 g a) (actF C1 g i)) =
    (pairRep os R1 C2 (a, j') == c && j' == j && matEntry H1 a i)
  rw [pairRep_act hos hR1 hC2 g hg (a, j') hp'.1 hp'.2, hE1 g a i hp'.1 hi,
    beq_congr_of_iff (a := actF C2 g j') (b := actF C2 g j) (c := j') (d := j)
      ⟨fun h => actF_inj C2 os g hC2 hg _ _ hp'.2 hj h, fun h => by rw [h]⟩]

/-- The right entry of an `X`-row does not depend on the pair that names
    the right qubit. -/
theorem cntXR_rep (hos : groupTyped os = true) (hR1 : ActTyped m1 R1 os)
    (hR2 : ActTyped m2 R2 os) (hC2 : ActTyped n2 C2 os)
    (hE2 : ∀ g b j, b < m2 → j < n2 → matEntry H2 (actF R2 g b) (actF C2 g j) = matEntry H2 b j)
    (c : Nat × Nat) (a0 b0 : Nat) (ha0 : a0 < m1) (hb0 : b0 < m2) :
    cntXR (pairRep os R1 C2) H2 m1 n2 c (pairRep os R1 R2 (a0, b0)) =
      cntXR (pairRep os R1 C2) H2 m1 n2 c (a0, b0) := by
  obtain ⟨g, hg, hrep⟩ := pairRep_mem hos hR1 hR2 (a0, b0) ha0 hb0
  rw [hrep]
  have hbij := filter_length_bij (indexPairs m1 n2) (nodup_indexPairs m1 n2)
    (pairAct R1 C2 g) (pairAct R1 C2 (gneg os g))
    (fun p hp => pairAct_mem_indexPairs hR1 hC2 g p hp)
    (fun p hp => pairAct_mem_indexPairs hR1 hC2 (gneg os g) p hp)
    (fun p hp => by
      obtain ⟨a, j'⟩ := p
      have hp' := mem_indexPairs.mp hp
      exact pairAct_gneg hR1 hC2 g hg (a, j') hp'.1 hp'.2)
    (fun p hp => by
      obtain ⟨a, j'⟩ := p
      have hp' := mem_indexPairs.mp hp
      exact pairAct_gneg' hR1 hC2 g hg (a, j') hp'.1 hp'.2)
    (fun p => pairRep os R1 C2 p == c && p.1 == actF R1 g a0 && matEntry H2 (actF R2 g b0) p.2)
  refine hbij.symm.trans (congrArg List.length (List.filter_congr (fun p hp => ?_)))
  obtain ⟨a, j'⟩ := p
  have hp' := mem_indexPairs.mp hp
  show (pairRep os R1 C2 (pairAct R1 C2 g (a, j')) == c && actF R1 g a == actF R1 g a0 &&
      matEntry H2 (actF R2 g b0) (actF C2 g j')) =
    (pairRep os R1 C2 (a, j') == c && a == a0 && matEntry H2 b0 j')
  rw [pairRep_act hos hR1 hC2 g hg (a, j') hp'.1 hp'.2, hE2 g b0 j' hb0 hp'.2,
    beq_congr_of_iff (a := actF R1 g a) (b := actF R1 g a0) (c := a) (d := a0)
      ⟨fun h => actF_inj R1 os g hR1 hg _ _ hp'.1 ha0 h, fun h => by rw [h]⟩]

/-- The overlap of the `X`-row of the orbit `c` with the `Z`-row of the
    pair `(i, b)` is even: the left qubits and the right qubits each
    contribute the number of pairs `(a, j)` of the orbit `c` with
    `H₁[a, i]` and `H₂[b, j]`. -/
theorem balanced_overlap_core (hos : groupTyped os = true) (hR1 : ActTyped m1 R1 os)
    (hC1 : ActTyped n1 C1 os) (hR2 : ActTyped m2 R2 os) (hC2 : ActTyped n2 C2 os)
    (hE1 : ∀ g a i, a < m1 → i < n1 → matEntry H1 (actF R1 g a) (actF C1 g i) = matEntry H1 a i)
    (hE2 : ∀ g b j, b < m2 → j < n2 → matEntry H2 (actF R2 g b) (actF C2 g j) = matEntry H2 b j)
    (left right : List (Nat × Nat)) (hleftnd : left.Nodup) (hrightnd : right.Nodup)
    (hleft : ∀ p : Nat × Nat, p.1 < n1 → p.2 < n2 → pairRep os C1 C2 p = p → p ∈ left)
    (hright : ∀ p : Nat × Nat, p.1 < m1 → p.2 < m2 → pairRep os R1 R2 p = p → p ∈ right)
    (c : Nat × Nat) (i b : Nat) (hi : i < n1) (hb : b < m2) :
    dotPar
      (left.map (fun o => cntXL (pairRep os R1 C2) H1 m1 n2 c o % 2 == 1) ++
        right.map (fun o => cntXR (pairRep os R1 C2) H2 m1 n2 c o % 2 == 1))
      (left.map (fun o => ((List.range n2).filter (fun j =>
          matEntry H2 b j && pairRep os C1 C2 (i, j) == o)).length % 2 == 1) ++
        right.map (fun o => ((List.range m1).filter (fun a =>
          matEntry H1 a i && pairRep os R1 R2 (a, b) == o)).length % 2 == 1)) % 2 = 0 := by
  rw [dotPar_append _ _ _ _ (by rw [List.length_map, List.length_map]), dotPar_map_map_gen,
    dotPar_map_map_gen]
  have hL := filter_odd_and_odd (cntXL (pairRep os R1 C2) H1 m1 n2 c)
    (fun o => ((List.range n2).filter (fun j =>
      matEntry H2 b j && pairRep os C1 C2 (i, j) == o)).length) left
  have hR := filter_odd_and_odd (cntXR (pairRep os R1 C2) H2 m1 n2 c)
    (fun o => ((List.range m1).filter (fun a =>
      matEntry H1 a i && pairRep os R1 R2 (a, b) == o)).length) right
  -- the left qubits
  have sL1 := sum_fiber (cntXL (pairRep os R1 C2) H1 m1 n2 c) (fun j => matEntry H2 b j)
    (fun j => pairRep os C1 C2 (i, j)) left hleftnd (List.range n2) (fun j hj => by
      have hj' := List.mem_range.mp hj
      have hlt := pairRep_lt hos hC1 hC2 (i, j) hi hj'
      exact hleft _ hlt.1 hlt.2 (pairRep_idem hos hC1 hC2 (i, j) hi hj'))
  have sL2 : (List.range n2).map (fun j => if matEntry H2 b j then
        cntXL (pairRep os R1 C2) H1 m1 n2 c (pairRep os C1 C2 (i, j)) else 0) =
      (List.range n2).map (fun j => (if matEntry H2 b j then 1 else 0) *
        ((indexPairs m1 n2).filter (fun p =>
          (pairRep os R1 C2 p == c && matEntry H1 p.1 i) && (p.2 == j))).length) :=
    List.map_congr_left (fun j hj => by
      rw [cntXL_rep hos hR1 hC1 hC2 hE1 c i j hi (List.mem_range.mp hj)]
      have e : cntXL (pairRep os R1 C2) H1 m1 n2 c (i, j) =
          ((indexPairs m1 n2).filter (fun p =>
            (pairRep os R1 C2 p == c && matEntry H1 p.1 i) && (p.2 == j))).length :=
        congrArg List.length (List.filter_congr (fun p _ => by
          show (pairRep os R1 C2 p == c && p.2 == j && matEntry H1 p.1 i) =
            ((pairRep os R1 C2 p == c && matEntry H1 p.1 i) && (p.2 == j))
          cases (pairRep os R1 C2 p == c) <;> cases (p.2 == j) <;>
            cases (matEntry H1 p.1 i) <;> rfl))
      rw [e]
      cases matEntry H2 b j with
      | true => exact (Nat.one_mul _).symm
      | false => exact (Nat.zero_mul _).symm)
  have sL3 := sum_fiber (fun j => if matEntry H2 b j then 1 else 0)
    (fun p : Nat × Nat => pairRep os R1 C2 p == c && matEntry H1 p.1 i) Prod.snd
    (List.range n2) (nodup_range_cf n2) (indexPairs m1 n2) (fun p hp => by
      obtain ⟨a, j⟩ := p
      exact List.mem_range.mpr (mem_indexPairs.mp hp).2)
  -- the right qubits
  have sR1 := sum_fiber (cntXR (pairRep os R1 C2) H2 m1 n2 c) (fun a => matEntry H1 a i)
    (fun a => pairRep os R1 R2 (a, b)) right hrightnd (List.range m1) (fun a ha => by
      have ha' := List.mem_range.mp ha
      have hlt := pairRep_lt hos hR1 hR2 (a, b) ha' hb
      exact hright _ hlt.1 hlt.2 (pairRep_idem hos hR1 hR2 (a, b) ha' hb))
  have sR2 : (List.range m1).map (fun a => if matEntry H1 a i then
        cntXR (pairRep os R1 C2) H2 m1 n2 c (pairRep os R1 R2 (a, b)) else 0) =
      (List.range m1).map (fun a => (if matEntry H1 a i then 1 else 0) *
        ((indexPairs m1 n2).filter (fun p =>
          (pairRep os R1 C2 p == c && matEntry H2 b p.2) && (p.1 == a))).length) :=
    List.map_congr_left (fun a ha => by
      rw [cntXR_rep hos hR1 hR2 hC2 hE2 c a b (List.mem_range.mp ha) hb]
      have e : cntXR (pairRep os R1 C2) H2 m1 n2 c (a, b) =
          ((indexPairs m1 n2).filter (fun p =>
            (pairRep os R1 C2 p == c && matEntry H2 b p.2) && (p.1 == a))).length :=
        congrArg List.length (List.filter_congr (fun p _ => by
          show (pairRep os R1 C2 p == c && p.1 == a && matEntry H2 b p.2) =
            ((pairRep os R1 C2 p == c && matEntry H2 b p.2) && (p.1 == a))
          cases (pairRep os R1 C2 p == c) <;> cases (p.1 == a) <;>
            cases (matEntry H2 b p.2) <;> rfl))
      rw [e]
      cases matEntry H1 a i with
      | true => exact (Nat.one_mul _).symm
      | false => exact (Nat.zero_mul _).symm)
  have sR3 := sum_fiber (fun a => if matEntry H1 a i then 1 else 0)
    (fun p : Nat × Nat => pairRep os R1 C2 p == c && matEntry H2 b p.2) Prod.fst
    (List.range m1) (nodup_range_cf m1) (indexPairs m1 n2) (fun p hp => by
      obtain ⟨a, j⟩ := p
      exact List.mem_range.mpr (mem_indexPairs.mp hp).1)
  -- the two contributions agree
  have hsame : (indexPairs m1 n2).map (fun p : Nat × Nat =>
        if pairRep os R1 C2 p == c && matEntry H2 b p.2 then
          (if matEntry H1 p.1 i then 1 else 0) else 0) =
      (indexPairs m1 n2).map (fun p : Nat × Nat =>
        if pairRep os R1 C2 p == c && matEntry H1 p.1 i then
          (if matEntry H2 b p.2 then 1 else 0) else 0) :=
    List.map_congr_left (fun p _ => by
      cases (pairRep os R1 C2 p == c) <;> cases (matEntry H2 b p.2) <;>
        cases (matEntry H1 p.1 i) <;> rfl)
  rw [sL1, sL2, sL3] at hL
  rw [sR1, sR2, sR3, hsame] at hR
  omega

end Overlap

/-! ## The natural rows of `L-BALANCED` -/

/-- The natural `X`-row of the orbit `c` of the pairs `(a, j)`. -/
def balancedXVector (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) (c : Nat × Nat) : List Bool :=
  (orbitReps orders cols1 cols2 (matCols H1) (matCols H2)).map (fun o =>
    ((indexPairs H1.length (matCols H2)).filter (fun p =>
      orbitRep orders rows1 cols2 p == c && p.2 == o.2 && matEntry H1 p.1 o.1)).length
        % 2 == 1) ++
  (orbitReps orders rows1 rows2 H1.length H2.length).map (fun o =>
    ((indexPairs H1.length (matCols H2)).filter (fun p =>
      orbitRep orders rows1 cols2 p == c && p.1 == o.1 && matEntry H2 o.2 p.2)).length
        % 2 == 1)

/-- The natural `Z`-row of the orbit of the pairs `(i, b)` with least pair
    `c`. -/
def balancedZVector (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) (c : Nat × Nat) : List Bool :=
  (orbitReps orders cols1 cols2 (matCols H1) (matCols H2)).map (fun o =>
    ((List.range (matCols H2)).filter (fun j =>
      matEntry H2 c.2 j && orbitRep orders cols1 cols2 (c.1, j) == o)).length % 2 == 1) ++
  (orbitReps orders rows1 rows2 H1.length H2.length).map (fun o =>
    ((List.range H1.length).filter (fun a =>
      matEntry H1 a c.1 && orbitRep orders rows1 rows2 (a, c.2) == o)).length % 2 == 1)

theorem balancedVectors_eq (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat)) :
    balancedVectors orders H1 rows1 cols1 H2 rows2 cols2 =
      (orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun c =>
        (Sector.X, balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c)) ++
      (orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun c =>
        (Sector.Z, balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c)) := rfl

theorem length_balancedXVector (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat))
    (c : Nat × Nat) :
    (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c).length =
      balancedQubits orders H1 rows1 cols1 H2 rows2 cols2 := by
  unfold balancedXVector balancedQubits
  rw [List.length_append, List.length_map, List.length_map]

theorem length_balancedZVector (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat))
    (c : Nat × Nat) :
    (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c).length =
      balancedQubits orders H1 rows1 cols1 H2 rows2 cols2 := by
  unfold balancedZVector balancedQubits
  rw [List.length_append, List.length_map, List.length_map]

theorem mem_orbitReps_of_fixed (orders : List Nat) (first second : List (List Nat))
    (m n : Nat) (p : Nat × Nat) (h1 : p.1 < m) (h2 : p.2 < n)
    (hfix : pairRep orders (first.map permApply) (second.map permInv) p = p) :
    p ∈ orbitReps orders first second m n := by
  obtain ⟨a, j⟩ := p
  unfold orbitReps
  exact List.mem_filter.mpr ⟨mem_indexPairs.mpr ⟨h1, h2⟩,
    beq_iff_eq.mpr ((orbitRep_eq orders first second (a, j)).trans hfix)⟩

/-- §4.35: the natural `X`-row of any orbit and the natural `Z`-row of any
    pair `(i, b)` have even overlap, for a typed input. -/
theorem balanced_overlap (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat))
    (hty : balancedTyped orders H1 rows1 cols1 H2 rows2 cols2 = true) (c e : Nat × Nat)
    (he : e ∈ indexPairs (matCols H1) H2.length) :
    dotPar (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c)
      (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 e) % 2 = 0 := by
  simp only [balancedTyped, Bool.and_eq_true] at hty
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨t1, _⟩, _⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩ := hty
  obtain ⟨i, b⟩ := e
  have he' := mem_indexPairs.mp he
  have hR1 := actTyped_fwd t4
  have hC1 := actTyped_fwd t5
  have hR2 := actTyped_inv t6
  have hC2 := actTyped_inv t7
  have hE1 : ∀ g a i, a < H1.length → i < matCols H1 →
      matEntry H1 (actF (rows1.map permApply) g a) (actF (cols1.map permApply) g i) =
        matEntry H1 a i :=
    fun g a i ha hi => matEntry_actF _ _ g
      ((actTyped_length _ _ hR1).trans (actTyped_length _ _ hC1).symm) (equivF_fwd t8)
      (actTyped_maps _ _ hR1) (actTyped_maps _ _ hC1) a i ha hi
  have hE2 : ∀ g b j, b < H2.length → j < matCols H2 →
      matEntry H2 (actF (rows2.map permInv) g b) (actF (cols2.map permInv) g j) =
        matEntry H2 b j :=
    fun g b j hb hj => matEntry_actF _ _ g
      ((actTyped_length _ _ hR2).trans (actTyped_length _ _ hC2).symm) (equivF_inv t6 t7 t9)
      (actTyped_maps _ _ hR2) (actTyped_maps _ _ hC2) b j hb hj
  have hX : orbitRep orders rows1 cols2 =
      pairRep orders (rows1.map permApply) (cols2.map permInv) :=
    funext (orbitRep_eq orders rows1 cols2)
  have hL : orbitRep orders cols1 cols2 =
      pairRep orders (cols1.map permApply) (cols2.map permInv) :=
    funext (orbitRep_eq orders cols1 cols2)
  have hR : orbitRep orders rows1 rows2 =
      pairRep orders (rows1.map permApply) (rows2.map permInv) :=
    funext (orbitRep_eq orders rows1 rows2)
  have hcore := balanced_overlap_core t1 hR1 hC1 hR2 hC2 hE1 hE2
    (orbitReps orders cols1 cols2 (matCols H1) (matCols H2))
    (orbitReps orders rows1 rows2 H1.length H2.length)
    (nodup_filter_cf _ _ (nodup_indexPairs _ _)) (nodup_filter_cf _ _ (nodup_indexPairs _ _))
    (fun p h1 h2 hfix => mem_orbitReps_of_fixed orders cols1 cols2 _ _ p h1 h2 hfix)
    (fun p h1 h2 hfix => mem_orbitReps_of_fixed orders rows1 rows2 _ _ p h1 h2 hfix)
    c i b he'.1 he'.2
  unfold balancedXVector balancedZVector
  rw [hX, hL, hR]
  exact hcore

/-- The natural rows of `L-BALANCED` have pairwise even overlap across the
    sectors, for every typed input. -/
theorem balanced_naturalOrthogonal (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat))
    (hty : balancedTyped orders H1 rows1 cols1 H2 rows2 cols2 = true) :
    NaturalOrthogonal (naturalRows (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
      (balancedVectors orders H1 rows1 cols1 H2 rows2 cols2)) := by
  have e : balancedVectors orders H1 rows1 cols1 H2 rows2 cols2 =
      ((orbitReps orders rows1 cols2 H1.length (matCols H2)).map
        (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2)).map
          (fun v => (Sector.X, v)) ++
      ((orbitReps orders cols1 rows2 (matCols H1) H2.length).map
        (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2)).map
          (fun v => (Sector.Z, v)) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [e]
  apply naturalOrthogonal_of_cross
  · intro v hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
    exact length_balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c
  · intro v hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
    exact length_balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c
  · intro vx hvx vz hvz
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hvx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hvz
    exact balanced_overlap orders H1 rows1 cols1 H2 rows2 cols2 hty c e'
      (List.mem_filter.mp he').1

/-- The output of `L-BALANCED` on a typed input is well-formed. -/
theorem wf_balancedState (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat))
    (hty : balancedTyped orders H1 rows1 cols1 H2 rows2 cols2 = true) :
    EncodingWellFormed (balancedState orders H1 rows1 cols1 H2 rows2 cols2) :=
  wf_constructedState _ _
    (balanced_naturalOrthogonal orders H1 rows1 cols1 H2 rows2 cols2 hty)

/-- `L-BALANCED`: every evaluation yields a well-formed state, with no
    hypothesis. -/
theorem evalExpr_balanced_wellFormed {orders : List Nat} {H1 H2 : List (List Bool)}
    {rows1 cols1 rows2 cols2 : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s) :
    EncodingWellFormed s := by
  cases h with
  | balanced hty _ => exact wf_balancedState orders H1 rows1 cols1 H2 rows2 cols2 hty

end CodeCalculus
