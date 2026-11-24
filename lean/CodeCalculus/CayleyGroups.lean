import CodeCalculus.Constructors

/-!
# Finite groups by operations, and the Cayley constructions over them

The definitions of the group-based constructors over an arbitrary finite
group (issue #565, `spec/OPERATIONAL_SEMANTICS.md` §4.44): the structure
`FiniteGroup`, the left and right regular rows, the natural vectors and
constructed states of `L-GROUP-ALGEBRA`, `L-LIFTED`, and `L-BALANCED`, and
the right and left actions the last one reads.

They live here, ahead of `Eval.lean`, so that the evaluation relation can
name them (issue #631). Their theorems stay where they were proved:
`ConstructorOverlap.lean` for the two-block and lifted constructions and
`BalancedOverlap.lean` for the balanced one.
-/

namespace CodeCalculus

/-- A finite group on `{0, ..., order - 1}` with explicit multiplication,
    inverse, and identity operations satisfying the group axioms. -/
structure FiniteGroup where
  order : Nat
  mul : Nat → Nat → Nat
  inv : Nat → Nat
  e : Nat
  h_e : e < order
  h_mul_lt : ∀ a b, a < order → b < order → mul a b < order
  h_inv_lt : ∀ a, a < order → inv a < order
  h_assoc : ∀ a b c, a < order → b < order → c < order →
    mul (mul a b) c = mul a (mul b c)
  h_mul_e : ∀ a, a < order → mul a e = a
  h_e_mul : ∀ a, a < order → mul e a = a
  h_mul_inv : ∀ a, a < order → mul a (inv a) = e
  h_inv_mul : ∀ a, a < order → mul (inv a) a = e

namespace FiniteGroup

theorem inv_inv (G : FiniteGroup) {a : Nat} (ha : a < G.order) :
    G.inv (G.inv a) = a := by
  have hia : G.inv a < G.order := G.h_inv_lt a ha
  have hiia : G.inv (G.inv a) < G.order := G.h_inv_lt _ hia
  calc
    G.inv (G.inv a) = G.mul (G.inv (G.inv a)) G.e := (G.h_mul_e _ hiia).symm
    _ = G.mul (G.inv (G.inv a)) (G.mul (G.inv a) a) := by rw [G.h_inv_mul a ha]
    _ = G.mul (G.mul (G.inv (G.inv a)) (G.inv a)) a := (G.h_assoc _ _ _ hiia hia ha).symm
    _ = G.mul G.e a := by rw [G.h_inv_mul _ hia]
    _ = a := G.h_e_mul a ha

theorem inv_mul (G : FiniteGroup) {a b : Nat} (ha : a < G.order) (hb : b < G.order) :
    G.inv (G.mul a b) = G.mul (G.inv b) (G.inv a) := by
  have hab : G.mul a b < G.order := G.h_mul_lt a b ha hb
  have hiab : G.inv (G.mul a b) < G.order := G.h_inv_lt _ hab
  have hia : G.inv a < G.order := G.h_inv_lt a ha
  have hib : G.inv b < G.order := G.h_inv_lt b hb
  have hba : G.mul (G.inv b) (G.inv a) < G.order := G.h_mul_lt _ _ hib hia
  have hcancel : G.mul (G.mul (G.inv b) (G.inv a)) (G.mul a b) = G.e := by
    calc
      G.mul (G.mul (G.inv b) (G.inv a)) (G.mul a b)
          = G.mul (G.inv b) (G.mul (G.inv a) (G.mul a b)) :=
              G.h_assoc _ _ _ hib hia hab
      _ = G.mul (G.inv b) (G.mul (G.mul (G.inv a) a) b) := by
              rw [G.h_assoc _ _ _ hia ha hb]
      _ = G.mul (G.inv b) (G.mul G.e b) := by rw [G.h_inv_mul a ha]
      _ = G.mul (G.inv b) b := by rw [G.h_e_mul b hb]
      _ = G.e := G.h_inv_mul b hb
  calc
    G.inv (G.mul a b) = G.mul G.e (G.inv (G.mul a b)) := (G.h_e_mul _ hiab).symm
    _ = G.mul (G.mul (G.mul (G.inv b) (G.inv a)) (G.mul a b)) (G.inv (G.mul a b)) := by
          rw [hcancel]
    _ = G.mul (G.mul (G.inv b) (G.inv a)) (G.mul (G.mul a b) (G.inv (G.mul a b))) :=
          G.h_assoc _ _ _ hba hab hiab
    _ = G.mul (G.mul (G.inv b) (G.inv a)) G.e := by rw [G.h_mul_inv _ hab]
    _ = G.mul (G.inv b) (G.inv a) := G.h_mul_e _ hba

/-- The bijection `φ_{h, h'}(k) = h k⁻¹ h'` of §4.44. -/
def phi (G : FiniteGroup) (h h' k : Nat) : Nat :=
  G.mul h (G.mul (G.inv k) h')

theorem phi_lt (G : FiniteGroup) {h h' k : Nat}
    (hh : h < G.order) (hh' : h' < G.order) (hk : k < G.order) :
    G.phi h h' k < G.order :=
  G.h_mul_lt h _ hh (G.h_mul_lt _ h' (G.h_inv_lt k hk) hh')

theorem phi_mul_inv_right (G : FiniteGroup) {h h' k : Nat}
    (hh : h < G.order) (hh' : h' < G.order) (hk : k < G.order) :
    G.mul (G.phi h h' k) (G.inv h') = G.mul h (G.inv k) := by
  have hik : G.inv k < G.order := G.h_inv_lt k hk
  have hih' : G.inv h' < G.order := G.h_inv_lt h' hh'
  have hikh' : G.mul (G.inv k) h' < G.order := G.h_mul_lt _ _ hik hh'
  unfold phi
  calc
    G.mul (G.mul h (G.mul (G.inv k) h')) (G.inv h')
        = G.mul h (G.mul (G.mul (G.inv k) h') (G.inv h')) :=
            G.h_assoc _ _ _ hh hikh' hih'
    _ = G.mul h (G.mul (G.inv k) (G.mul h' (G.inv h'))) := by
            rw [G.h_assoc _ _ _ hik hh' hih']
    _ = G.mul h (G.mul (G.inv k) G.e) := by rw [G.h_mul_inv h' hh']
    _ = G.mul h (G.inv k) := by rw [G.h_mul_e _ hik]

theorem inv_mul_phi (G : FiniteGroup) {h h' k : Nat}
    (hh : h < G.order) (hh' : h' < G.order) (hk : k < G.order) :
    G.mul (G.inv h) (G.phi h h' k) = G.mul (G.inv k) h' := by
  have hik : G.inv k < G.order := G.h_inv_lt k hk
  have hih : G.inv h < G.order := G.h_inv_lt h hh
  have hikh' : G.mul (G.inv k) h' < G.order := G.h_mul_lt _ _ hik hh'
  unfold phi
  calc
    G.mul (G.inv h) (G.mul h (G.mul (G.inv k) h'))
        = G.mul (G.mul (G.inv h) h) (G.mul (G.inv k) h') :=
            (G.h_assoc _ _ _ hih hh hikh').symm
    _ = G.mul G.e (G.mul (G.inv k) h') := by rw [G.h_inv_mul h hh]
    _ = G.mul (G.inv k) h' := G.h_e_mul _ hikh'

theorem inv_phi_mul_right (G : FiniteGroup) {h h' k : Nat}
    (hh : h < G.order) (hh' : h' < G.order) (hk : k < G.order) :
    G.mul (G.inv (G.phi h h' k)) h = G.mul (G.inv h') k := by
  have hik : G.inv k < G.order := G.h_inv_lt k hk
  have hih : G.inv h < G.order := G.h_inv_lt h hh
  have hih' : G.inv h' < G.order := G.h_inv_lt h' hh'
  have hikh' : G.mul (G.inv k) h' < G.order := G.h_mul_lt _ _ hik hh'
  have hh'k : G.mul (G.inv h') k < G.order := G.h_mul_lt _ _ hih' hk
  unfold phi
  rw [G.inv_mul hh hikh', G.inv_mul hik hh', G.inv_inv hk]
  calc
    G.mul (G.mul (G.mul (G.inv h') k) (G.inv h)) h
        = G.mul (G.mul (G.inv h') k) (G.mul (G.inv h) h) :=
            G.h_assoc _ _ _ hh'k hih hh
    _ = G.mul (G.mul (G.inv h') k) G.e := by rw [G.h_inv_mul h hh]
    _ = G.mul (G.inv h') k := G.h_mul_e _ hh'k

theorem phi_symm_inv (G : FiniteGroup) {h h' k : Nat}
    (hh : h < G.order) (hh' : h' < G.order) (hk : k < G.order) :
    G.phi h' h (G.phi h h' k) = k := by
  have hih' : G.inv h' < G.order := G.h_inv_lt h' hh'
  unfold phi
  show G.mul h' (G.mul (G.inv (G.phi h h' k)) h) = k
  rw [G.inv_phi_mul_right hh hh' hk]
  calc
    G.mul h' (G.mul (G.inv h') k)
        = G.mul (G.mul h' (G.inv h')) k := (G.h_assoc _ _ _ hh' hih' hk).symm
    _ = G.mul G.e k := by rw [G.h_mul_inv h' hh']
    _ = k := G.h_e_mul k hk

end FiniteGroup

/-- Coefficient of group element `g` in `x ∈ 𝔽₂[G]` (terms reduced modulo `G.order`). -/
def cayleyCoeff (G : FiniteGroup) (x : List Nat) (g : Nat) : Bool :=
  (x.filter (fun t => t % G.order == g)).length % 2 == 1

/-- Antipode involution `x* = ∑_{g ∈ x} g⁻¹` on `𝔽₂[G]`. -/
def cayleyInv (G : FiniteGroup) (x : List Nat) : List Nat :=
  x.map (fun t => G.inv (t % G.order))

/-- Row `h` of the left regular representation `L(x)[h, k] = x(h k⁻¹)`. -/
def cayleyLeftRow (G : FiniteGroup) (x : List Nat) (h : Nat) : List Bool :=
  (List.range G.order).map (fun k => cayleyCoeff G x (G.mul h (G.inv k)))

/-- Row `h` of the right regular representation `R(y)[h, k] = y(k⁻¹ h)`. -/
def cayleyRightRow (G : FiniteGroup) (y : List Nat) (h : Nat) : List Bool :=
  (List.range G.order).map (fun k => cayleyCoeff G y (G.mul (G.inv k) h))

/-- Natural vectors of `L-GROUP-ALGEBRA` over an arbitrary finite group `G`:
    `H_X = [L(a) | R(b)]` and `H_Z = [R(b*) | L(a*)]`. -/
def cayleyTwoblockVectors (G : FiniteGroup) (a b : List Nat) :
    List (Sector × List Bool) :=
  ((List.range G.order).map (fun h => cayleyLeftRow G a h ++ cayleyRightRow G b h)).map
    (fun v => (Sector.X, v)) ++
  ((List.range G.order).map (fun h =>
      cayleyRightRow G (cayleyInv G b) h ++ cayleyLeftRow G (cayleyInv G a) h)).map
    (fun v => (Sector.Z, v))

/-- Constructed state of `L-GROUP-ALGEBRA` over an arbitrary finite group `G`. -/
def cayleyTwoblockState (G : FiniteGroup) (a b : List Nat) : CodeState :=
  constructedState (2 * G.order) (cayleyTwoblockVectors G a b)

/-- Matrix entry helper over `𝔽₂[G]` with elements encoded as `List Nat`. -/
def cayleyEntry (M : List (List (List Nat))) (r c : Nat) : List Nat :=
  (M.getD r []).getD c []

/-- Number of columns of a matrix over `𝔽₂[G]`. -/
def cayleyMatCols (M : List (List (List Nat))) : Nat :=
  match M with
  | [] => 0
  | r :: _ => r.length

/-- Qubit count `|G| (n_A n_B + m_A m_B)` for `L-LIFTED` over `G`. -/
def cayleyLiftQubits (G : FiniteGroup) (A B : List (List (List Nat))) : Nat :=
  G.order * (cayleyMatCols A * cayleyMatCols B + A.length * B.length)

/-- Natural `X`-row `(a, j, h)` of `L-LIFTED` over an arbitrary finite group `G`. -/
def cayleyLiftXVector (G : FiniteGroup) (A B : List (List (List Nat)))
    (aj : Nat × Nat) (h : Nat) : List Bool :=
  (indexPairs (cayleyMatCols A) (cayleyMatCols B)).flatMap (fun ij =>
    if ij.2 = aj.2 then cayleyLeftRow G (cayleyEntry A aj.1 ij.1) h
    else List.replicate G.order false) ++
  (indexPairs A.length B.length).flatMap (fun ab =>
    if ab.1 = aj.1 then cayleyRightRow G (cayleyInv G (cayleyEntry B ab.2 aj.2)) h
    else List.replicate G.order false)

/-- Natural `Z`-row `(i, b, h)` of `L-LIFTED` over an arbitrary finite group `G`. -/
def cayleyLiftZVector (G : FiniteGroup) (A B : List (List (List Nat)))
    (ib : Nat × Nat) (h : Nat) : List Bool :=
  (indexPairs (cayleyMatCols A) (cayleyMatCols B)).flatMap (fun ij =>
    if ij.1 = ib.1 then cayleyRightRow G (cayleyEntry B ib.2 ij.2) h
    else List.replicate G.order false) ++
  (indexPairs A.length B.length).flatMap (fun ab =>
    if ab.2 = ib.2 then cayleyLeftRow G (cayleyInv G (cayleyEntry A ab.1 ib.1)) h
    else List.replicate G.order false)

/-- Natural vectors of `L-LIFTED` over an arbitrary finite group `G`. -/
def cayleyLiftVectors (G : FiniteGroup) (A B : List (List (List Nat))) :
    List (Sector × List Bool) :=
  ((indexPairs A.length (cayleyMatCols B)).flatMap (fun aj =>
    (List.range G.order).map (cayleyLiftXVector G A B aj))).map (fun v => (Sector.X, v)) ++
  ((indexPairs (cayleyMatCols A) B.length).flatMap (fun ib =>
    (List.range G.order).map (cayleyLiftZVector G A B ib))).map (fun v => (Sector.Z, v))

/-- Constructed state of `L-LIFTED` over an arbitrary finite group `G`. -/
def cayleyLiftState (G : FiniteGroup) (A B : List (List (List Nat))) : CodeState :=
  constructedState (cayleyLiftQubits G A B) (cayleyLiftVectors G A B)

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

/-- A right action of `G : FiniteGroup` on `{0, …, size - 1}`. -/
structure FiniteRightAction (G : FiniteGroup) (size : Nat) where
  act : Nat → Nat → Nat
  h_lt : ∀ g x, g < G.order → x < size → act g x < size
  h_e : ∀ x, x < size → act G.e x = x
  h_mul : ∀ g h x, g < G.order → h < G.order → x < size →
    act (G.mul g h) x = act h (act g x)

/-- A left action of `G : FiniteGroup` on `{0, …, size - 1}`. -/
structure FiniteLeftAction (G : FiniteGroup) (size : Nat) where
  act : Nat → Nat → Nat
  h_lt : ∀ g x, g < G.order → x < size → act g x < size
  h_e : ∀ x, x < size → act G.e x = x
  h_mul : ∀ g h x, g < G.order → h < G.order → x < size →
    act (G.mul g h) x = act g (act h x)

theorem FiniteGroup.inv_e (G : FiniteGroup) : G.inv G.e = G.e := by
  have h1 := G.h_e_mul (G.inv G.e) (G.h_inv_lt G.e G.h_e)
  have h2 := G.h_mul_inv G.e G.h_e
  exact h1.symm.trans h2

/-- Turning a left action `α₂` of `G` into the right action `g ↦ α₂(g⁻¹)`. -/
def FiniteLeftAction.toRight {G : FiniteGroup} {size : Nat}
    (A : FiniteLeftAction G size) : FiniteRightAction G size where
  act := fun g x => A.act (G.inv g) x
  h_lt := fun g x hg hx => A.h_lt (G.inv g) x (G.h_inv_lt g hg) hx
  h_e := fun x hx => by rw [G.inv_e]; exact A.h_e x hx
  h_mul := fun g h x hg hh hx => by
    rw [G.inv_mul hg hh, A.h_mul (G.inv h) (G.inv g) x (G.h_inv_lt h hh) (G.h_inv_lt g hg) hx]

/-- Diagonal right action `Φ_g(x, y) = (A1.act g x, A2.act g y)` of `G` on pairs. -/
def cayleyPairAct {G : FiniteGroup} {m n : Nat}
    (A1 : FiniteRightAction G m) (A2 : FiniteRightAction G n)
    (g : Nat) (p : Nat × Nat) : Nat × Nat :=
  (A1.act g p.1, A2.act g p.2)

/-- Least pair of the `G`-orbit of `p`. -/
def cayleyPairRep (G : FiniteGroup) {m n : Nat}
    (A1 : FiniteRightAction G m) (A2 : FiniteRightAction G n)
    (p : Nat × Nat) : Nat × Nat :=
  ((List.range G.order).map (fun g => cayleyPairAct A1 A2 g p)).foldl pairMin p

/-- Lexicographically ordered list of orbit representatives on `{0,…,m-1} × {0,…,n-1}`. -/
def cayleyOrbitReps (G : FiniteGroup) {m n : Nat}
    (A1 : FiniteRightAction G m) (A2 : FiniteRightAction G n) : List (Nat × Nat) :=
  (indexPairs m n).filter (fun p => cayleyPairRep G A1 A2 p == p)

/-- Qubit count of nonabelian `L-BALANCED`: left orbit count + right orbit count. -/
def cayleyBalancedQubits (G : FiniteGroup) (H1 H2 : List (List Bool))
    (R1 : FiniteRightAction G H1.length) (C1 : FiniteRightAction G (matCols H1))
    (R2 : FiniteLeftAction G H2.length) (C2 : FiniteLeftAction G (matCols H2)) : Nat :=
  (cayleyOrbitReps G C1 C2.toRight).length + (cayleyOrbitReps G R1 R2.toRight).length

/-- Natural `X`-row of orbit `c` in nonabelian `L-BALANCED`. -/
def cayleyBalancedXVector (G : FiniteGroup) (H1 H2 : List (List Bool))
    (R1 : FiniteRightAction G H1.length) (C1 : FiniteRightAction G (matCols H1))
    (R2 : FiniteLeftAction G H2.length) (C2 : FiniteLeftAction G (matCols H2))
    (c : Nat × Nat) : List Bool :=
  (cayleyOrbitReps G C1 C2.toRight).map (fun o =>
    cntXL (cayleyPairRep G R1 C2.toRight) H1 H1.length (matCols H2) c o % 2 == 1) ++
  (cayleyOrbitReps G R1 R2.toRight).map (fun o =>
    cntXR (cayleyPairRep G R1 C2.toRight) H2 H1.length (matCols H2) c o % 2 == 1)

/-- Natural `Z`-row of orbit `c` in nonabelian `L-BALANCED`. -/
def cayleyBalancedZVector (G : FiniteGroup) (H1 H2 : List (List Bool))
    (R1 : FiniteRightAction G H1.length) (C1 : FiniteRightAction G (matCols H1))
    (R2 : FiniteLeftAction G H2.length) (C2 : FiniteLeftAction G (matCols H2))
    (c : Nat × Nat) : List Bool :=
  (cayleyOrbitReps G C1 C2.toRight).map (fun o =>
    ((List.range (matCols H2)).filter (fun j =>
      matEntry H2 c.2 j && cayleyPairRep G C1 C2.toRight (c.1, j) == o)).length % 2 == 1) ++
  (cayleyOrbitReps G R1 R2.toRight).map (fun o =>
    ((List.range H1.length).filter (fun a =>
      matEntry H1 a c.1 && cayleyPairRep G R1 R2.toRight (a, c.2) == o)).length % 2 == 1)

/-- Natural vectors of nonabelian `L-BALANCED`. -/
def cayleyBalancedVectors (G : FiniteGroup) (H1 H2 : List (List Bool))
    (R1 : FiniteRightAction G H1.length) (C1 : FiniteRightAction G (matCols H1))
    (R2 : FiniteLeftAction G H2.length) (C2 : FiniteLeftAction G (matCols H2)) :
    List (Sector × List Bool) :=
  ((cayleyOrbitReps G R1 C2.toRight).map
    (cayleyBalancedXVector G H1 H2 R1 C1 R2 C2)).map (fun v => (Sector.X, v)) ++
  ((cayleyOrbitReps G C1 R2.toRight).map
    (cayleyBalancedZVector G H1 H2 R1 C1 R2 C2)).map (fun v => (Sector.Z, v))

/-- Constructed state of nonabelian `L-BALANCED` over an arbitrary finite group `G`. -/
def cayleyBalancedState (G : FiniteGroup) (H1 H2 : List (List Bool))
    (R1 : FiniteRightAction G H1.length) (C1 : FiniteRightAction G (matCols H1))
    (R2 : FiniteLeftAction G H2.length) (C2 : FiniteLeftAction G (matCols H2)) : CodeState :=
  constructedState (cayleyBalancedQubits G H1 H2 R1 C1 R2 C2)
    (cayleyBalancedVectors G H1 H2 R1 C1 R2 C2)

end CodeCalculus
