import Std

namespace CodeCalculus

inductive Sector where
  | X
  | Z
  deriving Repr, BEq, DecidableEq

structure Row where
  id : Nat
  sector : Sector
  support : List Nat
  deriving Repr, BEq, DecidableEq

structure CodeState where
  Q : List Nat
  rows : List Row
  used : List Nat
  deriving Repr, BEq, DecidableEq

/-- One more than the largest used identifier (0 when `used` is empty). -/
def bound (used : List Nat) : Nat := used.foldl (fun a y => max a y) 0 + 1

def canonicalMintGo (used : List Nat) : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => if used.contains n then canonicalMintGo used (n + 1) k else n

def canonicalMint (used : List Nat) : Nat := canonicalMintGo used 0 (bound used)

theorem acc_le_foldl_max (ys : List Nat) (acc : Nat) :
    acc ≤ ys.foldl (fun a y => max a y) acc := by
  induction ys generalizing acc with
  | nil => exact Nat.le_refl _
  | cons y ys ih => exact Nat.le_trans (Nat.le_max_left acc y) (ih _)

theorem le_foldl_max (ys : List Nat) (x : Nat) (hx : x ∈ ys) (acc : Nat) :
    x ≤ ys.foldl (fun a y => max a y) acc := by
  induction ys generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_trans (Nat.le_max_right acc x) (acc_le_foldl_max ys _)
    · exact ih h _

theorem mem_lt_bound (used : List Nat) (x : Nat) (hx : x ∈ used) : x < bound used :=
  Nat.lt_succ_of_le (le_foldl_max used x hx 0)

theorem go_fresh (used : List Nat) (n k : Nat) (hk : ∀ x ∈ used, x < n + k) :
    ¬ used.contains (canonicalMintGo used n k) := by
  induction k generalizing n with
  | zero =>
    simp only [canonicalMintGo]
    intro h
    have hmem : n ∈ used := List.contains_iff_mem.mp h
    have := hk n hmem
    omega
  | succ k ih =>
    simp only [canonicalMintGo]
    split
    · exact ih (n + 1) (fun x hx => by have := hk x hx; omega)
    · assumption

theorem go_least (used : List Nat) (n k : Nat)
    (hn : ∀ m, m < n → used.contains m = true)
    (m : Nat) (hm : m < canonicalMintGo used n k) : used.contains m = true := by
  induction k generalizing n with
  | zero =>
    simp only [canonicalMintGo] at hm
    exact hn m hm
  | succ k ih =>
    simp only [canonicalMintGo] at hm
    split at hm
    · rename_i h
      exact ih (n + 1) (fun m' hm' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with h' | rfl
        · exact hn m' h'
        · exact h) hm
    · exact hn m hm

/-- The canonical mint is never already used. -/
theorem canonicalMint_fresh (used : List Nat) :
    ¬ used.contains (canonicalMint used) :=
  go_fresh used 0 (bound used) (fun x hx => by
    have := mem_lt_bound used x hx
    omega)

/-- Canonical mint is the least fresh identifier. -/
theorem canonicalMint_least (used : List Nat) (n : Nat)
    (h : n < canonicalMint used) : used.contains n = true :=
  go_least used 0 (bound used) (fun m hm => absurd hm (Nat.not_lt_zero m)) n h

/-- The pinned identifier enumeration, in canonical order.

`spec/STATE_MODEL.md` I3 mints fresh identifiers as "the first element of a
fixed enumeration of the identifier namespace not in `used`". This is that
fixed enumeration, pinned to the machine transcription
`machine/priced_calculus.py` `IDENTIFIERS`:

`a1..a10000`, `b1..b10000`, `c1..c10000`, `d1..d10000`, `e1..e10000`,
`p1..p10000`, `q1..q10000`.

The `p` and `q` blocks carry the identifiers the acceptance surface uses
(`W14`, `W15` and `W21` in `machine/fixtures/mvp_fixtures.json`).

The Lean identifier type is the **rank**: the index of an identifier in this
enumeration. `Row.id` and `CodeState.used` carry ranks, and the rank order
is the enumeration order, so "the least rank not in `used`" is the spec's
"first element of the enumeration not in `used`". -/
def identifierPrefixes : List String := ["a", "b", "c", "d", "e", "p", "q"]

/-- Identifiers per block of the enumeration. -/
def identifiersPerBlock : Nat := 10000

/-- The block of the enumeration that holds `rank`. -/
def identifierBlock (rank : Nat) : Nat := rank / identifiersPerBlock

/-- The 1-based position of `rank` inside its block. -/
def identifierIndex (rank : Nat) : Nat := rank % identifiersPerBlock + 1

/-- The identifier at enumeration position `rank`; `none` past the end of
    the enumeration. -/
def identifierAt? (rank : Nat) : Option String :=
  match identifierPrefixes[identifierBlock rank]? with
  | some block => some (block ++ toString (identifierIndex rank))
  | none => none

/-- Total number of identifiers in the pinned enumeration. -/
def totalIdentifiers : Nat := identifierPrefixes.length * identifiersPerBlock

/-- Parse the rank of an identifier string, if it names a valid enumeration
    entry. -/
def rankOfString? (id : String) : Option Nat :=
  match identifierPrefixes.findIdx? (fun p => id.startsWith p) with
  | none => none
  | some block =>
      let rest := (id.drop (identifierPrefixes[block]!).length).toString
      match rest.toNat? with
      | none => none
      | some idx =>
          if rest = toString idx ∧ 1 ≤ idx ∧ idx ≤ identifiersPerBlock then
            some (block * identifiersPerBlock + (idx - 1))
          else none

/-- `rankOf?` accepts the `Option String` produced by `identifierAt?`, so the
    round-trip equation can be written exactly as `rankOf? (identifierAt? r)`. -/
def rankOf? : Option String → Option Nat
  | none => none
  | some s => rankOfString? s

/-- The round trip: every valid rank renders to a string that parses back to
    the same rank. Proved by `native_decide`, so the theorem depends on the
    per-theorem `native_decide` axiom
    (`rankOf_identifierAt._native.native_decide.ax_1_1`) in addition to
    `propext` and `Quot.sound`: the statement is checked by the Lean compiler,
    not by the kernel. -/
theorem rankOf_identifierAt :
    ∀ r, r < totalIdentifiers → rankOf? (identifierAt? r) = some r := by
  native_decide

/-- Pointwise form of `rankOf_identifierAt`. -/
theorem rankOf_identifierAt_of_lt (r : Nat) (hr : r < totalIdentifiers) :
    rankOf? (identifierAt? r) = some r :=
  rankOf_identifierAt r hr

/-- The rank of the identifier at (block, index). -/
def rankOfBlockIndex (block index : Nat) : Nat :=
  block * identifiersPerBlock + (index - 1)

/-- The block and index of a rank reconstruct that rank. -/
theorem identifierBlock_index_reconstruct (rank : Nat) :
    rankOfBlockIndex (identifierBlock rank) (identifierIndex rank) = rank := by
  simp only [identifierBlock, identifierIndex, rankOfBlockIndex, identifiersPerBlock]
  omega

/-- Distinct ranks occupy distinct enumeration positions. With
    `identifierBlock_index_reconstruct` this is the statement that the rank
    order is the enumeration order. -/
theorem identifierBlock_index_ne_of_lt {r s : Nat} (h : r < s) :
    (identifierBlock r, identifierIndex r) ≠ (identifierBlock s, identifierIndex s) := by
  intro heq
  have hr := identifierBlock_index_reconstruct r
  have hs := identifierBlock_index_reconstruct s
  have hb := congrArg Prod.fst heq
  have hi := congrArg Prod.snd heq
  simp only [identifierBlock, identifierIndex, rankOfBlockIndex, identifiersPerBlock] at *
  omega

/-- Presentation equality ≡: identical qubit namespace (as a set), identical
    labeled rows (as a set), and identical used-identifier set
    (`spec/STATE_MODEL.md` §2; the namespace clause was added by ,
    since two well-formed states with the same rows and `used` on different
    namespaces differ in `n`, `k`, and applicability). Read on well-formed
    states, where `Q` and supports are without repeats and sorted, list
    equality coincides with set equality. Representation equality `=` remains
    order-sensitive on the concrete lists. -/
def codeStateEquiv (a b : CodeState) : Prop :=
  (∀ q, a.Q.contains q ↔ b.Q.contains q) ∧
  (∀ r, a.rows.contains r ↔ b.rows.contains r) ∧
  (∀ x, a.used.contains x ↔ b.used.contains x)

notation:50 a " ≡ " b => codeStateEquiv a b

theorem codeStateEquiv_refl (a : CodeState) : a ≡ a :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem codeStateEquiv_symm {a b : CodeState} (h : a ≡ b) : b ≡ a :=
  ⟨fun q => (h.1 q).symm, fun r => (h.2.1 r).symm, fun x => (h.2.2 x).symm⟩

theorem codeStateEquiv_trans {a b c : CodeState} (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
  ⟨fun q => (h₁.1 q).trans (h₂.1 q), fun r => (h₁.2.1 r).trans (h₂.2.1 r),
   fun x => (h₁.2.2 x).trans (h₂.2.2 x)⟩

/-- Representation equality implies presentation equality. -/
theorem codeStateEquiv_of_eq {a b : CodeState} (h : a = b) : a ≡ b :=
  h ▸ codeStateEquiv_refl a

/-- Intersection size of two supports. -/
def supportIntersectionSize (a b : List Nat) : Nat :=
  a.foldl (fun n q => if b.contains q then n + 1 else n) 0

/-- I1: every displayed X-stabilizer commutes with every displayed
    Z-stabilizer, i.e. their supports intersect in an even number of qubits. -/
def I1 (s : CodeState) : Prop :=
  ∀ rX rZ, rX ∈ s.rows → rZ ∈ s.rows →
    rX.sector = Sector.X → rZ.sector = Sector.Z →
    supportIntersectionSize rX.support rZ.support % 2 = 0

/-- Vector of a displayed row over the qubit list `Q`. -/
def rowVector (Q : List Nat) (r : Row) : List Bool :=
  Q.map (fun q => r.support.contains q)

/-- XOR of two equal-length boolean vectors. -/
def xorVec (a b : List Bool) : List Bool :=
  match a, b with
  | [], [] => []
  | x :: xs, y :: ys => (x != y) :: xorVec xs ys
  | _, _ => []

/-- Combine rows with boolean coefficients over F2. The first argument is the
    common vector length (`s.Q.length` at the call sites); the base case returns
    the zero vector of that length so that the result is always a well-formed
    vector and the independence comparison is meaningful. -/
def combineRows (n : Nat) : List (List Bool) → List Bool → List Bool
  | [], _ => List.replicate n false
  | v :: vs, true :: cs => xorVec v (combineRows n vs cs)
  | _ :: vs, false :: cs => combineRows n vs cs
  | _, _ => List.replicate n false

/-- Membership of a vector in the F2-span of a list of rows. -/
def inSpanRows (Q : List Nat) (rows : List Row) (target : List Bool) : Prop :=
  ∃ coeffs : List Bool,
    coeffs.length = rows.length ∧
    combineRows Q.length (rows.map (rowVector Q)) coeffs = target

/-- The row named by an identifier, if it is displayed. -/
def rowById (s : CodeState) (r : Nat) : Option Row :=
  s.rows.find? (fun row => row.id = r)

/-- A displayed generator is independent when its vector is not in the F2-span
    of the other displayed rows of the same sector. -/
def IndependentGenerator (r : Nat) (s : CodeState) : Prop :=
  match rowById s r with
  | some row =>
      let peers := s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ r)
      ¬ inSpanRows s.Q peers (rowVector s.Q row)
  | none => False

/-- I2: the displayed rows of each sector are linearly independent over F2.
    Stated as "every displayed generator is independent", which is the same
    condition by construction (spec/STATE_MODEL.md §3). -/
def I2 (s : CodeState) : Prop :=
  ∀ r ∈ s.rows, IndependentGenerator r.id s

/-- Well-formedness predicate. List-level conditions plus I1 and I2.
    I3–I5 are added as standalone predicates by the follow-up slice ();
    they are not folded into this predicate. -/
def EncodingWellFormed (s : CodeState) : Prop :=
  s.Q.Nodup ∧
  (s.rows.map Row.id).Nodup ∧
  (s.rows.map Row.id).all (fun id => s.used.contains id) ∧
  s.rows.all (fun r => r.support.all (fun q => s.Q.contains q)) ∧
  s.rows.all (fun r => r.support.Nodup) ∧
  s.rows.all (fun r => r.support.Pairwise (· ≤ ·)) ∧
  I1 s ∧ I2 s

/-- All boolean lists of the given length. -/
def allBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBoolLists n).flatMap (fun bs => [false :: bs, true :: bs])

/-- Computable F2-span membership test, matching `inSpanRows`. -/
def inSpanRowsBool (Q : List Nat) (rows : List Row) (target : List Bool) : Bool :=
  (allBoolLists rows.length).any (fun coeffs =>
    combineRows Q.length (rows.map (rowVector Q)) coeffs == target)

/-- Computable independence test for a displayed generator, matching
    `IndependentGenerator`. -/
def independentGeneratorBool (r : Nat) (s : CodeState) : Bool :=
  match rowById s r with
  | some row =>
      let peers := s.rows.filter (fun r' => r'.sector == row.sector && r'.id != r)
      !inSpanRowsBool s.Q peers (rowVector s.Q row)
  | none => false

/-- Computable I1 check, matching `I1`. -/
def i1Bool (s : CodeState) : Bool :=
  s.rows.all (fun rX =>
    s.rows.all (fun rZ =>
      if rX.sector == Sector.X && rZ.sector == Sector.Z then
        supportIntersectionSize rX.support rZ.support % 2 == 0
      else true))

/-- Computable well-formedness test, matching `EncodingWellFormed`. -/
def wellFormedBool (s : CodeState) : Bool :=
  decide (s.Q.Nodup) &&
  decide ((s.rows.map Row.id).Nodup) &&
  (s.rows.map Row.id).all (fun id => s.used.contains id) &&
  s.rows.all (fun r => r.support.all (fun q => s.Q.contains q)) &&
  s.rows.all (fun r => decide (r.support.Nodup)) &&
  s.rows.all (fun r => decide (r.support.Pairwise (· ≤ ·))) &&
  i1Bool s &&
  s.rows.all (fun r => independentGeneratorBool r.id s)

-- Identifiers are Nat here, and that Nat is the **rank** of an identifier in
-- the pinned enumeration (`identifierPrefixes`, `identifierAt?`). The
-- enumeration contains the identifiers the acceptance surface uses (`p1`,
-- `q1`), so the Lean identifier type and the machine's enumeration are in
-- step. The string-level round trip is now proved by `rankOf_identifierAt`
-- (and its pointwise form `rankOf_identifierAt_of_lt`): every valid rank
-- renders to a string that parses back to the same rank. The proof is by
-- `native_decide`, which carries the per-theorem
-- `rankOf_identifierAt._native.native_decide.ax_1_1` axiom in addition to
-- `propext` and `Quot.sound`; the statement is checked by the Lean compiler,
-- not by the kernel. This discharges `the  tracker` item 8 and the 2026-10-22
-- diary gate on fixture conformance.

end CodeCalculus
