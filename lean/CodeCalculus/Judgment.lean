import CodeCalculus.State

namespace CodeCalculus

/-- A closed integer interval `[lower, upper]`, with `none` denoting
    `+∞` at either endpoint. Mirrors the ledger interval of
    `machine/priced_calculus.py`. -/
structure Interval where
  lower : Option Nat
  upper : Option Nat
  deriving Repr, BEq, DecidableEq

/-- `C-SKIP` carries every interval endpoint unchanged. -/
def skipInterval (i : Interval) : Interval := i

/-- Skip is the identity on intervals. -/
theorem skipInterval_id (i : Interval) : skipInterval i = i := by
  rfl

/-- A distance ledger carries per-sector intervals for `X` and `Z` plus a
    full-distance interval. -/
structure DistanceLedger where
  full : Interval
  x : Interval
  z : Interval
  deriving Repr

/-- `C-SKIP` carries the whole ledger unchanged. -/
def skipLedger (L : DistanceLedger) : DistanceLedger := L

theorem skipLedger_id (L : DistanceLedger) : skipLedger L = L := by
  rfl

/-- Global Hadamard (`T = Q`) exchanges the two sector intervals and leaves the
    full-distance interval unchanged (`d = min(d_X, d_Z)` is symmetric). -/
def hadamardLedger (L : DistanceLedger) : DistanceLedger :=
  { full := L.full, x := L.z, z := L.x }

/-- The global Hadamard ledger map is an involution. -/
theorem hadamardLedger_involutive (L : DistanceLedger) :
    hadamardLedger (hadamardLedger L) = L := by
  unfold hadamardLedger
  cases L
  rfl

/-- The full-distance interval is unchanged by the global Hadamard. -/
theorem hadamardLedger_full (L : DistanceLedger) :
    (hadamardLedger L).full = L.full := by
  rfl

end CodeCalculus
