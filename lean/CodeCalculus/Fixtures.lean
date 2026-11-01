import CodeCalculus.State
import CodeCalculus.Invariants

namespace CodeCalculus

-- Pinned fixture states selected from machine/fixtures/mvp_fixtures.json (). Definitions only; the replay of these states lives in FixtureReplay.lean, on kernel `decide` since 2026-10-29 ().
def fixture_W0_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W3_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W3_result : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W4_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W5_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

-- W5's result: the JSON names the new row `c1`, a metavariable for the next
-- canonical mint (caveat R5). Over `used = {a1, a2, b1}` that mint is rank 2
-- (`a3`), and the row is appended as `addState` appends it. Before 
-- (2026-10-29) this definition hard-coded rank 20000 and was not the
-- transition's output (review findings RG-8, RC-3).
def fixture_W5_result : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] },
    { id := 2, sector := Sector.Z, support := [1] }
  ],
  used := [0, 1, 10000, 2]
}

def fixture_W6_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W7_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

-- W7's result: the loop mints rank 2 (`a3`) for the JSON's `c2`, appended
-- after the surviving rows. Before  this definition hard-coded rank
-- 20001 (RG-8, RC-3).
def fixture_W7_result : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] },
    { id := 2, sector := Sector.X, support := [1, 3] }
  ],
  used := [0, 1, 10000, 2]
}

def fixture_W8_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W9_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

-- W9's result (): both X rows deleted, `used` unchanged.
def fixture_W9_result : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W10_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W11_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W12_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W13_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W14_result : CodeState := {
  Q := [1, 2, 3, 4],
  rows := [
    { id := 50000, sector := Sector.X, support := [1, 2] },
    { id := 60000, sector := Sector.X, support := [3, 4] }
  ],
  used := [50000, 60000]
}

def fixture_W16_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

-- W16's result (): one row of each sector deleted, `used` unchanged.
def fixture_W16_result : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W22_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 10000]
}

def fixture_W23_initial : CodeState := {
  Q := [0, 1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [0, 1] },
    { id := 10000, sector := Sector.Z, support := [0, 1] }
  ],
  used := [0, 10000]
}

def fixture_W23_result : CodeState := {
  Q := [0, 1, 2, 3],
  rows := [
    { id := 10000, sector := Sector.Z, support := [0, 1] }
  ],
  used := [0, 10000]
}



def fixture_W1_initial : CodeState := {
  Q := [1, 2, 3],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 1, sector := Sector.X, support := [2, 3] },
    { id := 2, sector := Sector.X, support := [1, 3] },
    { id := 10000, sector := Sector.Z, support := [1, 2, 3] }
  ],
  used := [0, 1, 2, 10000]
}

def fixture_W2_initial : CodeState := {
  Q := [1, 2],
  rows := [
    { id := 0, sector := Sector.X, support := [1, 2] },
    { id := 10000, sector := Sector.Z, support := [1] }
  ],
  used := [0, 10000]
}


-- Direct-sum pair fixtures (W14, W15, W21): the initial state of these
-- fixtures is a *pair* of named summands, not a single CodeState, so each
-- summand is transcribed under its fixture key. Identifiers follow the
-- W14 result convention (p1 = 50000, q1 = 60000); W21's two summands both
-- mint `p1`, which is exactly the used-set overlap the fixture tests.

def fixture_W14_S_L : CodeState := {
  Q := [1, 2],
  rows := [
    { id := 50000, sector := Sector.X, support := [1, 2] }
  ],
  used := [50000]
}

def fixture_W14_S_R : CodeState := {
  Q := [3, 4],
  rows := [
    { id := 60000, sector := Sector.X, support := [3, 4] }
  ],
  used := [60000]
}

-- W15: `S_L` is a ref to W14.initial_state.S_L; `S_R_prime` is the empty
-- display on Q = [2,3] (itself well-formed). The fixture's point: the two
-- namespaces overlap at qubit 2, so C-DIRECT-SUM is inapplicable.
def fixture_W15_S_L : CodeState := fixture_W14_S_L

def fixture_W15_S_R_prime : CodeState := {
  Q := [2, 3],
  rows := [],
  used := []
}

-- W21: `S_L` equals W14's left summand; `S_R_double_prime` carries the same
-- identifier p1 (50000) on the disjoint namespace [3,4], so the qubit
-- premise holds and the used-set premise fails.
def fixture_W21_S_L : CodeState := fixture_W14_S_L

def fixture_W21_S_R_double_prime : CodeState := {
  Q := [3, 4],
  rows := [
    { id := 50000, sector := Sector.X, support := [3, 4] }
  ],
  used := [50000]
}
end CodeCalculus
