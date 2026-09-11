import RunTests.Parser.Basic

/-!
# Test harness

A small harness for the tests that live next to each specification, e.g.
`Wychelean.DH.X25519.Tests`. `RunTests.Main` collects every suite and runs it.

Byte strings are written as the hex the source documents print, so a reader can check a test
vector against its specification by eye rather than by transcribing bytes.
-/

namespace RunTests

/-! ## Hex -/

/-- Render bytes as lowercase hex, the way specifications print test vectors. -/
def toHex (v: Vector UInt8 n): String :=
  v.foldl (fun acc b => acc ++ b.toBitVec.toHex) ""

/-- Report byte vectors as hex, so a failure can be read against its specification. -/
scoped instance: ToString (Vector UInt8 n) := ⟨toHex⟩

/-! ## Tests -/

/-- A single test. -/
structure Test where
  name: String
  /-- `none` if the answer matched, otherwise a description of the mismatch. -/
  failure: Option String

/-- A named group of tests, usually the vectors of one specification. -/
structure Suite where
  name: String
  /-- Load test vectors and evaluate checks when this suite runs. -/
  tests: IO (List Test)

/-- A test that checks `actual` against the `expected` answer the specification gives. -/
def check [BEq α] [ToString α] (name: String) (expected actual: α): Test :=
  { name,
    failure := if actual == expected then none else some s!"expected {expected}, got {actual}" }

/-- Run a suite, printing a line per test, and return the total and failure counts. -/
def Suite.run (suite: Suite): IO (Nat × Nat) := do
  IO.println s!"── {suite.name}"
  let tests ← suite.tests
  let mut failed := 0
  for t in tests do
    match t.failure with
    | none => IO.println s!"  ok   {t.name}"
    | some msg =>
      failed := failed + 1
      IO.println s!"  FAIL {t.name}: {msg}"
  return (tests.length, failed)

/-- Run every suite and return the exit code the test driver should exit with. -/
def runSuites (suites: List Suite): IO UInt32 := do
  let mut failed := 0
  let mut total := 0
  for s in suites do
    let (count, failures) ← s.run
    total := total + count
    failed := failed + failures
  if failed == 0 then
    IO.println s!"all {total} tests passed"
    return 0
  else
    IO.println s!"{failed} of {total} tests failed"
    return 1

end RunTests
