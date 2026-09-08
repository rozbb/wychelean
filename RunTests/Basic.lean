/-!
# Test harness

A small harness for the tests that live next to each specification, e.g.
`Wychelean.DH.X25519.Tests`. `RunTests.Main` collects every suite and runs it.

Byte strings are written as the hex the source documents print, so a reader can check a test
vector against its specification by eye rather than by transcribing bytes.
-/

namespace RunTests

/-! ## Hex -/

/-- The value of a hexadecimal digit, or `none` if `c` is not one. -/
def hexDigit? (c: Char): Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c ∧ c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

/-- Decode a hex string into bytes. Test vectors are literals copied out of a specification, so a
malformed one is a mistake in the test rather than a condition to recover from, and panics. -/
def hexBytes (s: String): List UInt8 :=
  go s.toList
where
  go: List Char → List UInt8
  | [] => []
  | [_] => panic! s!"hex string has an odd number of digits: {s}"
  | hi :: lo :: rest =>
    match hexDigit? hi, hexDigit? lo with
    | some h, some l => (h * 16 + l) :: go rest
    | _, _ => panic! s!"hex string contains a non-hex digit: {s}"

/-- Decode a hex string into a fixed-size byte vector, panicking if it is the wrong length. -/
def hexVector (s: String): Vector UInt8 n :=
  let bytes := (hexBytes s).toArray
  if h: bytes.size = n then ⟨bytes, h⟩
  else panic! s!"expected {n} bytes of hex, got {bytes.size}: {s}"

/-- Render bytes as lowercase hex, the way specifications print test vectors. -/
def toHex (v: Vector UInt8 n): String :=
  let digits := "0123456789abcdef".toList.toArray
  v.toList.foldl (fun acc b => (acc.push digits[b.toNat >>> 4]!).push digits[b.toNat &&& 15]!) ""

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
  /-- Load fixtures and evaluate checks when this suite runs. -/
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
