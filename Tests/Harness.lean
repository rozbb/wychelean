/-!
Minimal known-answer test harness.

A `Test` is a named check that either passed (`failure = none`) or carries a
message describing the mismatch. Suites are plain lists of tests.
-/

namespace Tests

structure Test where
  name : String
  failure : Option String

/-- Check that `actual` equals `expected`. -/
def expectEq {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) : Test :=
  { name
    failure :=
      if actual == expected then none
      else some s!"expected {repr expected}, got {repr actual}" }

/-- Run a suite, report failures on stderr, and return the number of failures. -/
def runSuite (suite : String) (tests : List Test) : IO Nat := do
  let mut failed := 0
  for t in tests do
    if let some msg := t.failure then
      IO.eprintln s!"FAIL {suite}/{t.name}: {msg}"
      failed := failed + 1
  IO.println s!"{suite}: {tests.length - failed}/{tests.length} passed"
  pure failed

end Tests
