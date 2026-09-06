import Tests.Utils.Bitwise
import Tests.Utils.Hex
import Tests.Hashes.SHA256

open Tests

def suites : List (String × List Test) := [
  ("Utils.Bitwise", Utils.Bitwise.tests),
  ("Utils.Hex", Utils.Hex.tests),
  ("Hashes.SHA256", Hashes.SHA256.tests)
]

def main : IO UInt32 := do
  let mut failed := 0
  for (name, tests) in suites do
    failed := failed + (← runSuite name tests)
  if failed == 0 then
    pure 0
  else
    IO.eprintln s!"{failed} test(s) failed"
    pure 1
