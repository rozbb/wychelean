import Tests.Hashes.SHA256

open Tests

def main : IO UInt32 := do
  let failed ← runSuite "SHA256" Hashes.SHA256.tests
  if failed == 0 then
    pure 0
  else
    IO.eprintln s!"{failed} test(s) failed"
    pure 1
