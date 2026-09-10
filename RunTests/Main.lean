import RunTests.Basic
import Wychelean.DH.X25519.Tests
import Wychelean.Hashes.SHA256.Tests
import Wychelean.Hashes.SHA512.Tests
import Wychelean.Hashes.SHA3.Tests
import Wychelean.Permutations.Keccak.Tests
import Wychelean.Utils.Tests

/-!
# Test driver

Runs every specification's test suites. Each suite lives next to the specification it tests; adding
one means importing its module and listing it here.
Use `lake test -- --full` to add the SHA3 long-message vectors and the bit-oriented SHA-2 Monte Carlo suites.
-/

namespace RunTests

open Wychelean

def suites (full := false): List Suite :=
  [ Utils.Tests.suites,
    X25519.Tests.suites,
    Hashes.SHA256.Tests.suites full,
    Hashes.SHA512.Tests.suites full,
    Hashes.SHA3.Tests.suites full,
    Permutations.Keccak.Tests.suites ].flatten

end RunTests

def main (args : List String): IO UInt32 := do
  unless args.isEmpty || args == ["--full"] do
    IO.eprintln "usage: lake test [-- --full]"
    return 1
  try
    RunTests.runSuites (RunTests.suites (args == ["--full"]))
  catch e =>
    IO.eprintln s!"test setup failed: {e}"
    return 1
