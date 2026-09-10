import RunTests.Basic
import Wychelean.DH.X25519.Tests
import Wychelean.Hashes.SHA256.Tests
import Wychelean.Hashes.SHA3.Tests
import Wychelean.Hashes.Keccak.Tests
import Wychelean.Permutations.Keccak.Tests
import Wychelean.Hashes.KangarooTwelve.Tests
import Wychelean.Utils.Tests

/-!
# Test driver

Runs every specification's test suites. Each suite lives next to the specification it tests; adding
one means importing its module and listing it here.
-/

namespace RunTests

open Wychelean

def suites: List Suite :=
  [ Utils.Tests.suites,
    X25519.Tests.suites,
    Hashes.SHA256.Tests.suites,
    Hashes.SHA3.Tests.suites,
    Hashes.Keccak.Tests.suites,
    Permutations.Keccak.Tests.suites,
    Hashes.KangarooTwelve.Tests.suites ].flatten

end RunTests

def main: IO UInt32 := do
  try
    RunTests.runSuites RunTests.suites
  catch e =>
    IO.eprintln s!"test setup failed: {e}"
    return 1
