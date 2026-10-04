import RunTests.Basic
import Wychelean.DH.X25519.Tests
import Wychelean.Hashes.SHA256.Tests
import Wychelean.Hashes.SHA512.Tests
import Wychelean.Hashes.SHA3.Tests
import Wychelean.KEM.MLKEM.Tests
import Wychelean.Utils.PolyRing.Tests
import Wychelean.Permutations.Keccak.Tests
import Wychelean.Utils.Tests

/-!
# Test driver

Runs every specification's test suites. Each suite lives next to the specification it tests; adding
one means importing its module and listing it here.
Use `lake test -- --full` to add the SHA3 and SHAKE long-message and Monte Carlo vectors and the
SHA-2 Monte Carlo suites, and to run every ML-KEM Wycheproof case rather than a sample of each group.
-/

namespace RunTests

open Wychelean

def suites (full := false): List Suite :=
  [ Utils.Tests.suites,
    X25519.Tests.suites,
    Hashes.SHA256.Tests.suites full,
    Hashes.SHA512.Tests.suites full,
    Hashes.SHA3.Tests.suites full,
    Hashes.SHA3.Tests.shakeSuites full,
    KEM.MLKEM.Tests.suites full,
    Utils.PolyRing.Tests.suites,
    Permutations.Keccak.Tests.suites ].flatten

end RunTests

def main (args : List String): IO UInt32 := do
  let full := args.contains "--full"
  let only := match args with
    | ["--only", pat] | ["--full", "--only", pat] | ["--only", pat, "--full"] => some pat
    | _ => none
  unless args.isEmpty || args == ["--full"] || only.isSome do
    IO.eprintln "usage: lake test [-- --full] [-- --only <suite name substring>]"
    return 1
  try
    let suites := RunTests.suites full
    RunTests.runSuites (match only with
      | some pat => suites.filter fun s => (s.name.splitOn pat).length > 1
      | none => suites)
  catch e =>
    IO.eprintln s!"test setup failed: {e}"
    return 1
