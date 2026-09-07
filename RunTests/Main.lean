import RunTests.Basic
import Wychelean.DH.X25519.Tests

/-!
# Test driver

Runs every specification's test suites. Each suite lives next to the specification it tests; adding
one means importing its module and listing it here.
-/

namespace RunTests

def suites: List Suite :=
  X25519.Tests.suites

end RunTests

def main: IO UInt32 :=
  RunTests.runSuites RunTests.suites
