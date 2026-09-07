import KnownAnswerTests.Basic
import Wychelean.Curves.Curve25519.Tests

/-!
# Known-answer test driver

Runs every specification's known-answer suites. Each suite lives next to the specification it
tests; adding one means importing its module and listing it here.
-/

def suites: List KnownAnswerTests.Suite :=
  Curve25519.Tests.suites

def main: IO UInt32 :=
  KnownAnswerTests.runSuites suites
