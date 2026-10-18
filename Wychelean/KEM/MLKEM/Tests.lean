module

public import Wychelean.KEM.MLKEM.Tests.Axioms
public import Wychelean.KEM.MLKEM.Tests.Arithmetic
public import Wychelean.KEM.MLKEM.Tests.Guards
public import Wychelean.KEM.MLKEM.Tests.Standalone
public import Wychelean.KEM.MLKEM.Tests.Cavp
public import Wychelean.KEM.MLKEM.Tests.Wycheproof

namespace Wychelean.KEM.MLKEM.Tests

/-- Known-answer tests; `full` runs every Wycheproof case instead of a sample per group. -/
public def suites (full := false) : List RunTests.Suite :=
  arithmeticSuite :: cavpSuites ++ wycheproofSuites full

end Wychelean.KEM.MLKEM.Tests
