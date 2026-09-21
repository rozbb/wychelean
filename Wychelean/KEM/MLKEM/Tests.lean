import Wychelean.KEM.MLKEM.Tests.Axioms
import Wychelean.KEM.MLKEM.Tests.Arithmetic
import Wychelean.KEM.MLKEM.Tests.Guards
import Wychelean.KEM.MLKEM.Tests.Cavp
import Wychelean.KEM.MLKEM.Tests.Wycheproof

namespace Wychelean.KEM.MLKEM.Tests

/-- Known-answer tests; `full` runs every Wycheproof case instead of a sample per group. -/
def suites (full := false) : List RunTests.Suite := arithmeticSuite :: cavpSuites ++ wycheproofSuites full

end Wychelean.KEM.MLKEM.Tests
