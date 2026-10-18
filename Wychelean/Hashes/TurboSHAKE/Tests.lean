module

public import Wychelean.Hashes.TurboSHAKE.Tests.Guards
public import Wychelean.Hashes.TurboSHAKE.Tests.Rfc9861

namespace Wychelean.Hashes.TurboSHAKE.Tests

/-- Known-answer tests; `full` adds the RFC 9861 vectors with 1.4 MB messages. -/
public def suites (full := false) : List RunTests.Suite := rfc9861 full

end Wychelean.Hashes.TurboSHAKE.Tests
