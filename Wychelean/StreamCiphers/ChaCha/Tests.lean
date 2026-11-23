module

public import Wychelean.StreamCiphers.ChaCha.Tests.Rfc8439

namespace Wychelean.StreamCiphers.ChaCha.Tests

/-- Known-answer tests. -/
public def suites : List RunTests.Suite := rfc8439

end Wychelean.StreamCiphers.ChaCha.Tests
