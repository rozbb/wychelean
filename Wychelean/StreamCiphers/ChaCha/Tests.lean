module

public import Wychelean.StreamCiphers.ChaCha.Tests.Rfc8439
public import Wychelean.StreamCiphers.ChaCha.Tests.Wycheproof

namespace Wychelean.StreamCiphers.ChaCha.Tests

/-- Known-answer tests. -/
public def suites : List RunTests.Suite := rfc8439 ++ [wycheproof]

end Wychelean.StreamCiphers.ChaCha.Tests
