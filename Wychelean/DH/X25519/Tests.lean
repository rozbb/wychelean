module

public import Wychelean.DH.X25519.Tests.Rfc7748
public import Wychelean.DH.X25519.Tests.WycheproofKat

/-!
# X25519 known-answer tests

RFC 7748 KATs are checked in `Wychelean.DH.X25519.Tests.Rfc7748`. Wycheproof's
KATs are checked in `Wychelean.DH.X25519.Tests.WycheproofKat`.
-/

public section

namespace X25519.Tests

def suites: List RunTests.Suite := [rfc7748, wycheproof]

end X25519.Tests
