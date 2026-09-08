import Wychelean.DH.X25519
import RunTests.Basic

/-!
# X25519 known-answer tests

Test vectors for the scalar/u-coordinate codec and for X25519 itself, taken from
* <https://www.rfc-editor.org/rfc/rfc7748.html#section-5.2> (X25519 test vectors), and
* <https://www.rfc-editor.org/rfc/rfc7748.html#section-6.1> (a Diffie-Hellman exchange).

Every hex string below is copied verbatim out of the RFC, as is every base-10 number that the RFC
itself prints. Where a test needs a number the RFC does not print — the clamped §6.1 private keys —
the comment says so and gives the rule it was derived from.

This module is built by `lake test`, not by `lake build`; it is deliberately not imported by
`Wychelean.DH.X25519`.
-/

namespace X25519.Tests

open RunTests
open Std.Internal.Parsec.String (digits)

/-! ## Vectors -/

/-- The u-coordinate of the basepoint, u = 9, as §5.2's iterated test writes it. -/
private def nine: String := "0900000000000000000000000000000000000000000000000000000000000000"

/--
Scalars, as (name, hex, the base-10 representation of `decodeScalar(hex)`).
 -/
private def scalars: List (String × String × String) := [
  ("§5.2 vector 1",
    "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
    "31029842492115040904895560451863089656472772604678260265531221036453811406496"),
  ("§5.2 vector 2",
    "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
    "35156891815674817266734212754503633747128614016119564763269015315466259359304"),
  ("§6.1 Alice's private key",
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a",
    "48024180843069071553745934684982006431825596986621126406018887516696408295280"),
  ("§6.1 Bob's private key",
    "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb",
    "48794194057373861652369136623399865312182792178494469274796512275582446775128")
]

/--
u-coordinates, as (name, hex, the base-10 representation of `decodeUCoordinate(hex)`)
-/
private def uCoordinates: List (String × String × String) := [
  ("§5.2 vector 1",
    "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
    "34426434033919594451155107781188821651316167215306631574996226621102155684838"),
  ("§5.2 vector 2",
    "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
    "8883857351183929894090759386610649319417338800022198945255395922347792736741")
]

/--
X25519 vectors, as (name, scalar hex, input u hex, output u hex).
We don't do the iterated tests, because they're super slow.
-/
private def products: List (String × String × String × String) := [
  ("§5.2 vector 1",
    "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
    "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
    "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"),
  ("§5.2 vector 2",
    "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
    "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
    "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"),
  ("§5.2 iterated test, round 1", nine, nine,
    "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"),
  ("§6.1 Alice's public key",
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a", nine,
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"),
  ("§6.1 Bob's public key",
    "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb", nine,
    "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"),
  ("§6.1 shared secret, Alice's side",
    "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a",
    "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f",
    "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"),
  ("§6.1 shared secret, Bob's side",
    "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb",
    "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
    "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"),
]

/-! ## Suite -/

/-- Every vector above, checked against the codec and against X25519. -/
def suite: Suite where
  name := "X25519 (RFC 7748 known-answer tests)"
  tests := do
    let mut tests: Array Test := #[]

    for (name, hex, value) in scalars do
      let scalar ← IO.ofExcept (fromHex hex)
      let expected ← IO.ofExcept (Parser.parse digits value)
      tests := tests.push <|
        check s!"{name}: scalar clamps and decodes to the given number"
          expected (decodeScalar scalar)

    for (name, hex, value) in uCoordinates do
      let u ← IO.ofExcept (fromHex hex)
      let expected ← IO.ofExcept (Parser.parse digits value)
      tests := tests.push <|
        check s!"{name}: u-coordinate decodes to the given number"
          expected (decodeUCoordinate u)

    for (name, scalar, u, out) in products do
      let scalar ← IO.ofExcept (fromHex scalar)
      let point ← IO.ofExcept (fromHex u)
      let expected ← IO.ofExcept (fromHex out)
      tests := tests.push <|
        check s!"{name}: X25519(scalar, u) is the given output u-coordinate"
          expected (x25519 scalar point)
      -- Where the input is the basepoint, the same vector pins down `basepointMul`
      if u == nine then
        tests := tests.push <|
          check s!"{name}: basepointMul(scalar) agrees with X25519(scalar, 9)"
            expected (basepointMul scalar)
      tests := tests.push <|
        check s!"{name}: encodeUCoordinate ⚬ decodeUCoordinate = id on the output of X25519"
          expected (encodeUCoordinate (decodeUCoordinate expected))

    return tests.toList

def suites: List Suite := [suite]

end X25519.Tests
