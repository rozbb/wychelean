import Wychelean.Curves.Curve25519
import KnownAnswerTests.Basic

/-!
# Curve25519 known-answer tests

Test vectors for the scalar/u-coordinate codec and for X25519 itself, taken from
* <https://www.rfc-editor.org/rfc/rfc7748.html#section-5.2> (X25519 test vectors), and
* <https://www.rfc-editor.org/rfc/rfc7748.html#section-6.1> (a Diffie-Hellman exchange).

Every hex string below is copied verbatim out of the RFC, as is every base-10 number that the RFC
itself prints. Where a test needs a number the RFC does not print — the clamped §6.1 private keys —
the comment says so and gives the rule it was derived from.

This module is built by `lake test`, not by `lake build`; it is deliberately not imported by
`Wychelean.Curves.Curve25519`.
-/

namespace Curve25519.Tests

open KnownAnswerTests

/-! ## RFC 7748 §5.2 -/

-- The two X25519 vectors of §5.2: an input scalar, an input u-coordinate, and the output
-- u-coordinate they produce.
private def scalar1: String := "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
private def u1: String := "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
private def out1: String := "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"
private def scalar2: String := "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"
private def u2: String := "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
private def out2: String := "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"

-- The starting value of the iterated test at the end of §5.2: u-coordinate 9, i.e. the basepoint.
private def nine: String := "0900000000000000000000000000000000000000000000000000000000000000"

/-- The §5.2 test vectors: the codec against the base-10 values printed there, then X25519
itself against the output u-coordinates. -/
def section52: Suite where
  name := "RFC 7748 §5.2 (X25519 test vectors)"
  tests := [
    -- Decoding, against the "as a number (base 10)" lines. Those lines print the result of the
    -- §5 decoding functions, not a plain base conversion of the hex: the scalars are clamped
    -- first (both differ from their raw little-endian value, e.g. vector 1's first byte goes
    -- a5 → a0 and its last c4 → 44), and vector 2's u-coordinate has bit 255 masked off.
    check "vector 1: input scalar clamps and decodes to the given number"
      31029842492115040904895560451863089656472772604678260265531221036453811406496
      (decodeScalar (hexVector scalar1)),
    check "vector 1: input u-coordinate decodes to the given number"
      34426434033919594451155107781188821651316167215306631574996226621102155684838
      (decodeUCoordinate (hexVector u1)),
    check "vector 2: input scalar clamps and decodes to the given number"
      35156891815674817266734212754503633747128614016119564763269015315466259359304
      (decodeScalar (hexVector scalar2)),
    check "vector 2: input u-coordinate decodes to the given number, bit 255 masked off"
      8883857351183929894090759386610649319417338800022198945255395922347792736741
      (decodeUCoordinate (hexVector u2)),

    -- Encoding, against the same pairs read the other way round
    check "vector 1: the given number encodes to the input u-coordinate"
      (hexVector u1: Vector UInt8 32)
      (encodeUCoordinate
        34426434033919594451155107781188821651316167215306631574996226621102155684838),
    check "vector 1: encoding inverts decoding on the output u-coordinate"
      (hexVector out1: Vector UInt8 32)
      (encodeUCoordinate (decodeUCoordinate (hexVector out1))),
    check "vector 2: encoding inverts decoding on the output u-coordinate"
      (hexVector out2: Vector UInt8 32)
      (encodeUCoordinate (decodeUCoordinate (hexVector out2))),

    -- X25519 end to end
    check "vector 1: X25519(scalar, u) is the given output u-coordinate"
      (hexVector out1: Vector UInt8 32)
      (scalarMul (hexVector u1) (hexVector scalar1)),
    check "vector 2: X25519(scalar, u) is the given output u-coordinate"
      (hexVector out2: Vector UInt8 32)
      (scalarMul (hexVector u2) (hexVector scalar2)),

    -- The iterated test, whose first round is X25519(9, 9). Later rounds (1,000 and 1,000,000
    -- iterations) are left out: they are the same computation repeated, at a cost `lake test`
    -- should not pay.
    check "after one iteration of the iterated test"
      (hexVector "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079":
        Vector UInt8 32)
      (scalarMul (hexVector nine) (hexVector nine))
  ]

/-! ## RFC 7748 §6.1 -/

-- The Diffie-Hellman exchange of §6.1. §6.1 gives no base-10 values, so the two clamped scalars
-- below were derived by applying the §5 `decodeScalar25519` rule (clear bits 0-2 of the first
-- byte, clear bit 255, set bit 254) to the private keys, independently of this implementation.
private def aliceSecret: String :=
  "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
private def alicePublic: String :=
  "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
private def bobSecret: String :=
  "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
private def bobPublic: String :=
  "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
private def shared: String :=
  "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"

/-- The §6.1 Diffie-Hellman vector: scalar clamping on the two private keys, the codec on the
public values, and both sides of the exchange. -/
def section61: Suite where
  name := "RFC 7748 §6.1 (Curve25519 Diffie-Hellman)"
  tests := [
    -- Scalar decoding. Bob's key is the interesting one: its last byte is 0xeb, so clamping has
    -- to clear bit 255 and set bit 254, and its first byte is 0x5d, so bits 0-2 are cleared.
    check "Alice's private key clamps to the expected scalar"
      48024180843069071553745934684982006431825596986621126406018887516696408295280
      (decodeScalar (hexVector aliceSecret)),
    check "Bob's private key clamps to the expected scalar"
      48794194057373861652369136623399865312182792178494469274796512275582446775128
      (decodeScalar (hexVector bobSecret)),

    -- u-coordinate decoding and encoding on the transmitted values
    check "encoding inverts decoding on Alice's public key"
      (hexVector alicePublic: Vector UInt8 32)
      (encodeUCoordinate (decodeUCoordinate (hexVector alicePublic))),
    check "encoding inverts decoding on Bob's public key"
      (hexVector bobPublic: Vector UInt8 32)
      (encodeUCoordinate (decodeUCoordinate (hexVector bobPublic))),
    check "encoding inverts decoding on the shared secret"
      (hexVector shared: Vector UInt8 32)
      (encodeUCoordinate (decodeUCoordinate (hexVector shared))),

    -- The exchange itself
    check "Alice's public key is X25519(a, 9)"
      (hexVector alicePublic: Vector UInt8 32)
      (basepointMul (hexVector aliceSecret)),
    check "Bob's public key is X25519(b, 9)"
      (hexVector bobPublic: Vector UInt8 32)
      (basepointMul (hexVector bobSecret)),
    check "Alice computes the shared secret as X25519(a, K_B)"
      (hexVector shared: Vector UInt8 32)
      (scalarMul (hexVector bobPublic) (hexVector aliceSecret)),
    check "Bob computes the shared secret as X25519(b, K_A)"
      (hexVector shared: Vector UInt8 32)
      (scalarMul (hexVector alicePublic) (hexVector bobSecret))
  ]

/-! ## Twist -/

/-- A u-coordinate that is not on Curve25519 but on its quadratic twist, so `scalarMul` takes its
`mkTwistPoint` branch. RFC 7748 gives no such vector; the expected output is that of the §5
Montgomery ladder, which is defined on the twist as well. -/
def twist: Suite where
  name := "Curve25519 twist (not from RFC 7748)"
  tests := [
    check "X25519 with u = 2, a point on the twist"
      (hexVector "71cacba0b65daf53ddf9c21fb434bc58ee5cfa3954d1b642fc5155048f03466f":
        Vector UInt8 32)
      (scalarMul
        (hexVector "0200000000000000000000000000000000000000000000000000000000000000")
        (hexVector scalar1))
  ]

/-- Every Curve25519 known-answer suite. -/
def suites: List Suite := [section52, section61, twist]

end Curve25519.Tests
