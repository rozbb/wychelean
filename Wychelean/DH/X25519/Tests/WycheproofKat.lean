import Wychelean.DH.X25519
import RunTests.Basic
import RunTests.Parser.Wycheproof

/-!
# X25519 Wycheproof known-answer tests

Project Wycheproof's X25519 suite, which is where the adversarial coverage lives: public keys on
the twist, of low order, or in non-canonical form, and scalars and shared secrets chosen to hit
edge cases of the field arithmetic. Each case gives a private key, a public u-coordinate, and the
shared secret X25519 must produce from them.

Wycheproof marks a case `valid` when an implementation must accept the input, and `acceptable` when
it may reject it — RFC 7748 §7 leaves libraries free to refuse low-order or twist public keys — but
must return the given shared secret if it does accept. `x25519` accepts every 32-byte
u-coordinate, as RFC 7748 §5 permits, so both kinds are checked the same way. The file has no
`invalid` cases; if a later revision adds one, the case fails rather than being skipped silently,
since rejection is an outcome `x25519` has no way to express.
-/

namespace X25519.Tests

open RunTests
open RunTests.Parser.Wycheproof

private def vectorFile: System.FilePath :=
  "Wychelean/DH/X25519/TestVectors/wycheproof_x25519_test.json"

/-- The fields of an `XdhComp` case: the two inputs of X25519, and the output it must return. -/
private structure Xdh where
  privateKey: Vector UInt8 32
  publicKey: Vector UInt8 32
  shared: Vector UInt8 32

private def Xdh.ofJson (j: Lean.Json): Except String Xdh := do
  return { privateKey := ← getHexField 32 j "private",
           publicKey := ← getHexField 32 j "public",
           shared := ← getHexField 32 j "shared" }

/-- Check one case, given that `x25519` accepts every public key the file can hold. -/
private def checkCase (c: Case Xdh): Test :=
  match c.result with
  | .valid | .acceptable =>
    check c.name c.data.shared (x25519 c.data.privateKey c.data.publicKey)
  | .invalid =>
    { name := c.name,
      failure := some "expects the public key to be rejected, which `x25519` cannot express" }

/-- Every Wycheproof vector, checked against X25519. -/
def wycheproof: Suite where
  name := "X25519 (Wycheproof known-answer tests)"
  tests := do
    let file ← parseFile Xdh.ofJson vectorFile
    -- Guard against the file being swapped for another algorithm's test vectors, which would
    -- otherwise show up as hundreds of mismatched shared secrets rather than as one clear error.
    for group in file.groups do
      let curve ← IO.ofExcept (getField String group.header "curve")
      unless group.type == "XdhComp" && curve == "curve25519" do
        throw (IO.userError s!"{vectorFile}: expected curve25519 XdhComp vectors, \
          got {curve} {group.type}")
    return (file.cases.map checkCase).toList

end X25519.Tests
