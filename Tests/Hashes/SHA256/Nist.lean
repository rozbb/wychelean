import Tests.Hashes.SHA256.Basic
import Tests.Hashes.SHA256.NistShortMsg
import Tests.Hashes.SHA256.NistLongMsg
import Tests.Hashes.SHA256.NistMonte

/-!
NIST CAVP SHA-256 byte-oriented tests:
ShortMsg, LongMsg and the Monte Carlo chain (SHAVS, section 6.4).
-/

namespace Tests.Hashes.SHA256.Nist

open Wychelean
open Wychelean.Hashes.SHA256

private def msgTests (label : String) (vectors : Array HashVector) : List Test :=
  vectors.toList.map fun v =>
    expectEq s!"{label} {v.msg.length / 2} bytes"
      (sha256Hex (Hex.decode v.msg).get!) v.digest

/--
One Monte Carlo checkpoint:
1000 iterations of `MDᵢ = SHA-256(MDᵢ₋₃ ‖ MDᵢ₋₂ ‖ MDᵢ₋₁)`, seeded with three copies of `seed`.
-/
private def checkpoint (seed : Array UInt8) : Array UInt8 := Id.run do
  let mut m0 := seed
  let mut m1 := seed
  let mut m2 := seed
  for _ in [0:1000] do
    let md := (sha256 (m0 ++ m1 ++ m2).toVector).toArray
    m0 := m1
    m1 := m2
    m2 := md
  return m2

private def monteTests : List Test := Id.run do
  let mut seed := (Hex.decode monteSeed).get!
  let mut tests := #[]
  for expected in monte, j in [0:monte.size] do
    seed := checkpoint seed
    tests := tests.push (expectEq s!"Monte COUNT = {j}" (Hex.encode seed) expected)
  return tests.toList

def tests : List Test :=
  msgTests "ShortMsg" shortMsg ++ msgTests "LongMsg" longMsg ++ monteTests

end Tests.Hashes.SHA256.Nist
