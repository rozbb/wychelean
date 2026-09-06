import Tests.Hashes.SHA256.Basic
import Tests.Hashes.SHA256.NistMonte

/-!
NIST CAVP SHA-256 Monte Carlo test (SHAVS, section 6.4).
Checking it runs the full chain of 100 000 hashes at elaboration time.
-/

namespace Tests.Hashes.SHA256.Nist

open Wychelean
open Wychelean.Hashes.SHA256

/--
One Monte Carlo checkpoint:
1000 iterations of `MDᵢ = SHA-256(MDᵢ₋₃ ‖ MDᵢ₋₂ ‖ MDᵢ₋₁)`, seeded with three copies of `seed`.
-/
def checkpoint (seed : Array UInt8) : Array UInt8 := Id.run do
  let mut m0 := seed
  let mut m1 := seed
  let mut m2 := seed
  for _ in [0:1000] do
    let md := (sha256 (m0 ++ m1 ++ m2).toVector).toArray
    m0 := m1
    m1 := m2
    m2 := md
  return m2

/-- The digest at every checkpoint, chained from `monteSeed`. -/
def monteDigests : Array String := Id.run do
  let mut seed := (Hex.decode monteSeed).get!
  let mut out := #[]
  for _ in [0:monte.size] do
    seed := checkpoint seed
    out := out.push (Hex.encode seed)
  return out

example : monteDigests = monte := by native_decide

end Tests.Hashes.SHA256.Nist
