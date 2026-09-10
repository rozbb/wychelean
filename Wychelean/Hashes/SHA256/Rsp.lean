import Wychelean.Hashes.SHA256
import RunTests.Parser.Rsp

/-! SHA256 response-file parsing and Monte Carlo support (SHAVS).
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/SHAVS.pdf
-/

namespace Wychelean.Hashes.SHA256.Rsp

open Std.Internal.Parsec Std.Internal.Parsec.String
open RunTests.Parser RunTests.Parser.Rsp

private def fixtureDir : System.FilePath := "Wychelean/Hashes/SHA256/Fixtures"

private def digestKey : String := "MD"
private def countKey : String := "COUNT"
private def seedKey : String := "Seed"
private def sectionHeader : String := s!"L = {digestSize}"

abbrev Digest := ByteVec digestSize

structure HashVector where
  msg : BitString
  digest : Digest

private def parseDigest : Parser Digest := field digestKey (readHexVec digestSize)

/-- Known-answer records; messages may have any bit length (SHAVS, sections 6.2 and 6.3). -/
def parseKat : Parser (List HashVector) := responseFile do
  header sectionHeader
  return (← many1 do return ⟨← message (msbFirst := true), ← parseDigest⟩).toList

/-- Seed and checkpoint digests; `COUNT` must run `0, 1, …` in order (SHAVS, section 6.4). -/
def parseMonte : Parser (Digest × List Digest) := responseFile do
  header sectionHeader
  let seed ← field seedKey (readHexVec digestSize)
  let checkpoints ← many1 do return (← field countKey digits, ← parseDigest)
  for ((count, _), i) in checkpoints.zipIdx do
    unless count == i do fail s!"{countKey} = {count} where {i} was expected"
  return (seed, checkpoints.toList.map (·.2))

/-- One SHAVS checkpoint: 1000 hashes of the previous three digests, initially all `seed`. -/
def checkpoint (seed : Digest) : Digest := Id.run do
  let mut (m0, m1, m2) := (seed, seed, seed)
  for _ in [0:1000] do
    (m0, m1, m2) := (m1, m2, sha256 (m0 ++ m1 ++ m2) (by decide))
  return m2

def loadRsp {α : Type} (dir file : String) (parser : Parser α) : IO α := do
  parseFile parser (fixtureDir / dir / file)

end Wychelean.Hashes.SHA256.Rsp
