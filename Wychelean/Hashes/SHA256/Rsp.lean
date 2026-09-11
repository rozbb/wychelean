import Wychelean.Hashes.SHA256
import RunTests.Parser.Rsp

/-! SHA256 response-file parsing and Monte Carlo support. -/

namespace Wychelean.Hashes.SHA256.Rsp

open Std.Internal.Parsec Std.Internal.Parsec.String
open RunTests.Parser RunTests.Parser.Rsp

private def vectorDir : System.FilePath := "Wychelean/Hashes/SHA256/TestVectors"

private def lengthKey : String := "Len"
private def messageKey : String := "Msg"
private def digestKey : String := "MD"
private def countKey : String := "COUNT"
private def seedKey : String := "Seed"
private def sectionHeader : String := s!"L = {digestSize}"

abbrev Digest := Vector UInt8 digestSize

structure HashVector where
  msg : Array UInt8
  digest : Digest
  deriving BEq, Repr

private def message : Parser (Array UInt8) := do
  let bits ← field lengthKey digits
  field messageKey do
    let bytes ← readHex
    -- NIST represents the empty message as Len = 0, Msg = 00.
    let bytes := if bits == 0 && bytes == #[0] then #[] else bytes
    unless bytes.size * 8 == bits do
      fail s!"{messageKey} has {bytes.size * 8} bits, but {lengthKey} is {bits}"
    return bytes

private def parseDigest : Parser Digest := field digestKey (readHexVec digestSize)

private def hashVector : Parser HashVector := do
  return ⟨← message, ← parseDigest⟩

def parseKat : Parser (List HashVector) := responseFile do
  header sectionHeader
  return (← many1 hashVector).toList

def parseMonte : Parser (Digest × List Digest) := responseFile do
  header sectionHeader
  let seed ← field seedKey (readHexVec digestSize)
  let checkpoints ← many1 (field countKey digits *> parseDigest)
  return (seed, checkpoints.toList)

/-- One SHAVS checkpoint: 1000 hashes of the previous three digests, initially all `seed`. -/
def checkpoint (seed : Digest) : Digest := Id.run do
  let mut (m0, m1, m2) := (seed, seed, seed)
  for _ in [0:1000] do
    (m0, m1, m2) := (m1, m2, sha256 (m0 ++ m1 ++ m2) (by decide))
  return m2

def loadRsp {α : Type} (name : String) (parser : Parser α) : IO α := do
  parseFile parser (vectorDir / name)

end Wychelean.Hashes.SHA256.Rsp
