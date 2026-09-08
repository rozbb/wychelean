import Wychelean.Hashes.SHA256
import RunTests.Rsp

/-! SHA256 response-file parsing and Monte Carlo support. -/

namespace Wychelean.Hashes.SHA256.Rsp

open RunTests.Rsp

private def fixtureDir : System.FilePath := "Wychelean/Hashes/SHA256/Fixtures"

private def lengthKey : String := "Len"
private def messageKey : String := "Msg"
private def digestKey : String := "MD"
private def countKey : String := "COUNT"
private def seedKey : String := "Seed"
private def sectionHeader : String := s!"L = {digestSize}"

/-- SHA256 on a byte array; test messages must fit the FIPS length bound. -/
def sha256Bytes (msg : Array UInt8) : Array UInt8 :=
  if h : 8 * msg.size < 2 ^ 64 then (sha256 msg.toVector h).toArray else panic! "message too long"

structure HashVector where
  msg : Array UInt8
  digest : Array UInt8
  deriving BEq, Repr

private def parseVectors : List Field → Except String (List HashVector)
  | [] => return []
  | len :: msg :: md :: rest => do
    let bits ← len.readNat lengthKey
    unless bits % 8 == 0 do throw s!"line {len.line}: only byte-oriented messages are supported"
    let mut bytes ← msg.readHex messageKey
    -- NIST represents the empty message as Len = 0, Msg = 00.
    if bits == 0 && bytes == #[0] then bytes := #[]
    unless bytes.size * 8 == bits do
      throw s!"line {msg.line}: {messageKey} has {bytes.size * 8} bits, but {lengthKey} is {bits}"
    unless bits < 2 ^ 64 do throw s!"line {len.line}: message exceeds the SHA256 length bound"
    let digest ← md.readHexSized digestKey digestSize
    return ⟨bytes, digest⟩ :: (← parseVectors rest)
  | f :: _ => throw s!"line {f.line}: incomplete {lengthKey}/{messageKey}/{digestKey} record"

def parseKat (text : String) : Except String (List HashVector) := do
  parseVectors (← parseSingleSection text sectionHeader)

private def parseCheckpoints (next : Nat) : List Field → Except String (List (Array UInt8))
  | [] => return []
  | count :: md :: rest => do
    let index ← count.readNat countKey
    unless index == next do throw s!"line {count.line}: expected {countKey} = {next}, found {index}"
    let digest ← md.readHexSized digestKey digestSize
    return digest :: (← parseCheckpoints (next + 1) rest)
  | f :: _ => throw s!"line {f.line}: incomplete {countKey}/{digestKey} record"

def parseMonte (text : String) : Except String (Array UInt8 × List (Array UInt8)) := do
  match ← parseSingleSection text sectionHeader with
  | seed :: rest =>
    let seed ← seed.readHexSized seedKey digestSize
    let checkpoints ← parseCheckpoints 0 rest
    if checkpoints.isEmpty then throw "missing Monte Carlo checkpoints"
    return (seed, checkpoints)
  | [] => throw "missing Monte Carlo seed"

/-- One SHAVS checkpoint: 1000 hashes of the previous three digests, initially all `seed`. -/
def checkpoint (seed : Array UInt8) : Array UInt8 := Id.run do
  let mut m0 := seed
  let mut m1 := seed
  let mut m2 := seed
  for _ in [0:1000] do
    let md := sha256Bytes (m0 ++ m1 ++ m2)
    m0 := m1
    m1 := m2
    m2 := md
  return m2

def loadRsp {α : Type} (name : String) (parse : String → Except String α) : IO α := do
  let path := fixtureDir / name
  let text ← IO.FS.readFile path
  match parse text with
  | .ok value => return value
  | .error error => throw (IO.userError s!"{path}: {error}")

end Wychelean.Hashes.SHA256.Rsp
