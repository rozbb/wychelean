import Wychelean.Hashes.SHA3
import RunTests.Parser.Rsp

/-! NIST SHA3VS response files, including non-byte-aligned messages.
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha3vs.pdf
-/
namespace Wychelean.Hashes.SHA3.Tests.Rsp
open Std.Internal.Parsec Std.Internal.Parsec.String
open RunTests.Parser RunTests.Parser.Rsp

structure Kat where
  msg : BitString
  output : BitString

def parseKat (d : Nat) : Parser (List Kat) := responseFile do
  header s!"L = {d}"
  return (← many1 do
    let m ← message
    let o ← field "MD" (encoded d)
    return ⟨m, o⟩).toList

/-- SHAKE known-answer files: `[Outputlen = d]`, then `Len`/`Msg`/`Output` per case. -/
def parseShakeKat (d : Nat) : Parser (List Kat) := responseFile do
  header s!"Outputlen = {d}"
  return (← many1 do
    let m ← message
    let o ← field "Output" (encoded d)
    return ⟨m, o⟩).toList

private def bounds : Parser (Nat × Nat) := do
  let lo ← natHeader "Minimum Output Length (bits)"
  let hi ← natHeader "Maximum Output Length (bits)"
  unless lo ≤ hi do fail "inverted output bounds"
  return (lo, hi)

/-- SHAKE variable-output files: fixed input length, one `Outputlen` per case. -/
def parseVariable (byteOriented : Bool) : Parser (List Kat) := responseFile do
  header s!"Tested for Output of {if byteOriented then "byte" else "bit"}-oriented messages"
  let n ← natHeader "Input Length"
  let (lo, hi) ← bounds
  let cases ← many1 do
    let count ← field "COUNT" digits
    let d ← field "Outputlen" digits
    unless lo ≤ d && d ≤ hi do fail "output length outside declared bounds"
    let m ← field "Msg" (encoded n)
    let o ← field "Output" (encoded d)
    return (count, (⟨m, o⟩ : Kat))
  for (entry, i) in cases.toList.zipIdx do
    unless entry.1 == i do fail "nonsequential COUNT"
  return cases.toList.map Prod.snd

structure Monte where
  initial : Array UInt8
  minBytes : Nat
  maxBytes : Nat
  outputs : List BitString

/-- SHAKE Monte Carlo files (SHA3VS §6.3.3): a 128-bit seed and 100 checkpoints. -/
def parseMonte : Parser Monte := responseFile do
  let (lo, hi) ← bounds
  let seed ← field "Msg" (encoded 128)
  let cases ← many1 do
    let count ← field "COUNT" digits
    let bits ← field "Outputlen" digits
    unless bits % 8 == 0 && lo ≤ bits && bits ≤ hi do fail "invalid Monte Carlo length"
    let output ← field "Output" (encoded bits)
    return (count, output)
  for (entry, i) in cases.toList.zipIdx do
    unless entry.1 == i do fail "nonsequential COUNT"
  unless cases.size == 100 do fail "expected 100 Monte Carlo checkpoints"
  return ⟨seed.bytes, (lo + 7) / 8, hi / 8, cases.toList.map Prod.snd⟩

end Wychelean.Hashes.SHA3.Tests.Rsp
