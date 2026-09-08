import Wychelean.Hashes.SHA3
import RunTests.Parser.Rsp

/-! NIST SHA3VS response files, including non-byte-aligned messages and outputs.
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha3vs.pdf
-/
namespace Wychelean.Hashes.SHA3.Rsp
open Std.Internal.Parsec Std.Internal.Parsec.String
open RunTests.Parser RunTests.Parser.Rsp

structure BitString where
  length : Nat
  bytes : Array UInt8
  fits : length ≤ 8 * bytes.size

/-- FIPS 202 Appendix B.1: bits within each byte are least significant first. -/
def BitString.bits (s : BitString) : Vector Bool s.length :=
  Vector.ofFn fun i => s.bytes[i.val / 8]'(by have := s.fits; omega)
    |>.toNat.testBit (i.val % 8)

/-- Reject malformed lengths and nonzero unused high bits. Len=0, Msg=00 is NIST's sentinel. -/
def encoded (n : Nat) : Parser BitString := do
  let bytes ← readHex
  let bytes := if n == 0 && bytes == #[0] then #[] else bytes
  unless bytes.size == (n + 7) / 8 do fail s!"expected {(n + 7) / 8} bytes, got {bytes.size}"
  if n % 8 != 0 && bytes.back!.toNat >>> (n % 8) != 0 then
    fail "nonzero unused high bits"
  if h : n ≤ 8 * bytes.size then return ⟨n, bytes, h⟩
  else fail "encoded bit string is too short"

structure Kat where
  msg : BitString
  output : BitString

private def message : Parser BitString := do
  let n ← field "Len" readNat
  field "Msg" (encoded n)

def parseKat (shake : Bool) (d : Nat) : Parser (List Kat) := responseFile do
  header s!"{if shake then "Outputlen" else "L"} = {d}"
  return (← many1 do
    let m ← message
    let o ← field (if shake then "Output" else "MD") (encoded d)
    return ⟨m, o⟩).toList

private def bounds : Parser (Nat × Nat) := do
  let lo ← natHeader "Minimum Output Length (bits)"
  let hi ← natHeader "Maximum Output Length (bits)"
  unless lo ≤ hi do fail "inverted output bounds"
  return (lo, hi)

def parseVariable (byteOriented : Bool) : Parser (List Kat) := responseFile do
  header s!"Tested for Output of {if byteOriented then "byte" else "bit"}-oriented messages"
  let n ← natHeader "Input Length"
  let (lo, hi) ← bounds
  let cases ← many1 do
    let count ← field "COUNT" readNat
    let d ← field "Outputlen" readNat
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

def parseMonte (shake : Bool) (d : Nat) : Parser Monte := responseFile do
  let (lo, hi) ← if shake then bounds else do
    header s!"L = {d}"
    pure (d, d)
  let seed ← field (if shake then "Msg" else "Seed") (encoded (if shake then 128 else d))
  let cases ← many1 do
    let count ← field "COUNT" readNat
    let bits ← if shake then field "Outputlen" readNat else pure d
    unless bits % 8 == 0 && lo ≤ bits && bits ≤ hi do fail "invalid Monte Carlo length"
    let output ← field (if shake then "Output" else "MD") (encoded bits)
    return (count, output)
  for (entry, i) in cases.toList.zipIdx do
    unless entry.1 == i do fail "nonsequential COUNT"
  unless cases.size == 100 do fail "expected 100 Monte Carlo checkpoints"
  return ⟨seed.bytes, (lo + 7) / 8, hi / 8, cases.toList.map Prod.snd⟩

end Wychelean.Hashes.SHA3.Rsp
