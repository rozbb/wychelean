import Std.Internal.Parsec.String

/-! String parser combinators and complete-input runners. -/

namespace RunTests.Parser

open Std.Internal.Parsec Std.Internal.Parsec.String

/-- Consume whitespace without crossing a newline. -/
def skipHSpace : Parser Unit :=
  many (satisfy fun c => c != '\n' && c.isWhitespace) *> pure ()

def readNat : Parser Nat := digits

private def hexNibble : Parser UInt8 := do
  let c ← hexDigit
  if c.isUpper then fail "expected lowercase hex digit"
  return UInt8.ofNat (if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)

/-- Parse pairs of lowercase hex digits, without a prefix. -/
def readHex : Parser (Array UInt8) := many do
  let hi ← hexNibble
  let lo ← hexNibble
  return 16 * hi + lo

def readHexVec (size : Nat) : Parser (Vector UInt8 size) := do
  let bytes ← readHex
  if h : bytes.size = size then return ⟨bytes, h⟩
  else fail s!"expected {size} bytes, found {bytes.size}"

/-- Run a combinator, requiring it to consume the entire input. -/
def parse (parser : Parser α) (text : String) : Except String α :=
  match (parser <* eof) ⟨text, text.startPos⟩ with
  | .success _ value => .ok value
  | .error pos error =>
    let line := ((pos.1.sliceTo pos.2).copy.toList.count '\n') + 1
    .error s!"line {line}: {error}"

/-- Read and parse a file, including its path in parse errors. -/
def parseFile (parser : Parser α) (path : System.FilePath) : IO α := do
  let text ← IO.FS.readFile path
  IO.ofExcept ((parse parser text).mapError fun error => s!"{path}: {error}")

end RunTests.Parser
