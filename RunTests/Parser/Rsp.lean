import RunTests.Parser.Basic

/-! Combinators for NIST CAVP response files. -/

namespace RunTests.Parser.Rsp

open Std.Internal.Parsec Std.Internal.Parsec.String

private def comment : Parser Unit :=
  skipChar '#' *> manyChars (satisfy (· != '\n')) *> pure ()

private def skipTrivia : Parser Unit :=
  ws *> many (comment <* ws) *> pure ()

private def lineEnd : Parser Unit :=
  skipHSpace *> (skipChar '\n' <|> eof <|> fail "expected end of line")

private def token (p : Parser α) : Parser α := p <* lineEnd <* skipTrivia

/-- Allow comments and whitespace around a response-file parser. -/
def responseFile (p : Parser α) : Parser α := skipTrivia *> p <* skipTrivia

/-- Match a section header, ignoring whitespace within it. -/
def header (expected : String) : Parser Unit := token do
  skipChar '['
  let value ← manyChars (satisfy fun c => c != ']' && c != '\n')
  skipChar ']' <|> fail "unclosed response-file header"
  let normalize := fun (s : String) => s.toList.filter (fun c => !c.isWhitespace)
  unless normalize value == normalize expected do fail s!"expected [{expected}]"

/-- Parse a named natural-number section header. -/
def natHeader (key : String) : Parser Nat := token do
  skipChar '['
  skipString key
  skipHSpace
  skipChar '='
  skipHSpace
  let n ← digits
  skipHSpace
  skipChar ']'
  return n

/-- Parse a named field using the supplied value combinator. -/
def field (key : String) (value : Parser α) : Parser α := token do
  skipString key
  skipHSpace
  skipChar '='
  skipHSpace
  value

/-- Match a standalone response-file flag. -/
def flag (name : String) : Parser Unit := token (skipString name)

/-- `length` bits packed into whole bytes; the unused bits of the last byte are zero. -/
structure BitString where
  length : Nat
  bytes : Array UInt8
  fits : length ≤ 8 * bytes.size

/-- FIPS 202 Appendix B.1 order: bits within each byte are least significant first. -/
def BitString.bits (s : BitString) : Vector Bool s.length :=
  Vector.ofFn fun i => s.bytes[i.val / 8]'(by have := s.fits; omega)
    |>.toNat.testBit (i.val % 8)

/-- Decode `n` bits of hex. NIST writes the empty string as `00`. With `msbFirst` the bits fill
each byte from its most significant end (SHAVS; FIPS 180-4 §3.1) and the unused bits are the low
bits of the last byte; otherwise from the least significant end (SHA3VS; FIPS 202 B.1). -/
def encoded (n : Nat) (msbFirst := false) : Parser BitString := do
  let bytes ← readHex
  let bytes := if n == 0 && bytes == #[0] then #[] else bytes
  unless bytes.size == (n + 7) / 8 do fail s!"expected {(n + 7) / 8} bytes, got {bytes.size}"
  if n % 8 != 0 then
    let unused := if msbFirst then bytes.back!.toNat % (1 <<< (8 - n % 8))
                  else bytes.back!.toNat >>> (n % 8)
    unless unused == 0 do fail "nonzero unused bits"
  if h : n ≤ 8 * bytes.size then return ⟨n, bytes, h⟩
  else fail "encoded bit string is too short"

/-- The `Len = n` / `Msg = …` pair that heads every CAVP known-answer vector. -/
def message (msbFirst := false) : Parser BitString := do
  field "Msg" (encoded (← field "Len" digits) msbFirst)

end RunTests.Parser.Rsp
