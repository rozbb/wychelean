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

end RunTests.Parser.Rsp
