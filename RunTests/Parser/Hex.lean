module

public import RunTests.Parser.Basic
-- The `hex!` macro decodes its literal with `fromHex` at elaboration time.
public meta import RunTests.Parser.Basic

/-! The `hex!` byte-vector literal. -/

public section

namespace RunTests.Parser

/-- Interpret a string literal as a hex byte sequence (Vector UInt8) -/
scoped syntax (name := hexLit) "hex! " str : term

open Lean in
macro_rules
  | `(hex! $s:str) => do
    let text := s.getString
    if text.length % 2 != 0 then
      Macro.throwErrorAt s s!"hex string has {text.length} digits, which is not a whole number of \
        bytes"
    match fromHex (n := text.length / 2) text with
    | .error error => Macro.throwErrorAt s error
    | .ok bytes =>
      let digits := bytes.toArray.map fun byte => (quote byte.toNat : Term)
      `((#v[$digits,*] : Vector UInt8 $(quote bytes.size)))

end RunTests.Parser
