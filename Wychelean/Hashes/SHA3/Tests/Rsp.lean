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

end Wychelean.Hashes.SHA3.Tests.Rsp
