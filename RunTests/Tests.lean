import RunTests.Basic
import RunTests.Parser.Rsp

/-! Regression tests for test-vector parsing and formatting. -/

namespace RunTests.Tests

open RunTests.Parser
open Std.Internal.Parsec.String (skipChar)

private instance : ToString (Option (Array UInt8)) := ⟨reprStr⟩

def hex : Suite where
  name := "Hex test helpers"
  tests := do
    let allBytes : Vector UInt8 256 := Vector.ofFn fun i => i.val.toUInt8
    let encoded := toHex allBytes
    let mut tests := [
      check "encode empty vector" "" (toHex (#v[] : Vector UInt8 0)),
      check "encode leading zeros" "000aff" (toHex #v[0x00, 0x0a, 0xff]),
      check "encode lowercase" "deadbeef" (toHex #v[0xde, 0xad, 0xbe, 0xef]),
      check "decode empty input" (some #[]) (parse readHex "").toOption,
      check "decode lowercase" (some #[0xde, 0xad, 0xbe, 0xef])
        (parse readHex "deadbeef").toOption,
      check "decode leading zeros" (some #[0x00, 0x0a, 0xff])
        (parse readHex "000aff").toOption,
      check "decode exact-size vector" (some #[0x00, 0x0a])
        ((hexVector (n := 2) "000a").toOption.map (·.toArray)),
      check "decode zero-size vector" (some #[])
        ((hexVector (n := 0) "").toOption.map (·.toArray)),
      check "reject short vector" true (hexVector (n := 2) "00").toOption.isNone,
      check "reject long vector" true (hexVector (n := 1) "000a").toOption.isNone,
      check "reject nonempty zero-size vector" true (hexVector (n := 0) "00").toOption.isNone,
      check "hexVector requires complete input" true (hexVector (n := 1) "00zz").toOption.isNone,
      check "two hex digits per byte" 512 encoded.length,
      check "round-trip every byte value" (some allBytes.toArray) (parse readHex encoded).toOption,
      check "hex token leaves its delimiter" (some #[0x00, 0xaf])
        (parse (readHex <* skipChar ':') "00af:").toOption
    ]
    for invalid in ["a", "abc", "zz", "00zz", "é0", "00é0", "DEADBEEF", "deadBEEF",
        "0x00", "0X00", "00 01", " 00", "00 ", "00\n01", "00\t01"] do
      tests := tests ++ [check s!"reject hex {repr invalid}" true (parse readHex invalid).toOption.isNone]
    let recoverable ← try
      let _ ← IO.ofExcept (hexVector (n := 1) "GG")
      pure false
    catch _ => pure true
    return tests ++ [check "invalid hex becomes a recoverable IO error" true recoverable]

def parsing : Suite where
  name := "Test-vector parsers"
  tests := do
    let rsp := Rsp.responseFile do
      Rsp.header "L = 2"
      Rsp.field "Msg" (readHexVec 2)
    let mut tests := [
      check "RSP comments, whitespace, and CRLF" (some #[0x00, 0x0a])
        ((parse rsp "# comment\r\n [ L = 2 ]\r\n Msg = 000a \t\r\n# end\r\n").toOption.map (·.toArray)),
      check "RSP rejects uppercase hex" true (parse rsp "[L = 2]\nMsg = 00Af\n").toOption.isNone,
      check "RSP rejects hex prefix" true (parse rsp "[L = 2]\nMsg = 0x000a\n").toOption.isNone,
      check "RSP rejects trailing junk" true (parse rsp "[L = 2]\nMsg = 000azz\n").toOption.isNone,
      check "RSP error retains line number" true
        (match parse rsp "[L = 2]\nMsg = 00Af\n" with
         | .error error => error.startsWith "line 2:"
         | .ok _ => false),
      check "parse decimal expected value" true ((parse readNat "12345").toOption == some 12345)
    ]
    for invalid in ["", "12x", "-1", " 12", "12 ", "0x12", "１２"] do
      tests := tests ++ [check s!"reject decimal {repr invalid}" true (parse readNat invalid).toOption.isNone]
    return tests

def suites : List Suite := [hex, parsing]

end RunTests.Tests
