import RunTests.Basic
import RunTests.Rsp

namespace RunTests.Rsp.Tests

private instance [Repr α] : ToString (Except String α) := ⟨reprStr⟩

private instance [BEq α] : BEq (Except String α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def rejects (text : String) : Bool :=
  match parse text with
  | .error _ => true
  | .ok _ => false

def suite : Suite where
  name := "RSP format parser"
  tests := pure [
    check "empty and comment-only files have no entries" (.ok []) (parse "# comment\r\n\r\n"),
    check "preserve headers, records, field order, empty values, and line numbers"
      (.ok [.header "ENCRYPT" 2, .header "KEYLEN = 128" 3,
        .record [⟨"COUNT", some "0", 5⟩, ⟨"PT", some "", 6⟩],
        .record [⟨"COUNT", some "1", 8⟩, ⟨"PT", some "AB", 9⟩],
        .header "DECRYPT" 10, .record [⟨"CT", some "cd", 11⟩]])
      (parse "# comment\r\n[ENCRYPT]\r\n[ KEYLEN = 128 ]\r\n\r\nCOUNT = 0\r\nPT =\r\n\r\nCOUNT = 1\r\nPT = AB\r\n[DECRYPT]\r\nCT = cd"),
    check "headerless records and equals signs in values"
      (.ok [.record [⟨"Label", some "a=b", 1⟩]]) (parse "Label = a=b"),
    check "comments within a record do not split it"
      (.ok [.record [⟨"A", some "1", 1⟩, ⟨"B", some "2", 3⟩]]) (parse "A = 1\n# note\nB = 2\n"),
    check "repeated fields are retained for schema validation"
      (.ok [.record [⟨"A", some "1", 1⟩, ⟨"A", some "2", 2⟩]]) (parse "A = 1\nA = 2"),
    check "bare flags are distinct from empty values"
      (.ok [.record [⟨"FAIL", none, 1⟩, ⟨"PT", some "", 2⟩]]) (parse "FAIL\nPT ="),
    check "reject missing closing bracket" true (rejects "[ENCRYPT"),
    check "reject empty header" true (rejects "[ ]"),
    check "reject empty key" true (rejects " = 123"),
    check "reject malformed line" true (rejects "COUNT 1"),
    check "error identifies source line"
      (.error "line 3: empty field name") (parse "# comment\n\n = 123"),
    check "collect a section with a caller-supplied header"
      (.ok [⟨"COUNT", some "0", 2⟩, ⟨"KEY", some "abcd", 4⟩])
      (parseSingleSection "[KEYLEN=16]\nCOUNT = 0\n\nKEY = abcd" "KEYLEN = 16"),
    check "reject an additional section with its source line"
      (.error "line 3: unexpected additional section")
      (parseSingleSection "[ENCRYPT]\nCOUNT = 0\n[DECRYPT]" "ENCRYPT"),
    check "reject missing section header"
      (.error "expected a response file starting with [ENCRYPT]")
      (parseSingleSection "COUNT = 0" "ENCRYPT"),
    check "reject empty section" (.error "missing response-file fields")
      (parseSingleSection "[ENCRYPT]" "ENCRYPT"),
    check "reject wrong section header" (.error "line 1: expected [ENCRYPT]")
      (parseSingleSection "[DECRYPT]\nCOUNT = 0" "ENCRYPT"),
    check "read a natural-number field" (.ok 12)
      ((Field.mk "COUNT" (some "12") 4).readNat "COUNT"),
    check "reject nonnumeric field" (.error "line 4: COUNT must be a natural number")
      ((Field.mk "COUNT" (some "x") 4).readNat "COUNT"),
    check "reject a mismatched field name"
      (.error "line 4: expected COUNT, found KEY")
      ((Field.mk "KEY" (some "12") 4).readNat "COUNT"),
    check "reject a flag where a value is required"
      (.error "line 4: COUNT requires a value")
      ((Field.mk "COUNT" none 4).readNat "COUNT"),
    check "read hex with a caller-supplied byte count" (.ok #[0xab, 0xcd])
      ((Field.mk "KEY" (some "AbCd") 4).readHexSized "KEY" 2),
    check "reject malformed hex field" (.error "line 4: malformed hexadecimal KEY")
      ((Field.mk "KEY" (some "zz") 4).readHex "KEY"),
    check "reject a mismatched byte count"
      (.error "line 4: KEY must contain 2 bytes")
      ((Field.mk "KEY" (some "ab") 4).readHexSized "KEY" 2)
  ]

def suites : List Suite := [suite]

end RunTests.Rsp.Tests
