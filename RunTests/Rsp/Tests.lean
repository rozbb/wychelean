import RunTests.Basic
import RunTests.Rsp

namespace RunTests.Rsp.Tests

private instance : ToString (Except String (List Entry)) := ⟨reprStr⟩

private instance : BEq (Except String (List Entry)) where
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
      (.error "line 3: empty field name") (parse "# comment\n\n = 123")
  ]

def suites : List Suite := [suite]

end RunTests.Rsp.Tests
