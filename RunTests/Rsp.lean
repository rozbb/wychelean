/-! Generic parser for NIST CAVP response files. -/

namespace RunTests.Rsp

/-- An assignment (`some value`) or bare flag (`none`), with its one-based source line. -/
structure Field where
  key : String
  value : Option String
  line : Nat
  deriving BEq, Repr

/-- A bracketed header (such as `ENCRYPT` or `L = 32`), or a block of assignments. -/
inductive Entry where
  | header (value : String) (line : Nat)
  | record (fields : List Field)
  deriving BEq, Repr

/-- Parse a response file. Algorithm-specific requirements belong to the consumer. -/
def parse (text : String) : Except String (List Entry) := do
  let mut entries := #[]
  let mut fields : Array Field := #[]
  for (raw, i) in (text.splitOn "\n").zipIdx do
    let line := raw.trimAscii.toString
    if line.startsWith "#" then continue
    if line.isEmpty || line.startsWith "[" then
      if !fields.isEmpty then
        entries := entries.push (.record fields.toList)
        fields := #[]
      if line.isEmpty then continue
      unless line.endsWith "]" do throw s!"line {i + 1}: unclosed response-file header"
      let value := (String.ofList ((line.toList.drop 1).dropLast)).trimAscii.toString
      if value.isEmpty then throw s!"line {i + 1}: empty response-file header"
      entries := entries.push (.header value (i + 1))
    else
      match line.splitOn "=" with
      | key :: value :: rest =>
        let key := key.trimAscii.toString
        if key.isEmpty then throw s!"line {i + 1}: empty field name"
        let value := (String.intercalate "=" (value :: rest)).trimAscii.toString
        fields := fields.push ⟨key, some value, i + 1⟩
      | [flag] =>
        unless flag.toList.all (fun c => c.isAlphanum || c == '_') do
          throw s!"line {i + 1}: malformed response-file flag"
        fields := fields.push ⟨flag, none, i + 1⟩
      | _ => throw s!"line {i + 1}: expected a key = value field or bracketed header"
  if !fields.isEmpty then entries := entries.push (.record fields.toList)
  return entries.toList

end RunTests.Rsp
