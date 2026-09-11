import Lean.Data.Json
import RunTests.Parser.Basic

/-!
# Project Wycheproof test-vector files

Wycheproof publishes its vectors as JSON with a shape that is the same for every algorithm: a file
header, a list of test groups, and inside each group a list of test cases carrying `tcId`,
`comment`, `flags` and `result`. This module reads that envelope and leaves the algorithm-specific
part of a group header and of a case to the caller.

<https://github.com/C2SP/wycheproof/blob/main/doc/files.md>
-/

namespace RunTests.Parser.Wycheproof

open Lean

/-! ## Field accessors -/

/-- Read a field, naming the key in the error -/
def getField (α) [FromJson α] (j : Json) (key : String) : Except String α :=
  match j.getObjVal? key with
  | .error _ => .error s!"missing field \"{key}\""
  | .ok value => (fromJson? value).mapError fun error => s!"field \"{key}\": {error}"

/-- Read a field holding exactly `n` bytes of hex -/
def getHexField (n : Nat) (j : Json) (key : String) : Except String (Vector UInt8 n) := do
  (fromHex (← getField String j key)).mapError fun error => s!"field \"{key}\": {error}"

/-! ## Files -/

/-- The outcome a conforming implementation must produce, from a case's `result` field. -/
inductive ExpectedResult where
  /-- The implementation must accept the input and return the given answer. -/
  | valid
  /-- The implementation may reject the input, but must return the given answer if it accepts. -/
  | acceptable
  /-- The implementation must reject the input. -/
  | invalid
deriving BEq, Inhabited

instance : ToString ExpectedResult where
  toString
    | .valid => "valid"
    | .acceptable => "acceptable"
    | .invalid => "invalid"

/-- The fields every Wycheproof case carries, alongside its algorithm-specific payload. -/
structure Case (α : Type) where
  tcId : Nat
  comment : String
  /-- Names of the file's `notes` entries explaining what this case exercises, e.g. `Twist`. -/
  flags : Array String
  result : ExpectedResult
  data : α

/-- How a failing test should name a case: `tcId 1, normal case [Normal]`. -/
def Case.name (c : Case α) : String :=
  s!"tcId {c.tcId}, {c.comment} [{String.intercalate ", " c.flags.toList}]"

/-- A group of cases sharing a header, e.g. one curve or one key size. -/
structure Group (α : Type) where
  /-- The kind of test the group holds, e.g. `XdhComp`. -/
  type : String
  /-- The group's own JSON object, for header fields specific to the algorithm, e.g. `curve`. -/
  header : Json
  cases : Array (Case α)

structure File (α : Type) where
  algorithm : String
  /-- The count the header declares; `parse` checks the cases it read against it. -/
  numberOfTests : Nat
  groups : Array (Group α)

/-- Every case in the file, in the order it appears. -/
def File.cases (f : File α) : Array (Case α) := f.groups.flatMap (·.cases)

private def parseResult (j : Json) : Except String ExpectedResult := do
  match ← getField String j "result" with
  | "valid" => return .valid
  | "acceptable" => return .acceptable
  | "invalid" => return .invalid
  | other => throw s!"field \"result\": unknown result {other}"

private def parseCase (payload : Json → Except String α) (j : Json) : Except String (Case α) := do
  let tcId ← getField Nat j "tcId"
  let case : Except String (Case α) := do
    return { tcId,
             comment := ← getField String j "comment",
             flags := ← getField (Array String) j "flags",
             result := ← parseResult j,
             data := ← payload j }
  case.mapError fun error => s!"tcId {tcId}: {error}"

private def parseGroup (payload : Json → Except String α) (j : Json) : Except String (Group α) := do
  return { type := ← getField String j "type",
           header := j,
           cases := ← (← getField (Array Json) j "tests").mapM (parseCase payload) }

/-- Read a Wycheproof file, decoding each case's algorithm-specific fields with `payload`. -/
def parse (payload : Json → Except String α) (text : String) : Except String (File α) := do
  let json ← Json.parse text
  let file : File α :=
    { algorithm := ← getField String json "algorithm",
      numberOfTests := ← getField Nat json "numberOfTests",
      groups := ← (← getField (Array Json) json "testGroups").mapM (parseGroup payload) }
  unless file.cases.size == file.numberOfTests do
    throw s!"header declares {file.numberOfTests} tests, found {file.cases.size}"
  return file

/-- Read and parse a Wycheproof file, including its path in parse errors. -/
def parseFile (payload : Json → Except String α) (path : System.FilePath) : IO (File α) := do
  let text ← IO.FS.readFile path
  IO.ofExcept ((parse payload text).mapError fun error => s!"{path}: {error}")

end RunTests.Parser.Wycheproof
