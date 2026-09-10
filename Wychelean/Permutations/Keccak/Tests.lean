import Wychelean.Permutations.Keccak
import RunTests.Basic
import RunTests.Parser.Basic

/-!
The fixture files are unchanged Keccak-author traces from XKCP:
https://github.com/XKCP/XKCP/tree/eb5244d6b95fb1c434b211bac293093e18aa8fd1/tests/TestVectors

Each file contains two full permutations. For Keccak-p[800,12], the input and expected
output are the published states after rounds 9 and 21, respectively (rounds 10–21).
The byte dumps use little-endian lane order; intermediate states print lane words in hex.
-/

namespace Wychelean.Permutations.Keccak.Tests
open RunTests RunTests.Parser
open Std.Internal.Parsec Std.Internal.Parsec.String

private def readState (width : Width) (wordBytes : Nat) (text : String) : IO (BitVec (b width)) := do
  let words ← IO.ofExcept (parse (many1 (readHexVec wordBytes <* ws)) text)
  let bytes := (words.map fun word => word.toArray.reverse).flatten
  unless bytes.size * 8 == b width do
    throw (IO.userError s!"expected a {b width}-bit state, got {bytes.size} bytes")
  return (BitVec.ofBytesLE bytes.toVector).extractLsb' 0 (b width)

/-- Read the rows following a labeled state in the upstream trace format. -/
private def stateAfter (trace label : String) (occurrence rows : Nat) : IO String := do
  let some block := (trace.splitOn (label ++ "\n"))[occurrence + 1]?
    | throw (IO.userError s!"missing {label} occurrence {occurrence}")
  let lines := block.splitOn "\n"
  unless rows ≤ lines.length do
    throw (IO.userError s!"incomplete state after {label}")
  return String.intercalate "\n" (lines.take rows)

private def permutations (width : Width) : Suite where
  name := s!"XKCP Keccak-f[{b width}] published traces"
  tests := do
    let file := s!"KeccakF-{b width}-IntermediateValues.txt"
    let text ← IO.FS.readFile ("Wychelean/Permutations/Keccak/Fixtures" / file)
    let traces := (text.splitOn "Input of permutation:\n").drop 1
    unless traces.length == 2 do
      throw (IO.userError s!"{file}: expected two permutation traces")
    let mut tests := []
    for (trace, i) in traces.zipIdx do
      let input ← readState width 1 ((trace.splitOn "\n").head!)
      let expected ← readState width 1 (← stateAfter trace "State after permutation:" 0 1)
      tests := tests ++ [check s!"trace {i + 1}, full permutation" expected (keccak_f width input)]
      if width == .w800 then
        let input ← readState width (w width / 8) (← stateAfter trace "After iota:" 9 5)
        let expected ← readState width (w width / 8) (← stateAfter trace "After iota:" 21 5)
        tests := tests ++ [check s!"trace {i + 1}, rounds 10–21" expected (keccak_p width 12 input)]
    return tests

def suites : List Suite := [.w200, .w400, .w800, .w1600].map permutations

end Wychelean.Permutations.Keccak.Tests
