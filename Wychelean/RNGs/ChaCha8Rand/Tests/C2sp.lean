module

public import Wychelean.RNGs.ChaCha8Rand.Basic
public import RunTests.Basic
public import RunTests.Parser.Basic

/-!
# ChaCha8Rand C2SP known-answer tests

The sample output of <https://c2sp.org/chacha8rand>: the first 2976 bytes, i.e., three iterations,
for the seed `ABCDEFGHIJKLMNOPQRSTUVWXYZ123456`. It is checked whole, iteration by iteration, and
as prefixes that end inside and on the edges of an iteration.
-/

namespace Wychelean.RNGs.ChaCha8Rand.Tests
open RunTests RunTests.Parser

private def vectorFile : System.FilePath :=
  "Wychelean/RNGs/ChaCha8Rand/TestVectors/c2sp_sample_output.txt"

/-- The sample seed, in ASCII. -/
private def seed : ByteVec seedBytes :=
  let bytes := "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456".toUTF8
  Vector.ofFn fun i => bytes[i.val]!

/-- Prefix lengths to check: empty, within the first iteration, at and around each iteration
boundary, and the whole sample. -/
private def prefixLengths : List Nat := [0, 1, 8, 31, 32, 33, 991, 992, 993, 1984, 2000, 2976]

private def hexOf (bytes : Array UInt8) : String := toHex bytes.toVector

/-- The sample output, read from the vector file. -/
private def loadSample : IO (Array UInt8) := do
  let text ← IO.FS.readFile vectorFile
  let lines := (text.splitOn "\n").filter (· ≠ "")
  let bytes ← IO.ofExcept ((parse readHex (String.join lines)).mapError (s!"{vectorFile}: " ++ ·))
  unless bytes.size == 3 * outputBytes do
    throw (IO.userError s!"{vectorFile}: expected {3 * outputBytes} bytes, got {bytes.size}")
  return bytes

public def c2sp : Suite where
  name := "ChaCha8Rand (C2SP sample output)"
  tests := do
    let sample ← loadSample
    let whole := (iterations seed 3).toArray
    let iterTests := (List.range 3).map fun i =>
      check s!"iteration {i + 1} of 3"
        (hexOf (sample.extract (i * outputBytes) ((i + 1) * outputBytes)))
        (hexOf (whole.extract (i * outputBytes) ((i + 1) * outputBytes)))
    let prefixTests := prefixLengths.map fun len =>
      check s!"first {len} bytes" (hexOf (sample.extract 0 len))
        (hexOf (chacha8rand seed len).toArray)
    return iterTests ++ prefixTests

end Wychelean.RNGs.ChaCha8Rand.Tests
