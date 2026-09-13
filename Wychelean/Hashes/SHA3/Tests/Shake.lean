import Wychelean.Hashes.SHA3.Tests.Rsp
import Wychelean.Hashes.SHA3.XOF
import RunTests.Basic

/-!
# SHAKE known-answer tests

NIST CAVP SHAKE response files (see `TestVectors/README.md`): short and long messages, variable
output lengths, and the SHA3VS §6.3.3 Monte Carlo recurrence, each in byte- and bit-oriented
form. The variable-output files also exercise the incremental XOF: the output is squeezed three
bytes at a time, as ML-KEM's SampleNTT does, and must equal the one-shot result.
-/

namespace Wychelean.Hashes.SHA3.Tests
open RunTests Rsp Std.Internal.Parsec.String

inductive Xof where
  | shake128
  | shake256

private def Xof.name : Xof → String
  | .shake128 => "SHAKE128"
  | .shake256 => "SHAKE256"

/-- The bit API, packing the output least significant bit first with a zero-padded last byte. -/
private def evaluateBits (xof : Xof) (m : Vector Bit n) (d : Nat) : Array UInt8 :=
  let msg := BitVec.ofBitsLE m
  let out : BitVec d := match xof with
    | .shake128 => shake128_bits msg d
    | .shake256 => shake256_bits msg d
  (out.setWidth (8 * ((d + 7) / 8))).toBytesLE.toArray

/-- The byte API. -/
private def evaluateBytes (xof : Xof) (m : Array UInt8) (len : Nat) : Array UInt8 :=
  match xof with
  | .shake128 => (shake128 m.toVector len).toArray
  | .shake256 => (shake256 m.toVector len).toArray

/-- The incremental API, squeezing `chunk` bytes at a time. -/
private def evaluateIncremental (xof : Xof) (m : Array UInt8) (len chunk : Nat) : Array UInt8 :=
  Id.run do
    let mut out : Array UInt8 := #[]
    match xof with
    | .shake128 =>
      let mut s := SHAKE128.absorb SHAKE128.init m.toVector
      while out.size < len do
        let (s', c) := SHAKE128.squeeze s (min chunk (len - out.size))
        s := s'
        out := out ++ c.toArray
    | .shake256 =>
      let mut s := SHAKE256.absorb SHAKE256.init m.toVector
      while out.size < len do
        let (s', c) := SHAKE256.squeeze s (min chunk (len - out.size))
        s := s'
        out := out ++ c.toArray
    return out

private def vectorDir : System.FilePath := "Wychelean/Hashes/SHA3/TestVectors"

private def knownAnswers (dir file : String) (xof : Xof) (parser : Parser (List Kat))
    (byteOriented := true) (incremental := false) : Suite where
  name := s!"{dir}/{file}"
  tests := do
    let vectors ← RunTests.Parser.parseFile parser (vectorDir / dir / file)
    vectors.zipIdx.mapM fun (v, i) => do
      let expected := toHex v.output.bytes.toVector
      let name := s!"{i}, Len={v.msg.length}, Outputlen={v.output.length}"
      if byteOriented then do
        unless v.msg.length % 8 == 0 && v.output.length % 8 == 0 do
          throw (IO.userError s!"{file}: byte-oriented case has a partial byte")
        let len := v.output.length / 8
        let actual := evaluateBytes xof v.msg.bytes len
        if incremental then
          let chunked := evaluateIncremental xof v.msg.bytes len 3
          unless chunked == actual do
            return { name, failure := some "incremental squeeze differs from one-shot output" }
        return check name expected (toHex actual.toVector)
      else
        return check name expected (toHex (evaluateBits xof v.msg.bits v.output.length).toVector)

/-- SHA3VS §6.3.3: 100 checkpoints of 1000 iterations; the rightmost two output bytes, read as a
big-endian integer, choose the next output length. -/
private def monte (dir file : String) (xof : Xof) : Suite where
  name := s!"{dir}/{file}"
  tests := do
    let data ← RunTests.Parser.parseFile parseMonte (vectorDir / dir / file)
    let mut output := data.initial
    let mut nextLen := data.maxBytes
    let mut usedLen := nextLen
    let mut tests := #[]
    for (expected, i) in data.outputs.zipIdx do
      for _ in [0:1000] do
        let msg := (Array.range 16).map (fun j => output[j]?.getD 0)
        usedLen := nextLen
        output := evaluateBytes xof msg usedLen
        let tail := output[output.size - 2]!.toNat * 256 + output[output.size - 1]!.toNat
        nextLen := data.minBytes + tail % (data.maxBytes - data.minBytes + 1)
      tests := tests.push (check s!"COUNT={i} length" expected.length (8 * usedLen))
      tests := tests.push (check s!"COUNT={i}" (toHex expected.bytes.toVector) (toHex output.toVector))
    return tests.toList

/-- Short-message and variable-output vectors; `full` adds long messages and Monte Carlo. -/
def shakeSuites (full := false) : List Suite := Id.run do
  let mut short := []
  let mut long := []
  for (xof, bits) in [(Xof.shake128, 128), (Xof.shake256, 256)] do
    for byteOriented in [true, false] do
      let dir := s!"shake{if byteOriented then "byte" else "bit"}testvectors"
      let stem := xof.name
      short := short ++ [
        knownAnswers dir (stem ++ "ShortMsg.rsp") xof (parseShakeKat bits) byteOriented,
        knownAnswers dir (stem ++ "VariableOut.rsp") xof (parseVariable byteOriented) byteOriented
          (incremental := byteOriented) ]
      long := long ++ [
        knownAnswers dir (stem ++ "LongMsg.rsp") xof (parseShakeKat bits) byteOriented,
        monte dir (stem ++ "Monte.rsp") xof ]
  return if full then short ++ long else short

end Wychelean.Hashes.SHA3.Tests
