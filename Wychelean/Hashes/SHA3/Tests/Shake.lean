import Wychelean.Hashes.SHA3.Tests.Rsp
import Wychelean.Hashes.SHA3.XOF
import RunTests.Basic

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

/-- Absorb input chunks, then squeeze `len` bytes using the cycled request sizes. -/
private def evaluateIncremental (xof : Xof) (chunks : List (Array UInt8)) (len : Nat)
    (schedule : Array Nat) : Array UInt8 :=
  let run {Absorbing Squeezing : Type} (init : Absorbing)
      (absorb : {n : Nat} → Absorbing → ByteVec n → Absorbing)
      (finalize : Absorbing → Squeezing)
      (squeeze : Squeezing → (n : Nat) → Squeezing × ByteVec n) := Id.run do
    let input := chunks.foldl (fun s chunk => absorb s chunk.toVector) init
    let mut s := finalize input
    let mut out : Array UInt8 := #[]
    let mut k := 0
    while out.size < len do
      let (s', c) := squeeze s (min schedule[k % schedule.size]! (len - out.size))
      s := s'
      out := out ++ c.toArray
      k := k + 1
    return out
  match xof with
  | .shake128 =>
    run SHAKE128.init SHAKE128.absorb SHAKE128.finalize SHAKE128.squeeze
  | .shake256 =>
    run SHAKE256.init SHAKE256.absorb SHAKE256.finalize SHAKE256.squeeze

/-- Exercise partial-byte input chunks through the generic stateful API. -/
private def evaluateIncrementalBits (xof : Xof) (chunks : List (Array Bit)) (d : Nat) :
    Array UInt8 := Id.run do
  let r := match xof with | .shake128 => Internal.b - 256 | .shake256 => Internal.b - 512
  have hr : 0 < r ∧ r < Internal.b := by cases xof <;> decide
  let f := Permutations.Keccak.keccak_f .w1600
  let mut input := Incremental.sponge.init r hr
  for chunk in chunks do
    input := Incremental.sponge.absorb f r hr input chunk.toList
  let s := Incremental.sponge.finalize f r hr input Internal.xofSuffix.toBitsLE.toList
  let (_, bits) := Incremental.sponge.squeeze f r hr s d
  let out := BitVec.ofBitsLE bits
  return (out.setWidth (8 * ((d + 7) / 8))).toBytesLE.toArray

/-- SampleNTT-sized requests and rate-boundary crossings. -/
private def schedules (xof : Xof) : List (Array Nat) :=
  let rate := match xof with | .shake128 => 168 | .shake256 => 136
  [#[3], #[1, rate - 1, 0, rate + 1, rate, 5, 0, 2]]

private def incrementalSuite : Suite where
  name := "SHAKE stateful"
  verbose := false
  tests := do
    let mut tests := []
    for (xof, rate) in [(Xof.shake128, 168), (Xof.shake256, 136)] do
      let len := 2 * rate + 1
      let requests := schedules xof ++ [#[0, 3]]
      for schedule in requests do
        tests := tests ++ [check s!"{xof.name}, no absorbs, requests={schedule}"
          (toHex (evaluateBytes xof #[] len).toVector)
          (toHex (evaluateIncremental xof [] len schedule).toVector)]
      for size in [0, 1, rate - 1, rate, rate + 1, 2 * rate - 1, 2 * rate, 2 * rate + 1] do
        let msg := (Array.range size).map (fun i => UInt8.ofNat i)
        let expected := toHex (evaluateBytes xof msg len).toVector
        for split in [0, 1, rate - 1, rate, rate + 1] do
          let chunks := [#[], msg.extract 0 split, #[], msg.extract split size, #[]]
          for schedule in requests do
            tests := tests ++ [check s!"{xof.name}, Len={size}, split={split}, requests={schedule}"
              expected (toHex (evaluateIncremental xof chunks len schedule).toVector)]
        let byteChunks := msg.toList.map (fun byte => #[byte])
        for schedule in requests do
          tests := tests ++ [check s!"{xof.name}, Len={size}, byte chunks, requests={schedule}"
            expected (toHex (evaluateIncremental xof byteChunks len schedule).toVector)]
      let r := 8 * rate
      let d := 8 * len + 3
      for size in [r - 5, r - 4, r - 3, r - 2, r - 1, r, r + 1] do
        let msg := (Array.range size).map (fun i => i % 3 == 1)
        let expected := toHex (evaluateBits xof msg.toVector d).toVector
        for split in [1, r - 1, r] do
          let chunks := [#[], msg.extract 0 split, #[], msg.extract split size, #[]]
          tests := tests ++ [check s!"{xof.name}, bit Len={size}, split={split}"
            expected (toHex (evaluateIncrementalBits xof chunks d).toVector)]
    return tests

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
          for schedule in schedules xof do
            let chunked := evaluateIncremental xof [v.msg.bytes] len schedule
            unless chunked == actual do
              return { name, failure := some s!"incremental squeeze with requests {schedule} \
                differs from one-shot output" }
        return check name expected (toHex actual.toVector)
      else
        return check name expected (toHex (evaluateBits xof v.msg.bits v.output.length).toVector)

/-- SHA3VS §6.3.3: Monte Carlo test. -/
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
  let mut short := [incrementalSuite]
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
