import Wychelean.Hashes.SHA3.Tests.Rsp
import Wychelean.Utils.Hex
import RunTests.Basic

/-!
# NIST SHA3 fixtures

Fixture sources and archive digests: [Fixtures/README.md](../Fixtures/README.md).
The default run selects 104 cases from the list below.
`lake test -- --full` runs all 4,912 short- and long-message cases.

Non-byte-aligned bit strings use low bits of the final byte; unused high bits must be zero.
The parser validates encoded lengths.
Empty messages use NIST's `Len = 0, Msg = 00` convention.
-/

namespace Wychelean.Hashes.SHA3.Tests
open RunTests Rsp

/-- Exercise the public bit API on bit-oriented fixtures. -/
def evaluateBits (variant : Nat) (m : Vector Bit n) : Array UInt8 :=
  let msg := BitVec.ofBitsLE m
  match variant with
    | 224 => ((sha3_224_bits msg).toBytesLE (n := 28)).toArray
    | 256 => ((sha3_256_bits msg).toBytesLE (n := 32)).toArray
    | 384 => ((sha3_384_bits msg).toBytesLE (n := 48)).toArray
    | _ => ((sha3_512_bits msg).toBytesLE (n := 64)).toArray

/-- Exercise the public byte API on byte-oriented fixtures. -/
private def evaluateBytes (variant : Nat) (m : Array UInt8) : Array UInt8 :=
  match variant with
    | 224 => (sha3_224 m.toVector).toArray
    | 256 => (sha3_256 m.toVector).toArray
    | 384 => (sha3_384 m.toVector).toArray
    | _ => (sha3_512 m.toVector).toArray

private def fixtureDir : System.FilePath := "Wychelean/Hashes/SHA3/Fixtures"

private def knownAnswers (dir file : String) (variant count : Nat)
    (cases : List Nat) (byteOriented := true) (full := false) : Suite where
  name := s!"{dir}/{file}"
  tests := do
    let vectors ← RunTests.Parser.parseFile
      (parseKat variant) (fixtureDir / dir / file)
    unless vectors.length == count do
      throw (IO.userError s!"{file}: expected {count} cases, got {vectors.length}")
    let vectors := vectors.toArray
    let cases := if full then List.range count else cases
    cases.mapM fun i => do
      let some v := vectors[i]? | throw (IO.userError s!"{file}: no case {i}")
      let actual ← if byteOriented then do
        unless v.msg.length % 8 == 0 && v.output.length % 8 == 0 do
          throw (IO.userError s!"{file}: byte-oriented case has a partial byte")
        pure (evaluateBytes variant v.msg.bytes)
      else pure (evaluateBits variant v.msg.bits)
      return check s!"{i}, Len={v.msg.length}, Outputlen={v.output.length}"
        (Hex.encode v.output.bytes) (Hex.encode actual)

/-- Explicit zero-based fixture cases; `full` runs every case in each file. -/
def suites (full := false) : List Suite :=
  let byte (file : String) (variant count : Nat) (cases : List Nat) :=
    knownAnswers "sha-3bytetestvectors" file variant count cases (full := full)
  let bit (file : String) (variant count : Nat) (cases : List Nat) :=
    knownAnswers "sha-3bittestvectors" file variant count cases
      (byteOriented := false) (full := full)
  [ byte "SHA3_224ShortMsg.rsp" 224 145 [0, 1, 36, 72, 108, 143, 144],
    byte "SHA3_256ShortMsg.rsp" 256 137 [0, 1, 34, 68, 102, 135, 136],
    byte "SHA3_384ShortMsg.rsp" 384 105 [0, 1, 26, 52, 78, 103, 104],
    byte "SHA3_512ShortMsg.rsp" 512 73 [0, 1, 18, 36, 54, 71, 72],
    bit "SHA3_224ShortMsg.rsp" 224 1153
      [0, 1, 2, 7, 8, 9, 288, 576, 864, 1144, 1148, 1149, 1150, 1151, 1152],
    bit "SHA3_256ShortMsg.rsp" 256 1089
      [0, 1, 2, 7, 8, 9, 272, 544, 816, 1080, 1084, 1085, 1086, 1087, 1088],
    bit "SHA3_384ShortMsg.rsp" 384 833
      [0, 1, 2, 7, 8, 9, 208, 416, 624, 824, 828, 829, 830, 831, 832],
    bit "SHA3_512ShortMsg.rsp" 512 577
      [0, 1, 2, 7, 8, 9, 144, 288, 432, 568, 572, 573, 574, 575, 576],
    byte "SHA3_224LongMsg.rsp" 224 100 [0, 99],
    byte "SHA3_256LongMsg.rsp" 256 100 [0, 99],
    byte "SHA3_384LongMsg.rsp" 384 100 [0, 99],
    byte "SHA3_512LongMsg.rsp" 512 100 [0, 99],
    bit "SHA3_224LongMsg.rsp" 224 100 [0, 99],
    bit "SHA3_256LongMsg.rsp" 256 100 [0, 99],
    bit "SHA3_384LongMsg.rsp" 384 100 [0, 99],
    bit "SHA3_512LongMsg.rsp" 512 100 [0, 99] ]

end Wychelean.Hashes.SHA3.Tests
