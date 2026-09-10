import Wychelean.Hashes.SHA3.Tests.Rsp
import RunTests.Basic

namespace Wychelean.Hashes.SHA3.Tests
open RunTests Rsp

inductive Variant where
  | sha3_224
  | sha3_256
  | sha3_384
  | sha3_512

private def Variant.digestBits : Variant → Nat
  | .sha3_224 => 224
  | .sha3_256 => 256
  | .sha3_384 => 384
  | .sha3_512 => 512

/-- Exercise the public bit API on bit-oriented fixtures. -/
def evaluateBits (variant : Variant) (m : Vector Bit n) : Array UInt8 :=
  let msg := BitVec.ofBitsLE m
  let digest : BitVec variant.digestBits := match variant with
    | .sha3_224 => sha3_224_bits msg
    | .sha3_256 => sha3_256_bits msg
    | .sha3_384 => sha3_384_bits msg
    | .sha3_512 => sha3_512_bits msg
  let bytes : ByteVec (variant.digestBits / 8) :=
    (digest.cast (by cases variant <;> rfl)).toBytesLE
  bytes.toArray

/-- Exercise the public byte API on byte-oriented fixtures. -/
private def evaluateBytes (variant : Variant) (m : Array UInt8) : Array UInt8 :=
  match variant with
    | .sha3_224 => (sha3_224 m.toVector).toArray
    | .sha3_256 => (sha3_256 m.toVector).toArray
    | .sha3_384 => (sha3_384 m.toVector).toArray
    | .sha3_512 => (sha3_512 m.toVector).toArray

private def fixtureDir : System.FilePath := "Wychelean/Hashes/SHA3/Fixtures"

private def knownAnswers (dir file : String) (variant : Variant)
    (byteOriented := true) : Suite where
  name := s!"{dir}/{file}"
  verbose := false
  tests := do
    let vectors ← RunTests.Parser.parseFile
      (parseKat variant.digestBits) (fixtureDir / dir / file)
    vectors.zipIdx.mapM fun (v, i) => do
      let actual ← if byteOriented then do
        unless v.msg.length % 8 == 0 && v.output.length % 8 == 0 do
          throw (IO.userError s!"{file}: byte-oriented case has a partial byte")
        pure (evaluateBytes variant v.msg.bytes)
      else pure (evaluateBits variant v.msg.bits)
      return check s!"{i}, Len={v.msg.length}, Outputlen={v.output.length}"
        (toHex v.output.bytes.toVector) (toHex actual.toVector)

/-- All short-message fixtures; `full` also includes the long-message fixtures. -/
def suites (full := false) : List Suite :=
  let byte (file : String) (variant : Variant) :=
    knownAnswers "sha-3bytetestvectors" file variant
  let bit (file : String) (variant : Variant) :=
    knownAnswers "sha-3bittestvectors" file variant (byteOriented := false)
  let short := [
    byte "SHA3_224ShortMsg.rsp" .sha3_224,
    byte "SHA3_256ShortMsg.rsp" .sha3_256,
    byte "SHA3_384ShortMsg.rsp" .sha3_384,
    byte "SHA3_512ShortMsg.rsp" .sha3_512,
    bit "SHA3_224ShortMsg.rsp" .sha3_224,
    bit "SHA3_256ShortMsg.rsp" .sha3_256,
    bit "SHA3_384ShortMsg.rsp" .sha3_384,
    bit "SHA3_512ShortMsg.rsp" .sha3_512 ]
  let long := [
    byte "SHA3_224LongMsg.rsp" .sha3_224,
    byte "SHA3_256LongMsg.rsp" .sha3_256,
    byte "SHA3_384LongMsg.rsp" .sha3_384,
    byte "SHA3_512LongMsg.rsp" .sha3_512,
    bit "SHA3_224LongMsg.rsp" .sha3_224,
    bit "SHA3_256LongMsg.rsp" .sha3_256,
    bit "SHA3_384LongMsg.rsp" .sha3_384,
    bit "SHA3_512LongMsg.rsp" .sha3_512 ]
  if full then short ++ long else short

end Wychelean.Hashes.SHA3.Tests
