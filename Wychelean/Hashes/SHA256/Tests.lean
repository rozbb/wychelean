import Wychelean.Hashes.SHA256.Rsp
import RunTests.Basic

/-! SHA256 FIPS examples and NIST CAVP suites. -/

namespace Wychelean.Hashes.SHA256.Tests

open RunTests
open Wychelean.Hashes.SHA256.Rsp

/-- SHA256 examples from FIPS 180-2, Appendix B. -/
def basic : Suite where
  name := "SHA256 FIPS examples"
  tests := do
    -- FIPS 180-2, Appendix B.1–B.3: https://csrc.nist.gov/files/pubs/fips/180-2/final/docs/fips180-2.pdf
    let abc ← IO.ofExcept (fromHex
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    let multiBlock ← IO.ofExcept (fromHex
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
    let millionA ← IO.ofExcept (fromHex
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")
    return [
      check "FIPS abc" abc (sha256 "abc".toUTF8.data.toVector (by decide)),
      check "FIPS 56-byte message" multiBlock
        (sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data.toVector (by decide)),
      check "FIPS million-a message" millionA
        (sha256 (Vector.replicate 1000000 (0x61 : UInt8)) (by decide))
    ]

/-! ## NIST response files -/

private def byteDir : String := "shabytetestvectors"
private def bitDir : String := "shabittestvectors"

/-- Evaluate a vector through the byte interface. -/
private def evaluateBytes (file : String) (v : HashVector) : IO Digest := do
  unless v.msg.length % 8 == 0 do
    throw (IO.userError s!"{file}: byte-oriented vector has a partial byte")
  if h : 8 * v.msg.bytes.size < 2 ^ 64 then return sha256 v.msg.bytes.toVector h
  else throw (IO.userError s!"{file}: vector exceeds the SHA256 length bound")

/-- Evaluate a vector through the bit interface. -/
private def evaluateBits (file : String) (v : HashVector) : IO Digest := do
  if h : v.msg.length < 2 ^ 64 then
    return (sha256_bits (BitVec.ofBytesBEPrefix v.msg.length v.msg.bytes.toVector) h).toBytesBE
  else throw (IO.userError s!"{file}: vector exceeds the SHA256 length bound")

private def knownAnswers (dir file : String) (count : Nat) (byteOriented := true) : Suite where
  name := s!"SHA256 {dir}/{file}"
  tests := do
    let vectors ← loadRsp dir file parseKat
    unless vectors.length == count do
      throw (IO.userError s!"{file}: expected {count} vectors, found {vectors.length}")
    vectors.zipIdx.mapM fun (v, i) => do
      let actual ← if byteOriented then evaluateBytes file v else evaluateBits file v
      return check s!"vector {i}, Len = {v.msg.length}" v.digest actual

private def monteCarlo (dir : String) : Suite where
  name := s!"SHA256 {dir}/SHA256Monte.rsp"
  tests := do
    let file := "SHA256Monte.rsp"
    let (initial, expected) ← loadRsp dir file parseMonte
    unless expected.length == 100 do
      throw (IO.userError s!"{file}: expected 100 checkpoints, found {expected.length}")
    let mut seed := initial
    let mut tests := #[]
    for (digest, i) in expected.zipIdx do
      seed := checkpoint seed
      tests := tests.push (check s!"COUNT = {i}" digest seed)
    return tests.toList

/-! ## Response-file validation -/

private def katText (len : Nat) (msg : String) : String :=
  s!"[L = 32]\n\nLen = {len}\nMsg = {msg}\nMD = {"".pushn '0' 64}\n"

private def monteText (counts : List Nat) : String :=
  let seed := s!"Seed = {"".pushn '0' 64}\n\n"
  let record := fun (c : Nat) => s!"COUNT = {c}\nMD = {"".pushn '0' 64}\n\n"
  s!"[L = 32]\n\n{seed}{String.join (counts.map record)}"

private def parserChecks : Suite where
  name := "SHA256 response-file validation"
  tests := pure [
    check "Len = 2, Msg = 40 gives 2 bits" (some 2)
      ((Parser.parse parseKat (katText 2 "40")).toOption.bind (·.head?) |>.map (·.msg.length)),
    check "Len = 2, Msg = 41 is rejected" false (Parser.parse parseKat (katText 2 "41")).toBool,
    check "Len = 9, Msg = 43 is rejected" false (Parser.parse parseKat (katText 9 "43")).toBool,
    check "COUNT in order is accepted" true (Parser.parse parseMonte (monteText [0, 1, 2])).toBool,
    check "COUNT out of order is rejected" false (Parser.parse parseMonte (monteText [0, 2, 1])).toBool
  ]

/-- All SHA256 suites. The byte-oriented Monte Carlo suite (100,000 hashes) always runs;
`full` adds the bit-oriented one, which repeats it from a different seed. -/
def suites (full := false) : List Suite :=
  let default := [basic,
    knownAnswers byteDir "SHA256ShortMsg.rsp" 65,
    knownAnswers byteDir "SHA256LongMsg.rsp" 64,
    knownAnswers bitDir "SHA256ShortMsg.rsp" 513 (byteOriented := false),
    monteCarlo byteDir,
    parserChecks]
  if full then default ++ [monteCarlo bitDir] else default

end Wychelean.Hashes.SHA256.Tests
