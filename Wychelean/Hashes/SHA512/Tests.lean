import Wychelean.Hashes.SHA512.Rsp
import RunTests.Basic

/-! SHA512 FIPS examples and NIST CAVP suites. -/

namespace Wychelean.Hashes.SHA512.Tests

open RunTests
open Wychelean.Hashes.SHA512.Rsp

/-- SHA512 examples from FIPS 180-2, Appendix C. -/
def basic : Suite where
  name := "SHA512 FIPS examples"
  tests := do
    -- FIPS 180-2, Appendix C.1–C.3: https://csrc.nist.gov/files/pubs/fips/180-2/final/docs/fips180-2.pdf
    let abc ← IO.ofExcept (fromHex
      "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
    let multiBlock ← IO.ofExcept (fromHex
      "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
    let millionA ← IO.ofExcept (fromHex
      "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b")
    return [
      check "FIPS abc" abc (sha512 "abc".toUTF8.data.toVector (by decide)),
      check "FIPS 112-byte message" multiBlock
        (sha512 "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.data.toVector (by decide)),
      check "FIPS million-a message" millionA
        (sha512 (Vector.replicate 1000000 (0x61 : UInt8)) (by decide))
    ]

/-! ## NIST response files -/

private def byteDir : String := "shabytetestvectors"
private def bitDir : String := "shabittestvectors"

/-- Evaluate a vector through the byte interface. -/
private def evaluateBytes (file : String) (v : HashVector) : IO Digest := do
  unless v.msg.length % 8 == 0 do
    throw (IO.userError s!"{file}: byte-oriented vector has a partial byte")
  if h : 8 * v.msg.bytes.size < 2 ^ 128 then return sha512 v.msg.bytes.toVector h
  else throw (IO.userError s!"{file}: vector exceeds the SHA512 length bound")

/-- Evaluate a vector through the bit interface. -/
private def evaluateBits (file : String) (v : HashVector) : IO Digest := do
  if h : v.msg.length < 2 ^ 128 then
    return (sha512_bits (BitVec.ofBytesBEPrefix v.msg.length v.msg.bytes.toVector) h).toBytesBE
  else throw (IO.userError s!"{file}: vector exceeds the SHA512 length bound")

private def knownAnswers (dir file : String) (count : Nat) (byteOriented := true) : Suite where
  name := s!"SHA512 {dir}/{file}"
  verbose := false
  tests := do
    let vectors ← loadRsp dir file parseKat
    unless vectors.length == count do
      throw (IO.userError s!"{file}: expected {count} vectors, found {vectors.length}")
    vectors.zipIdx.mapM fun (v, i) => do
      let actual ← if byteOriented then evaluateBytes file v else evaluateBits file v
      return check s!"vector {i}, Len = {v.msg.length}" v.digest actual

private def monteCarlo (dir : String) : Suite where
  name := s!"SHA512 {dir}/SHA512Monte.rsp"
  verbose := false
  tests := do
    let file := "SHA512Monte.rsp"
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
  s!"[L = 64]\n\nLen = {len}\nMsg = {msg}\nMD = {"".pushn '0' 128}\n"

private def monteText (counts : List Nat) : String :=
  let seed := s!"Seed = {"".pushn '0' 128}\n\n"
  let record := fun (c : Nat) => s!"COUNT = {c}\nMD = {"".pushn '0' 128}\n\n"
  s!"[L = 64]\n\n{seed}{String.join (counts.map record)}"

private def parserChecks : Suite where
  name := "SHA512 response-file validation"
  tests := pure [
    check "Len = 2, Msg = 40 gives 2 bits" (some 2)
      ((Parser.parse parseKat (katText 2 "40")).toOption.bind (·.head?) |>.map (·.msg.length)),
    check "Len = 2, Msg = 41 is rejected" false (Parser.parse parseKat (katText 2 "41")).toBool,
    check "Len = 9, Msg = 43 is rejected" false (Parser.parse parseKat (katText 9 "43")).toBool,
    check "COUNT in order is accepted" true (Parser.parse parseMonte (monteText [0, 1, 2])).toBool,
    check "COUNT out of order is rejected" false (Parser.parse parseMonte (monteText [0, 2, 1])).toBool
  ]

/-- All SHA512 suites. The byte-oriented Monte Carlo suite (100,000 hashes) always runs;
`full` adds the bit-oriented one, which repeats it from a different seed. -/
def suites (full := false) : List Suite :=
  let default := [basic,
    knownAnswers byteDir "SHA512ShortMsg.rsp" 129,
    knownAnswers byteDir "SHA512LongMsg.rsp" 128,
    knownAnswers bitDir "SHA512ShortMsg.rsp" 1025 (byteOriented := false),
    monteCarlo byteDir,
    parserChecks]
  if full then default ++ [monteCarlo bitDir] else default

end Wychelean.Hashes.SHA512.Tests
