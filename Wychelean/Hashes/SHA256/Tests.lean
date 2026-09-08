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
        (sha256 (Array.replicate 1000000 (0x61 : UInt8)).toVector (by simp))
    ]

/-! ## NIST response files -/

private def knownAnswers (file : String) (count : Nat) : Suite where
  name := s!"SHA256 {file}"
  tests := do
    let vectors ← loadRsp file parseKat
    unless vectors.length == count do
      throw (IO.userError s!"{file}: expected {count} vectors, found {vectors.length}")
    vectors.zipIdx.mapM fun (v, i) => do
      if h : 8 * v.msg.size < 2 ^ 64 then
        return check s!"vector {i}, Len = {v.msg.size * 8}"
          v.digest (sha256 v.msg.toVector h)
      else
        throw (IO.userError s!"{file}: vector {i} exceeds the SHA256 length bound")

private def monteCarlo : Suite where
  name := "SHA256 SHA256Monte.rsp"
  tests := do
    let file := "SHA256Monte.rsp"
    let (initial, expected) ← loadRsp file parseMonte
    unless expected.length == 100 do
      throw (IO.userError s!"{file}: expected 100 checkpoints, found {expected.length}")
    let mut seed := initial
    let mut tests := #[]
    for (digest, i) in expected.zipIdx do
      seed := checkpoint seed
      tests := tests.push (check s!"COUNT = {i}" digest seed)
    return tests.toList

/-- All SHA256 suites, including all 100 Monte Carlo checkpoints (100,000 hashes). -/
def suites : List Suite := [basic,
  knownAnswers "SHA256ShortMsg.rsp" 65, knownAnswers "SHA256LongMsg.rsp" 64, monteCarlo]

end Wychelean.Hashes.SHA256.Tests
