import Wychelean.Hashes.SHA256.Rsp
import Wychelean.Utils.Hex
import RunTests.Basic

/-! SHA256 FIPS examples and NIST CAVP suites. -/

namespace Wychelean.Hashes.SHA256.Tests

open RunTests
open Wychelean.Hashes.SHA256.Rsp

private def sha256Hex (msg : Array UInt8) (h : 8 * msg.size < 2 ^ 64) : String :=
  Hex.encode (sha256 msg.toVector h).toArray

/-- SHA256 examples from FIPS 180-2, Appendix B. -/
def basic : Suite where
  name := "SHA256 FIPS examples"
  tests := pure [
    -- FIPS 180-2, Appendix B.1–B.3: https://csrc.nist.gov/files/pubs/fips/180-2/final/docs/fips180-2.pdf
    check "FIPS abc"
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      (sha256Hex "abc".toUTF8.data (by decide)),
    check "FIPS 56-byte message"
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
      (sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data (by decide)),
    check "FIPS million-a message"
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
      (sha256Hex (Array.replicate 1000000 (0x61 : UInt8)) (by simp))
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
          (Hex.encode v.digest.toArray) (sha256Hex v.msg h)
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
      tests := tests.push (check s!"COUNT = {i}" (Hex.encode digest.toArray) (Hex.encode seed.toArray))
    return tests.toList

/-- All SHA256 suites, including all 100 Monte Carlo checkpoints (100,000 hashes). -/
def suites : List Suite := [basic,
  knownAnswers "SHA256ShortMsg.rsp" 65, knownAnswers "SHA256LongMsg.rsp" 64, monteCarlo]

end Wychelean.Hashes.SHA256.Tests
