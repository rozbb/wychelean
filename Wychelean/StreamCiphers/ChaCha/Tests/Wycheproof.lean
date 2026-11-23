module

public import Wychelean.StreamCiphers.ChaCha.Basic
public import RunTests.Basic
public import RunTests.Parser.Wycheproof

/-!
# ChaCha20 Wycheproof known-answer tests

Project Wycheproof's ChaCha20 counter-boundary suite. Each case gives a key, a nonce, an initial
block counter and a message, and either the ciphertext or the verdict that the message must be
rejected because encrypting it would run the block counter past its last value.

`chacha20` has no way to reject at run time: instead it requires a proof that the counter does not
wrap (RFC 8439 §2.3 limits a (key, nonce) pair to `2 ^ 32` blocks). So a `valid` case must satisfy
that precondition and produce the given ciphertext, and an `invalid` case must violate it. The file
has no `acceptable` cases; if a later revision adds one, it fails rather than being skipped.

Only the `ChaCha20-IETF` group is checked. The `XChaCha20` group needs HChaCha20 and a 64-bit block
counter, which are not specified here; its cases are left out explicitly by name, and a group of any
other algorithm fails the suite.
-/

namespace Wychelean.StreamCiphers.ChaCha.Tests

open RunTests
open RunTests.Parser.Wycheproof

private def vectorFile : System.FilePath :=
  "Wychelean/StreamCiphers/ChaCha/TestVectors/wycheproof_chacha20_counter_test.json"

/-- The fields of a `StreamCipherTest` case. The counter is kept as bytes, since its width depends
on the group. -/
private structure StreamCase where
  key : Array UInt8
  iv : Array UInt8
  initialCounter : Array UInt8
  msg : Array UInt8
  /-- Absent from `invalid` cases. -/
  ct : Option (Array UInt8)

private def StreamCase.ofJson (j : Lean.Json) : Except String StreamCase := do
  return { key := ← getHexBytes j "key",
           iv := ← getHexBytes j "iv",
           initialCounter := ← getHexBytes j "initialCounter",
           msg := ← getHexBytes j "msg",
           ct := ← getHexBytes? j "ct" }

/-- Check one ChaCha20-IETF case. -/
private def checkCase (c : Case StreamCase) : Except String Test := do
  let key ← RunTests.Parser.toFixed keyBytes c.data.key
  let nonce ← RunTests.Parser.toFixed nonceBytes c.data.iv
  let counter := (wordsOfBytesLE (n := 1)
    (← RunTests.Parser.toFixed 4 c.data.initialCounter))[0]
  let msg := c.data.msg.toVector
  let fits := counter.toNat + numBlocks msg.size ≤ 2 ^ 32
  return match c.result with
    | .valid =>
      match c.data.ct with
      | none => { name := c.name, failure := some "valid, but no ciphertext given" }
      | some ct =>
        if h : fits then check c.name (toHex ct.toVector) (toHex (chacha20 key counter nonce msg h))
        else { name := c.name, failure := some "valid, but the block counter would wrap" }
    | .invalid =>
      { name := c.name,
        failure := if fits then some "invalid, but the block counter does not wrap" else none }
    | .acceptable =>
      { name := c.name, failure := some "acceptable cases are not expected in this file" }

/-- The ChaCha20-IETF Wycheproof vectors, checked against `chacha20`. -/
public def wycheproof : Suite where
  name := "ChaCha20 (Wycheproof counter-boundary tests)"
  tests := do
    let file ← parseFile StreamCase.ofJson vectorFile
    let mut tests := #[]
    for group in file.groups do
      let alg ← IO.ofExcept (getField String group.header "algorithm")
      unless group.type == "StreamCipherTest" do
        throw (IO.userError s!"{vectorFile}: unexpected group type {group.type}")
      match alg with
      | "ChaCha20-IETF" =>
        tests := tests ++ (← IO.ofExcept (group.cases.mapM checkCase))
      | "XChaCha20" => pure ()
      | other => throw (IO.userError s!"{vectorFile}: unexpected algorithm {other}")
    return tests.toList

end Wychelean.StreamCiphers.ChaCha.Tests
