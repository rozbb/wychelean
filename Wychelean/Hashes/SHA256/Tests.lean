import Wychelean.Hashes.SHA256
import Wychelean.Utils.Hex
import RunTests.Basic
import RunTests.Rsp

/-! SHA256 unit tests and NIST CAVP suites. -/

namespace Wychelean.Hashes.SHA256.Tests

open RunTests

/-- SHA256 on a byte array; test messages must fit the FIPS length bound. -/
private def sha256Bytes (msg : Array UInt8) : Array UInt8 :=
  if h : 8 * msg.size < 2 ^ 64 then (sha256 msg.toVector h).toArray else panic! "message too long"

private def sha256Hex (msg : Array UInt8) : String := Hex.encode (sha256Bytes msg)

private def paddedSize (len : Nat) : Nat := (padded (Vector.replicate len (0 : UInt8))).size

/-- Known answers, padding boundaries, and compression-function helpers. -/
def basic : Suite where
  name := "SHA256 unit tests"
  tests := pure [
    check "empty message"
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
      (sha256Hex #[]),
    check "abc"
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      (sha256Hex "abc".toUTF8.data),
    check "single-byte message"
      "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb"
      (sha256Hex "a".toUTF8.data),
    check "quick brown fox"
      "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"
      (sha256Hex "The quick brown fox jumps over the lazy dog".toUTF8.data),
    check "quick brown fox with trailing period"
      "ef537f25c895bfa782526529a9b63d97aa631564d5d789c2b765448c8635fb6c"
      (sha256Hex "The quick brown fox jumps over the lazy dog.".toUTF8.data),
    check "FIPS 56-byte message"
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
      (sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data),
    check "FIPS 112-byte message"
      "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
      (sha256Hex "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.data),
    check "paddedSize 0" 64 (paddedSize 0),
    check "paddedSize 55" 64 (paddedSize 55),
    check "paddedSize 56" 128 (paddedSize 56),
    check "paddedSize 64" 128 (paddedSize 64),
    check "paddedSize 119" 128 (paddedSize 119),
    check "paddedSize 120" 192 (paddedSize 120),
    check "empty-message padding" (0x80 :: List.replicate 63 0) ((padded #v[]).toList),
    check "empty-message block words"
      ((0x80000000 : UInt32) :: List.replicate 15 0)
      ((parse (padded #v[]) (padded_aligned 0))[0].toList),
    check "Ch 0xffffffff 0x12345678 0xdeadbeef" 0x12345678 (Ch 0xffffffff 0x12345678 0xdeadbeef),
    check "Ch 0 0x12345678 0xdeadbeef" 0xdeadbeef (Ch 0 0x12345678 0xdeadbeef),
    check "Ch 0xff00ff00 0xaaaaaaaa 0x55555555" 0xaa55aa55 (Ch 0xff00ff00 0xaaaaaaaa 0x55555555),
    check "Maj 0 0 0" 0 (Maj 0 0 0),
    check "Maj 0xffffffff 0xffffffff 0xffffffff" 0xffffffff (Maj 0xffffffff 0xffffffff 0xffffffff),
    check "Maj 0xffffffff 0xffffffff 0" 0xffffffff (Maj 0xffffffff 0xffffffff 0),
    check "Maj 0xffffffff 0 0" 0 (Maj 0xffffffff 0 0),
    check "Maj 0xff00ff00 0x00ffff00 0xffff0000" 0xffffff00 (Maj 0xff00ff00 0x00ffff00 0xffff0000),
    check "lowerSigma0 0" 0 (lowerSigma0 0),
    check "lowerSigma1 0" 0 (lowerSigma1 0),
    check "upperSigma0 0" 0 (upperSigma0 0),
    check "upperSigma1 0" 0 (upperSigma1 0),
    check "lowerSigma0 1" 0x02004000 (lowerSigma0 1),
    check "lowerSigma1 1" 0x0000a000 (lowerSigma1 1),
    check "upperSigma0 1" 0x40080400 (upperSigma0 1),
    check "upperSigma1 1" 0x04200080 (upperSigma1 1),
    check "upperSigma0 0xffffffff" 0xffffffff (upperSigma0 0xffffffff),
    check "upperSigma1 0xffffffff" 0xffffffff (upperSigma1 0xffffffff),
    check "lowerSigma0 0xffffffff" 0x1fffffff (lowerSigma0 0xffffffff),
    check "lowerSigma1 0xffffffff" 0x003fffff (lowerSigma1 0xffffffff)
  ]

/-! ## NIST response files -/

/-- Validate the SHA256 section header and collect its fields. -/
private def parseFields (text : String) : Except String (List Rsp.Field) := do
  match ← Rsp.parse text with
  | .header value line :: entries =>
    unless String.ofList (value.toList.filter (fun c => !c.isWhitespace)) == "L=32" do
      throw s!"line {line}: expected [L = 32]"
    let mut fields := #[]
    for entry in entries do
      match entry with
      | .record record => fields := fields ++ record.toArray
      | .header _ line => throw s!"line {line}: unexpected additional SHA256 section"
    if fields.isEmpty then throw "missing SHA256 vectors"
    return fields.toList
  | _ => throw "expected a SHA256 response file starting with [L = 32]"

private def readField (f : Rsp.Field) (key : String) : Except String String := do
  unless f.key == key do throw s!"line {f.line}: expected {key}, found {f.key}"
  match f.value with
  | some value => return value
  | none => throw s!"line {f.line}: {key} requires a value"

private def readNat (f : Rsp.Field) (key : String) : Except String Nat := do
  let value ← readField f key
  match value.toNat? with
  | some n => return n
  | none => throw s!"line {f.line}: {key} must be a natural number"

private def readHex (f : Rsp.Field) (key : String) : Except String (Array UInt8) := do
  let value ← readField f key
  match Hex.decode value with
  | some bytes => return bytes
  | none => throw s!"line {f.line}: malformed hexadecimal {key}"

private def readDigest (f : Rsp.Field) (key : String) : Except String (Array UInt8) := do
  let bytes ← readHex f key
  unless bytes.size == digestSize do
    throw s!"line {f.line}: {key} must contain {digestSize} bytes"
  return bytes

private structure HashVector where
  msg : Array UInt8
  digest : Array UInt8
  deriving BEq, Repr

private def parseVectors : List Rsp.Field → Except String (List HashVector)
  | [] => return []
  | len :: msg :: md :: rest => do
    let bits ← readNat len "Len"
    unless bits % 8 == 0 do throw s!"line {len.line}: only byte-oriented messages are supported"
    let mut bytes ← readHex msg "Msg"
    -- NIST represents the empty message as Len = 0, Msg = 00.
    if bits == 0 && bytes == #[0] then bytes := #[]
    unless bytes.size * 8 == bits do
      throw s!"line {msg.line}: Msg has {bytes.size * 8} bits, but Len is {bits}"
    unless bits < 2 ^ 64 do throw s!"line {len.line}: message exceeds the SHA256 length bound"
    let digest ← readDigest md "MD"
    return ⟨bytes, digest⟩ :: (← parseVectors rest)
  | f :: _ => throw s!"line {f.line}: incomplete Len/Msg/MD record"

private def parseKat (text : String) : Except String (List HashVector) := do
  parseVectors (← parseFields text)

private def parseCheckpoints (next : Nat) : List Rsp.Field → Except String (List (Array UInt8))
  | [] => return []
  | count :: md :: rest => do
    let index ← readNat count "COUNT"
    unless index == next do throw s!"line {count.line}: expected COUNT = {next}, found {index}"
    let digest ← readDigest md "MD"
    return digest :: (← parseCheckpoints (next + 1) rest)
  | f :: _ => throw s!"line {f.line}: incomplete COUNT/MD record"

private def parseMonte (text : String) : Except String (Array UInt8 × List (Array UInt8)) := do
  match ← parseFields text with
  | seed :: rest =>
    let seed ← readDigest seed "Seed"
    let checkpoints ← parseCheckpoints 0 rest
    if checkpoints.isEmpty then throw "missing Monte Carlo checkpoints"
    return (seed, checkpoints)
  | [] => throw "missing Monte Carlo seed"

/-- One SHAVS checkpoint: 1000 hashes of the previous three digests, initially all `seed`. -/
private def checkpoint (seed : Array UInt8) : Array UInt8 := Id.run do
  let mut m0 := seed
  let mut m1 := seed
  let mut m2 := seed
  for _ in [0:1000] do
    let md := sha256Bytes (m0 ++ m1 ++ m2)
    m0 := m1
    m1 := m2
    m2 := md
  return m2

private def fixtureDir : System.FilePath := "Wychelean/Hashes/SHA256/Vectors"

private def loadRsp {α : Type} (name : String) (parse : String → Except String α) : IO α := do
  let path := fixtureDir / name
  let text ← IO.FS.readFile path
  match parse text with
  | .ok value => return value
  | .error error => throw (IO.userError s!"{path}: {error}")

private def knownAnswers (file : String) (count : Nat) : Suite where
  name := s!"SHA256 {file}"
  tests := do
    let vectors ← loadRsp file parseKat
    unless vectors.length == count do
      throw (IO.userError s!"{file}: expected {count} vectors, found {vectors.length}")
    return vectors.zipIdx.map fun (v, i) =>
      check s!"vector {i}, Len = {v.msg.size * 8}" (Hex.encode v.digest) (sha256Hex v.msg)

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
      tests := tests.push (check s!"COUNT = {i}" (Hex.encode digest) (Hex.encode seed))
    return tests.toList

/-! ## Parser regression tests -/

private def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

private def emptyDigest : String :=
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

private def katText (len msg : String) (digest : String := emptyDigest) : String :=
  s!"[L = 32]\nLen = {len}\nMsg = {msg}\nMD = {digest}\n"

private def monteText (count : String := "0") : String :=
  s!"[L = 32]\nSeed = {emptyDigest}\nCOUNT = {count}\nMD = {emptyDigest}\n"

private def parserTests : Suite where
  name := "SHA256 response-file parser"
  tests := pure [
    check "Len = 0, Msg = 00 is the empty message" (some [0])
      ((parseKat (katText "0" "00")).toOption.map (·.map (·.msg.size))),
    check "empty Msg is also accepted for Len = 0" true (succeeds (parseKat (katText "0" ""))),
    check "comments, CRLF, whitespace, uppercase hex, and no final newline" true
      (succeeds (parseKat s!"# comment\r\n\r\n [ L = 32 ]\r\n Len = 8\r\n Msg = AB\r\n MD = {emptyDigest}")),
    check "reject empty file" false (succeeds (parseKat "")),
    check "reject header without vectors" false (succeeds (parseKat "[L = 32]\n")),
    check "reject wrong digest size header" false
      (succeeds (parseKat ((katText "0" "00").replace "[L = 32]" "[L = 64]"))),
    check "reject missing header" false
      (succeeds (parseKat ((katText "0" "00").replace "[L = 32]\n" ""))),
    check "reject nonnumeric Len" false (succeeds (parseKat (katText "x" "00"))),
    check "reject bit-oriented message" false (succeeds (parseKat (katText "1" "00"))),
    check "reject mismatched message length" false (succeeds (parseKat (katText "16" "ab"))),
    check "reject nonzero empty-message placeholder" false (succeeds (parseKat (katText "0" "ab"))),
    check "reject malformed message hex" false (succeeds (parseKat (katText "8" "zz"))),
    check "reject odd-length message hex" false (succeeds (parseKat (katText "8" "a"))),
    check "reject short digest" false (succeeds (parseKat (katText "8" "ab" "00"))),
    check "reject long digest" false (succeeds (parseKat (katText "8" "ab" (emptyDigest ++ "00")))),
    check "reject malformed digest" false (succeeds (parseKat (katText "8" "ab" "zz"))),
    check "reject incomplete record" false (succeeds (parseKat "[L = 32]\nLen = 8\nMsg = ab\n")),
    check "reject duplicate field" false
      (succeeds (parseKat ((katText "0" "00").replace "Msg = 00" "Msg = 00\nMsg = 00"))),
    check "reject trailing garbage" false (succeeds (parseKat (katText "0" "00" ++ "garbage"))),
    check "accept consecutive records without blank separators" (some 2)
      ((parseKat (katText "0" "00" ++ s!"Len = 8\nMsg = ab\nMD = {emptyDigest}")).toOption.map List.length),
    check "accept Monte Carlo seed and checkpoint" true (succeeds (parseMonte monteText)),
    check "reject nonsequential COUNT" false (succeeds (parseMonte (monteText "1"))),
    check "reject duplicate COUNT" false
      (succeeds (parseMonte (monteText ++ s!"COUNT = 0\nMD = {emptyDigest}\n"))),
    check "reject malformed seed" false
      (succeeds (parseMonte (monteText.replace s!"Seed = {emptyDigest}" "Seed = zz"))),
    check "reject incomplete Monte Carlo record" false
      (succeeds (parseMonte (monteText ++ "COUNT = 1\n")))
  ]

/-- All SHA256 suites, including all 100 Monte Carlo checkpoints (100,000 hashes). -/
def suites : List Suite := [basic, parserTests,
  knownAnswers "SHA256ShortMsg.rsp" 65, knownAnswers "SHA256LongMsg.rsp" 64, monteCarlo]

end Wychelean.Hashes.SHA256.Tests
