import Wychelean.Hashes.SHA256
import Wychelean.Utils.Hex

namespace Tests.Hashes.SHA256

open Wychelean
open Wychelean.Hashes.SHA256

/-- `sha256` on a byte array. Panics on messages of `2 ^ 64` bits or more. -/
def sha256Bytes (msg : Array UInt8) : Array UInt8 :=
  if h : 8 * msg.size < 2 ^ 64 then (sha256 msg.toVector h).toArray else panic! "message too long"

def sha256Hex (msg : Array UInt8) : String := Hex.encode (sha256Bytes msg)

example : sha256Hex #[] =
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by native_decide
example : sha256Hex "abc".toUTF8.data =
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by native_decide
example : sha256Hex "a".toUTF8.data =
    "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb" := by native_decide
example : sha256Hex "The quick brown fox jumps over the lazy dog".toUTF8.data =
    "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592" := by native_decide
-- A single trailing byte change must produce a completely different digest.
example : sha256Hex "The quick brown fox jumps over the lazy dog.".toUTF8.data =
    "ef537f25c895bfa782526529a9b63d97aa631564d5d789c2b765448c8635fb6c" := by native_decide
-- FIPS 180-4 two-block test: 56-byte message forces a second padding block.
example : sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data =
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by native_decide
-- FIPS 180-4 multi-block test: 112-byte message spans three padded blocks.
example : sha256Hex "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.data =
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" := by native_decide

/-!
Padding boundary:
55 bytes is the last input that still fits in one block,
56 bytes is the first input that requires a second block.
-/
private def paddedSize (len : Nat) : Nat := (padded (Vector.replicate len (0 : UInt8))).size
example : paddedSize 0 = 64 := by native_decide
example : paddedSize 55 = 64 := by native_decide
example : paddedSize 56 = 128 := by native_decide
example : paddedSize 64 = 128 := by native_decide
example : paddedSize 119 = 128 := by native_decide
example : paddedSize 120 = 192 := by native_decide

-- The padded empty message is 0x80 followed by 63 `0x00` bytes,
-- which parses into a block starting with 0x80000000 and ending with 0.
example : (padded #v[]).toList = 0x80 :: List.replicate 63 0 := by native_decide
example : (parse (padded #v[]) (padded_aligned 0))[0].toList = 0x80000000 :: List.replicate 15 0 := by
  native_decide

-- Ch(e, f, g) selects f where e = 1 and g where e = 0.
example : Ch 0xffffffff 0x12345678 0xdeadbeef = 0x12345678 := by native_decide
example : Ch 0 0x12345678 0xdeadbeef = 0xdeadbeef := by native_decide
example : Ch 0xff00ff00 0xaaaaaaaa 0x55555555 = 0xaa55aa55 := by native_decide

-- Maj(a, b, c) is the bitwise majority function.
example : Maj 0 0 0 = 0 := by native_decide
example : Maj 0xffffffff 0xffffffff 0xffffffff = 0xffffffff := by native_decide
example : Maj 0xffffffff 0xffffffff 0 = 0xffffffff := by native_decide
example : Maj 0xffffffff 0 0 = 0 := by native_decide
example : Maj 0xff00ff00 0x00ffff00 0xffff0000 = 0xffffff00 := by native_decide

-- The sigma functions on zero are zero.
example : lowerSigma0 0 = 0 := by native_decide
example : lowerSigma1 0 = 0 := by native_decide
example : upperSigma0 0 = 0 := by native_decide
example : upperSigma1 0 = 0 := by native_decide
-- On a single low bit they expose the rotation amounts.
example : lowerSigma0 1 = 0x02004000 := by native_decide
example : lowerSigma1 1 = 0x0000a000 := by native_decide
example : upperSigma0 1 = 0x40080400 := by native_decide
example : upperSigma1 1 = 0x04200080 := by native_decide
-- Rotations are bijections of 32-bit words, so each capital sigma fixes 0xffffffff.
example : upperSigma0 0xffffffff = 0xffffffff := by native_decide
example : upperSigma1 0xffffffff = 0xffffffff := by native_decide
-- The lowercase sigmas include a shift, so they drop the top 3 / 10 bits.
example : lowerSigma0 0xffffffff = 0x1fffffff := by native_decide
example : lowerSigma1 0xffffffff = 0x003fffff := by native_decide

end Tests.Hashes.SHA256
