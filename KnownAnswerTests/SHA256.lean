import Wychelean.Hashes.SHA256
import KnownAnswerTests.Harness

namespace KnownAnswerTests.SHA256

open Wychelean.Hashes.SHA256

/-- UTF-8 bytes of a string. -/
def ascii (s : String) : Array UInt8 := s.toUTF8.data

/-- Lowercase hex encoding of a 32-bit word, zero-padded to 8 digits. -/
def hexWord (w : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 w.toNat)
  "".pushn '0' (8 - s.length) ++ s

/-- Lowercase hex encoding of a digest. -/
def hexDigest (d : Vector UInt32 8) : String := String.join (d.toList.map hexWord)

def sha256Hex {n : Nat} (msg : Vector UInt8 n) : String := hexDigest (sha256 msg)

def digestTests : List Test := [
  expectEq "empty" (sha256Hex #v[])
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  expectEq "\"abc\"" (sha256Hex (ascii "abc").toVector)
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
  expectEq "\"a\"" (sha256Hex (ascii "a").toVector)
    "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb",
  expectEq "quick brown fox"
    (sha256Hex (ascii "The quick brown fox jumps over the lazy dog").toVector)
    "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592",
  -- A single trailing byte change must produce a completely different digest.
  expectEq "quick brown fox, trailing period"
    (sha256Hex (ascii "The quick brown fox jumps over the lazy dog.").toVector)
    "ef537f25c895bfa782526529a9b63d97aa631564d5d789c2b765448c8635fb6c",
  -- FIPS 180-4 two-block test: 56-byte message forces a second padding block.
  expectEq "FIPS 180-4 two-block (56 bytes)"
    (sha256Hex (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq").toVector)
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
  -- FIPS 180-4 multi-block test: 112-byte message spans three padded blocks.
  expectEq "FIPS 180-4 multi-block (112 bytes)"
    (sha256Hex (ascii ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")).toVector)
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
]

/-- Padding boundary: 55 bytes is the last input that still fits in one 512-bit
block; 56 bytes is the first input that requires a second block. -/
def padTests : List Test := [
  expectEq "pad 0 bytes -> 1 block" (pad #v[]).size 1,
  expectEq "pad 55 bytes -> 1 block" (pad (Vector.replicate 55 0)).size 1,
  expectEq "pad 56 bytes -> 2 blocks" (pad (Vector.replicate 56 0)).size 2,
  expectEq "pad 64 bytes -> 2 blocks" (pad (Vector.replicate 64 0)).size 2,
  expectEq "pad 119 bytes -> 2 blocks" (pad (Vector.replicate 119 0)).size 2,
  expectEq "pad 120 bytes -> 3 blocks" (pad (Vector.replicate 120 0)).size 3,
  -- The padding block for the empty message is 0x80 followed by 63 zero bytes,
  -- which packs into a block starting with 0x80000000 and ending with 0.
  expectEq "pad empty message block" (pad #v[])[0].toList
    [0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

def helperTests : List Test := [
  -- Ch(e, f, g) selects f where e = 1 and g where e = 0.
  expectEq "Ch all ones" (Ch 0xffffffff 0x12345678 0xdeadbeef) 0x12345678,
  expectEq "Ch all zeros" (Ch 0 0x12345678 0xdeadbeef) 0xdeadbeef,
  expectEq "Ch mixed" (Ch 0xff00ff00 0xaaaaaaaa 0x55555555) 0xaa55aa55,
  -- Maj(a, b, c) is the bitwise majority function.
  expectEq "Maj 0 0 0" (Maj 0 0 0) 0,
  expectEq "Maj 1 1 1" (Maj 0xffffffff 0xffffffff 0xffffffff) 0xffffffff,
  expectEq "Maj 1 1 0" (Maj 0xffffffff 0xffffffff 0) 0xffffffff,
  expectEq "Maj 1 0 0" (Maj 0xffffffff 0 0) 0,
  expectEq "Maj mixed" (Maj 0xff00ff00 0x00ffff00 0xffff0000) 0xffffff00,
  -- The sigma functions on zero are zero.
  expectEq "lowerSigma0 0" (lowerSigma0 0) 0,
  expectEq "lowerSigma1 0" (lowerSigma1 0) 0,
  expectEq "upperSigma0 0" (upperSigma0 0) 0,
  expectEq "upperSigma1 0" (upperSigma1 0) 0,
  -- On a single low bit they expose the rotation amounts.
  expectEq "lowerSigma0 1 = 1<<25 ^ 1<<14" (lowerSigma0 1) 0x02004000,
  expectEq "lowerSigma1 1 = 1<<15 ^ 1<<13" (lowerSigma1 1) 0x0000a000,
  expectEq "upperSigma0 1 = 1<<30 ^ 1<<19 ^ 1<<10" (upperSigma0 1) 0x40080400,
  expectEq "upperSigma1 1 = 1<<26 ^ 1<<21 ^ 1<<7" (upperSigma1 1) 0x04200080,
  -- Rotations are bijections of 32-bit words, so each capital sigma fixes 0xffffffff.
  expectEq "upperSigma0 all ones" (upperSigma0 0xffffffff) 0xffffffff,
  expectEq "upperSigma1 all ones" (upperSigma1 0xffffffff) 0xffffffff,
  -- The lowercase sigmas include a shift, so they drop the top 3 / 10 bits.
  expectEq "lowerSigma0 all ones" (lowerSigma0 0xffffffff) 0x1fffffff,
  expectEq "lowerSigma1 all ones" (lowerSigma1 0xffffffff) 0x003fffff,
  -- bytesToWord32BE packs four bytes in big-endian order.
  expectEq "bytesToWord32BE 12 34 56 78" (bytesToWord32BE 0x12 0x34 0x56 0x78) 0x12345678,
  expectEq "bytesToWord32BE zeros" (bytesToWord32BE 0 0 0 0) 0,
  expectEq "bytesToWord32BE ones" (bytesToWord32BE 0xff 0xff 0xff 0xff) 0xffffffff,
  expectEq "bytesToWord32BE de ad be ef" (bytesToWord32BE 0xde 0xad 0xbe 0xef) 0xdeadbeef
]

def tests : List Test := digestTests ++ padTests ++ helperTests

end KnownAnswerTests.SHA256
