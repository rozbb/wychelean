import Wychelean.Utils.Bytes
import Wychelean.Utils.Bitwise
import Wychelean.Utils.Vector
import RunTests.Basic

/-! Utility regression tests. -/

namespace Wychelean.Utils.Tests

open RunTests

private def v6 : Vector Nat 6 := #v[1, 2, 3, 4, 5, 6]

private def chunks {α : Type} {n m : Nat} (v : Vector (Vector α m) n) : List (List α) :=
  v.toList.map (·.toList)

def bitwise : Suite where
  name := "Bitwise utilities"
  tests := pure [
    check "(0 : UInt32).rotr 7" 0 ((0 : UInt32).rotr 7),
    check "(1 : UInt32).rotr 1" 0x80000000 ((1 : UInt32).rotr 1),
    check "(0x80000000 : UInt32).rotr 31" 1 ((0x80000000 : UInt32).rotr 31),
    check "(0x12345678 : UInt32).rotr 4" 0x81234567 ((0x12345678 : UInt32).rotr 4),
    check "(0x12345678 : UInt32).rotr 32" 0x12345678 ((0x12345678 : UInt32).rotr 32),
    check "(0x12345678 : UInt32).rotr 36" 0x81234567 ((0x12345678 : UInt32).rotr 36),
    check "(0 : UInt32).rotl 7" 0 ((0 : UInt32).rotl 7),
    check "(0x80000000 : UInt32).rotl 1" 1 ((0x80000000 : UInt32).rotl 1),
    check "(1 : UInt32).rotl 31" 0x80000000 ((1 : UInt32).rotl 31),
    check "(0x12345678 : UInt32).rotl 4" 0x23456781 ((0x12345678 : UInt32).rotl 4),
    check "(0x12345678 : UInt32).rotl 32" 0x12345678 ((0x12345678 : UInt32).rotl 32),
    check "((0xdeadbeef : UInt32).rotr 13).rotl 13" 0xdeadbeef (((0xdeadbeef : UInt32).rotr 13).rotl 13),
    check "(0 : UInt64).rotr 7" 0 ((0 : UInt64).rotr 7),
    check "(1 : UInt64).rotr 1" 0x8000000000000000 ((1 : UInt64).rotr 1),
    check "(0x8000000000000000 : UInt64).rotr 63" 1 ((0x8000000000000000 : UInt64).rotr 63),
    check "(0x123456789abcdef0 : UInt64).rotr 4" 0x0123456789abcdef ((0x123456789abcdef0 : UInt64).rotr 4),
    check "(0x123456789abcdef0 : UInt64).rotr 64" 0x123456789abcdef0 ((0x123456789abcdef0 : UInt64).rotr 64),
    check "(0x123456789abcdef0 : UInt64).rotr 68" 0x0123456789abcdef ((0x123456789abcdef0 : UInt64).rotr 68),
    check "(0x8000000000000000 : UInt64).rotl 1" 1 ((0x8000000000000000 : UInt64).rotl 1),
    check "(1 : UInt64).rotl 63" 0x8000000000000000 ((1 : UInt64).rotl 63),
    check "(0x123456789abcdef0 : UInt64).rotl 4" 0x23456789abcdef01 ((0x123456789abcdef0 : UInt64).rotl 4),
    check "((0xdeadbeefcafebabe : UInt64).rotr 13).rotl 13" 0xdeadbeefcafebabe
      (((0xdeadbeefcafebabe : UInt64).rotr 13).rotl 13)
  ]

def vector : Suite where
  name := "Vector utilities"
  tests := pure [
    check "chunks (v6.toChunks 2 (by decide))" ([[1, 2], [3, 4], [5, 6]]) (chunks (v6.toChunks 2 (by decide))),
    check "chunks (v6.toChunks 6 (by decide))" ([[1, 2, 3, 4, 5, 6]]) (chunks (v6.toChunks 6 (by decide))),
    check "chunks (v6.toChunks 1 (by decide))" ([[1], [2], [3], [4], [5], [6]]) (chunks (v6.toChunks 1 (by decide))),
    check "chunks ((#v[] : Vector Nat 0).toChunks 4 (by decide))" ([]) (chunks ((#v[] : Vector Nat 0).toChunks 4 (by decide)))
  ]

def bytes : Suite where
  name := "Byte / BitVec encodings"
  tests := pure [
    check "LE byte order" (0x030201 : BitVec 24) (BitVec.ofBytesLE #v[1,2,3]),
    check "BE byte order" (0x010203 : BitVec 24) (BitVec.ofBytesBE #v[1,2,3]),
    check "empty LE" (0 : BitVec 0) (BitVec.ofBytesLE #v[]),
    check "empty BE" (0 : BitVec 0) (BitVec.ofBytesBE #v[]),
    check "LE unpack" (#v[1,2,3] : Vector UInt8 3) (BitVec.toBytesLE (0x030201 : BitVec 24)),
    check "BE unpack" (#v[1,2,3] : Vector UInt8 3) (BitVec.toBytesBE (0x010203 : BitVec 24)),
    check "FIPS byte bit order" [true,false,false,false,false,false,false,true]
      (bytesToBits #v[0x81]).toList,
    check "LE fast path, 1 byte" (0xab : BitVec 8) (BitVec.ofBytesLEFast #v[0xab]),
    check "LE fast path, 3 bytes" (0x030201 : BitVec 24) (BitVec.ofBytesLEFast #v[1,2,3]),
    check "LE fast path, 100 bytes" (BitVec.ofBytesLE (Vector.ofFn fun (i : Fin 100) => i.val.toUInt8))
      (BitVec.ofBytesLEFast (Vector.ofFn fun (i : Fin 100) => i.val.toUInt8)),
    check "BE chunks of 8" [1, 2, 3] ((0x010203 : BitVec 24).toChunksBE 8 (by decide)).toList,
    check "BE chunks of 24" [0x010203] ((0x010203 : BitVec 24).toChunksBE 24 (by decide)).toList,
    check "BE chunks of 12" [0x010, 0x203] ((0x010203 : BitVec 24).toChunksBE 12 (by decide)).toList,
    check "BE chunks of empty" [] ((0 : BitVec 0).toChunksBE 8 (by decide)).toList,
    check "BE prefix, 0 of 0" (0 : BitVec 0) (BitVec.ofBytesBEPrefix 0 #v[]),
    check "BE prefix, 2 of 8" (0b01 : BitVec 2) (BitVec.ofBytesBEPrefix 2 #v[0x40]),
    check "BE prefix, 3 of 8" (0b011 : BitVec 3) (BitVec.ofBytesBEPrefix 3 #v[0x60]),
    check "BE prefix, 8 of 8" (0x81 : BitVec 8) (BitVec.ofBytesBEPrefix 8 #v[0x81]),
    check "BE prefix, 9 of 16" (0b010000110 : BitVec 9) (BitVec.ofBytesBEPrefix 9 #v[0x43, 0x00])
  ]

def suites : List Suite := [bitwise, vector, bytes]

end Wychelean.Utils.Tests
