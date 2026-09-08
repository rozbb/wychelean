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
    check "rotr 7 0" 0 (rotr 7 0),
    check "rotr 1 1" 0x80000000 (rotr 1 1),
    check "rotr 31 0x80000000" 1 (rotr 31 0x80000000),
    check "rotr 4 0x12345678" 0x81234567 (rotr 4 0x12345678),
    check "rotr 32 0x12345678" 0x12345678 (rotr 32 0x12345678),
    check "rotr 36 0x12345678" 0x81234567 (rotr 36 0x12345678),
    check "rotl 7 0" 0 (rotl 7 0),
    check "rotl 1 0x80000000" 1 (rotl 1 0x80000000),
    check "rotl 31 1" 0x80000000 (rotl 31 1),
    check "rotl 4 0x12345678" 0x23456781 (rotl 4 0x12345678),
    check "rotl 32 0x12345678" 0x12345678 (rotl 32 0x12345678),
    check "rotl 13 (rotr 13 0xdeadbeef)" 0xdeadbeef (rotl 13 (rotr 13 0xdeadbeef)),
    check "UInt32.fromBytesBE #v[0x12, 0x34, 0x56, 0x78]" 0x12345678 (UInt32.fromBytesBE #v[0x12, 0x34, 0x56, 0x78]),
    check "UInt32.fromBytesBE #v[0, 0, 0, 0]" 0 (UInt32.fromBytesBE #v[0, 0, 0, 0]),
    check "UInt32.fromBytesBE #v[0xff, 0xff, 0xff, 0xff]" 0xffffffff (UInt32.fromBytesBE #v[0xff, 0xff, 0xff, 0xff]),
    check "UInt32.fromBytesBE #v[0xde, 0xad, 0xbe, 0xef]" 0xdeadbeef (UInt32.fromBytesBE #v[0xde, 0xad, 0xbe, 0xef]),
    check "(0x12345678 : UInt32).toBytesBE" (#v[0x12, 0x34, 0x56, 0x78]) ((0x12345678 : UInt32).toBytesBE),
    check "(0xdeadbeef : UInt32).toBytesBE" (#v[0xde, 0xad, 0xbe, 0xef]) ((0xdeadbeef : UInt32).toBytesBE),
    check "(0x0102030405060708 : UInt64).toBytesBE" (#v[1, 2, 3, 4, 5, 6, 7, 8]) ((0x0102030405060708 : UInt64).toBytesBE),
    check "(0x1c8 : UInt64).toBytesBE" (#v[0, 0, 0, 0, 0, 0, 1, 0xc8]) ((0x1c8 : UInt64).toBytesBE)
  ]

def vector : Suite where
  name := "Vector utilities"
  tests := pure [
    check "chunks (v6.toChunks 2 (by decide))" ([[1, 2], [3, 4], [5, 6]]) (chunks (v6.toChunks 2 (by decide))),
    check "chunks (v6.toChunks 6 (by decide))" ([[1, 2, 3, 4, 5, 6]]) (chunks (v6.toChunks 6 (by decide))),
    check "chunks (v6.toChunks 1 (by decide))" ([[1], [2], [3], [4], [5], [6]]) (chunks (v6.toChunks 1 (by decide))),
    check "chunks ((#v[] : Vector Nat 0).toChunks 4 (by decide))" ([]) (chunks ((#v[] : Vector Nat 0).toChunks 4 (by decide)))
  ]

def suites : List Suite := [bitwise, vector]

end Wychelean.Utils.Tests
