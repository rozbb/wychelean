import Wychelean.Utils.Bitwise
import Tests.Harness

namespace Tests.Utils.Bitwise

open Wychelean

def tests : List Test := [
  -- rotr
  expectEq "rotr 0" (rotr 7 0) 0,
  expectEq "rotr 1 by 1 wraps to the top bit" (rotr 1 1) 0x80000000,
  expectEq "rotr top bit by 31" (rotr 31 0x80000000) 1,
  expectEq "rotr by a nibble" (rotr 4 0x12345678) 0x81234567,
  expectEq "rotr by 32 is the identity" (rotr 32 0x12345678) 0x12345678,
  expectEq "rotr by 36 equals by 4" (rotr 36 0x12345678) 0x81234567,
  -- rotl
  expectEq "rotl 0" (rotl 7 0) 0,
  expectEq "rotl top bit by 1 wraps to the bottom bit" (rotl 1 0x80000000) 1,
  expectEq "rotl 1 by 31" (rotl 31 1) 0x80000000,
  expectEq "rotl by a nibble" (rotl 4 0x12345678) 0x23456781,
  expectEq "rotl by 32 is the identity" (rotl 32 0x12345678) 0x12345678,
  expectEq "rotl undoes rotr" (rotl 13 (rotr 13 0xdeadbeef)) 0xdeadbeef,
  -- ofBytesBE packs four bytes in big-endian order.
  expectEq "ofBytesBE 12 34 56 78" (UInt32.ofBytesBE #v[0x12, 0x34, 0x56, 0x78]) 0x12345678,
  expectEq "ofBytesBE zeros" (UInt32.ofBytesBE #v[0, 0, 0, 0]) 0,
  expectEq "ofBytesBE ones" (UInt32.ofBytesBE #v[0xff, 0xff, 0xff, 0xff]) 0xffffffff,
  expectEq "ofBytesBE de ad be ef" (UInt32.ofBytesBE #v[0xde, 0xad, 0xbe, 0xef]) 0xdeadbeef,
  -- toBytesBE is the inverse.
  expectEq "toBytesBE 12345678" (0x12345678 : UInt32).toBytesBE.toList [0x12, 0x34, 0x56, 0x78],
  expectEq "toBytesBE deadbeef" (0xdeadbeef : UInt32).toBytesBE.toList [0xde, 0xad, 0xbe, 0xef],
  expectEq "UInt64.toBytesBE"
    (0x0102030405060708 : UInt64).toBytesBE.toList [1, 2, 3, 4, 5, 6, 7, 8],
  expectEq "UInt64.toBytesBE small" (0x1c8 : UInt64).toBytesBE.toList [0, 0, 0, 0, 0, 0, 1, 0xc8]
]

end Tests.Utils.Bitwise
