import Wychelean.Utils.Bitwise
import Tests.Harness

namespace Tests.Utils.Bitwise

def tests : List Test := [
  -- rotateRight
  expectEq "rotateRight 0" ((0 : UInt32).rotateRight 7) 0,
  expectEq "rotateRight 1 by 1 wraps to the top bit" ((1 : UInt32).rotateRight 1) 0x80000000,
  expectEq "rotateRight top bit by 31" ((0x80000000 : UInt32).rotateRight 31) 1,
  expectEq "rotateRight by a nibble" ((0x12345678 : UInt32).rotateRight 4) 0x81234567,
  expectEq "rotateRight by 32 is the identity" ((0x12345678 : UInt32).rotateRight 32) 0x12345678,
  expectEq "rotateRight by 36 equals by 4" ((0x12345678 : UInt32).rotateRight 36) 0x81234567,
  -- ofBytesBE packs four bytes in big-endian order.
  expectEq "ofBytesBE 12 34 56 78" (UInt32.ofBytesBE 0x12 0x34 0x56 0x78) 0x12345678,
  expectEq "ofBytesBE zeros" (UInt32.ofBytesBE 0 0 0 0) 0,
  expectEq "ofBytesBE ones" (UInt32.ofBytesBE 0xff 0xff 0xff 0xff) 0xffffffff,
  expectEq "ofBytesBE de ad be ef" (UInt32.ofBytesBE 0xde 0xad 0xbe 0xef) 0xdeadbeef,
  -- toBytesBE is the inverse.
  expectEq "toBytesBE 12345678" (0x12345678 : UInt32).toBytesBE.toList [0x12, 0x34, 0x56, 0x78],
  expectEq "toBytesBE deadbeef" (0xdeadbeef : UInt32).toBytesBE.toList [0xde, 0xad, 0xbe, 0xef]
]

end Tests.Utils.Bitwise
