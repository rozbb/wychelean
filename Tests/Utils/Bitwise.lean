import Wychelean.Utils.Bitwise

open Wychelean

-- rotr
example : rotr 7 0 = 0 := by native_decide
example : rotr 1 1 = 0x80000000 := by native_decide
example : rotr 31 0x80000000 = 1 := by native_decide
example : rotr 4 0x12345678 = 0x81234567 := by native_decide
example : rotr 32 0x12345678 = 0x12345678 := by native_decide
example : rotr 36 0x12345678 = 0x81234567 := by native_decide

-- rotl
example : rotl 7 0 = 0 := by native_decide
example : rotl 1 0x80000000 = 1 := by native_decide
example : rotl 31 1 = 0x80000000 := by native_decide
example : rotl 4 0x12345678 = 0x23456781 := by native_decide
example : rotl 32 0x12345678 = 0x12345678 := by native_decide
example : rotl 13 (rotr 13 0xdeadbeef) = 0xdeadbeef := by native_decide

-- ofBytesBE packs four bytes in big-endian order, toBytesBE is its inverse.
example : UInt32.ofBytesBE #v[0x12, 0x34, 0x56, 0x78] = 0x12345678 := by native_decide
example : UInt32.ofBytesBE #v[0, 0, 0, 0] = 0 := by native_decide
example : UInt32.ofBytesBE #v[0xff, 0xff, 0xff, 0xff] = 0xffffffff := by native_decide
example : UInt32.ofBytesBE #v[0xde, 0xad, 0xbe, 0xef] = 0xdeadbeef := by native_decide
example : (0x12345678 : UInt32).toBytesBE = #v[0x12, 0x34, 0x56, 0x78] := by native_decide
example : (0xdeadbeef : UInt32).toBytesBE = #v[0xde, 0xad, 0xbe, 0xef] := by native_decide
example : (0x0102030405060708 : UInt64).toBytesBE = #v[1, 2, 3, 4, 5, 6, 7, 8] := by native_decide
example : (0x1c8 : UInt64).toBytesBE = #v[0, 0, 0, 0, 0, 0, 1, 0xc8] := by native_decide
