import Wychelean.Utils.Hex

open Wychelean

example : Hex.encode #[] = "" := by native_decide
example : Hex.encode #[0x00, 0x0a, 0xff] = "000aff" := by native_decide
example : Hex.encode #[0xde, 0xad, 0xbe, 0xef] = "deadbeef" := by native_decide
example : Hex.decode "" = some #[] := by native_decide
example : Hex.decode "deadbeef" = some #[0xde, 0xad, 0xbe, 0xef] := by native_decide
example : Hex.decode "DEADBEEF" = some #[0xde, 0xad, 0xbe, 0xef] := by native_decide
example : Hex.decode "abc" = none := by native_decide
example : Hex.decode "zz" = none := by native_decide
example : Hex.decode (Hex.encode #[1, 2, 3, 250]) = some #[1, 2, 3, 250] := by native_decide
