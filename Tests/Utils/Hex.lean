import Wychelean.Utils.Hex
import Tests.Harness

namespace Tests.Utils.Hex

open Wychelean

def tests : List Test := [
  expectEq "encode empty" (Hex.encode #[]) "",
  expectEq "encode pads single digits" (Hex.encode #[0x00, 0x0a, 0xff]) "000aff",
  expectEq "encode is lowercase" (Hex.encode #[0xde, 0xad, 0xbe, 0xef]) "deadbeef",
  expectEq "decode empty" (Hex.decode "") (some #[]),
  expectEq "decode lowercase" (Hex.decode "deadbeef") (some #[0xde, 0xad, 0xbe, 0xef]),
  expectEq "decode uppercase" (Hex.decode "DEADBEEF") (some #[0xde, 0xad, 0xbe, 0xef]),
  expectEq "decode odd length" (Hex.decode "abc") none,
  expectEq "decode non-hex digit" (Hex.decode "zz") none,
  expectEq "decode inverts encode" (Hex.decode (Hex.encode #[1, 2, 3, 250])) (some #[1, 2, 3, 250])
]

end Tests.Utils.Hex
