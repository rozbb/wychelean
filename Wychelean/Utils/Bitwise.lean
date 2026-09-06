/-!
Fixed-width arithmetic helpers on `Nat`.

Words are represented as natural numbers; callers are responsible for keeping
inputs below `2 ^ 32`.
-/

namespace Wychelean

/-- Addition modulo `2 ^ 32`. -/
def add32 (a b : Nat) : Nat := (a + b) % 2 ^ 32

/-- Rotate a 32-bit word right by `offset` bits. -/
def rotRight32 (x : Nat) (offset : Nat) : Nat :=
  let offset := offset % 32
  let low := x % 2 ^ offset
  let high := x / 2 ^ offset
  low * 2 ^ (32 - offset) + high

end Wychelean
