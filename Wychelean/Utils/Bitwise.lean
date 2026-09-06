/-!
Bitwise helpers on fixed-width integers not provided by core Lean.
-/

/-- Rotate right by `n` bits. The amount is taken modulo 32. -/
def UInt32.rotateRight (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

namespace Wychelean

/-- `x ⋙ n` rotates `x` right by `n` bits, at the precedence of `>>>`. -/
scoped infixl:75 " ⋙ " => UInt32.rotateRight

end Wychelean

/-- Pack four bytes into a word, big-endian. -/
def UInt32.ofBytesBE (b : Vector UInt8 4) : UInt32 :=
  b[0].toUInt32 <<< 24 ||| b[1].toUInt32 <<< 16 ||| b[2].toUInt32 <<< 8 ||| b[3].toUInt32

/-- The four bytes of a word, big-endian. -/
def UInt32.toBytesBE (x : UInt32) : Vector UInt8 4 :=
  #v[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The eight bytes of a word, big-endian. -/
def UInt64.toBytesBE (x : UInt64) : Vector UInt8 8 :=
  #v[(x >>> 56).toUInt8, (x >>> 48).toUInt8, (x >>> 40).toUInt8, (x >>> 32).toUInt8,
     (x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]
