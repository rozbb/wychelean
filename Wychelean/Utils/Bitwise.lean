/-!
Bitwise helpers on fixed-width integers not provided by core Lean.
-/

/-- Rotate right by `n` bits. The amount is taken modulo 32. -/
def UInt32.rotateRight (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- Pack four bytes into a word, big-endian. -/
def UInt32.ofBytesBE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32

/-- The four bytes of a word, big-endian. -/
def UInt32.toBytesBE (x : UInt32) : Vector UInt8 4 :=
  #v[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]
