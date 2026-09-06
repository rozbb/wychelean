/-!
Bitwise helpers on fixed-width integers not provided by core Lean.
-/

/-- Rotate right by `n` bits. The amount is taken modulo 32. -/
def UInt32.rotateRight (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateRight n⟩
