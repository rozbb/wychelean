/-!
Bitwise helpers on fixed-width integers not provided by core Lean.
-/

/-- `x.rotr n` rotates `x` right by `n` bits, `ROTRⁿ(x)` in FIPS 180-4. The amount is taken modulo 32. -/
def UInt32.rotr (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- `x.rotl n` rotates `x` left by `n` bits, `ROTLⁿ(x)` in FIPS 180-4. The amount is taken modulo 32. -/
def UInt32.rotl (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateLeft n⟩

/-- `x.rotr n` rotates `x` right by `n` bits, `ROTRⁿ(x)` in FIPS 180-4. The amount is taken modulo 64. -/
def UInt64.rotr (x : UInt64) (n : Nat) : UInt64 := ⟨x.toBitVec.rotateRight n⟩

/-- `x.rotl n` rotates `x` left by `n` bits, `ROTLⁿ(x)` in FIPS 180-4. The amount is taken modulo 64. -/
def UInt64.rotl (x : UInt64) (n : Nat) : UInt64 := ⟨x.toBitVec.rotateLeft n⟩
