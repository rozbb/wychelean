import Wychelean.Utils.Bitwise
import Wychelean.Utils.Bytes

/-!
# SHA-256
Specification of SHA-256 as defined in FIPS 180-4.
https://doi.org/10.6028/NIST.FIPS.180-4
-/

namespace Wychelean.Hashes.SHA256

/-- Size of a word in bits (FIPS 180-4, section 3.2). -/
abbrev wordBits : Nat := 32
/-- Size of a message block in bits (FIPS 180-4, section 5.2.1). -/
abbrev blockBits : Nat := 512
/-- Number of words in a message block. -/
abbrev blockWords : Nat := blockBits / wordBits
/-- Number of rounds (FIPS 180-4, section 6.2.2, step 3). -/
abbrev numRounds : Nat := 64
/-- Size in bits of the message length appended by padding (FIPS 180-4, section 5.1.1). -/
abbrev lengthBits : Nat := 64
/-- Size of the digest in bits (FIPS 180-4, section 6.2). -/
abbrev digestBits : Nat := 256
/-- Size of the digest in bytes. -/
abbrev digestSize : Nat := 32

/-- Round constants: (FIPS 180-4, section 4.2.2). -/
def K : Vector UInt32 numRounds := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- The eight 32-bit working variables `a` to `h` (FIPS 180-4, section 6.2). -/
structure State where
  (a b c d e f g h : UInt32)

/-- Word-wise addition modulo `2 ^ 32`. -/
instance : Add State where
  add st st' :=
    ⟨st.a + st'.a, st.b + st'.b, st.c + st'.c, st.d + st'.d,
     st.e + st'.e, st.f + st'.f, st.g + st'.g, st.h + st'.h⟩

/-- The state as a bit string: the words `a` to `h` in order, `a` most significant
(FIPS 180-4, section 6.2.2, step 4). -/
def State.toBitVec (st : State) : BitVec digestBits :=
  st.a.toBitVec ++ st.b.toBitVec ++ st.c.toBitVec ++ st.d.toBitVec ++
  st.e.toBitVec ++ st.f.toBitVec ++ st.g.toBitVec ++ st.h.toBitVec

/-- Initial state value: (FIPS 180-4, section 5.3.3). -/
def H0 : State :=
  { a := 0x6a09e667, b := 0xbb67ae85, c := 0x3c6ef372, d := 0xa54ff53a,
    e := 0x510e527f, f := 0x9b05688c, g := 0x1f83d9ab, h := 0x5be0cd19 }

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def lowerSigma0 (x : UInt32) : UInt32 := x.rotr 7 ^^^ x.rotr 18 ^^^ x >>> 3

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def lowerSigma1 (x : UInt32) : UInt32 := x.rotr 17 ^^^ x.rotr 19 ^^^ x >>> 10

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def upperSigma0 (x : UInt32) : UInt32 := x.rotr 2 ^^^ x.rotr 13 ^^^ x.rotr 22

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def upperSigma1 (x : UInt32) : UInt32 := x.rotr 6 ^^^ x.rotr 11 ^^^ x.rotr 25

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- One round of the compression function with round constant `k` and schedule word `w`
(FIPS 180-4, section 6.2.2, step 3). -/
def round (st : State) (k w : UInt32) : State :=
  let t1 := st.h + upperSigma1 st.e + Ch st.e st.f st.g + k + w
  let t2 := upperSigma0 st.a + Maj st.a st.b st.c
  { a := t1 + t2, b := st.a, c := st.b, d := st.c,
    e := st.d + t1, f := st.e, g := st.f, h := st.g }

/-- The message schedule `W₀, …, W₆₃` of a block (FIPS 180-4, section 6.2.2, step 1). -/
def messageSchedule (block : Vector UInt32 blockWords) : Vector UInt32 numRounds :=
  Nat.fold numRounds (init := Vector.replicate numRounds 0) fun t _ W =>
    W.set t <|
      if h : t < blockWords then block[t]
      else lowerSigma1 W[t - 2] + W[t - 7] + lowerSigma0 W[t - 15] + W[t - 16]

/-- Apply all rounds to `state` using the message schedule `W`. -/
def rounds (st : State) (W : Vector UInt32 numRounds) : State :=
  Fin.foldl numRounds (fun st t => round st K[t] W[t]) st

/-- Process one block, given as words (FIPS 180-4, section 6.2.2). -/
def compress (st : State) (block : Vector UInt32 blockWords) : State :=
  st + rounds st (messageSchedule block)

/-- Parse a block into words, most significant first (FIPS 180-4, section 5.2.1). -/
def bitsToBlock (block : BitVec blockBits) : Vector UInt32 blockWords :=
  (block.toChunksBE wordBits (by decide)).map UInt32.ofBitVec

/-- Number of `0` bits appended by padding: the least count that fills the final block. -/
def numZeros (n : Nat) : Nat := (blockBits - (n + 1 + lengthBits) % blockBits) % blockBits

/-- Pad a message (FIPS 180-4, section 5.1.1) -/
def padded {n : Nat} (msg : BitVec n) : BitVec (n + 1 + numZeros n + lengthBits) :=
  msg ++ 1#1 ++ 0#(numZeros n) ++ BitVec.ofNat lengthBits n

/-- The padded length is a multiple of the block size. -/
theorem padded_aligned (n : Nat) : (n + 1 + numZeros n + lengthBits) % blockBits = 0 := by
  simp only [numZeros, blockBits, lengthBits]; omega

/-- Parse a padded message into blocks of words (FIPS 180-4, section 5.2.1). -/
def parse {n : Nat} (msg : BitVec n) (h : n % blockBits = 0) :
    Vector (Vector UInt32 blockWords) (n / blockBits) :=
  (msg.toChunksBE blockBits h).map bitsToBlock

/-- SHA-256 of a message of fewer than `2 ^ 64` bits (FIPS 180-4, section 1).
Bit `n - 1` of `msg` is the first message bit (FIPS 180-4, section 3.1). -/
def sha256_bits {n : Nat} (msg : BitVec n) (_ : n < 2 ^ 64) : BitVec digestBits :=
  ((parse (padded msg) (padded_aligned n)).foldl compress H0).toBitVec

/-- SHA-256 of a byte string; byte zero is most significant (FIPS 180-4, section 3.1). -/
def sha256 {len : Nat} (msg : ByteVec len) (h : 8 * len < 2 ^ 64) : ByteVec digestSize :=
  (sha256_bits (BitVec.ofBytesBE msg) h).toBytesBE

end Wychelean.Hashes.SHA256
