import Wychelean.Utils.Bitwise
import Wychelean.Utils.Bytes

/-!
# SHA-512
Specification of SHA-512 as defined in FIPS 180-4.
https://doi.org/10.6028/NIST.FIPS.180-4
-/

namespace Wychelean.Hashes.SHA512

/-- Size of a word in bits (FIPS 180-4, section 3.2). -/
abbrev wordBits : Nat := 64
/-- Size of a message block in bits (FIPS 180-4, section 5.2.2). -/
abbrev blockBits : Nat := 1024
/-- Number of words in a message block. -/
abbrev blockWords : Nat := blockBits / wordBits
/-- Number of rounds (FIPS 180-4, section 6.4.2, step 3). -/
abbrev numRounds : Nat := 80
/-- Size in bits of the message length appended by padding (FIPS 180-4, section 5.1.2). -/
abbrev lengthBits : Nat := 128
/-- Size of the digest in bits (FIPS 180-4, section 6.4). -/
abbrev digestBits : Nat := 512
/-- Size of the digest in bytes. -/
abbrev digestSize : Nat := 64

/-- Round constants: (FIPS 180-4, section 4.2.3). -/
def K : Vector UInt64 numRounds := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

/-- The eight 64-bit working variables `a` to `h` (FIPS 180-4, section 6.4). -/
structure State where
  (a b c d e f g h : UInt64)

/-- Word-wise addition modulo `2 ^ 64`. -/
instance : Add State where
  add st st' :=
    ⟨st.a + st'.a, st.b + st'.b, st.c + st'.c, st.d + st'.d,
     st.e + st'.e, st.f + st'.f, st.g + st'.g, st.h + st'.h⟩

/-- The state as a bit string: the words `a` to `h` in order, `a` most significant
(FIPS 180-4, section 6.4.2, step 4). -/
def State.toBitVec (st : State) : BitVec digestBits :=
  st.a.toBitVec ++ st.b.toBitVec ++ st.c.toBitVec ++ st.d.toBitVec ++
  st.e.toBitVec ++ st.f.toBitVec ++ st.g.toBitVec ++ st.h.toBitVec

/-- Initial state value: (FIPS 180-4, section 5.3.5). -/
def H0 : State :=
  { a := 0x6a09e667f3bcc908, b := 0xbb67ae8584caa73b, c := 0x3c6ef372fe94f82b, d := 0xa54ff53a5f1d36f1,
    e := 0x510e527fade682d1, f := 0x9b05688c2b3e6c1f, g := 0x1f83d9abfb41bd6b, h := 0x5be0cd19137e2179 }

/-- `σ₀(x) = ROTR¹(x) ⊕ ROTR⁸(x) ⊕ SHR⁷(x)` -/
def lowerSigma0 (x : UInt64) : UInt64 := x.rotr 1 ^^^ x.rotr 8 ^^^ x >>> 7

/-- `σ₁(x) = ROTR¹⁹(x) ⊕ ROTR⁶¹(x) ⊕ SHR⁶(x)` -/
def lowerSigma1 (x : UInt64) : UInt64 := x.rotr 19 ^^^ x.rotr 61 ^^^ x >>> 6

/-- `Σ₀(x) = ROTR²⁸(x) ⊕ ROTR³⁴(x) ⊕ ROTR³⁹(x)` -/
def upperSigma0 (x : UInt64) : UInt64 := x.rotr 28 ^^^ x.rotr 34 ^^^ x.rotr 39

/-- `Σ₁(x) = ROTR¹⁴(x) ⊕ ROTR¹⁸(x) ⊕ ROTR⁴¹(x)` -/
def upperSigma1 (x : UInt64) : UInt64 := x.rotr 14 ^^^ x.rotr 18 ^^^ x.rotr 41

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def Ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def Maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- One round of the compression function with round constant `k` and schedule word `w`
(FIPS 180-4, section 6.4.2, step 3). -/
def round (st : State) (k w : UInt64) : State :=
  let t1 := st.h + upperSigma1 st.e + Ch st.e st.f st.g + k + w
  let t2 := upperSigma0 st.a + Maj st.a st.b st.c
  { a := t1 + t2, b := st.a, c := st.b, d := st.c,
    e := st.d + t1, f := st.e, g := st.f, h := st.g }

/-- The message schedule `W₀, …, W₇₉` of a block (FIPS 180-4, section 6.4.2, step 1). -/
def messageSchedule (block : Vector UInt64 blockWords) : Vector UInt64 numRounds :=
  Nat.fold numRounds (init := Vector.replicate numRounds 0) fun t _ W =>
    W.set t <|
      if h : t < blockWords then block[t]
      else lowerSigma1 W[t - 2] + W[t - 7] + lowerSigma0 W[t - 15] + W[t - 16]

/-- Apply all rounds to `state` using the message schedule `W`. -/
def rounds (st : State) (W : Vector UInt64 numRounds) : State :=
  Fin.foldl numRounds (fun st t => round st K[t] W[t]) st

/-- Process one block, given as words (FIPS 180-4, section 6.4.2). -/
def compress (st : State) (block : Vector UInt64 blockWords) : State :=
  st + rounds st (messageSchedule block)

/-- Parse a block into words, most significant first (FIPS 180-4, section 5.2.2). -/
def bitsToBlock (block : BitVec blockBits) : Vector UInt64 blockWords :=
  (block.toChunksBE wordBits (by decide)).map UInt64.ofBitVec

/-- Number of `0` bits appended by padding: the least count that fills the final block. -/
def numZeros (n : Nat) : Nat := (blockBits - (n + 1 + lengthBits) % blockBits) % blockBits

/-- Pad a message (FIPS 180-4, section 5.1.2) -/
def padded {n : Nat} (msg : BitVec n) : BitVec (n + 1 + numZeros n + lengthBits) :=
  msg ++ 1#1 ++ 0#(numZeros n) ++ BitVec.ofNat lengthBits n

/-- The padded length is a multiple of the block size. -/
theorem padded_aligned (n : Nat) : (n + 1 + numZeros n + lengthBits) % blockBits = 0 := by
  simp only [numZeros, blockBits, lengthBits]; omega

/-- Parse a padded message into blocks of words (FIPS 180-4, section 5.2.2). -/
def parse {n : Nat} (msg : BitVec n) (h : n % blockBits = 0) :
    Vector (Vector UInt64 blockWords) (n / blockBits) :=
  (msg.toChunksBE blockBits h).map bitsToBlock

/-- SHA-512 of a message of fewer than `2 ^ 128` bits (FIPS 180-4, section 1).
Bit `n - 1` of `msg` is the first message bit (FIPS 180-4, section 3.1). -/
def sha512_bits {n : Nat} (msg : BitVec n) (_ : n < 2 ^ 128) : BitVec digestBits :=
  ((parse (padded msg) (padded_aligned n)).foldl compress H0).toBitVec

/-- SHA-512 of a byte string; byte zero is most significant (FIPS 180-4, section 3.1). -/
def sha512 {len : Nat} (msg : ByteVec len) (h : 8 * len < 2 ^ 128) : ByteVec digestSize :=
  (sha512_bits (BitVec.ofBytesBE msg) h).toBytesBE

end Wychelean.Hashes.SHA512
