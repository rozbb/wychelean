import Wychelean.Utils.Bitwise
import Wychelean.Utils.Vector

/-!
# SHA-256
Specification of SHA-256 as defined in FIPS 180-4.
-/

namespace Wychelean.Hashes.SHA256

/-- Size of a word in bytes. -/
abbrev wordSize : Nat := 4
/-- Size of a message block in bytes. -/
abbrev blockSize : Nat := 64
/-- Number of words in a message block. -/
abbrev blockWords : Nat := blockSize / wordSize
/-- Number of rounds, and of words in the message schedule. -/
abbrev numRounds : Nat := 64
/-- Size in bytes of the message length appended by padding. -/
abbrev lengthSize : Nat := 8
/-- Size of the digest in bytes. -/
abbrev digestSize : Nat := 32

/-- Round constants:
First 32 bits of the fractional parts of the cube roots of
the first 64 primes (FIPS 180-4, section 4.2.2).
-/
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

/-- Word-wise addition. -/
instance : Add State where
  add s t :=
    ⟨s.a + t.a, s.b + t.b, s.c + t.c, s.d + t.d,
     s.e + t.e, s.f + t.f, s.g + t.g, s.h + t.h⟩

/-- The state as bytes: the words `a` to `h` in order, each big-endian. -/
def State.toBytes (s : State) : Vector UInt8 digestSize :=
  #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].flatMap UInt32.toBytesBE

/--
Initial state value:
First 32 bits of the fractional parts of the square
roots of the first 8 primes (FIPS 180-4, section 5.3.3).
-/
def H0 : State :=
  { a := 0x6a09e667, b := 0xbb67ae85, c := 0x3c6ef372, d := 0xa54ff53a,
    e := 0x510e527f, f := 0x9b05688c, g := 0x1f83d9ab, h := 0x5be0cd19 }

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def lowerSigma0 (x : UInt32) : UInt32 := x ⋙ 7 ^^^ x ⋙ 18 ^^^ x >>> 3

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def lowerSigma1 (x : UInt32) : UInt32 := x ⋙ 17 ^^^ x ⋙ 19 ^^^ x >>> 10

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def upperSigma0 (x : UInt32) : UInt32 := x ⋙ 2 ^^^ x ⋙ 13 ^^^ x ⋙ 22

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def upperSigma1 (x : UInt32) : UInt32 := x ⋙ 6 ^^^ x ⋙ 11 ^^^ x ⋙ 25

/-- `Ch(e, f, g) = (e ∧ f) ⊕ (¬e ∧ g)` -/
def Ch (e f g : UInt32) : UInt32 := (e &&& f) ^^^ (~~~e &&& g)

/-- `Maj(a, b, c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` -/
def Maj (a b c : UInt32) : UInt32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- One round of the compression function with round constant `k` and schedule word `w`. -/
def round (s : State) (k w : UInt32) : State :=
  let t1 := s.h + upperSigma1 s.e + Ch s.e s.f s.g + k + w
  let t2 := upperSigma0 s.a + Maj s.a s.b s.c
  { a := t1 + t2, b := s.a, c := s.b, d := s.c, e := s.d + t1, f := s.e, g := s.f, h := s.g }

/-- The message schedule `W₀, …, W₆₃` of a block (FIPS 180-4, section 6.2.2, step 1). -/
def messageSchedule (block : Vector UInt32 blockWords) : Vector UInt32 numRounds :=
  Fin.foldl numRounds (init := Vector.replicate numRounds 0) fun w t =>
    if h : t.val < blockWords then
      w.set t block[t.val]
    else
      w.set t (lowerSigma1 w[t.val - 2] + w[t.val - 7]
        + lowerSigma0 w[t.val - 15] + w[t.val - 16])

/-- Apply all rounds to `state` using the message schedule `w`. -/
def rounds (state : State) (w : Vector UInt32 numRounds) : State :=
  Fin.foldl numRounds (fun s i => round s K[i] w[i]) state

/-- Process one block, given as big-endian words (FIPS 180-4, section 6.2.2). -/
def compress (state : State) (block : Vector UInt32 blockWords) : State :=
  state + rounds state (messageSchedule block)

/-- Parse a block into big-endian words (FIPS 180-4, section 5.2.1). -/
def bytesToBlock (bytes : Vector UInt8 blockSize) : Vector UInt32 blockWords :=
  (bytes.toChunks blockWords wordSize).map UInt32.ofBytesBE

/--
Number of blocks in the padded message:
the message, one `0x80` byte and the encoded length, rounded up to whole blocks.
-/
def numBlocks (len : Nat) : Nat := (len + 1 + lengthSize + (blockSize - 1)) / blockSize

/--
Pad a message and split it into blocks (FIPS 180-4, section 5.1.1):
append the byte `0x80`, then `0x00` bytes up to the last `lengthSize` bytes of the final block,
which hold the message length in bits, big-endian.
-/
def pad {len : Nat} (msg : Vector UInt8 len) :
    Vector (Vector UInt32 blockWords) (numBlocks len) :=
  let total := numBlocks len * blockSize
  let bitLength : Vector UInt8 lengthSize := (len * 8).toUInt64.toBytesBE
  let padded : Vector UInt8 total := Vector.ofFn fun (i : Fin total) =>
    if h : i.val < len then
      msg[i.val]
    else if i.val = len then
      0x80
    else if h : i.val < total - lengthSize then
      0
    else
      bitLength[i.val - (total - lengthSize)]
  (padded.toChunks (numBlocks len) blockSize).map bytesToBlock

/-- SHA-256 of a byte string: the message digest. -/
def sha256 {len : Nat} (msg : Vector UInt8 len) : Vector UInt8 digestSize :=
  ((pad msg).foldl compress H0).toBytes

end Wychelean.Hashes.SHA256
