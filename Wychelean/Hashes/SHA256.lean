import Wychelean.Utils.Bitwise
import Wychelean.Utils.Vector

/-!
# SHA-256
Specification of SHA-256 as defined in FIPS 180-4.
-/

namespace Wychelean.Hashes.SHA256

/-- Round constants:
First 32 bits of the fractional parts of the cube roots of
the first 64 primes (FIPS 180-4, section 4.2.2).
-/
def K : Vector UInt32 64 := #v[
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

/-- Word-wise addition of two states. -/
def State.add (s t : State) : State :=
  { a := s.a + t.a, b := s.b + t.b, c := s.c + t.c, d := s.d + t.d,
    e := s.e + t.e, f := s.f + t.f, g := s.g + t.g, h := s.h + t.h }

/-- The state as eight words, `a` first. -/
def State.toVector (s : State) : Vector UInt32 8 := #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/--
Initial state value:
First 32 bits of the fractional parts of the square
roots of the first 8 primes (FIPS 180-4, section 5.3.3).
-/
def H0 : State :=
  { a := 0x6a09e667, b := 0xbb67ae85, c := 0x3c6ef372, d := 0xa54ff53a,
    e := 0x510e527f, f := 0x9b05688c, g := 0x1f83d9ab, h := 0x5be0cd19 }

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def lowerSigma0 (x : UInt32) : UInt32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def lowerSigma1 (x : UInt32) : UInt32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def upperSigma0 (x : UInt32) : UInt32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def upperSigma1 (x : UInt32) : UInt32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `Ch(e, f, g) = (e ∧ f) ⊕ (¬e ∧ g)` -/
def Ch (e f g : UInt32) : UInt32 := (e &&& f) ^^^ (~~~e &&& g)

/-- `Maj(a, b, c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)` -/
def Maj (a b c : UInt32) : UInt32 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- One round of the compression function with round constant `k` and schedule word `w`. -/
def sha256Round (s : State) (k w : UInt32) : State :=
  let t1 := s.h + upperSigma1 s.e + Ch s.e s.f s.g + k + w
  let t2 := upperSigma0 s.a + Maj s.a s.b s.c
  { a := t1 + t2, b := s.a, c := s.b, d := s.c, e := s.d + t1, f := s.e, g := s.f, h := s.g }

/-- Expand a 16-word block into the 64-word message schedule. -/
def messageSchedule (block : Vector UInt32 16) : Vector UInt32 64 :=
  let init : Vector UInt32 64 := Vector.ofFn fun (i : Fin 64) =>
    if h : i.val < 16 then block[i.val] else 0
  Fin.foldl 48 (fun w (i : Fin 48) =>
    let j := i.val + 16
    let wj := lowerSigma1 w[j - 2] + w[j - 7] + lowerSigma0 w[j - 15] + w[j - 16]
    have hj : j < 64 := by omega
    w.set j wj) init

/-- Apply the 64 rounds to `state` using the message schedule `w`. -/
def sha256Compress (state : State) (w : Vector UInt32 64) : State :=
  Fin.foldl 64 (fun s i => sha256Round s K[i] w[i]) state

/-- Process one 512-bit block, given as 16 big-endian 32-bit words. -/
def compressBlock (state : State) (block : Vector UInt32 16) : State :=
  state.add (sha256Compress state (messageSchedule block))

/-- Pack four bytes into a 32-bit word, big-endian. -/
def bytesToWord32BE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32

/-- Pack 64 bytes into a block of 16 big-endian 32-bit words. -/
def bytesToBlock (bytes : Vector UInt8 64) : Vector UInt32 16 :=
  Vector.ofFn fun (i : Fin 16) =>
    bytesToWord32BE bytes[4 * i.val] bytes[4 * i.val + 1]
      bytes[4 * i.val + 2] bytes[4 * i.val + 3]

/-- Pad a message and split it into blocks (FIPS 180-4, section 5.1.1):
append the byte `0x80`, then zero bytes until the length is 56 modulo 64,
then the original length in bits as a big-endian 64-bit integer. -/
def pad {len : Nat} (msg : Vector UInt8 len) :
    Vector (Vector UInt32 16) ((len + (55 + 64 - len % 64) % 64 + 9) / 64) :=
  let bitLen := len * 8
  let zeros := (55 + 64 - len % 64) % 64
  let numBlocks := (len + zeros + 9) / 64
  let totalLen := numBlocks * 64
  let padded : Vector UInt8 totalLen := Vector.ofFn fun (i : Fin totalLen) =>
    if h : i.val < len then
      msg[i.val]
    else if i.val = len then
      0x80
    else if i.val < totalLen - 8 then
      0
    else
      (bitLen >>> (8 * (totalLen - 1 - i.val))).toUInt8
  (padded.toChunks 64).map bytesToBlock

/-- SHA-256 of a byte string, as eight 32-bit words (most significant first). -/
def sha256 {len : Nat} (msg : Vector UInt8 len) : Vector UInt32 8 :=
  ((pad msg).foldl compressBlock H0).toVector

end Wychelean.Hashes.SHA256
