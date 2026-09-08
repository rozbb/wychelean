import Wychelean.Hashes.Keccak

/-!
# SHA3 and SHAKE
FIPS 202 §§5–6: https://doi.org/10.6028/NIST.FIPS.202
Adapted from Microsoft SymCrypt (MIT; see LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
-/
namespace Wychelean.Hashes.SHA3
open Wychelean
open scoped Wychelean.Notations

/-- KECCAK[c], FIPS 202 §5.2: width 1600, 24 rounds, rate 1600-c. -/
def KECCAK (c : Nat) (N : Vector Bool n) (d : Nat)
    (hc : 0 < c ∧ c < 1600 := by grind) : Vector Bool d :=
  Keccak.KECCAK 6 24 (1600 - c) N d (by change 0 < 1600-c ∧ 1600-c < 1600; omega)

/-! ## SHA-3 Hash Functions (§6.1)

SHA3-224(M) = KECCAK[448](M || 01, 224), etc.
The two-bit suffix 01 supports domain separation. -/

-- hashSuffix = FIPS "01": bit 0 = 0, bit 1 = 1 (LSB-first)
def hashSuffix : Vector Bool 2 := #v[0, 1]

def SHA3_224 {n} (M : Vector Bool n) := KECCAK  448 (M ‖ hashSuffix) 224
def SHA3_256 {n} (M : Vector Bool n) := KECCAK  512 (M ‖ hashSuffix) 256
def SHA3_384 {n} (M : Vector Bool n) := KECCAK  768 (M ‖ hashSuffix) 384
def SHA3_512 {n} (M : Vector Bool n) := KECCAK 1024 (M ‖ hashSuffix) 512


/-! ## Alternate Definitions (§6.3)

RawSHAKE128(J, d) = KECCAK[256](J || 11, d)
RawSHAKE256(J, d) = KECCAK[512](J || 11, d)
The suffix 11 supports domain separation and Sakura compatibility. -/

-- rawSuffix = FIPS "11": bit 0 = 1, bit 1 = 1 (LSB-first)
def rawSuffix : Vector Bool 2 := #v[1, 1]

def RawSHAKE128 {n} (J : Vector Bool n) (d : Nat) := KECCAK 256 (J ‖ rawSuffix) d
def RawSHAKE256 {n} (J : Vector Bool n) (d : Nat) := KECCAK 512 (J ‖ rawSuffix) d


/-! ## SHA-3 Extendable-Output Functions (§6.2)

SHAKE128(M, d) = KECCAK[256](M || 1111, d)
SHAKE256(M, d) = KECCAK[512](M || 1111, d)
Equivalently (§6.3): SHAKE(M, d) = RawSHAKE(M || 11, d).
The four-bit suffix 1111 = 11 || 11. -/

-- xofSuffix = FIPS "1111": all four bits 1 (LSB-first)
def xofSuffix : Vector Bool 4 := #v[1, 1, 1, 1]

def SHAKE128 {n} (M : Vector Bool n) (d : Nat) : Vector Bool d := KECCAK 256 (M ‖ xofSuffix) d
def SHAKE256 {n} (M : Vector Bool n) (d : Nat) : Vector Bool d := KECCAK 512 (M ‖ xofSuffix) d


/-! ## Byte-Level Interface

Convert between `Vector UInt8 n` (byte vectors) and `Vector Bool (8*n)`.
Uses `bytesToBits`/`bitsToBytes` from `Wychelean.Utils.Bytes` — the SHA-3
LSB-first bit ordering within bytes (§B.1) matches FIPS 203 Algorithms 3–4. -/

def sha3_224 {n} (msg : Vector UInt8 n) : Vector UInt8 28 := bitsToBytes (SHA3_224 (bytesToBits msg))
def sha3_256 {n} (msg : Vector UInt8 n) : Vector UInt8 32 := bitsToBytes (SHA3_256 (bytesToBits msg))
def sha3_384 {n} (msg : Vector UInt8 n) : Vector UInt8 48 := bitsToBytes (SHA3_384 (bytesToBits msg))
def sha3_512 {n} (msg : Vector UInt8 n) : Vector UInt8 64 := bitsToBytes (SHA3_512 (bytesToBits msg))

def shake128 {n} (msg : Vector UInt8 n) length : Vector UInt8 length  :=
  bitsToBytes (SHAKE128 (bytesToBits msg) (8 * length))

def shake256 {n} (msg : Vector UInt8 n) length : Vector UInt8 length :=
  bitsToBytes (SHAKE256 (bytesToBits msg) (8 * length))

end Wychelean.Hashes.SHA3
