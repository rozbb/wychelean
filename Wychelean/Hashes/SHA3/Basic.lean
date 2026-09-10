import Wychelean.Permutations.Keccak.Basic

/-!
# SHA3
FIPS 202 §§3–6: https://doi.org/10.6028/NIST.FIPS.202
Adapted from Microsoft SymCrypt (MIT; see LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
-/
namespace Wychelean.Hashes.SHA3
open Wychelean

namespace Internal

/-- FIPS 202 §3.1, Table 1, specialized to SHA3. -/
abbrev b : Nat := 1600

/-- Padding length for pad10*1(x, m) (§5.1). -/
abbrev padLen.j (x m : Nat) := ((-(m : Int) - 2) % x).toNat
abbrev padLen x m := 1 + padLen.j x m + 1

/-- FIPS 202 §5.1, Algorithm 9: pad10*1. -/
def «pad10*1» (x m : Nat) : BitVec (padLen x m) :=
  (1 : BitVec 1) ++ (0 : BitVec (padLen.j x m)) ++ (1 : BitVec 1)

/-- FIPS 202 Algorithm 8, steps 8–10: emit rate blocks, truncating the last. -/
def squeeze (f : BitVec b → BitVec b) (r : Nat)
    (S : BitVec b) (d : Nat) (hr : 0 < r ∧ r < b) : BitVec d :=
  if h : d ≤ r then S.extractLsb' 0 d
  else
    let Z := S.extractLsb' 0 r
    let remaining := squeeze f r (f S) (d - r) hr
    (remaining ++ Z).cast (by omega)
termination_by d

/-- SPONGE[f, pad10*1, r], FIPS 202 Algorithm 8. -/
def sponge {n : Nat} (f : BitVec b → BitVec b) (r : Nat)
    (N : BitVec n) (d : Nat) (hr : 0 < r ∧ r < b := by dsimp [b]; omega) : BitVec d :=
  let P := «pad10*1» r n ++ N
  let blocks := (n + padLen r n) / r
  let S := Fin.foldl blocks (fun S block =>
    let Pᵢ := P.extractLsb' (block.val * r) r
    f (S ^^^ Pᵢ.zeroExtend b)) 0
  squeeze f r S d hr

/-- KECCAK[c], FIPS 202 §5.2: width 1600, 24 rounds, rate 1600-c. -/
def keccak (c : Nat) (N : BitVec n) (d : Nat)
    (hc : 0 < c ∧ c < 1600 := by grind) : BitVec d :=
  sponge (Permutations.Keccak.keccak_f .w1600) (1600 - c) N d

/-- FIPS 202 §6.1: suffix 01, with bit zero least significant. -/
def hashSuffix : BitVec 2 := 0b10

end Internal

/-- SHA3-224, FIPS 202 §6.1. Any finite bit string; 224-bit digest. -/
def sha3_224_bits {n : Nat} (msg : BitVec n) : BitVec 224 :=
  Internal.keccak 448 (Internal.hashSuffix ++ msg) 224

/-- SHA3-256, FIPS 202 §6.1. Any finite bit string; 256-bit digest. -/
def sha3_256_bits {n : Nat} (msg : BitVec n) : BitVec 256 :=
  Internal.keccak 512 (Internal.hashSuffix ++ msg) 256

/-- SHA3-384, FIPS 202 §6.1. Any finite bit string; 384-bit digest. -/
def sha3_384_bits {n : Nat} (msg : BitVec n) : BitVec 384 :=
  Internal.keccak 768 (Internal.hashSuffix ++ msg) 384

/-- SHA3-512, FIPS 202 §6.1. Any finite bit string; 512-bit digest. -/
def sha3_512_bits {n : Nat} (msg : BitVec n) : BitVec 512 :=
  Internal.keccak 1024 (Internal.hashSuffix ++ msg) 512

/-- SHA3-224, FIPS 202 §6.1. Any finite byte string; 28-byte digest. -/
def sha3_224 {n} (msg : ByteVec n) : ByteVec 28 :=
  (sha3_224_bits (BitVec.ofBytesLE msg)).toBytesLE

/-- SHA3-256, FIPS 202 §6.1. Any finite byte string; 32-byte digest. -/
def sha3_256 {n} (msg : ByteVec n) : ByteVec 32 :=
  (sha3_256_bits (BitVec.ofBytesLE msg)).toBytesLE

/-- SHA3-384, FIPS 202 §6.1. Any finite byte string; 48-byte digest. -/
def sha3_384 {n} (msg : ByteVec n) : ByteVec 48 :=
  (sha3_384_bits (BitVec.ofBytesLE msg)).toBytesLE

/-- SHA3-512, FIPS 202 §6.1. Any finite byte string; 64-byte digest. -/
def sha3_512 {n} (msg : ByteVec n) : ByteVec 64 :=
  (sha3_512_bits (BitVec.ofBytesLE msg)).toBytesLE

end Wychelean.Hashes.SHA3
