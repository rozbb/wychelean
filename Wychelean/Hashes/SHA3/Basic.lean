import Wychelean.Permutations.Keccak.Basic

/-!
# SHA3
FIPS 202 §§3–6: https://doi.org/10.6028/NIST.FIPS.202
Adapted from Microsoft SymCrypt (MIT; see LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/Spec.lean
-/
namespace Wychelean.Hashes.SHA3
open Wychelean
open scoped Wychelean.Notations

namespace Internal

/-- FIPS 202 §3.1, Table 1, specialized to SHA3. -/
abbrev b : Nat := 1600

/-- Padding length for pad10*1(x, m) (§5.1). -/
abbrev padLen.j (x m : Nat) := ((-(m : Int) - 2) % x).toNat
abbrev padLen x m := 1 + padLen.j x m + 1

/-- FIPS 202 §5.1, Algorithm 9: pad10*1. -/
def «pad10*1» x m : Vector Bool (padLen x m) :=
  #v[1]  ‖ .replicate (padLen.j x m) 0 ‖ #v[1]

/-- Successive states during squeezing, including the initial state (Algorithm 8, steps 8–10). -/
def squeezeStates (f : α → α) (S : α) : (k : Nat) → Vector α (k + 1)
  | 0 => #v[S]
  | k + 1 => let states := squeezeStates f S k
             states.push (f states[k])

/-- The first d output bits; the state prefix is computed once and shared by all bits. -/
def squeeze (f : Vector Bool b → Vector Bool b) (r : Nat)
    (S : Vector Bool b) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  let states := squeezeStates f S (d / r)
  Vector.ofFn fun (i : Fin d) =>
    have hs : i.val / r < d / r + 1 := Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt i.isLt))
    (states[i.val / r]'hs)[i.val % r]'(by have := Nat.mod_lt i.val hr.1; omega)

/-- SPONGE[f, pad10*1, r], FIPS 202 Algorithm 8. -/
def SPONGE {n : Nat} (f : Vector Bool b → Vector Bool b) (r : Nat)
    (N : Vector Bool n) (d : Nat) (hr : 0 < r ∧ r < b) : Vector Bool d :=
  let total := n + padLen r n
  let S := Fin.foldl (total / r) (fun S block =>
    f (Vector.ofFn fun j => S[j] ^^ (if j.val < r then
      let k := block.val * r + j.val
      if h : k < n then N[k] else decide (k = n ∨ k + 1 = total)
      else false))) (Vector.replicate b false)
  squeeze f r S d hr

/-- KECCAK[c], FIPS 202 §5.2: width 1600, 24 rounds, rate 1600-c. -/
def KECCAK (c : Nat) (N : Vector Bool n) (d : Nat)
    (hc : 0 < c ∧ c < 1600 := by grind) : Vector Bool d :=
  SPONGE (fun S => (Permutations.Keccak.keccak_f .w1600 (BitVec.ofBitsLE S)).toBitsLE) (1600 - c) N d (by
    change 0 < 1600 - c ∧ 1600 - c < 1600
    omega)

/-! ## SHA-3 Hash Functions (§6.1)

SHA3-224(M) = KECCAK[448](M || 01, 224), etc.
The two-bit suffix 01 supports domain separation. -/

-- hashSuffix = FIPS "01": bit 0 = 0, bit 1 = 1 (LSB-first)
def hashSuffix : Vector Bool 2 := #v[0, 1]

def SHA3_224 {n} (M : Vector Bool n) := KECCAK  448 (M ‖ hashSuffix) 224
def SHA3_256 {n} (M : Vector Bool n) := KECCAK  512 (M ‖ hashSuffix) 256
def SHA3_384 {n} (M : Vector Bool n) := KECCAK  768 (M ‖ hashSuffix) 384
def SHA3_512 {n} (M : Vector Bool n) := KECCAK 1024 (M ‖ hashSuffix) 512


end Internal

/-! ## Byte interface

FIPS 202 §2.1 permits messages of any finite bit length; there is no maximum input
length. These functions accept whole bytes, including the empty message.
Bit ordering follows FIPS 202 Appendix B.1.
-/

/-- SHA3-224, FIPS 202 §6.1. Any finite byte string; 28-byte digest. -/
def sha3_224 {n} (msg : Vector UInt8 n) : Vector UInt8 28 :=
  bitsToBytes (Internal.SHA3_224 (bytesToBits msg))

/-- SHA3-256, FIPS 202 §6.1. Any finite byte string; 32-byte digest. -/
def sha3_256 {n} (msg : Vector UInt8 n) : Vector UInt8 32 :=
  bitsToBytes (Internal.SHA3_256 (bytesToBits msg))

/-- SHA3-384, FIPS 202 §6.1. Any finite byte string; 48-byte digest. -/
def sha3_384 {n} (msg : Vector UInt8 n) : Vector UInt8 48 :=
  bitsToBytes (Internal.SHA3_384 (bytesToBits msg))

/-- SHA3-512, FIPS 202 §6.1. Any finite byte string; 64-byte digest. -/
def sha3_512 {n} (msg : Vector UInt8 n) : Vector UInt8 64 :=
  bitsToBytes (Internal.SHA3_512 (bytesToBits msg))

end Wychelean.Hashes.SHA3
