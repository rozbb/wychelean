import Wychelean.KEM.MLKEM.Basic

/-! FIPS 203 §4.2.1: encoding and decoding of integer arrays as bytes. -/

namespace Wychelean.KEM.MLKEM

open Wychelean
open scoped Wychelean.Notations

namespace Bounds

/-! ### Nonlinear index bounds -/

/-- `i * d + j < n * d` from `i < n, j < d`. -/
@[scoped grind ←]
theorem idx_mul_add_lt (i d j n : Nat) (hi : i < n) (hj : j < d) :
    i * d + j < n * d := by
  calc i * d + j < i * d + d := by omega
    _ = (i + 1) * d := by ring
    _ ≤ n * d := Nat.mul_le_mul_right d hi

/-- `i * d ≤ 255 * d` from `i < 256` (ByteEncode/ByteDecode, Algorithms 5–6). -/
@[scoped grind ←]
theorem byte_encode_idx_le (i d : Nat) (hi : i < 256) : i * d ≤ 255 * d :=
  Nat.mul_le_mul_right d (by omega)

/-- `32 * d * (i + 1) ≤ 32 * d * k` from `i < k` (PolyVector.ByteDecode). -/
@[scoped grind ←]
theorem poly_vec_decode_idx_le (d i : Nat) {k : Nat} (hi : i < k) :
    32 * d * (i + 1) ≤ 32 * d * k :=
  Nat.mul_le_mul_left _ hi

end Bounds

open Bounds

/-! ## §4.2.1 Algorithm 5 — ByteEncode_d(F) -/
def ByteEncode (d : ℕ) (F : Vector (ZMod (m d)) 256) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (32 * d) := Id.run do
  let mut b := Vector.replicate (256 * d) 0
  for hi: i in [0:256] do                                                     -- Alg. 5, step 1
    have := byte_encode_idx_le i d
    let mut a := F[i].val                                                     -- Alg. 5, step 2
    for hj: j in [0:d] do                                                     -- Alg. 5, step 3
      b := b.set (i * d + j) (Bool.ofNat (a % 2))                             -- Alg. 5, step 4
      a := (a - b[i * d + j].toNat) / 2                                       -- Alg. 5, step 5
  let B := bitsToBytes (b.cast (by grind))                                    -- Alg. 5, step 8
  return B                                                                    -- Alg. 5, step 9

/-! ## §4.2.1 Algorithm 6 — ByteDecode_d(B) -/
def ByteDecode {d : ℕ} (B : ByteVec (32 * d)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) :
    Vector (ZMod (m d)) 256 := Id.run do
  let b := bytesToBits B                                                      -- Alg. 6, step 1
  let mut F : Vector (ZMod (m d)) 256 := Vector.replicate 256 0
  for hi: i in [0:256] do                                                     -- Alg. 6, step 2
    have := byte_encode_idx_le i d
    F := F.set i (∑ j : Fin d, b[i * d + j].toNat * 2 ^ j.val)               -- Alg. 6, step 3
  return F                                                                    -- Alg. 6, step 5

/-- `ByteEncode_d` of each entry, concatenated (§2.4.8). -/
def PolyVector.ByteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (32 * d * k) :=
  (v.map fun f => MLKEM.ByteEncode d f.coeffs).flatten.cast (Nat.mul_comm _ _)

def PolyVector.ByteDecode {k : K} (d : ℕ) (bytes : ByteVec (32 * d * k)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : PolyVector (m d) k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le d i i.isLt
    ⟨MLKEM.ByteDecode (slice bytes (32 * d * i) (32 * d) (by grind))⟩

/-- `ByteEncode₁₂` of a vector over `T_q` (§2.4.4, Eq. 2.7). -/
def ByteEncode₁₂ {k : K} (v : NTTVector k) : ByteVec (vecLen' k) :=
  (v.map fun «f̂» => MLKEM.ByteEncode 12 «f̂».coeffs).flatten.cast (Nat.mul_comm _ _)

def ByteDecode₁₂ {k : K} (bytes : ByteVec (vecLen' k)) : NTTVector k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le 12 i i.isLt
    Tq.mk (MLKEM.ByteDecode (slice bytes (32 * 12 * i) (32 * 12) (by grind)))

end Wychelean.KEM.MLKEM
