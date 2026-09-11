import Mathlib.Data.List.Defs
import Mathlib.Tactic.GCongr

namespace Wychelean

abbrev Bit := Bool
abbrev Byte := UInt8
abbrev ByteVec (n : Nat) := Vector Byte n

end Wychelean

namespace BitVec
open Wychelean

/-- Pack a Boolean vector with index zero as the least significant bit. -/
def ofBitsLE (v : Vector Bit n) : BitVec n :=
  (ofBoolListLE v.toList).cast (by simp)
/-- Unpack a word, least significant bit first. -/
def toBitsLE (v : BitVec n) : Vector Bit n := Vector.ofFn fun i => v.getLsbD i

@[simp] theorem getLsbD_ofBitsLE (v : Vector Bit n) (i : Nat) (hi : i < n) :
    (ofBitsLE v).getLsbD i = v[i] := by
  simp only [ofBitsLE, getLsbD_cast, getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  simp [hi]

@[simp] theorem getElem_ofBitsLE (v : Vector Bit n) (i : Nat) (hi : i < n) :
    (ofBitsLE v)[i] = v[i] := getLsbD_ofBitsLE v i hi

@[simp] theorem toBitsLE_ofBitsLE (v : Vector Bit n) : toBitsLE (ofBitsLE v) = v := by
  apply Vector.ext
  intro i hi
  simp [toBitsLE]

@[simp] theorem ofBitsLE_toBitsLE (v : BitVec n) : ofBitsLE (toBitsLE v) = v := by
  apply eq_of_getLsbD_eq
  intro i hi
  simp [hi, toBitsLE]

/-- Byte zero holds bits 0–7. This convention is used by FIPS 202, Appendix B.1. -/
def ofBytesLE (v : ByteVec n) : BitVec (8 * n) :=
  ofBitsLE (Vector.ofFn fun (i : Fin (8 * n)) =>
    v[i.val / 8]'(by omega) |>.toBitVec.getLsbD (i.val % 8))

/-- Decode a whole number of bytes; no truncation or padding is performed. -/
def toBytesLE (v : BitVec (8 * n)) : ByteVec n :=
  Vector.ofFn fun i => ⟨ofBitsLE (Vector.ofFn fun (j : Fin 8) => v.getLsbD (8 * i.val + j.val))⟩

@[simp] theorem getLsbD_ofBytesLE (v : ByteVec n) (i : Nat) (hi : i < 8 * n) :
    (ofBytesLE v).getLsbD i = (v[i / 8]'(by omega)).toBitVec.getLsbD (i % 8) := by
  simp [ofBytesLE, hi]

@[simp] theorem getLsbD_toBytesLE (v : BitVec (8 * n)) (i : Nat) (hi : i < n)
    (j : Nat) (hj : j < 8) :
    (toBytesLE v)[i].toBitVec.getLsbD j = v.getLsbD (8 * i + j) := by
  simp [toBytesLE, hj]

@[simp] theorem ofBytesLE_toBytesLE (v : BitVec (8 * n)) :
    ofBytesLE (toBytesLE v) = v := by
  apply eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBytesLE _ _ hi, getLsbD_toBytesLE _ _ (by omega) _ (by omega)]
  congr 1
  omega

@[simp] theorem toBytesLE_ofBytesLE (v : ByteVec n) :
    toBytesLE (ofBytesLE v) = v := by
  apply Vector.ext
  intro i hi
  apply UInt8.toBitVec_inj.mp
  apply eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_toBytesLE _ _ hi _ hj, getLsbD_ofBytesLE _ _ (by omega)]
  have hdiv : (8 * i + j) / 8 = i := by omega
  have hmod : (8 * i + j) % 8 = j := by omega
  simp [hdiv, hmod]

/-- Byte zero is most significant, as in FIPS 180-4 §3.1. -/
def ofBytesBE (v : ByteVec n) : BitVec (8 * n) := ofBytesLE v.reverse
/-- Whole-byte big-endian decoding, inverse to ofBytesBE. -/
def toBytesBE (v : BitVec (8 * n)) : ByteVec n := (toBytesLE v).reverse

@[simp] theorem ofBytesBE_toBytesBE (v : BitVec (8 * n)) :
    ofBytesBE (toBytesBE v) = v := by simp [ofBytesBE, toBytesBE]
@[simp] theorem toBytesBE_ofBytesBE (v : ByteVec n) :
    toBytesBE (ofBytesBE v) = v := by simp [ofBytesBE, toBytesBE]
/-- Bit i is in byte n-1-i/8, with the same bit position within that byte. -/
theorem getLsbD_ofBytesBE (v : ByteVec n) (i : Nat) (hi : i < 8 * n) :
    (ofBytesBE v).getLsbD i = (v[n - 1 - i / 8]'(by omega)).toBitVec.getLsbD (i % 8) := by
  rw [ofBytesBE, getLsbD_ofBytesLE _ _ hi]
  simp [Vector.getElem_reverse]

/-- Encoding commutes with XOR, pointwise on the Boolean representation. -/
theorem ofBitsLE_xor (a b : Vector Bit n) :
    ofBitsLE (a.zipWith (· ^^ ·) b) = ofBitsLE a ^^^ ofBitsLE b := by
  apply eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_xor, getLsbD_ofBitsLE _ _ hi, Vector.getElem_zipWith]

theorem ofBitsLE_and (a b : Vector Bit n) :
    ofBitsLE (a.zipWith (· && ·) b) = ofBitsLE a &&& ofBitsLE b := by
  apply eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_and, getLsbD_ofBitsLE _ _ hi, Vector.getElem_zipWith]

theorem ofBitsLE_not (a : Vector Bit n) :
    ofBitsLE (a.map (!·)) = ~~~ofBitsLE a := by
  apply eq_of_getLsbD_eq
  intro i hi
  simp [hi]

end BitVec

namespace Wychelean
/-- Expand bytes in FIPS 202 Appendix B.1 order, least significant bit first within each byte. -/
def bytesToBits (v : ByteVec n) : Vector Bit (8 * n) :=
  Vector.ofFn fun i => (v[i.val / 8]'(by omega)).toBitVec.getLsbD (i.val % 8)
/-- Pack complete bytes in FIPS 202 Appendix B.1 order. -/
def bitsToBytes (v : Vector Bit (8 * n)) : ByteVec n :=
  Vector.ofFn fun i => ⟨BitVec.ofBitsLE (Vector.ofFn fun (j : Fin 8) => v[8 * i.val + j.val]'(by omega))⟩

@[simp] theorem bitsToBytes_getLsbD (v : Vector Bit (8 * n)) (i : Nat) (hi : i < n)
    (j : Nat) (hj : j < 8) :
    (bitsToBytes v)[i].toBitVec.getLsbD j = v[8 * i + j]'(by omega) := by
  simp [bitsToBytes, hj]

@[simp] theorem bytesToBits_bitsToBytes (v : Vector Bit (8 * n)) :
    bytesToBits (bitsToBytes v) = v := by
  apply Vector.ext
  intro i hi
  simp only [bytesToBits, Vector.getElem_ofFn]
  rw [bitsToBytes_getLsbD _ _ (by omega) _ (by omega)]
  congr 1
  omega

@[simp] theorem bitsToBytes_bytesToBits (v : ByteVec n) :
    bitsToBytes (bytesToBits v) = v := by
  apply Vector.ext
  intro i hi
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [bitsToBytes_getLsbD _ _ hi _ hj]
  simp only [bytesToBits, Vector.getElem_ofFn]
  have hdiv : (8 * i + j) / 8 = i := by omega
  have hmod : (8 * i + j) % 8 = j := by omega
  simp [hdiv, hmod]
end Wychelean
