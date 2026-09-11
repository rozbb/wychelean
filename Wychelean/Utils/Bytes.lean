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

/-- Split into `n / m` consecutive chunks of `m` bits; chunk zero is the most significant. -/
def toChunksBE (m : Nat) (v : BitVec n) (_ : n % m = 0) : Vector (BitVec m) (n / m) :=
  Vector.ofFn fun (i : Fin (n / m)) => v.extractLsb' (n - (i.val + 1) * m) m

@[simp] theorem getLsbD_toChunksBE (m : Nat) (v : BitVec n) (h : n % m = 0)
    (i : Nat) (hi : i < n / m) (j : Nat) :
    ((v.toChunksBE m h)[i]).getLsbD j = (decide (j < m) && v.getLsbD (n - (i + 1) * m + j)) := by
  simp [toChunksBE, getLsbD_extractLsb']

/-- `ofBytesLE` by halving: quasilinear big-integer work instead of a quadratic bit-by-bit fold,
and bounded recursion depth. Used at run time through `ofBytesLE_eq_ofBytesLEFast`. -/
def ofBytesLEFast {n : Nat} (v : ByteVec n) : BitVec (8 * n) :=
  if h1 : n ≤ 1 then
    if h0 : n = 0 then (0#0).cast (by omega)
    else (v[0]'(by omega)).toBitVec.cast (by omega)
  else
    let k := n / 2
    let hi : ByteVec (n - k) := v.drop k
    let lo : ByteVec k := (v.take k).cast (by omega)
    (ofBytesLEFast hi ++ ofBytesLEFast lo).cast (by omega)
termination_by n
decreasing_by all_goals omega

theorem ofBytesLEFast_eq {n : Nat} (v : ByteVec n) : ofBytesLEFast v = ofBytesLE v := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    apply eq_of_getLsbD_eq; intro i hi
    unfold ofBytesLEFast
    by_cases h1 : n ≤ 1
    · by_cases h0 : n = 0
      · omega
      · have hn : n = 1 := by omega
        subst hn
        rw [getLsbD_ofBytesLE _ _ hi]
        have e1 : i / 8 = 0 := by omega
        have e2 : i % 8 = i := by omega
        simp only [h1, h0, ↓reduceDIte, getLsbD_cast, e1, e2]
    · simp only [h1, ↓reduceDIte, getLsbD_cast, getLsbD_append]
      rw [ih (n / 2) (by omega), ih (n - n / 2) (by omega), getLsbD_ofBytesLE _ _ hi]
      split
      · rw [getLsbD_ofBytesLE _ _ (by omega)]
        simp only [Vector.getElem_cast, Vector.getElem_take]
      · rw [getLsbD_ofBytesLE _ _ (by omega)]
        simp only [Vector.getElem_drop]
        have e1 : n / 2 + (i - 8 * (n / 2)) / 8 = i / 8 := by omega
        have e2 : (i - 8 * (n / 2)) % 8 = i % 8 := by omega
        simp only [e1, e2]

@[csimp] theorem ofBytesLE_eq_ofBytesLEFast : @ofBytesLE = @ofBytesLEFast := by
  funext n v; exact (ofBytesLEFast_eq v).symm

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

/-- The first `n` bits of a byte string, read most significant bit first (FIPS 180-4 §3.1); the
unused low bits of the last byte are dropped. This is how SHAVS packs bit-oriented messages. -/
def ofBytesBEPrefix (n : Nat) (v : ByteVec len) : BitVec n :=
  (ofBytesBE v).extractLsb' (8 * len - n) n

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
