import Wychelean.Utils.Bytes
import Wychelean.Utils.Vector

/-!
Bits and Boolean-string operations used by bit-oriented specifications.
The rotation, notations, extension, and slicing definitions are adapted from Microsoft SymCrypt:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/Defs.lean
MIT notice: Wychelean/Hashes/SHA3/LICENSE.SymCrypt.
-/
namespace Wychelean

/-- Replace the bit at LSB index `i`; an index outside the vector leaves it unchanged. -/
def _root_.BitVec.setBit (v : BitVec n) (i : Nat) (bit : Bit) : BitVec n :=
  if bit then v ||| (1#n <<< i) else v &&& ~~~(1#n <<< i)

@[simp] theorem _root_.BitVec.getLsbD_setBit (v : BitVec n) (i : Nat) (bit : Bit) (j : Nat) :
    (v.setBit i bit).getLsbD j = if j = i ∧ i < n then bit else v.getLsbD j := by
  simp only [BitVec.setBit]
  by_cases hj : j < n
  · by_cases hji : j = i
    · subst hji
      cases bit <;> simp [hj]
    · cases bit <;> simp [BitVec.getLsbD_shiftLeft, hji, Nat.sub_eq_zero_iff_le]
      <;> omega
  · cases bit <;> simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hj)] <;> omega

/-- Rotate a vector at the index level: output[i] = input[(i + n - (k % n)) % n].
    Used by FIPS 202 (SHA3), where index zero is the least significant bit. -/
def _root_.Vector.rotateLeft (v : Vector α n) (k : Nat) : Vector α n :=
  if h : n = 0 then v
  else Vector.ofFn fun (i : Fin n) => v[(i.val + n - k % n) % n]'(Nat.mod_lt _ (by omega))

namespace Notations
scoped instance : OfNat Bool 0 := ⟨false⟩
scoped instance : OfNat Bool 1 := ⟨true⟩
scoped macro_rules
| `(tactic| get_elem_tactic) => `(tactic| grind)
scoped infixl:65 " ‖ " => Vector.append
/-- Specifications write small counters directly as bytes, e.g. `(i : Byte)`; the cast wraps
modulo 256 like `UInt8.ofNat`. Scoped, as Mathlib scopes its `UIntX` casts, because a global
cast into `UInt8` interferes with coercion elaboration. -/
scoped instance : NatCast Byte := ⟨UInt8.ofNat⟩
scoped instance : HXor (Vector Bit n) (Vector Bit n) (Vector Bit n) :=
  ⟨Vector.zipWith (· != ·)⟩
scoped instance : HAnd (Vector Bit n) (Vector Bit n) (Vector Bit n) :=
  ⟨Vector.zipWith (· && ·)⟩
scoped instance : Complement (Vector Bit n) := ⟨Vector.map (!·)⟩
end Notations
open Notations
def Bits.zeroExtend (v : Vector Bit n) (m : Nat) : Vector Bit m :=
  Vector.ofFn fun (i : Fin m) => if h : i.val < n then v[i.val] else false

def Bits.ofNatLE {n : Nat} (val : Nat) : Vector Bit n :=
  Vector.ofFn fun (i : Fin n) => (val >>> i.val) % 2 != 0

def slice {n : ℕ} (v : Vector α n) (off len : ℕ) (h : off + len ≤ n := by grind) : Vector α len :=
  Vector.ofFn fun i => v[off + i]

/-- The prefix of length `a` and the suffix of length `b`; the inverse of `‖`. -/
def split {n : ℕ} (v : Vector α n) (a b : ℕ) (h : n = a + b := by first | rfl | omega) :
    Vector α a × Vector α b :=
  (slice v 0 a (by omega), slice v a b (by omega))

/-! ## Bit reversal

`bitRev n i` reverses the `n` least-significant bits of `i` (FIPS 203 §2.3, BitRev₇).
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/NatBit.lean
`Nat.ofBitsList` is spelled out directly; upstream uses Aeneas' `Nat.ofBits`. -/

/-- The `n` least-significant bits of `x`, least significant first. -/
def _root_.Nat.bitsn (x n : ℕ) : Vector Bool n := Vector.ofFn fun i => x.testBit i

/-- The number whose bits, least significant first, are `bits`. -/
def _root_.Nat.ofBitsList (bits : List Bool) : Nat :=
  bits.foldr (fun b acc => 2 * acc + b.toNat) 0

/-- Reverse the `n` least-significant bits of `i` (FIPS 203 BitRev₇). -/
def bitRev (n : Nat) (i : Nat) : Nat :=
  let bits := i.bitsn n
  let bits := List.reverse bits.toList
  Nat.ofBitsList bits

#guard List.map (bitRev 2) [0, 1, 2, 3] = [0, 2, 1, 3]
#guard List.map (bitRev 3) [0, 1, 2, 3, 4, 5, 6, 7] = [0, 4, 2, 6, 1, 5, 3, 7]

theorem Nat.ofBitsList_lt (bits : List Bool) : Nat.ofBitsList bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [Nat.ofBitsList]
  | cons b bits ih =>
    simp only [Nat.ofBitsList, List.foldr_cons, List.length_cons, Nat.pow_succ]
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [Nat.ofBitsList] at ih
    omega

theorem Nat.testBit_ofBitsList (bits : List Bool) (j : ℕ) :
    (Nat.ofBitsList bits).testBit j = bits.getD j false := by
  induction bits generalizing j with
  | nil => simp [Nat.ofBitsList]
  | cons b bits ih =>
    simp only [Nat.ofBitsList, List.foldr_cons]
    cases j with
    | zero => cases b <;> simp [Nat.testBit_zero]
    | succ j =>
      rw [List.getD_cons_succ, ← ih]
      simp only [Nat.ofBitsList]
      rw [Nat.testBit_succ, show 2 * List.foldr (fun b acc => 2 * acc + b.toNat) 0 bits + b.toNat =
        b.toNat + 2 * List.foldr (fun b acc => 2 * acc + b.toNat) 0 bits by omega,
        Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by cases b <;> decide), Nat.zero_add]

theorem bitRev_lt (n i : ℕ) : bitRev n i < 2 ^ n := by
  have := Nat.ofBitsList_lt (List.reverse (i.bitsn n).toList)
  simpa [bitRev] using this

theorem testBit_bitRev (n i j : ℕ) (hj : j < n) :
    (bitRev n i).testBit j = i.testBit (n - 1 - j) := by
  simp only [bitRev, Nat.testBit_ofBitsList, Nat.bitsn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_reverse]
  simp

theorem Nat.ofBitsList_append (xs ys : List Bool) :
    Nat.ofBitsList (xs ++ ys) = Nat.ofBitsList xs + 2 ^ xs.length * Nat.ofBitsList ys := by
  induction xs with
  | nil => simp [Nat.ofBitsList]
  | cons b xs ih =>
    simp only [List.cons_append, List.length_cons, Nat.pow_succ]
    simp only [Nat.ofBitsList, List.foldr_cons] at ih ⊢
    rw [ih, Nat.mul_add, Nat.mul_comm (2 ^ xs.length) 2, Nat.mul_assoc]
    omega

/-- The low bit of `i` becomes the top bit of its reversal. -/
theorem bitRev_succ (n i : ℕ) : bitRev (n + 1) i = bitRev n (i / 2) + 2 ^ n * (i % 2) := by
  simp only [bitRev, Nat.bitsn, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
    Nat.testBit_succ, List.reverse_cons, Nat.ofBitsList_append, List.length_reverse, List.length_ofFn]
  congr 2
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [Nat.ofBitsList, Nat.testBit_zero, h]

theorem bitRev_zero (i : ℕ) : bitRev 0 i = 0 := rfl

/-- The low `b` bits of `i` become the top `b` bits of its `(l + b)`-bit reversal, above the
reversal of the next `l` bits. -/
theorem bitRev_add (l b i : ℕ) :
    bitRev (l + b) i = bitRev l (i / 2 ^ b) + 2 ^ l * bitRev b (i % 2 ^ b) := by
  induction b generalizing i with
  | zero => simp [bitRev_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, bitRev_succ, ih, bitRev_succ, Nat.div_div_eq_div_mul, Nat.pow_succ',
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ ⟨2 ^ b, rfl⟩, Nat.pow_add, Nat.mul_add,
      Nat.add_assoc, Nat.mul_assoc]

theorem bitRev_zero_right (n : ℕ) : bitRev n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bitRev_succ, Nat.zero_div, ih]; rfl

/-- Reversing the low `n` bits twice gives the number back (for numbers below `2^n`). -/
theorem bitRev_bitRev (n i : ℕ) (hi : i < 2 ^ n) : bitRev n (bitRev n i) = i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · rw [testBit_bitRev _ _ _ hj, testBit_bitRev _ _ _ (by omega)]
    congr 1
    omega
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (bitRev_lt n _) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega)))]

end Wychelean

/-- The bit-vector rotation agrees with the index-level rotation of Boolean vectors. -/
theorem BitVec.ofBitsLE_rotateLeft (v : Vector Wychelean.Bit n) (k : Nat) :
    BitVec.ofBitsLE (v.rotateLeft k) = (BitVec.ofBitsLE v).rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : n ≠ 0 := by omega
  have hk : k % n < n := Nat.mod_lt _ (by omega)
  rw [BitVec.getLsbD_ofBitsLE _ _ hi, BitVec.getLsbD_rotateLeft]
  simp only [Vector.rotateLeft, hn, ↓reduceDIte, Vector.getElem_ofFn]
  split
  · rename_i h
    rw [BitVec.getLsbD_ofBitsLE _ _ (by omega)]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    rw [BitVec.getLsbD_ofBitsLE _ _ (by omega)]
    simp only [hi, decide_true, Bool.true_and]
    congr 1
    rw [show i + n - k % n = (i - k % n) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
