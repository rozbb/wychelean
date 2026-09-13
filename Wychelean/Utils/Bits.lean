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
