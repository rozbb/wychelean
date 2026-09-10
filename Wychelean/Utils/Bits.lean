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
def _root_.BitVec.setBit (v : BitVec n) (i : Nat) (bit : Bool) : BitVec n :=
  BitVec.ofBitsLE (Vector.ofFn fun j => if j.val = i then bit else v[j.val])

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
scoped instance : HXor (Vector Bool n) (Vector Bool n) (Vector Bool n) :=
  ⟨Vector.zipWith (· != ·)⟩
scoped instance : HAnd (Vector Bool n) (Vector Bool n) (Vector Bool n) :=
  ⟨Vector.zipWith (· && ·)⟩
scoped instance : Complement (Vector Bool n) := ⟨Vector.map (!·)⟩
end Notations
open Notations
def Bits.zeroExtend (v : Vector Bool n) (m : Nat) : Vector Bool m :=
  Vector.ofFn fun (i : Fin m) => if h : i.val < n then v[i.val] else false

def Bits.ofNatLE {n : Nat} (val : Nat) : Vector Bool n :=
  Vector.ofFn fun (i : Fin n) => (val >>> i.val) % 2 != 0

def slice {n : ℕ} (v : Vector α n) (off len : ℕ) (h : off + len ≤ n := by grind) : Vector α len :=
  Vector.ofFn fun i => v[off + i]

end Wychelean

/-- The bit-vector rotation agrees with the index-level rotation of Boolean vectors. -/
theorem BitVec.ofBitsLE_rotateLeft (v : Vector Bool n) (k : Nat) :
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
