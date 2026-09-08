import Mathlib.Data.List.Defs
import Mathlib.Tactic.GCongr

/-!
Compatibility excerpt from Microsoft SymCrypt, Spec/Defs.lean at
c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be. See LICENSE.SymCrypt.
Only the definitions needed by SHA3 are retained; Byte replaces Aeneas's identical alias.
-/
abbrev Byte := BitVec 8
namespace Spec
/-- Rotate a vector at the index level: output[i] = input[(i + n - k) % n].
    Used by FIPS 202 (SHA-3) where index 0 is the least significant bit.
    For big-endian contexts (index 0 = MSB), use `Bits.rotlBE`. -/
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
abbrev 𝔹 := Vector Byte
def Bits.zeroExtend (v : Vector Bool n) (m : Nat) : Vector Bool m :=
  Vector.ofFn fun (i : Fin m) => if h : i.val < n then v[i.val] else false

def Bits.ofNatLE {n : Nat} (val : Nat) : Vector Bool n :=
  Vector.ofFn fun (i : Fin n) => (val >>> i.val) % 2 != 0

def bitsToBytes {ℓ : Nat} (b : Vector Bool (8 * ℓ)) : 𝔹 ℓ :=
  Vector.ofFn fun ⟨i, _⟩ =>
    Fin.foldl 8 (fun (acc : Byte) (j : Fin 8) =>
      acc + b[8 * i + j.val].toNat * (2 ^ j.val)) 0

def bytesToBits {ℓ : Nat} (B : 𝔹 ℓ) : Vector Bool (8 * ℓ) :=
  Vector.ofFn fun ⟨i, _⟩ => B[i / 8].toNat.testBit (i % 8)

def slice {n : ℕ} (v : Vector α n) (off len : ℕ) (h : off + len ≤ n := by grind) : Vector α len :=
  Vector.ofFn fun i => v[off + i]

end Spec
