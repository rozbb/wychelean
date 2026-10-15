module

public import Wychelean.Hashes.SHA3.Basic

@[expose] public section

namespace Wychelean.Hashes.SHA3
open Wychelean

namespace Internal

/-! ## Sponge properties -/

/-- Padded input consists of whole rate blocks (FIPS 202 §5.1). -/
theorem padLen_dvd (r n : Nat) (hr : 0 < r := by grind) : (n + padLen r n) % r = 0 := by
  simp only [padLen, padLen.j]
  have hnn : (-(↑n : Int) - 2) % ↑r ≥ 0 := Int.emod_nonneg _ (by omega)
  have h_eq : (n : Int) + (1 + ((-(↑n : Int) - 2) % ↑r).toNat + 1) =
    ((-(↑n : Int) - 2) % ↑r + ↑n + 2) := by omega
  have h_mod : ((-(↑n : Int) - 2) % ↑r + ↑n + 2) % ↑r = 0 := by
    have := Int.emod_add_mul_ediv (-(n : Int) - 2) r
    rw [show (-(↑n : Int) - 2) % ↑r + ↑n + 2 = -(↑r * ((-(↑n : Int) - 2) / ↑r)) from by omega]
    exact Int.neg_mul_emod_right r _
  grind

/-- FIPS 202 §5.1 mandates both a leading and trailing one. -/
theorem padLen_ge_two (r n : Nat) : 2 ≤ padLen r n := by simp [padLen]

theorem pad_last (r n : Nat) : («pad10*1» r n)[padLen r n - 1]'(by simp [padLen]) = true := by
  simp [«pad10*1», padLen, BitVec.getElem_append]

/-- The padding length depends on the message length only modulo the rate. -/
theorem padLen.j_mod (r n : Nat) : padLen.j r (n % r) = padLen.j r n := by
  simp only [padLen.j, Int.natCast_emod, Int.emod_def (n : Int) r]
  generalize (n : Int) / r = q
  rw [show -((n : Int) - r * q) - 2 = (-(n : Int) - 2) + r * q by omega, Int.add_mul_emod_self_left]

/-- Padding with the same number of zeros gives the same bits. -/
theorem toList_toBitsLE_pad {r m m' : Nat} (h : padLen.j r m = padLen.j r m') :
    (BitVec.toBitsLE («pad10*1» r m)).toList = (BitVec.toBitsLE («pad10*1» r m')).toList := by
  have : ∀ J J' : Nat, J = J' →
      (BitVec.toBitsLE ((1 : BitVec 1) ++ (0 : BitVec J) ++ (1 : BitVec 1))).toList =
        (BitVec.toBitsLE ((1 : BitVec 1) ++ (0 : BitVec J') ++ (1 : BitVec 1))).toList := by
    intros; subst_vars; rfl
  exact this _ _ h

end Internal

end Wychelean.Hashes.SHA3
