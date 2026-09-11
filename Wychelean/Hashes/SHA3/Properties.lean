import Wychelean.Hashes.SHA3.Basic

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

end Internal

end Wychelean.Hashes.SHA3
