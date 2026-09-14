import Wychelean.KEM.MLKEM.Basic
import Wychelean.Lattice.NTTProperties
import Mathlib.Tactic.NormNum.Prime

/-!
# Properties of the ML-KEM arithmetic

The facts about ML-KEM's parameters that the library theorems need (`q = 3329` is an odd prime
and `ζ = 17` satisfies `ζ^128 = -1`), and the resulting statement that multiplying in the NTT
domain computes the product in `R_q = ℤ_q[X]/(X^256 + 1)`, for the residue forms of the
transform. The butterfly loops `NTT`/`NTTInv` and `MultiplyNTTs` of `Basic.lean` are checked
against those forms by the Lattice test suite; proving them equal is future work.
-/

namespace Wychelean.KEM.MLKEM

open Wychelean.Lattice

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

instance : Fact (2 < q) := ⟨by decide⟩

/-- `ζ^128 = -1`: `ζ = 17` is a primitive 256-th root of unity (§4.3). -/
theorem ζ_pow_128 : ζ ^ 2 ^ 7 = -1 := by decide +kernel

/-- FIPS 203 §4.3: multiplication in `T_q` (Algorithms 11–12) implements multiplication in `R_q`,
stated for the residue form of the transform. -/
theorem nttInvSpec_mul (f g : Polynomial) :
    NTT.nttInvSpec ζ 7 (NTT.nttSpec ζ 7 f * NTT.nttSpec ζ 7 g) = f * g :=
  NTT.nttInvSpec_mul ζ (by decide) ζ_pow_128 f g

end Wychelean.KEM.MLKEM
