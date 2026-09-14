import Wychelean.KEM.MLKEM.Basic
import Wychelean.Lattice.NTTProperties
import Mathlib.Tactic.NormNum.Prime

/-!
# Properties of the ML-KEM arithmetic

The facts about ML-KEM's parameters that the library theorems need (`q = 3329` is an odd prime
and `ζ = 17` satisfies `ζ^128 = -1`), and the resulting statement that multiplying in the NTT
domain computes the product in `R_q = ℤ_q[X]/(X^256 + 1)`, for the residue forms of the
transform. The butterfly loops `ntt`/`nttInv` of `Lattice.NTT` are checked
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

/-- FIPS 203 Algorithms 11–12: residue `i` of `f̂ · ĝ` is the base-case product at
`γ = ζ^(2·BitRev₇(i) + 1)`. -/
theorem mul_residue («f̂» «ĝ» : NTTPolynomial) (i : ℕ) (hi : i < 128) :
    («f̂» * «ĝ»)[i] = #v[«f̂»[i][0] * «ĝ»[i][0] + «f̂»[i][1] * «ĝ»[i][1] * ζ ^ (2 * bitRev 7 i + 1),
                       «f̂»[i][0] * «ĝ»[i][1] + «f̂»[i][1] * «ĝ»[i][0]] :=
  EvalDomain.getElem_mul_two «f̂» «ĝ» i hi

end Wychelean.KEM.MLKEM
