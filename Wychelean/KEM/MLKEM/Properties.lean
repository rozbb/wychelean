import Wychelean.KEM.MLKEM.Basic
import Wychelean.PolyRing.NTTProperties

/-!
# Properties of the ML-KEM arithmetic

ML-KEM's parameters instantiate the library: `q = 3329` is prime and `ζ = 17` is a primitive
256-th root of unity (`Basic`), so the transform the scheme runs is the closed form, multiplying
in the NTT domain computes the product in `R_q = ℤ_q[X]/(X^256 + 1)`, and a candidate NTT output
is characterised by its coefficients.
-/

namespace Wychelean.KEM.MLKEM

open Wychelean.PolyRing

/-- The transform the scheme runs (Algorithm 9 as a fold of layers) is the closed form:
residue `i` is `f mod (X² - ζ^(2·BitRev₇(i) + 1))`. -/
theorem ntt_eq_nttSpec (f : Polynomial) : (f.ntt : Tq) = NTT.nttSpec ζ f (by decide) :=
  NTT.ntt_eq_nttSpec 7 ζ f (by decide)

/-- FIPS 203 §4.3: multiplication in `T_q` (Algorithms 11–12) implements multiplication in `R_q`. -/
theorem nttInv_mul (f g : Polynomial) : (f.ntt * g.ntt : Tq).nttInv = f * g :=
  NTT.nttInv_mul ζ f g (by decide)

/-- FIPS 203 Algorithms 11–12: residue `i` of `f̂ · ĝ` is the base-case product at
`γ = ζ^(2·BitRev₇(i) + 1)`. -/
theorem mul_residue («f̂» «ĝ» : Tq) (i : Fin 128) :
    («f̂» * «ĝ») i = ⟨#v[(«f̂» i)[0] * («ĝ» i)[0] + («f̂» i)[1] * («ĝ» i)[1] * ζ.val ^ (2 * bitRev 7 i + 1),
                       («f̂» i)[0] * («ĝ» i)[1] + («f̂» i)[1] * («ĝ» i)[0]]⟩ :=
  Residues.mul_two «f̂» «ĝ» i

/-- A candidate NTT output is the transform of `f` iff each residue has the coefficients
`f[x] + f[x + 2] γᵢ + f[x + 4] γᵢ² + …`, which an external verifier can check without running
the butterflies. -/
theorem ntt_eq_iff (f : Polynomial) (a : Tq) :
    f.ntt = a ↔ ∀ (i : Fin 128) (x : ℕ) (hx : x < 2),
      (a i)[x]'hx = ∑ t : Fin 128,
        f[x + 2 * t.val]'(by omega) * (ζ.val ^ (2 * bitRev 7 i + 1)) ^ t.val :=
  NTT.ntt_eq_iff' ζ rfl f (by decide) a

theorem nttInv_eq_iff (a : Tq) (f : Polynomial) : a.nttInv = f ↔ f.ntt = a :=
  NTT.nttInv_eq_iff ζ a (by decide) f

end Wychelean.KEM.MLKEM
