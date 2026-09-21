import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod
import Wychelean.Utils.PolyRing.NTT

namespace Wychelean.KEM.MLKEM

open Wychelean

/-! ## §2.4 / §8 Constants and Parameters (Table 2) -/

/- `ByteVec n` (from Defs) is the standard interface type in FIPS 203. -/

/-- q = 3329, the modulus for ML-KEM (§2). -/
abbrev q : Nat := 3329

/-- ℤ_q = ℤ/3329ℤ, the coefficient ring. -/
abbrev Zq := ZMod q

/-- `ℤ_m[X] / (X^256 + 1)`: `R_q` for `m = q`, and the compressed coefficients for `m = 2^d`
(§4.2.1). -/
abbrev Polynomial (m : ℕ := q) := Utils.PolyRing.PolyMod (ZMod m) 256 (-1)

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- ζ = 17 ∈ ℤ_q is a primitive 256-th root of unity modulo q (§4.3), from `ζ^128 = -1`. -/
def ζ : Utils.PolyRing.PrimitiveRoot Zq (2 ^ 8) :=
  Utils.PolyRing.PrimitiveRoot.ofPowEqNegOne 17 (by decide +kernel) (by decide)

/-- `T_q`, the NTT representation of `R_q` (§2.4.6). -/
structure Tq where
  coeffs : Vector Zq 256
deriving DecidableEq

namespace Tq

abbrev flatten (a : Tq) : Vector Zq 256 := a.coeffs

instance : GetElem Tq ℕ Zq (fun _ i => i < 256) where
  getElem a i h := a.coeffs[i]

/-- The quadratic component at `X² - ζ^(2·BitRev₇(i)+1)`. -/
def component (a : Tq) (i : Fin 128) : Utils.PolyRing.Poly Zq 2 :=
  Utils.PolyRing.Poly.ofFn fun r => a[r.val + 2 * i.val]'(by omega)

instance : CoeFun Tq (fun _ => Fin 128 → Utils.PolyRing.Poly Zq 2) := ⟨component⟩

@[ext] theorem ext {a b : Tq} (h : ∀ (i : ℕ) (hi : i < 256), a[i] = b[i]) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext h

instance : Zero Tq := ⟨⟨Vector.replicate 256 0⟩⟩
instance : One Tq := ⟨⟨Vector.ofFn fun i => if i.val % 2 = 0 then 1 else 0⟩⟩
instance : Add Tq := ⟨fun a b => ⟨Vector.zipWith (· + ·) a.coeffs b.coeffs⟩⟩
instance : Sub Tq := ⟨fun a b => ⟨Vector.zipWith (· - ·) a.coeffs b.coeffs⟩⟩
instance : Neg Tq := ⟨fun a => ⟨a.coeffs.map (- ·)⟩⟩
instance : SMul Zq Tq := ⟨fun c a => ⟨a.coeffs.map (c * ·)⟩⟩

end Tq

instance : Fact (2 ^ 7 ∣ 256) := ⟨by decide⟩

/-- m(d) = 2^d if d < 12, q if d = 12 (§4.2.1). -/
abbrev m (d : ℕ) := if d < 12 then 2^d else q

/-- ML-KEM parameter sets (§8, Table 2).
    ML-KEM-512, ML-KEM-768, and ML-KEM-1024 correspond to
    NIST security categories 1, 3, and 5 respectively. -/
inductive ParameterSet where
  | ML_KEM_512
  | ML_KEM_768
  | ML_KEM_1024

/-- Module rank `k` (Table 2): dimension of the polynomial module lattice. -/
abbrev K := {k : ℕ // k ∈ ({2, 3, 4} : Set ℕ)}
/-- CBD noise parameter type: η ∈ {2, 3} (Table 2). -/
abbrev Η := {η : ℕ // η ∈ ({2, 3} : Set ℕ)}

/-- Module rank k: 2 for ML-KEM-512, 3 for 768, 4 for 1024 (Table 2). -/

@[reducible, scoped grind] def k (p : ParameterSet) : K :=
  match p with
  | .ML_KEM_512  => ⟨2, by grind⟩
  | .ML_KEM_768  => ⟨3, by grind⟩
  | .ML_KEM_1024 => ⟨4, by grind⟩

/-- CBD noise parameter η₁ (Table 2): 3 for ML-KEM-512, 2 for 768/1024. -/
@[reducible] def η₁ (p : ParameterSet) : Η :=
  match p with
  | .ML_KEM_512  => ⟨3, by grind⟩
  | .ML_KEM_768  => ⟨2, by grind⟩
  | .ML_KEM_1024 => ⟨2, by grind⟩

/-- CBD noise parameter η₂ = 2 for all parameter sets (Table 2). -/
def η₂ : Η := ⟨2, by grind⟩

/-- Ciphertext compression parameter dᵤ (Table 2): 10 for 512/768, 11 for 1024. -/
@[reducible] def dᵤ (p : ParameterSet) : ℕ :=
  match p with
  | .ML_KEM_512  => 10
  | .ML_KEM_768  => 10
  | .ML_KEM_1024 => 11

/-- Ciphertext compression parameter dᵥ (Table 2): 4 for 512/768, 5 for 1024. -/
@[reducible] def dᵥ (p : ParameterSet) : ℕ :=
  match p with
  | .ML_KEM_512  => 4
  | .ML_KEM_768  => 4
  | .ML_KEM_1024 => 5

/-! ### Sizes in bytes (Table 3) -/

/-- Seeds, messages and shared secret keys are 32 bytes (§3.3, §7). -/
abbrev seedLen : ℕ := 32
abbrev Seed := ByteVec seedLen
abbrev SharedKey := ByteVec seedLen
/-- The outputs of `H`, `J` and each half of `G` are 32 bytes (§4.1). -/
abbrev hashLen : ℕ := 32
/-- `ByteEncode₁₂` of a vector of `k` polynomials: `384k`. -/
abbrev vecLen' (k : K) : ℕ := 384 * k
abbrev vecLen (p : ParameterSet) : ℕ := vecLen' (k p)
/-- K-PKE encryption key: the encoded `t̂` and the seed `ρ`. -/
abbrev ekPKELen (p : ParameterSet) : ℕ := vecLen p + seedLen
/-- K-PKE decryption key: the encoded `ŝ`. -/
abbrev dkPKELen (p : ParameterSet) : ℕ := vecLen p
/-- ML-KEM encapsulation key: the K-PKE encryption key. -/
abbrev ekLen (p : ParameterSet) : ℕ := ekPKELen p
/-- ML-KEM decapsulation key: `dkPKE ‖ ek ‖ H(ek) ‖ z`, i.e. `768k + 96`. -/
abbrev dkLen (p : ParameterSet) : ℕ := dkPKELen p + ekLen p + hashLen + seedLen
/-- First ciphertext component, `ByteEncode_dᵤ` of a compressed vector. -/
abbrev c₁Len (p : ParameterSet) : ℕ := 32 * dᵤ p * k p
/-- Second ciphertext component, `ByteEncode_dᵥ` of a compressed polynomial. -/
abbrev c₂Len (p : ParameterSet) : ℕ := 32 * dᵥ p
/-- Ciphertext: `32(dᵤk + dᵥ)`. -/
abbrev ctLen (p : ParameterSet) : ℕ := c₁Len p + c₂Len p

/-! ## Vectors and Matrices of Polynomials (§2.4.4–§2.4.8) -/

abbrev PolyVector (m : ℕ) (k : K) := Utils.PolyRing.PolyVec (ZMod m) 256 (-1) k

/-- Vectors and matrices over `T_q` (§2.4.7–§2.4.8). -/
abbrev NTTVector (k : K) := Vector Tq k
abbrev NTTMatrix (k : K) := Utils.PolyRing.Mat Tq k k


end Wychelean.KEM.MLKEM
