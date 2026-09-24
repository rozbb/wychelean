import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod
import Wychelean.Utils.Matrix
import Wychelean.Utils.Bits

namespace Wychelean.KEM.MLKEM

open Wychelean

/-! ## §2.4 / §8 Constants and Parameters (Table 2) -/

/- `ByteVec n` (from Defs) is the standard interface type in FIPS 203. -/

/-- q = 3329, the modulus for ML-KEM (§2). -/
abbrev q : Nat := 3329

/-- ℤ_q = ℤ/3329ℤ, the coefficient ring. -/
abbrev Zq := ZMod q

/-- Coefficient array `(f₀, …, f₂₅₅)` over `ℤ_m` (§2.4.4). -/
structure Polynomial (m : ℕ := q) where
  coeffs : Vector (ZMod m) 256
deriving DecidableEq

namespace Polynomial

variable {m : ℕ}

/-- `f[i]` is the `i`-th coefficient `fᵢ` (§2.4.4). -/
instance : GetElem (Polynomial m) ℕ (ZMod m) (fun _ i => i < 256) where
  getElem f i h := f.coeffs[i]

@[simp] theorem getElem_mk (v : Vector (ZMod m) 256) (i : ℕ) (h : i < 256) :
    (Polynomial.mk v)[i] = v[i] := rfl

def ofFn (f : Fin 256 → ZMod m) : Polynomial m := ⟨Vector.ofFn f⟩

@[ext] theorem ext {f g : Polynomial m} (h : ∀ (i : ℕ) (hi : i < 256), f[i] = g[i]) : f = g := by
  cases f; cases g
  congr 1
  exact Vector.ext h

/-- Addition is coordinate-wise (§2.4.5, Eq. 2.3). -/
instance : Zero (Polynomial m) := ⟨⟨Vector.replicate 256 0⟩⟩
instance : Add (Polynomial m) := ⟨fun f g => ⟨Vector.zipWith (· + ·) f.coeffs g.coeffs⟩⟩
instance : Sub (Polynomial m) := ⟨fun f g => ⟨Vector.zipWith (· - ·) f.coeffs g.coeffs⟩⟩
instance : Neg (Polynomial m) := ⟨fun f => ⟨f.coeffs.map (- ·)⟩⟩

end Polynomial

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- ζ = 17 ∈ ℤ_q, a primitive 256-th root of unity modulo q (§4.3). -/
def ζ : Zq := 17

/-- An element of `T_q` (§4.3, Eq. 4.11), represented by the array
`(ĝ₀,₀, ĝ₀,₁, …, ĝ₁₂₇,₀, ĝ₁₂₇,₁)` (§2.4.4, Eq. 2.7). -/
structure Tq where
  coeffs : Vector Zq 256
deriving DecidableEq

namespace Tq

instance : GetElem Tq ℕ Zq (fun _ i => i < 256) where
  getElem a i h := a.coeffs[i]

@[simp] theorem getElem_mk (v : Vector Zq 256) (i : ℕ) (h : i < 256) : (Tq.mk v)[i] = v[i] := rfl

@[ext] theorem ext {a b : Tq} (h : ∀ (i : ℕ) (hi : i < 256), a[i] = b[i]) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext h

/-- Addition is coordinate-wise (§2.4.5); multiplication is `MultiplyNTTs` (Eq. 2.8). -/
instance : Zero Tq := ⟨⟨Vector.replicate 256 0⟩⟩
instance : Add Tq := ⟨fun a b => ⟨Vector.zipWith (· + ·) a.coeffs b.coeffs⟩⟩
instance : Sub Tq := ⟨fun a b => ⟨Vector.zipWith (· - ·) a.coeffs b.coeffs⟩⟩
instance : Neg Tq := ⟨fun a => ⟨a.coeffs.map (- ·)⟩⟩

end Tq

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

abbrev PolyVector (m : ℕ) (k : K) := Vector (Polynomial m) k

/-- Vectors and matrices over `T_q` (§2.4.7–§2.4.8). -/
abbrev NTTVector (k : K) := Vector Tq k
abbrev NTTMatrix (k : K) := Utils.Linear.Mat Tq k k


end Wychelean.KEM.MLKEM
