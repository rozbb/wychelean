import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

/-!
Vectors and matrices over any ring of entries (FIPS 203 §2.4.7–§2.4.8, FIPS 204 §2.3).
-/

namespace Wychelean.Utils.Linear

section Linear

variable {α : Type*} {k l : ℕ}

scoped instance [Add α] : Add (Vector α k) where add v w := Vector.zipWith (· + ·) v w
scoped instance [Sub α] : Sub (Vector α k) where sub v w := Vector.zipWith (· - ·) v w
scoped instance [Neg α] : Neg (Vector α k) where neg v := v.map (- ·)
scoped instance [Mul α] : SMul α (Vector α k) where smul a v := v.map (a * ·)

/-- `∑ᵢ v[i] * w[i]`. -/
def innerProduct [Mul α] [Add α] [Zero α] (v w : Vector α k) : α :=
  (Vector.zipWith (· * ·) v w).foldl (· + ·) 0

@[inherit_doc innerProduct]
scoped notation:max "⟪" v ", " w "⟫" => innerProduct v w

/-- `k × l` matrices as vectors of `k` rows of length `l` (FIPS 203 §2.4.5, FIPS 204 §2.3). -/
abbrev Mat (α : Type*) (k l : ℕ) := Vector (Vector α l) k

namespace Mat

/-- `Mᵀ`. -/
def transpose (M : Mat α k l) : Mat α l k :=
  Vector.ofFn fun i => Vector.ofFn fun j => M[j][i]

/-- `M · v`. -/
def mulVec [Mul α] [Add α] [Zero α] (M : Mat α k l) (v : Vector α l) : Vector α k :=
  M.map fun row => innerProduct row v

end Mat

@[inherit_doc Mat.transpose]
scoped postfix:max "ᵀ" => Mat.transpose

/-- `M * v` is the matrix-vector product. -/
@[default_instance]
instance [Mul α] [Add α] [Zero α] : HMul (Mat α k l) (Vector α l) (Vector α k) where
  hMul := Mat.mulVec

end Linear

end Wychelean.Utils.Linear
