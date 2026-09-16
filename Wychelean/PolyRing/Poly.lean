import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.PolyRing

/-- `A[X]/(X^n - c)`: the coefficient vector of the representative of degree below `n`. -/
structure Poly (A : Type*) (n : ℕ) (c : A) where
  coeffs : Vector A n
deriving DecidableEq

namespace Poly

variable {A : Type*} {n : ℕ} {c : A}

def ofFn (f : Fin n → A) : Poly A n c := ⟨Vector.ofFn f⟩

instance : GetElem (Poly A n c) ℕ A fun _ i => i < n where
  getElem f i h := f.coeffs[i]

@[simp] theorem getElem_mk (v : Vector A n) (i : ℕ) (hi : i < n) : (⟨v⟩ : Poly A n c)[i] = v[i] := rfl

@[simp] theorem coeffs_getElem (f : Poly A n c) (i : ℕ) (hi : i < n) : f.coeffs[i] = f[i] := rfl

@[simp] theorem getElem_ofFn (f : Fin n → A) (i : ℕ) (hi : i < n) :
    (ofFn f : Poly A n c)[i] = f ⟨i, hi⟩ :=
  Vector.getElem_ofFn ..

@[ext] theorem ext {f g : Poly A n c} (h : ∀ (i : ℕ) (hi : i < n), f[i] = g[i]) : f = g := by
  cases f; cases g
  congr 1
  exact Vector.ext h

variable [CommRing A]

/-- The constant polynomial `a`. -/
def const (a : A) : Poly A n c := ofFn fun i => if i.val = 0 then a else 0

instance : Zero (Poly A n c) where zero := ⟨Vector.replicate n 0⟩
instance : One (Poly A n c) where one := const 1
instance : Add (Poly A n c) where add f g := ⟨Vector.zipWith (· + ·) f.coeffs g.coeffs⟩
instance : Sub (Poly A n c) where sub f g := ⟨Vector.zipWith (· - ·) f.coeffs g.coeffs⟩
instance : Neg (Poly A n c) where neg f := ⟨f.coeffs.map (- ·)⟩
instance : SMul A (Poly A n c) where smul a f := ⟨f.coeffs.map (· * a)⟩

/-- The convolution, terms of degree `n` or more wrapped around with `X^n = c`. -/
instance : Mul (Poly A n c) where
  mul f g := ofFn fun k => ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = k.val then f[i] * g[j]
    else if i.val + j.val = k.val + n then c * (f[i] * g[j])
    else 0

@[simp] theorem getElem_zero (i : ℕ) (hi : i < n) : (0 : Poly A n c)[i] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_const (a : A) (i : ℕ) (hi : i < n) :
    (const a : Poly A n c)[i] = if i = 0 then a else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_one (i : ℕ) (hi : i < n) : (1 : Poly A n c)[i] = if i = 0 then 1 else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_add (f g : Poly A n c) (i : ℕ) (hi : i < n) : (f + g)[i] = f[i] + g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (f g : Poly A n c) (i : ℕ) (hi : i < n) : (f - g)[i] = f[i] - g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_neg (f : Poly A n c) (i : ℕ) (hi : i < n) : (-f)[i] = -f[i] :=
  Vector.getElem_map ..

@[simp] theorem getElem_smul (a : A) (f : Poly A n c) (i : ℕ) (hi : i < n) : (a • f)[i] = f[i] * a :=
  Vector.getElem_map ..

theorem getElem_mul (f g : Poly A n c) (k : ℕ) (hk : k < n) :
    (f * g)[k] = ∑ i : Fin n, ∑ j : Fin n,
      if i.val + j.val = k then f[i] * g[j]
      else if i.val + j.val = k + n then c * (f[i] * g[j])
      else 0 :=
  Vector.getElem_ofFn ..

/-- Degree one: the ring is `A` itself, `(a₀)(b₀) = a₀b₀`. -/
theorem getElem_mul_one (f g : Poly A 1 c) : (f * g)[0] = f[0] * g[0] := by
  rw [getElem_mul]
  simp

/-- Degree two: `(a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + a₁b₁c) + (a₀b₁ + a₁b₀)X`
(FIPS 203 Algorithm 12). -/
theorem mul_two (f g : Poly A 2 c) :
    f * g = ⟨#v[f[0] * g[0] + f[1] * g[1] * c, f[0] * g[1] + f[1] * g[0]]⟩ := by
  ext k hk
  rw [getElem_mul]
  interval_cases k
  · simp +decide [Fin.sum_univ_two]
    ring
  · simp +decide [Fin.sum_univ_two]

end Poly

/-- Vectors of `k` ring elements (FIPS 203 §2.4.4). -/
abbrev PolyVec (A : Type*) (n : ℕ) (c : A) (k : ℕ) := Vector (Poly A n c) k

/-! ### Vectors and matrices over any ring of entries -/

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

end Wychelean.PolyRing
