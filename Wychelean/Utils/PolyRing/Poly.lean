import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.Utils.PolyRing

/-- A polynomial of degree below `n`: its coefficient vector, `f[i]` the coefficient of `X^i`. -/
structure Poly (A : Type*) (n : ℕ) where
  coeffs : Vector A n
deriving DecidableEq

namespace Poly

variable {A : Type*} {n : ℕ}

def ofFn (f : Fin n → A) : Poly A n := ⟨Vector.ofFn f⟩

instance : GetElem (Poly A n) ℕ A fun _ i => i < n where
  getElem f i h := f.coeffs[i]

@[simp] theorem getElem_mk (v : Vector A n) (i : ℕ) (hi : i < n) : (⟨v⟩ : Poly A n)[i] = v[i] := rfl

@[simp] theorem coeffs_getElem (f : Poly A n) (i : ℕ) (hi : i < n) : f.coeffs[i] = f[i] := rfl

@[simp] theorem getElem_ofFn (f : Fin n → A) (i : ℕ) (hi : i < n) : (ofFn f : Poly A n)[i] = f ⟨i, hi⟩ :=
  Vector.getElem_ofFn ..

@[ext] theorem ext {f g : Poly A n} (h : ∀ (i : ℕ) (hi : i < n), f[i] = g[i]) : f = g := by
  cases f; cases g
  congr 1
  exact Vector.ext h

instance [Subsingleton A] : Subsingleton (Poly A n) :=
  ⟨fun _ _ => ext fun _ _ => Subsingleton.elim _ _⟩

instance : Subsingleton (Poly A 0) :=
  ⟨fun _ _ => ext fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

section Zero

variable [Zero A] {d : ℕ}

/-- `f` with `k` zero coefficients added on top. -/
def pad (k : ℕ) (f : Poly A n) : Poly A (k + n) :=
  ofFn fun i => if h : i.val < n then f[i.val] else 0

@[simp] theorem getElem_pad (k : ℕ) (f : Poly A n) (i : ℕ) (hi : i < k + n) :
    (pad k f)[i] = if h : i < n then f[i] else 0 :=
  getElem_ofFn ..

/-- `X^k · μ`. -/
def shift (k : ℕ) (μ : Poly A d) : Poly A (d + k) :=
  ofFn fun i => if h : k ≤ i.val then μ[i.val - k]'(by omega) else 0

@[simp] theorem getElem_shift (k : ℕ) (μ : Poly A d) (i : ℕ) (hi : i < d + k) :
    (shift k μ)[i] = if h : k ≤ i then μ[i - k]'(by omega) else 0 :=
  getElem_ofFn ..

end Zero

variable [CommRing A]

/-- The constant polynomial `a`. -/
def const (a : A) : Poly A n := ofFn fun i => if i.val = 0 then a else 0

instance : Zero (Poly A n) where zero := ⟨Vector.replicate n 0⟩
instance : One (Poly A n) where one := const 1
instance : Add (Poly A n) where add f g := ⟨Vector.zipWith (· + ·) f.coeffs g.coeffs⟩
instance : Sub (Poly A n) where sub f g := ⟨Vector.zipWith (· - ·) f.coeffs g.coeffs⟩
instance : Neg (Poly A n) where neg f := ⟨f.coeffs.map (- ·)⟩
instance : SMul A (Poly A n) where smul a f := ⟨f.coeffs.map (· * a)⟩

/-- The lower coefficients of `X^d - c`. -/
def binomial {d : ℕ} (c : A) : Poly A d := -const c

/-- The product modulo `X^n - c`: the convolution, terms of degree `n` or more wrapped around
with `X^n = c`. -/
def mulMod (c : A) (f g : Poly A n) : Poly A n :=
  ofFn fun k => ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = k.val then f[i] * g[j]
    else if i.val + j.val = k.val + n then c * (f[i] * g[j])
    else 0

@[simp] theorem getElem_zero (i : ℕ) (hi : i < n) : (0 : Poly A n)[i] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_const (a : A) (i : ℕ) (hi : i < n) :
    (const a : Poly A n)[i] = if i = 0 then a else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_one (i : ℕ) (hi : i < n) : (1 : Poly A n)[i] = if i = 0 then 1 else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_add (f g : Poly A n) (i : ℕ) (hi : i < n) : (f + g)[i] = f[i] + g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (f g : Poly A n) (i : ℕ) (hi : i < n) : (f - g)[i] = f[i] - g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_neg (f : Poly A n) (i : ℕ) (hi : i < n) : (-f)[i] = -f[i] :=
  Vector.getElem_map ..

@[simp] theorem getElem_smul (a : A) (f : Poly A n) (i : ℕ) (hi : i < n) : (a • f)[i] = f[i] * a :=
  Vector.getElem_map ..

@[simp] theorem getElem_binomial {d : ℕ} (c : A) (i : ℕ) (hi : i < d) :
    (binomial c : Poly A d)[i] = if i = 0 then -c else 0 := by
  rw [binomial, getElem_neg, getElem_const]
  split_ifs <;> simp

theorem getElem_mulMod (c : A) (f g : Poly A n) (k : ℕ) (hk : k < n) :
    (mulMod c f g)[k] = ∑ i : Fin n, ∑ j : Fin n,
      if i.val + j.val = k then f[i] * g[j]
      else if i.val + j.val = k + n then c * (f[i] * g[j])
      else 0 :=
  Vector.getElem_ofFn ..

/-- Degree one: the product of the values. -/
theorem getElem_mulMod_one (c : A) (f g : Poly A 1) : (mulMod c f g)[0] = f[0] * g[0] := by
  rw [getElem_mulMod]
  simp

/-- Degree two: `(a₀ + a₁X)(b₀ + b₁X) = (a₀b₀ + a₁b₁c) + (a₀b₁ + a₁b₀)X`
(FIPS 203 Algorithm 12). -/
theorem mulMod_two (c : A) (f g : Poly A 2) :
    mulMod c f g = ⟨#v[f[0] * g[0] + f[1] * g[1] * c, f[0] * g[1] + f[1] * g[0]]⟩ := by
  ext k hk
  rw [getElem_mulMod]
  interval_cases k
  · simp +decide [Fin.sum_univ_two]
    ring
  · simp +decide [Fin.sum_univ_two]

end Poly

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

end Wychelean.Utils.PolyRing
