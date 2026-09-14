import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Polynomials modulo X^n + 1

Elements of `A[X] / (X^n + 1)` over a commutative coefficient ring `A` (`ℤ`, or `ℤ_q`) as
coefficient vectors, with the pointwise operations and the negacyclic product, shared by the
module-lattice schemes (FIPS 203 §2.4, FIPS 204 §2.3).
The pointwise definitions are adapted from Microsoft SymCrypt (MIT; see
Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.Lattice

/-- A polynomial of degree below `n` with coefficients in `A`, coefficient `i` at index `i`;
read modulo `X^n + 1`. -/
abbrev Poly (A : Type) (n : ℕ) := Vector A n

namespace Poly

variable {A : Type} [CommRing A] {n : ℕ}

def zero : Poly A n := Vector.replicate n 0

/-- Pointwise addition.

The body uses `Vector.zipWith` rather than the seemingly-equivalent
`Vector.ofFn (fun i => f[i] + g[i])`. This is a *grind workaround*: the latter shape causes
`grind`'s `whnf` to descend through `Vector.ofFn`'s lambda and infinitely unfold `Add` on the
element type, blowing `maxRecDepth` on any goal containing `_ + _ : Poly A n`. `Vector.zipWith`
avoids it because its body is a non-recursive `Array.zipWith` wrapper that `whnf` does not
recurse into. -/
def add (f g : Poly A n) : Poly A n := Vector.zipWith (· + ·) f g

/-- Pointwise subtraction. See `add` for the `zipWith` rationale. -/
def sub (f g : Poly A n) : Poly A n := Vector.zipWith (· - ·) f g

/-- Multiplication by a scalar. -/
def scalarMul (f : Poly A n) (c : A) : Poly A n := f.map fun v => v * c

/-- The product in `ℤ_q[X] / (X^n - c)`: the convolution of the coefficients, with the terms of
degree `n` or more wrapped around and multiplied by `c` since `X^n = c`. -/
def mulBinomial (c : A) (f g : Poly A n) : Poly A n :=
  Vector.ofFn fun k => ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = k.val then f[i] * g[j]
    else if i.val + j.val = k.val + n then c * (f[i] * g[j])
    else 0

/-- The product in `ℤ_q[X] / (X^n + 1)`, the case `c = -1`. -/
def mul (f g : Poly A n) : Poly A n := mulBinomial (-1) f g

/-- The constant polynomial `c`. -/
def const (c : A) : Poly A n := Vector.ofFn fun i => if i.val = 0 then c else 0

/-- Pointwise negation. -/
def neg (f : Poly A n) : Poly A n := f.map (- ·)

instance : Zero (Poly A n) where zero := zero
instance : One (Poly A n) where one := const 1
instance : Add (Poly A n) where add := add
instance : Sub (Poly A n) where sub := sub
instance : Neg (Poly A n) where neg := neg
instance : Mul (Poly A n) where mul := mul
instance : SMul A (Poly A n) where smul c f := scalarMul f c
instance : NatCast (Poly A n) where natCast k := const k
instance : IntCast (Poly A n) where intCast k := const k
instance : SMul ℕ (Poly A n) where smul k f := scalarMul f k
instance : SMul ℤ (Poly A n) where smul k f := scalarMul f k
instance : Pow (Poly A n) ℕ where pow f k := npowRec k f

@[simp] theorem getElem_zero (i : ℕ) (hi : i < n) : (0 : Poly A n)[i] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_const (c : A) (i : ℕ) (hi : i < n) :
    (const c : Poly A n)[i] = if i = 0 then c else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_one (i : ℕ) (hi : i < n) : (1 : Poly A n)[i] = if i = 0 then 1 else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_natCast (k : ℕ) (i : ℕ) (hi : i < n) :
    ((k : ℕ) : Poly A n)[i] = if i = 0 then (k : A) else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_intCast (k : ℤ) (i : ℕ) (hi : i < n) :
    ((k : ℤ) : Poly A n)[i] = if i = 0 then (k : A) else 0 :=
  Vector.getElem_ofFn ..

@[simp] theorem getElem_neg (f : Poly A n) (i : ℕ) (hi : i < n) : (-f)[i] = -f[i] :=
  Vector.getElem_map ..

@[simp] theorem getElem_add (f g : Poly A n) (i : ℕ) (hi : i < n) : (f + g)[i] = f[i] + g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (f g : Poly A n) (i : ℕ) (hi : i < n) : (f - g)[i] = f[i] - g[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_smul (c : A) (f : Poly A n) (i : ℕ) (hi : i < n) :
    (c • f)[i] = f[i] * c :=
  Vector.getElem_map ..

@[simp] theorem getElem_nsmul (k : ℕ) (f : Poly A n) (i : ℕ) (hi : i < n) :
    (k • f)[i] = f[i] * k :=
  Vector.getElem_map ..

@[simp] theorem getElem_zsmul (k : ℤ) (f : Poly A n) (i : ℕ) (hi : i < n) :
    (k • f)[i] = f[i] * k :=
  Vector.getElem_map ..

theorem pow_zero' (f : Poly A n) : f ^ 0 = 1 := rfl
theorem pow_succ' (f : Poly A n) (k : ℕ) : f ^ (k + 1) = f ^ k * f := rfl

theorem getElem_mulBinomial (c : A) (f g : Poly A n) (k : ℕ) (hk : k < n) :
    (mulBinomial c f g)[k] = ∑ i : Fin n, ∑ j : Fin n,
      if i.val + j.val = k then f[i] * g[j]
      else if i.val + j.val = k + n then c * (f[i] * g[j])
      else 0 :=
  Vector.getElem_ofFn ..

theorem mul_eq (f g : Poly A n) : f * g = mulBinomial (-1) f g := rfl

end Poly

/-- A vector of `k` polynomials (FIPS 203 §2.4.4). -/
abbrev PolyVec (A : Type) (n k : ℕ) := Vector (Poly A n) k

namespace PolyVec

variable {A : Type} [CommRing A] {n k : ℕ}

def zero : PolyVec A n k := Vector.replicate k Poly.zero

def set (v : PolyVec A n k) (i : ℕ) (f : Poly A n) (_ : i < k := by get_elem_tactic) :
    PolyVec A n k :=
  Vector.set v i f

instance : Add (PolyVec A n k) where
  add v w := Vector.ofFn fun i => v[i] + w[i]

end PolyVec

/-- A `k × k` matrix as a vector of rows (FIPS 203 §2.4.5), stored rather than represented as a
function so that entries are computed once. -/
abbrev Mat (α : Type) (k : ℕ) := Vector (Vector α k) k

namespace Mat

variable {α : Type} {k : ℕ}

def zero [Zero α] : Mat α k := Vector.replicate k (Vector.replicate k 0)

/-- `M.update i j val` sets entry `(i, j)` to `val`. -/
def update (M : Mat α k) (i j : ℕ) (val : α)
    (hi : i < k := by get_elem_tactic) (_ : j < k := by get_elem_tactic) : Mat α k :=
  M.set i (M[i].set j val)

/-- `Mᵀ`. -/
def transpose (M : Mat α k) : Mat α k :=
  Vector.ofFn fun i => Vector.ofFn fun j => M[j][i]

end Mat

/-- A `k × k` matrix of polynomials. -/
abbrev PolyMat (A : Type) (n k : ℕ) := Mat (Poly A n) k

end Wychelean.Lattice
