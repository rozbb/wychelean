import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Polynomials over ℤ_q modulo X^n + 1

Elements of `ℤ_q[X] / (X^n + 1)` as coefficient vectors, with the pointwise operations and the
negacyclic product, shared by the module-lattice schemes (FIPS 203 §2.4, FIPS 204 §2.3).
The pointwise definitions are adapted from Microsoft SymCrypt (MIT; see
Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.Lattice

/-- A polynomial of degree below `n` with coefficients in `ℤ_q`, coefficient `i` at index `i`;
read modulo `X^n + 1`. -/
abbrev Poly (q n : ℕ) := Vector (ZMod q) n

namespace Poly

variable {q n : ℕ}

def zero : Poly q n := Vector.replicate n 0

/-- Pointwise addition.

The body uses `Vector.zipWith` rather than the seemingly-equivalent
`Vector.ofFn (fun i => f[i] + g[i])`. This is a *grind workaround*: the latter shape causes
`grind`'s `whnf` to descend through `Vector.ofFn`'s lambda and infinitely unfold `Add` on the
element type, blowing `maxRecDepth` on any goal containing `_ + _ : Poly q n`. `Vector.zipWith`
avoids it because its body is a non-recursive `Array.zipWith` wrapper that `whnf` does not
recurse into. -/
def add (f g : Poly q n) : Poly q n := Vector.zipWith (· + ·) f g

/-- Pointwise subtraction. See `add` for the `zipWith` rationale. -/
def sub (f g : Poly q n) : Poly q n := Vector.zipWith (· - ·) f g

/-- Multiplication by a scalar. -/
def scalarMul (f : Poly q n) (c : ZMod q) : Poly q n := f.map fun v => v * c

/-- The product in `ℤ_q[X] / (X^n + 1)`: the convolution of the coefficients, with the terms of
degree `n` or more wrapped around with a sign change since `X^n = -1`. -/
def mul (f g : Poly q n) : Poly q n :=
  Vector.ofFn fun k => ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = k.val then f[i] * g[j]
    else if i.val + j.val = k.val + n then -(f[i] * g[j])
    else 0

instance : Add (Poly q n) where add := add
instance : Sub (Poly q n) where sub := sub
instance : Mul (Poly q n) where mul := mul
instance : HMul (Poly q n) (ZMod q) (Poly q n) where hMul := scalarMul

end Poly

/-- A vector of `k` polynomials (FIPS 203 §2.4.4). -/
abbrev PolyVec (q n k : ℕ) := Vector (Poly q n) k

namespace PolyVec

variable {q n k : ℕ}

def zero : PolyVec q n k := Vector.replicate k Poly.zero

def set (v : PolyVec q n k) (i : ℕ) (f : Poly q n) (_ : i < k := by get_elem_tactic) :
    PolyVec q n k :=
  Vector.set v i f

instance : Add (PolyVec q n k) where
  add v w := Vector.ofFn fun i => v[i] + w[i]

end PolyVec

/-- A `k × k` matrix of polynomials as a vector of rows (FIPS 203 §2.4.5), stored rather than
represented as a function so that entries are computed once. -/
abbrev PolyMat (q n k : ℕ) := Vector (Vector (Poly q n) k) k

namespace PolyMat

variable {q n k : ℕ}

def zero : PolyMat q n k := Vector.replicate k (Vector.replicate k Poly.zero)

/-- `M.update i j val` sets entry `(i, j)` to `val`. -/
def update (M : PolyMat q n k) (i j : ℕ) (val : Poly q n)
    (hi : i < k := by get_elem_tactic) (_ : j < k := by get_elem_tactic) : PolyMat q n k :=
  M.set i (M[i].set j val)

/-- `Mᵀ`. -/
def transpose (M : PolyMat q n k) : PolyMat q n k :=
  Vector.ofFn fun i => Vector.ofFn fun j => M[j][i]

end PolyMat

end Wychelean.Lattice
