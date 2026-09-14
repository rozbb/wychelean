import Wychelean.Lattice.Poly
import Wychelean.Utils.Bits

namespace Wychelean.Lattice

open Wychelean

/-- The product ring `∏ᵢ ℤ_q[X]/(X^d - γᵢ)` for the `m` evaluation points `γ`: residue `i` is a
polynomial of degree below `d`, read modulo `X^d - γᵢ`. Elements are multiplied residue by
residue; the points need no relation to each other here. -/
structure Residues (q d m : ℕ) (γ : Fin m → ZMod q) where
  residues : Vector (Poly (ZMod q) d) m
deriving DecidableEq

namespace Residues

variable {q d m : ℕ} {γ : Fin m → ZMod q}

instance : GetElem (Residues q d m γ) ℕ (Poly (ZMod q) d) fun _ i => i < m where
  getElem a i h := a.residues[i]

instance : Zero (Residues q d m γ) where zero := ⟨Vector.replicate m 0⟩

instance : Add (Residues q d m γ) where
  add a b := ⟨Vector.zipWith (· + ·) a.residues b.residues⟩

instance : Sub (Residues q d m γ) where
  sub a b := ⟨Vector.zipWith (· - ·) a.residues b.residues⟩

/-- Residue `i` is multiplied in `ℤ_q[X]/(X^d - γᵢ)`. -/
instance : Mul (Residues q d m γ) where
  mul a b := ⟨Vector.ofFn fun i => Poly.mulBinomial (γ i) a.residues[i] b.residues[i]⟩

@[simp] theorem getElem_mk (v : Vector (Poly (ZMod q) d) m) (i : ℕ) (hi : i < m) :
    (⟨v⟩ : Residues q d m γ)[i] = v[i] := rfl

@[simp] theorem residues_getElem (a : Residues q d m γ) (i : ℕ) (hi : i < m) :
    a.residues[i] = a[i] := rfl

theorem ext {a b : Residues q d m γ} (h : ∀ (i : ℕ) (hi : i < m), a[i] = b[i]) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext h

@[simp] theorem getElem_add (a b : Residues q d m γ) (i : ℕ) (hi : i < m) :
    (a + b)[i] = a[i] + b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (a b : Residues q d m γ) (i : ℕ) (hi : i < m) :
    (a - b)[i] = a[i] - b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_zero (i : ℕ) (hi : i < m) : (0 : Residues q d m γ)[i] = 0 :=
  Vector.getElem_replicate ..

@[simp] theorem getElem_mul (a b : Residues q d m γ) (i : ℕ) (hi : i < m) :
    (a * b)[i] = Poly.mulBinomial (γ ⟨i, hi⟩) a[i] b[i] :=
  Vector.getElem_ofFn ..

/-- With residues of degree two, residue `i` of a product is the base case of FIPS 203
Algorithm 12 at `γᵢ`. -/
theorem getElem_mul_two {γ : Fin m → ZMod q} (a b : Residues q 2 m γ) (i : ℕ) (hi : i < m) :
    (a * b)[i] = #v[a[i][0] * b[i][0] + a[i][1] * b[i][1] * γ ⟨i, hi⟩,
                   a[i][0] * b[i][1] + a[i][1] * b[i][0]] := by
  rw [getElem_mul, Poly.mulBinomial_two]

/-- The residues laid out consecutively, residue `i` at indices `d·i, …, d·i + d - 1`
(the coefficient order of FIPS 203 §2.4.6). -/
def flatten (a : Residues q d m γ) : Vector (ZMod q) (m * d) := a.residues.flatten

theorem flat_idx_lt {r i : ℕ} (hr : r < d) (hi : i < m) : r + d * i < m * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm m d]
  omega

/-- The inverse of `flatten`: cut a coefficient vector into `m` residues of size `d`. -/
def ofFlat (v : Vector (ZMod q) (m * d)) : Residues q d m γ :=
  ⟨Vector.ofFn fun i => Vector.ofFn fun r => v[r.val + d * i.val]'(flat_idx_lt r.isLt i.isLt)⟩

end Residues

namespace NTT

variable {q : ℕ}

/-- The `i`-th evaluation point after `levels` butterfly layers, `ζ^(2·BitRev(i) + 1)`
(FIPS 203 §4.3, FIPS 204 §7.5). -/
def point (ζ : ZMod q) (levels i : ℕ) : ZMod q := ζ ^ (2 * bitRev levels i + 1)

/-- The evaluation points as a family over the `2^levels` residues. -/
abbrev points (ζ : ZMod q) (levels : ℕ) : Fin (2 ^ levels) → ZMod q := fun i => point ζ levels i

/-- The residue degree after `levels` layers, `d = 256 / 2^levels`. -/
abbrev blockSize (levels : ℕ) : ℕ := 2 ^ (8 - levels)

theorem blockSize_mul_pow {levels : ℕ} (hL : levels ≤ 8) : blockSize levels * 2 ^ levels = 256 := by
  rw [blockSize, ← pow_add, Nat.sub_add_cancel hL]
  rfl

theorem pow_mul_blockSize {levels : ℕ} (hL : levels ≤ 8) : 2 ^ levels * blockSize levels = 256 := by
  rw [Nat.mul_comm, blockSize_mul_pow hL]

theorem blockSize_pos (levels : ℕ) : 0 < blockSize levels := Nat.two_pow_pos _

theorem block_idx_lt {levels r t : ℕ} (hL : levels ≤ 8) (hr : r < blockSize levels)
    (ht : t < 2 ^ levels) : r + blockSize levels * t < 256 := by
  have h := Nat.mul_le_mul_left (blockSize levels) (Nat.succ_le_of_lt ht)
  rw [blockSize_mul_pow hL, Nat.mul_succ] at h
  omega

theorem div_blockSize_lt {levels k : ℕ} (hL : levels ≤ 8) (hk : k < 256) :
    k / blockSize levels < 2 ^ levels :=
  (Nat.div_lt_iff_lt_mul (blockSize_pos levels)).2 (by rw [pow_mul_blockSize hL]; exact hk)

end NTT

/-- The NTT domain `T_q`: the evaluation domain at the `2^levels` points `ζ^(2·BitRev(i) + 1)`,
with residues of degree below `256 / 2^levels` (FIPS 203 §2.4.6 for `levels = 7`, FIPS 204 §7.5
for `levels = 8`). -/
abbrev NTTDomain (ζ : ZMod q) (levels : ℕ) :=
  Residues q (NTT.blockSize levels) (2 ^ levels) (NTT.points ζ levels)

namespace NTT

variable {q : ℕ}

/-- `f mod (X^d - γ)` for `d = blockSize levels`: since `X^d ≡ γ`, coefficient `r` collects
`f[r + d·t] γ^t`. -/
def modBinomial (levels : ℕ) (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q) :
    Poly (ZMod q) (blockSize levels) :=
  Vector.ofFn fun r => ∑ t : Fin (2 ^ levels),
    f[r.val + blockSize levels * t.val]'(block_idx_lt hL r.isLt t.isLt) * γ ^ t.val

/-- The transform as residues: residue `i` is `f mod (X^d - point i)`. -/
def nttSpec (ζ : ZMod q) (levels : ℕ) (f : Poly (ZMod q) 256) (hL : levels ≤ 8 := by decide) :
    NTTDomain ζ levels :=
  ⟨Vector.ofFn fun i => modBinomial levels hL f (point ζ levels i)⟩

/-- The inverse transform: `f[r + d·t] = 2^(-levels) ∑ᵢ (residue i)[r] · (point i)^(-t)`. -/
def nttInvSpec (ζ : ZMod q) (levels : ℕ) («f̂» : NTTDomain ζ levels) : Poly (ZMod q) 256 :=
  Vector.ofFn fun k =>
    (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      «f̂»[i][k.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k.val / blockSize levels)

theorem getElem_modBinomial {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q)
    (r : ℕ) (hr : r < blockSize levels) :
    (modBinomial levels hL f γ)[r] = ∑ t : Fin (2 ^ levels),
      f[r + blockSize levels * t.val]'(block_idx_lt hL hr t.isLt) * γ ^ t.val :=
  Vector.getElem_ofFn ..

theorem getElem_nttSpec (ζ : ZMod q) {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256)
    (i : ℕ) (hi : i < 2 ^ levels) :
    (nttSpec ζ levels f hL)[i] = modBinomial levels hL f (point ζ levels i) :=
  Vector.getElem_ofFn ..

theorem getElem_nttInvSpec (ζ : ZMod q) (levels : ℕ) (a : NTTDomain ζ levels)
    (k : ℕ) (hk : k < 256) :
    (nttInvSpec ζ levels a)[k] = (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      a[i][k % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k / blockSize levels) :=
  Vector.getElem_ofFn ..

end NTT

end Wychelean.Lattice
