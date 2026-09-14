import Wychelean.Lattice.Poly
import Wychelean.Utils.Bits

/-!
# The NTT domain and the transform as residues

`T_q`, the NTT domain (FIPS 203 §2.4.6, FIPS 204 §7.5): after `levels` layers a polynomial splits
into `2^levels` residues, block `i` of size `d = 2^(8 - levels)` being `f mod (X^d - γᵢ)` with
`γᵢ = ζ^(2·BitRev(i) + 1)`. Since `X^d ≡ γᵢ` there, coefficient `r` of block `i` is
`∑ₜ f[r + d·t] γᵢ^t`. Multiplication in `T_q` is block by block; the inverse transform reads
the coefficients back through the inverse points and divides by the number of blocks. These
closed forms are the definitions the correctness theorems are about; `Tests.lean` checks the
butterfly loops of `NTT.lean` agree with them.
-/

namespace Wychelean.Lattice.NTT

open Wychelean

variable {q : ℕ}

/-- The block size after `levels` layers. -/
abbrev blockSize (levels : ℕ) : ℕ := 2 ^ (8 - levels)

theorem blockSize_mul_pow {levels : ℕ} (hL : levels ≤ 8) : blockSize levels * 2 ^ levels = 256 := by
  rw [blockSize, ← pow_add, Nat.sub_add_cancel hL]
  rfl

theorem blockSize_pos (levels : ℕ) : 0 < blockSize levels := Nat.two_pow_pos _

theorem block_idx_lt {levels r t : ℕ} (hL : levels ≤ 8) (hr : r < blockSize levels)
    (ht : t < 2 ^ levels) : r + blockSize levels * t < 256 := by
  have h := Nat.mul_le_mul_left (blockSize levels) (Nat.succ_le_of_lt ht)
  rw [blockSize_mul_pow hL, Nat.mul_succ] at h
  omega

/-- The `i`-th evaluation point `ζ^(2·BitRev(i) + 1)`. -/
def point (ζ : ZMod q) (levels i : ℕ) : ZMod q := ζ ^ (2 * bitRev levels i + 1)

end NTT

/-- The NTT domain `T_q` for `ζ` and `levels`: the residues of a polynomial, block `i` stored at
indices `d·i, …, d·i + d - 1`. A separate type from `Poly`, with blockwise multiplication. -/
structure Tq (q : ℕ) (ζ : ZMod q) (levels : ℕ) where
  residues : Vector (ZMod q) 256
deriving DecidableEq

namespace Tq

variable {q levels : ℕ} {ζ : ZMod q}

instance : GetElem (Tq q ζ levels) ℕ (ZMod q) fun _ i => i < 256 where
  getElem a i h := a.residues[i]

instance : Zero (Tq q ζ levels) where zero := ⟨Vector.replicate 256 0⟩

/-- Residues add pointwise. -/
instance : Add (Tq q ζ levels) where add a b := ⟨Vector.zipWith (· + ·) a.residues b.residues⟩

instance : Sub (Tq q ζ levels) where sub a b := ⟨Vector.zipWith (· - ·) a.residues b.residues⟩

@[simp] theorem getElem_mk (v : Vector (ZMod q) 256) (i : ℕ) (hi : i < 256) :
    (⟨v⟩ : Tq q ζ levels)[i] = v[i] := rfl

@[simp] theorem residues_getElem (a : Tq q ζ levels) (i : ℕ) (hi : i < 256) :
    a.residues[i] = a[i] := rfl

theorem ext {a b : Tq q ζ levels} (h : ∀ (i : ℕ) (hi : i < 256), a[i] = b[i]) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext h

@[simp] theorem getElem_add (a b : Tq q ζ levels) (i : ℕ) (hi : i < 256) :
    (a + b)[i] = a[i] + b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (a b : Tq q ζ levels) (i : ℕ) (hi : i < 256) :
    (a - b)[i] = a[i] - b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_zero (i : ℕ) (hi : i < 256) : (0 : Tq q ζ levels)[i] = 0 :=
  Vector.getElem_replicate ..

end Tq

namespace NTT

variable {q : ℕ}

/-- `f mod (X^d - γ)` for `d = blockSize levels`: coefficient `r` collects `f[r + d·t] γ^t`. -/
def modBinomial (levels : ℕ) (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q) :
    Poly (ZMod q) (blockSize levels) :=
  Vector.ofFn fun r => ∑ t : Fin (2 ^ levels),
    f[r.val + blockSize levels * t.val]'(block_idx_lt hL r.isLt t.isLt) * γ ^ t.val

/-- The transform: block `i` is `f mod (X^d - point i)`. -/
def nttSpec (ζ : ZMod q) (levels : ℕ) (f : Poly (ZMod q) 256) (hL : levels ≤ 8 := by decide) :
    Tq q ζ levels :=
  ⟨Vector.ofFn fun idx =>
    let block := modBinomial levels hL f (point ζ levels (idx.val / blockSize levels))
    block[idx.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels))⟩

theorem div_blockSize_lt {levels idx : ℕ} (hL : levels ≤ 8) (h : idx < 256) :
    idx / blockSize levels < 2 ^ levels :=
  (Nat.div_lt_iff_lt_mul (blockSize_pos levels)).2 (by rw [Nat.mul_comm, blockSize_mul_pow hL]; exact h)

/-- Block `i` of an element of the NTT domain: the residue at `point i`. -/
def block (hL : levels ≤ 8) (a : Tq q ζ levels) (i : Fin (2 ^ levels)) : Poly (ZMod q) (blockSize levels) :=
  Vector.ofFn fun r => a[r.val + blockSize levels * i.val]'(block_idx_lt hL r.isLt i.isLt)

/-- The inverse transform: `f[r + d·t] = 2^(-levels) ∑ᵢ (block i)[r] · (point i)^(-t)`. -/
def nttInvSpec (ζ : ZMod q) (levels : ℕ) («f̂» : Tq q ζ levels) (hL : levels ≤ 8 := by decide) :
    Poly (ZMod q) 256 :=
  Vector.ofFn fun k =>
    (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      (block hL «f̂» i)[k.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k.val / blockSize levels)

/-- Multiplication in the NTT domain: block by block in `ℤ_q[X]/(X^d - point i)`
(FIPS 203 Algorithms 11–12 for `d = 2`, pointwise for `d = 1`). -/
def mulNTT (ζ : ZMod q) (levels : ℕ) (a b : Tq q ζ levels) (hL : levels ≤ 8 := by decide) :
    Tq q ζ levels :=
  ⟨Vector.ofFn fun idx =>
    let i : Fin (2 ^ levels) := ⟨idx.val / blockSize levels, div_blockSize_lt hL idx.isLt⟩
    let p := Poly.mulBinomial (point ζ levels i) (block hL a i) (block hL b i)
    p[idx.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels))⟩

/-- `*` on `T_q` is `mulNTT`, for at most eight layers. -/
instance (ζ : ZMod q) (levels : ℕ) [h : Fact (levels ≤ 8)] : Mul (Tq q ζ levels) where
  mul a b := mulNTT ζ levels a b h.out

/-! ### Coefficient lemmas, the interface the proofs use -/

theorem getElem_modBinomial (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q) (r : ℕ)
    (hr : r < blockSize levels) :
    (modBinomial levels hL f γ)[r] = ∑ t : Fin (2 ^ levels),
      f[r + blockSize levels * t.val]'(block_idx_lt hL hr t.isLt) * γ ^ t.val :=
  Vector.getElem_ofFn ..

theorem getElem_nttSpec (ζ : ZMod q) (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (k : ℕ) (hk : k < 256) :
    (nttSpec ζ levels f hL)[k] =
      (modBinomial levels hL f (point ζ levels (k / blockSize levels)))[k % blockSize levels]'(
        Nat.mod_lt _ (blockSize_pos levels)) :=
  Vector.getElem_ofFn ..

theorem getElem_block {ζ : ZMod q} (hL : levels ≤ 8) (a : Tq q ζ levels) (i : Fin (2 ^ levels)) (r : ℕ)
    (hr : r < blockSize levels) :
    (block hL a i)[r] = a[r + blockSize levels * i.val]'(block_idx_lt hL hr i.isLt) :=
  Vector.getElem_ofFn ..

theorem getElem_nttInvSpec (ζ : ZMod q) (hL : levels ≤ 8) (a : Tq q ζ levels) (k : ℕ)
    (hk : k < 256) :
    (nttInvSpec ζ levels a hL)[k] = (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      (block hL a i)[k % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k / blockSize levels) :=
  Vector.getElem_ofFn ..

theorem getElem_mulNTT (ζ : ZMod q) (hL : levels ≤ 8) (a b : Tq q ζ levels) (k : ℕ) (hk : k < 256) :
    (mulNTT ζ levels a b hL)[k] =
      (Poly.mulBinomial (point ζ levels (k / blockSize levels))
        (block hL a ⟨k / blockSize levels, div_blockSize_lt hL hk⟩)
        (block hL b ⟨k / blockSize levels, div_blockSize_lt hL hk⟩))[k % blockSize levels]'(
        Nat.mod_lt _ (blockSize_pos levels)) :=
  Vector.getElem_ofFn ..

end Wychelean.Lattice.NTT
