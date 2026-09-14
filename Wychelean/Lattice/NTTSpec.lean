import Wychelean.Lattice.Poly
import Wychelean.Utils.Bits

/-!
# The NTT domain and the transform as residues

The NTT domain `T_q` (FIPS 203 §2.4.6, FIPS 204 §7.5) is the product ring `∏ᵢ ℤ_q[X]/(X^d - γᵢ)`
for evaluation points `γ₀, …, γₘ₋₁`, `d = 256 / m`. It is determined by the points alone; how the
points arise (`γᵢ = ζ^(2·BitRev(i) + 1)` after `levels` butterfly layers, `m = 2^levels`) belongs
to the transform. An element stores residue `i` at indices `d·i, …, d·i + d - 1`; multiplication
is block by block. The transform sends `f` to its residues: since `X^d ≡ γᵢ` in block `i`,
coefficient `r` there is `∑ₜ f[r + d·t] γᵢ^t`, and the inverse reads the coefficients back through
the inverse points and divides by `m`. These closed forms are the definitions the correctness
theorems are about; `Tests.lean` checks the butterfly loops of `NTT.lean` agree with them.
-/

namespace Wychelean.Lattice

open Wychelean

/-- The NTT domain for the `m` evaluation points `γ`: residues modulo `X^(256/m) - γᵢ`, stored
consecutively. A separate type from `Poly`, with blockwise multiplication. -/
structure NTTDomain (q : ℕ) (m : ℕ) (γ : Fin m → ZMod q) where
  residues : Vector (ZMod q) 256
deriving DecidableEq

namespace NTTDomain

variable {q m : ℕ} {γ : Fin m → ZMod q}

/-- The block size `d = 256 / m`. -/
abbrev blockSize (m : ℕ) : ℕ := 256 / m

theorem blockSize_mul (hm : m ∣ 256) : blockSize m * m = 256 := Nat.div_mul_cancel hm

theorem blockSize_pos (hm : m ∣ 256) : 0 < blockSize m :=
  Nat.div_pos (Nat.le_of_dvd (by decide) hm) (Nat.pos_of_dvd_of_pos hm (by decide))

theorem block_idx_lt (hm : m ∣ 256) {r t : ℕ} (hr : r < blockSize m) (ht : t < m) :
    r + blockSize m * t < 256 := by
  have h := Nat.mul_le_mul_left (blockSize m) (Nat.succ_le_of_lt ht)
  rw [blockSize_mul hm, Nat.mul_succ] at h
  omega

theorem div_blockSize_lt (hm : m ∣ 256) {idx : ℕ} (h : idx < 256) : idx / blockSize m < m :=
  (Nat.div_lt_iff_lt_mul (blockSize_pos hm)).2 (by rw [Nat.mul_comm, blockSize_mul hm]; exact h)

instance : GetElem (NTTDomain q m γ) ℕ (ZMod q) fun _ i => i < 256 where
  getElem a i h := a.residues[i]

instance : Zero (NTTDomain q m γ) where zero := ⟨Vector.replicate 256 0⟩

/-- Residues add pointwise. -/
instance : Add (NTTDomain q m γ) where
  add a b := ⟨Vector.zipWith (· + ·) a.residues b.residues⟩

instance : Sub (NTTDomain q m γ) where
  sub a b := ⟨Vector.zipWith (· - ·) a.residues b.residues⟩

@[simp] theorem getElem_mk (v : Vector (ZMod q) 256) (i : ℕ) (hi : i < 256) :
    (⟨v⟩ : NTTDomain q m γ)[i] = v[i] := rfl

@[simp] theorem residues_getElem (a : NTTDomain q m γ) (i : ℕ) (hi : i < 256) :
    a.residues[i] = a[i] := rfl

theorem ext {a b : NTTDomain q m γ} (h : ∀ (i : ℕ) (hi : i < 256), a[i] = b[i]) : a = b := by
  cases a; cases b
  congr 1
  exact Vector.ext h

@[simp] theorem getElem_add (a b : NTTDomain q m γ) (i : ℕ) (hi : i < 256) :
    (a + b)[i] = a[i] + b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_sub (a b : NTTDomain q m γ) (i : ℕ) (hi : i < 256) :
    (a - b)[i] = a[i] - b[i] :=
  Vector.getElem_zipWith hi

@[simp] theorem getElem_zero (i : ℕ) (hi : i < 256) : (0 : NTTDomain q m γ)[i] = 0 :=
  Vector.getElem_replicate ..

/-- Residue `i`, an element of `ℤ_q[X]/(X^d - γᵢ)`. -/
def block (hm : m ∣ 256) (a : NTTDomain q m γ) (i : Fin m) : Poly (ZMod q) (blockSize m) :=
  Vector.ofFn fun r => a[r.val + blockSize m * i.val]'(block_idx_lt hm r.isLt i.isLt)

theorem getElem_block (hm : m ∣ 256) (a : NTTDomain q m γ) (i : Fin m) (r : ℕ)
    (hr : r < blockSize m) :
    (block hm a i)[r] = a[r + blockSize m * i.val]'(block_idx_lt hm hr i.isLt) :=
  Vector.getElem_ofFn ..

/-- Multiplication: block by block in `ℤ_q[X]/(X^d - γᵢ)` (FIPS 203 Algorithms 11–12 for
`d = 2`, pointwise for `d = 1`). -/
def mul (hm : m ∣ 256) (a b : NTTDomain q m γ) : NTTDomain q m γ :=
  ⟨Vector.ofFn fun idx =>
    let i : Fin m := ⟨idx.val / blockSize m, div_blockSize_lt hm idx.isLt⟩
    let p := Poly.mulBinomial (γ i) (block hm a i) (block hm b i)
    p[idx.val % blockSize m]'(Nat.mod_lt _ (blockSize_pos hm))⟩

theorem getElem_mul (hm : m ∣ 256) (a b : NTTDomain q m γ) (k : ℕ) (hk : k < 256) :
    (mul hm a b)[k] =
      (Poly.mulBinomial (γ ⟨k / blockSize m, div_blockSize_lt hm hk⟩)
        (block hm a ⟨k / blockSize m, div_blockSize_lt hm hk⟩)
        (block hm b ⟨k / blockSize m, div_blockSize_lt hm hk⟩))[k % blockSize m]'(
        Nat.mod_lt _ (blockSize_pos hm)) :=
  Vector.getElem_ofFn ..

instance [h : Fact (m ∣ 256)] : Mul (NTTDomain q m γ) where mul a b := mul h.out a b

end NTTDomain

namespace NTT

variable {q : ℕ}

/-- The `i`-th evaluation point after `levels` layers, `ζ^(2·BitRev(i) + 1)`. -/
def point (ζ : ZMod q) (levels i : ℕ) : ZMod q := ζ ^ (2 * bitRev levels i + 1)

/-- The evaluation points as a family over the `2^levels` blocks. -/
abbrev points (ζ : ZMod q) (levels : ℕ) : Fin (2 ^ levels) → ZMod q := fun i => point ζ levels i

/-- `2^levels` blocks fit into 256 coefficients when `levels ≤ 8`. -/
theorem pow_dvd {levels : ℕ} (hL : levels ≤ 8) : 2 ^ levels ∣ 256 :=
  pow_dvd_pow 2 hL

/-- The block size after `levels` layers. -/
abbrev blockSize (levels : ℕ) : ℕ := NTTDomain.blockSize (2 ^ levels)

theorem blockSize_mul_pow {levels : ℕ} (hL : levels ≤ 8) : blockSize levels * 2 ^ levels = 256 :=
  NTTDomain.blockSize_mul (pow_dvd hL)

theorem blockSize_pos {levels : ℕ} (hL : levels ≤ 8) : 0 < blockSize levels :=
  NTTDomain.blockSize_pos (pow_dvd hL)

theorem block_idx_lt {levels r t : ℕ} (hL : levels ≤ 8) (hr : r < blockSize levels)
    (ht : t < 2 ^ levels) : r + blockSize levels * t < 256 :=
  NTTDomain.block_idx_lt (pow_dvd hL) hr ht

theorem div_blockSize_lt {levels idx : ℕ} (hL : levels ≤ 8) (h : idx < 256) :
    idx / blockSize levels < 2 ^ levels :=
  NTTDomain.div_blockSize_lt (pow_dvd hL) h

/-- `f mod (X^d - γ)` for `d = blockSize levels`: coefficient `r` collects `f[r + d·t] γ^t`. -/
def modBinomial (levels : ℕ) (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q) :
    Poly (ZMod q) (blockSize levels) :=
  Vector.ofFn fun r => ∑ t : Fin (2 ^ levels),
    f[r.val + blockSize levels * t.val]'(block_idx_lt hL r.isLt t.isLt) * γ ^ t.val

/-- The transform: block `i` is `f mod (X^d - point i)`. -/
def nttSpec (ζ : ZMod q) (levels : ℕ) (f : Poly (ZMod q) 256) (hL : levels ≤ 8 := by decide) :
    NTTDomain q (2 ^ levels) (points ζ levels) :=
  ⟨Vector.ofFn fun idx =>
    let block := modBinomial levels hL f (point ζ levels (idx.val / blockSize levels))
    block[idx.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos hL))⟩

/-- The inverse transform: `f[r + d·t] = 2^(-levels) ∑ᵢ (block i)[r] · (point i)^(-t)`. -/
def nttInvSpec (ζ : ZMod q) (levels : ℕ) («f̂» : NTTDomain q (2 ^ levels) (points ζ levels))
    (hL : levels ≤ 8 := by decide) : Poly (ZMod q) 256 :=
  Vector.ofFn fun k =>
    (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      (NTTDomain.block (pow_dvd hL) «f̂» i)[k.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos hL)) *
        (point ζ levels i.val)⁻¹ ^ (k.val / blockSize levels)

/-! ### Coefficient lemmas, the interface the proofs use -/

theorem getElem_modBinomial {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256) (γ : ZMod q)
    (r : ℕ) (hr : r < blockSize levels) :
    (modBinomial levels hL f γ)[r] = ∑ t : Fin (2 ^ levels),
      f[r + blockSize levels * t.val]'(block_idx_lt hL hr t.isLt) * γ ^ t.val :=
  Vector.getElem_ofFn ..

theorem getElem_nttSpec (ζ : ZMod q) {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256)
    (k : ℕ) (hk : k < 256) :
    (nttSpec ζ levels f hL)[k] =
      (modBinomial levels hL f (point ζ levels (k / blockSize levels)))[k % blockSize levels]'(
        Nat.mod_lt _ (blockSize_pos hL)) :=
  Vector.getElem_ofFn ..

theorem getElem_nttInvSpec (ζ : ZMod q) {levels : ℕ} (hL : levels ≤ 8)
    (a : NTTDomain q (2 ^ levels) (points ζ levels)) (k : ℕ) (hk : k < 256) :
    (nttInvSpec ζ levels a hL)[k] = (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      (NTTDomain.block (pow_dvd hL) a i)[k % blockSize levels]'(Nat.mod_lt _ (blockSize_pos hL)) *
        (point ζ levels i.val)⁻¹ ^ (k / blockSize levels) :=
  Vector.getElem_ofFn ..

end NTT

end Wychelean.Lattice
