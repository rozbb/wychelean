import Wychelean.Lattice.NTT

/-!
# The transform as residues

What the butterflies of `NTT.ntt` compute, stated directly (FIPS 203 §4.3, FIPS 204 §7.5):
after `levels` layers the coefficients split into blocks of size `d = 2^(8 - levels)`, and block
`i` holds `f mod (X^d - γᵢ)` with `γᵢ = ζ^(2·BitRev(i) + 1)`. Since `X^d ≡ γᵢ` there, coefficient
`r` of the block is `∑ₜ f[r + d·t] γᵢ^t`. The inverse reads the coefficients back through the
inverse points and divides by the number of blocks. These closed forms are the definitions the
correctness theorems are about; `Tests.lean` checks the loops agree with them.
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

/-- `f mod (X^d - γ)` for `d = blockSize levels`: coefficient `r` collects `f[r + d·t] γ^t`. -/
def modBinomial (levels : ℕ) (hL : levels ≤ 8) (f : Poly q 256) (γ : ZMod q) :
    Poly q (blockSize levels) :=
  Vector.ofFn fun r => ∑ t : Fin (2 ^ levels),
    f[r.val + blockSize levels * t.val]'(block_idx_lt hL r.isLt t.isLt) * γ ^ t.val

/-- The transform: block `i` is `f mod (X^d - point i)`. -/
def nttSpec (ζ : ZMod q) (levels : ℕ) (f : Poly q 256) (hL : levels ≤ 8 := by decide) :
    Poly q 256 :=
  Vector.ofFn fun idx =>
    let block := modBinomial levels hL f (point ζ levels (idx.val / blockSize levels))
    block[idx.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels))

/-- The inverse transform: `f[r + d·t] = 2^(-levels) ∑ᵢ (block i)[r] · (point i)^(-t)`. -/
def nttInvSpec (ζ : ZMod q) (levels : ℕ) («f̂» : Poly q 256) (hL : levels ≤ 8 := by decide) :
    Poly q 256 :=
  Vector.ofFn fun k =>
    (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      «f̂»[k.val % blockSize levels + blockSize levels * i.val]'(block_idx_lt hL (Nat.mod_lt _ (blockSize_pos levels)) i.isLt) *
        (point ζ levels i.val)⁻¹ ^ (k.val / blockSize levels)

theorem div_blockSize_lt {levels idx : ℕ} (hL : levels ≤ 8) (h : idx < 256) :
    idx / blockSize levels < 2 ^ levels :=
  (Nat.div_lt_iff_lt_mul (blockSize_pos levels)).2 (by rw [Nat.mul_comm, blockSize_mul_pow hL]; exact h)

/-- Block `i` of a transformed polynomial. -/
def block (hL : levels ≤ 8) (a : Poly q 256) (i : Fin (2 ^ levels)) : Poly q (blockSize levels) :=
  Vector.ofFn fun r => a[r.val + blockSize levels * i.val]'(block_idx_lt hL r.isLt i.isLt)

/-- Multiplication in the NTT domain: block by block in `ℤ_q[X]/(X^d - point i)`
(FIPS 203 Algorithms 11–12 for `d = 2`, pointwise for `d = 1`). -/
def mulNTT (ζ : ZMod q) (levels : ℕ) (a b : Poly q 256) (hL : levels ≤ 8 := by decide) :
    Poly q 256 :=
  Vector.ofFn fun idx =>
    let i : Fin (2 ^ levels) := ⟨idx.val / blockSize levels, div_blockSize_lt hL idx.isLt⟩
    let p := Poly.mulBinomial (point ζ levels i) (block hL a i) (block hL b i)
    p[idx.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels))

end Wychelean.Lattice.NTT
