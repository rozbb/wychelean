import Wychelean.PolyRing.Residues
import Wychelean.Utils.Bits

namespace Wychelean.PolyRing

open Wychelean

namespace NTT

variable {q : ℕ}

/-- The `i`-th evaluation point after `levels` layers, `ζ^(2·BitRev(i) + 1)` (FIPS 203 §4.3). -/
def point (ζ : ZMod q) (levels i : ℕ) : ZMod q := ζ ^ (2 * bitRev levels i + 1)

abbrev points (ζ : ZMod q) (levels : ℕ) : Fin (2 ^ levels) → ZMod q := fun i => point ζ levels i

/-- The residue degree after `levels` layers, `256 / 2^levels`. -/
abbrev blockSize (levels : ℕ) : ℕ := 2 ^ (8 - levels)

theorem blockSize_mul_pow {levels : ℕ} (hL : levels ≤ 8) : blockSize levels * 2 ^ levels = 256 := by
  rw [blockSize, ← pow_add, Nat.sub_add_cancel hL]
  rfl

theorem pow_mul_blockSize {levels : ℕ} (hL : levels ≤ 8) : 2 ^ levels * blockSize levels = 256 := by
  rw [Nat.mul_comm, blockSize_mul_pow hL]

theorem blockSize_pos (levels : ℕ) : 0 < blockSize levels := Nat.two_pow_pos _

theorem blockSize_succ {levels : ℕ} (hL : levels + 1 ≤ 8) :
    blockSize levels = 2 * blockSize (levels + 1) := by
  rw [blockSize, blockSize, show 8 - levels = (8 - (levels + 1)) + 1 by omega, pow_succ]
  ring

theorem block_idx_lt {levels r t : ℕ} (hL : levels ≤ 8) (hr : r < blockSize levels)
    (ht : t < 2 ^ levels) : r + blockSize levels * t < 256 := by
  have h := Nat.mul_le_mul_left (blockSize levels) (Nat.succ_le_of_lt ht)
  rw [blockSize_mul_pow hL, Nat.mul_succ] at h
  omega

theorem div_blockSize_lt {levels k : ℕ} (hL : levels ≤ 8) (hk : k < 256) :
    k / blockSize levels < 2 ^ levels :=
  (Nat.div_lt_iff_lt_mul (blockSize_pos levels)).2 (by rw [pow_mul_blockSize hL]; exact hk)

end NTT

/-- The NTT domain `T_q` after `levels` layers: residues of degree below `256 / 2^levels` at the
points `ζ^(2·BitRev(i) + 1)` (FIPS 203 §2.4.6 with `levels = 7`, FIPS 204 §7.5 with `8`). -/
abbrev NTTDomain (ζ : ZMod q) (levels : ℕ) :=
  Residues (ZMod q) (NTT.blockSize levels) (2 ^ levels) (NTT.points ζ levels)

namespace NTT

variable {q : ℕ}

/-- `f mod (X^d - γ)` for `d = blockSize levels`: coefficient `r` is `∑ₜ f[r + d·t] γ^t`. -/
def modBinomial (levels : ℕ) (hL : levels ≤ 8) (f : Poly (ZMod q) 256 (-1)) (γ : ZMod q) :
    Poly (ZMod q) (blockSize levels) γ :=
  Poly.ofFn fun r => ∑ t : Fin (2 ^ levels),
    f[r.val + blockSize levels * t.val]'(block_idx_lt hL r.isLt t.isLt) * γ ^ t.val

/-- The transform as residues. -/
def nttSpec (ζ : ZMod q) (levels : ℕ) (f : Poly (ZMod q) 256 (-1)) (hL : levels ≤ 8 := by decide) :
    NTTDomain ζ levels :=
  Residues.ofFn fun i => modBinomial levels hL f (point ζ levels i)

/-- The transform as `levels` splitting layers. -/
def nttRec (ζ : ZMod q) : (levels : ℕ) → levels ≤ 8 → Poly (ZMod q) 256 (-1) → NTTDomain ζ levels
  | 0, _, f => ⟨#v[f.coeffs]⟩
  | l + 1, hL, f =>
    Residues.split (nttRec (ζ ^ 2) l (by omega) f) (points ζ (l + 1)) (blockSize_succ hL) (Nat.pow_succ ..)

/-- The inverse transform: `f[r + d·t] = 2^(-levels) ∑ᵢ (residue i)[r] · (point i)^(-t)`. -/
def nttInvSpec (ζ : ZMod q) (levels : ℕ) («f̂» : NTTDomain ζ levels) : Poly (ZMod q) 256 (-1) :=
  Poly.ofFn fun k =>
    (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      («f̂» i)[k.val % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k.val / blockSize levels)

theorem getElem_modBinomial {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256 (-1)) (γ : ZMod q)
    (r : ℕ) (hr : r < blockSize levels) :
    (modBinomial levels hL f γ)[r] = ∑ t : Fin (2 ^ levels),
      f[r + blockSize levels * t.val]'(block_idx_lt hL hr t.isLt) * γ ^ t.val :=
  Poly.getElem_ofFn ..

theorem nttSpec_apply (ζ : ZMod q) {levels : ℕ} (hL : levels ≤ 8) (f : Poly (ZMod q) 256 (-1))
    (i : Fin (2 ^ levels)) : nttSpec ζ levels f hL i = modBinomial levels hL f (point ζ levels i) :=
  Residues.apply_ofFn _ i

theorem getElem_nttInvSpec (ζ : ZMod q) (levels : ℕ) (a : NTTDomain ζ levels)
    (k : ℕ) (hk : k < 256) :
    (nttInvSpec ζ levels a)[k] = (2 ^ levels : ZMod q)⁻¹ * ∑ i : Fin (2 ^ levels),
      (a i)[k % blockSize levels]'(Nat.mod_lt _ (blockSize_pos levels)) *
        (point ζ levels i.val)⁻¹ ^ (k / blockSize levels) :=
  Poly.getElem_ofFn ..

end NTT

end Wychelean.PolyRing
