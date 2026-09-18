import Wychelean.PolyRing.NTT

/-!
The in-place butterflies of FIPS 203 Algorithms 9–10 and FIPS 204 Algorithms 41–42, adapted from
Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean

They are the executable oracle for `NTT.ntt`/`NTT.nttInv`, checked against them by the test
suite; the specifications and proofs are about the layer form.
-/

namespace Wychelean.PolyRing.NTT.Loops

open scoped Wychelean.Notations

/-- Stepped ranges `[a : b : s]` whose step is a variable, as in the butterfly loops: the
positivity proof is taken from the context when `decide` cannot supply it. -/
scoped macro_rules
| `([ $start : $stop : $step ]) =>
  `({ start := $start, stop := $stop, step := $step, step_pos := by first | decide | omega :
      Std.Legacy.Range })

variable {F : Type*} {n : ℕ}

/-- The butterfly half-lengths of the `levels` layers: `n/2, n/4, …, n/2^levels`. -/
def lens (n levels : ℕ) : List ℕ := (List.range levels).map fun l => n / 2 ^ (l + 1)

theorem mem_lens {levels len : ℕ} (h : len ∈ lens n levels) : ∃ l < levels, len = n / 2 ^ (l + 1) := by
  simp only [lens, List.mem_map, List.mem_range] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

/-! ### Index bounds for the butterfly loops, activated by `open Bounds`. -/
namespace Bounds

/-- Forward-chaining: extract `i < stop` from `i ∈ [start : stop]`. -/
@[scoped grind →]
theorem range_upper {i n0 n1 : ℕ} (hm : i ∈ [n0:n1]) : i < n1 := hm.2.1

theorem two_mul_len {levels l : ℕ} (hL : 2 ^ levels ∣ n) (hl : l < levels) :
    2 * (n / 2 ^ (l + 1)) = n / 2 ^ l :=
  (blockSize_succ (dvd_of_le hl hL)).symm

theorem two_mul_len_dvd {levels l : ℕ} (hL : 2 ^ levels ∣ n) (hl : l < levels) :
    2 * (n / 2 ^ (l + 1)) ∣ n := by
  rw [two_mul_len hL hl]
  exact Nat.div_dvd_of_dvd (dvd_of_le hl.le hL)

/-- Every half-length is positive, so `[0 : n : 2 * len]` is a well-formed range. -/
theorem len_pos [NeZero n] {levels len : ℕ} (hL : 2 ^ levels ∣ n) (h : len ∈ lens n levels) :
    0 < 2 * len := by
  obtain ⟨l, hl, rfl⟩ := mem_lens h
  rw [two_mul_len hL hl]
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) (dvd_of_le hl.le hL))
    (Nat.two_pow_pos _)

/-- `j + len < n` inside a butterfly. -/
theorem idx_lt {levels len start j : ℕ} {hlen : 0 < 2 * len} (hL : 2 ^ levels ∣ n)
    (h0 : len ∈ lens n levels)
    (h1 : start ∈ ({ start := 0, stop := n, step := 2 * len, step_pos := hlen } : Std.Legacy.Range))
    (hj : j ∈ [start : start + len]) : j + len < n := by
  have hs : start < n := h1.2.1
  have hm : (start - 0) % (2 * len) = 0 := h1.2.2
  have hj' : j < start + len := hj.2.1
  obtain ⟨l, hl, hlen⟩ := mem_lens h0
  obtain ⟨q, hq⟩ : 2 * len ∣ n := hlen ▸ two_mul_len_dvd hL hl
  rw [Nat.sub_zero] at hm
  obtain ⟨s, hs'⟩ := Nat.dvd_of_mod_eq_zero hm
  have hsq : s < q := by
    rw [hs', hq] at hs
    exact Nat.lt_of_mul_lt_mul_left hs
  have := Nat.mul_le_mul_left (2 * len) hsq
  rw [Nat.mul_succ] at this
  omega

end Bounds

open Bounds

/-- Forward transform, FIPS 203 Algorithm 9 / FIPS 204 Algorithm 41: Cooley–Tukey butterflies
with twiddles `ζ^BitRev(i)`. -/
def ntt [CommRing F] [NeZero n] (levels : ℕ) (ζ : F) (f : PolyMod F n (-1)) (hL : 2 ^ levels ∣ n) :
    Residues.Binomial F (n / 2 ^ levels) (2 ^ levels) (points ζ levels) :=
  Residues.ofFlat <| Vector.cast (blockSize_mul hL) <| Id.run do
  let mut «f̂» := f.coeffs
  let mut i : ℕ := 1
  for h0: len in lens n levels do
    have hlen := len_pos hL h0
    for h1: start in [0 : n : 2*len] do
      let zeta := ζ ^ (bitRev levels i)
      i := i + 1
      for h: j in [start : start+len] do
        have := idx_lt hL h0 h1 h
        let t := zeta * «f̂»[j + len]
        «f̂» := «f̂».set (j + len) («f̂»[j] - t)
        «f̂» := «f̂».set j         («f̂»[j] + t)
  pure «f̂»

/-- Inverse transform, FIPS 203 Algorithm 10 / FIPS 204 Algorithm 42: Gentleman–Sande
butterflies followed by division by `2^levels`. -/
def nttInv [Field F] [NeZero n] (levels : ℕ) (ζ : F)
    («f̂» : Residues.Binomial F (n / 2 ^ levels) (2 ^ levels) (points ζ levels)) (hL : 2 ^ levels ∣ n) :
    PolyMod F n (-1) := Id.run do
  let mut f := «f̂».flatten.cast (blockSize_mul hL).symm
  let mut i : ℕ := 2 ^ levels - 1
  for h0: len in (lens n levels).reverse do
    have h0' := List.mem_reverse.mp h0
    have hlen := len_pos hL h0'
    for h1: start in [0:n:2*len] do
      let zeta := ζ ^ bitRev levels i
      i := i - 1
      for h: j in [start:start+len] do
        have := idx_lt hL h0' h1 h
        let t := f[j]
        f := f.set j (t + f[j + len])
        f := f.set (j + len) (zeta * (f[j + len] - t))
  pure ((2 ^ levels : F)⁻¹ • PolyQuot.ofCoeffs f)

end Wychelean.PolyRing.NTT.Loops
