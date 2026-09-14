import Wychelean.Lattice.NTTSpec
import Mathlib.Tactic.IntervalCases

/-!
# Number-theoretic transform over ℤ_q[X] / (X^256 + 1)

The in-place Cooley–Tukey transform and its Gentleman–Sande inverse, as written in FIPS 203
Algorithms 9–10 (ML-KEM: `ζ = 17`, seven layers) and FIPS 204 Algorithms 41–42 (ML-DSA:
`ζ = 1753`, eight layers). `ζ` is a primitive `2^(levels + 1)`-th root of unity, and layer `l`
splits each factor `X^(2·len) - ζ^(2m)` into `(X^len - ζ^m)(X^len + ζ^m)` with
`len = 128 / 2^l`. The loops are adapted from Microsoft SymCrypt (MIT; see
Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.Lattice

open Wychelean
open scoped Wychelean.Notations

/-- Stepped ranges `[a : b : s]` whose step is a variable, as in the butterfly loops: the
positivity proof is taken from the context when `decide` cannot supply it. -/
scoped macro_rules
| `([ $start : $stop : $step ]) =>
  `({ start := $start, stop := $stop, step := $step, step_pos := by first | decide | omega :
      Std.Legacy.Range })

namespace NTT

/-- The butterfly half-lengths of the first `levels` layers: `128, 64, …, 128 / 2^(levels-1)`. -/
def lens (levels : ℕ) : List ℕ := (List.range levels).map fun l => 128 / 2 ^ l

theorem mem_lens {levels len : ℕ} (h : len ∈ lens levels) : ∃ l < levels, len = 128 / 2 ^ l := by
  simp only [lens, List.mem_map, List.mem_range] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

/-! ### Index bounds for the butterfly loops, activated by `open Bounds`. -/
namespace Bounds

/-- Forward-chaining: extract `i < stop` from `i ∈ [start : stop]`. -/
@[scoped grind →]
theorem range_upper {i n0 n1 : ℕ} (hm : i ∈ [n0:n1]) : i < n1 := hm.2.1

/-- With at most eight layers, every half-length is positive, so `[0 : 256 : 2 * len]` is a
well-formed range. -/
theorem len_pos {levels len : ℕ} (hL : levels ≤ 8) (h : len ∈ lens levels) : 0 < 2 * len := by
  obtain ⟨l, hl, rfl⟩ := mem_lens h
  have : l < 8 := by omega
  interval_cases l <;> decide

/-- `j + len < 256` inside a butterfly. -/
theorem idx_lt {levels len start j : ℕ} {hlen : 0 < 2 * len} (hL : levels ≤ 8)
    (h0 : len ∈ lens levels)
    (h1 : start ∈ ({ start := 0, stop := 256, step := 2 * len, step_pos := hlen } : Std.Legacy.Range))
    (hj : j ∈ [start : start + len]) : j + len < 256 := by
  have hs : start < 256 := h1.2.1
  have hm : (start - 0) % (2 * len) = 0 := h1.2.2
  have hj' : j < start + len := hj.2.1
  obtain ⟨l, hl, rfl⟩ := mem_lens h0
  have : l < 8 := by omega
  interval_cases l <;> simp only [Nat.reducePow, Nat.reduceDiv] at * <;> omega

end Bounds

open Bounds

/-- Forward transform, FIPS 203 Algorithm 9 / FIPS 204 Algorithm 41: Cooley–Tukey butterflies
with twiddles `ζ^BitRev(i)`. -/
def ntt (ζ : ZMod q) (levels : ℕ) (f : Poly q 256) (hL : levels ≤ 8 := by decide) :
    Tq q ζ levels := ⟨Id.run do
  let mut «f̂» := f
  let mut i := 1
  for h0: len in lens levels do
    have hlen := len_pos hL h0
    for h1: start in [0 : 256 : 2*len] do
      let zeta := ζ ^ (bitRev levels i)
      i := i + 1
      for h: j in [start : start+len] do
        have := idx_lt hL h0 h1 h
        let t := zeta * «f̂»[j + len]
        «f̂» := «f̂».set (j + len) («f̂»[j] - t)
        «f̂» := «f̂».set j         («f̂»[j] + t)
  pure «f̂»⟩

/-- Inverse transform, FIPS 203 Algorithm 10 / FIPS 204 Algorithm 42: Gentleman–Sande
butterflies followed by division by `2^levels`. -/
def nttInv (ζ : ZMod q) (levels : ℕ) («f̂» : Tq q ζ levels) (hL : levels ≤ 8 := by decide) :
    Poly q 256 := Id.run do
  let mut f := «f̂».residues
  let mut i := 2 ^ levels - 1
  for h0: len in (lens levels).reverse do
    have h0' := List.mem_reverse.mp h0
    have hlen := len_pos hL h0'
    for h1: start in [0:256:2*len] do
      let zeta := ζ ^ bitRev levels i
      i := i - 1
      for h: j in [start:start+len] do
        have := idx_lt hL h0' h1 h
        let t := f[j]
        f := f.set j (t + f[j + len])
        f := f.set (j + len) (zeta * (f[j + len] - t))
  f := ((2 ^ levels : ZMod q)⁻¹) • f
  pure f

end NTT

end Wychelean.Lattice
