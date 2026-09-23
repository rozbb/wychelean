import Wychelean.KEM.MLKEM.Parameters

/-! FIPS 203 §4.3: the number-theoretic transform and multiplication in `T_q`. -/

namespace Wychelean.KEM.MLKEM

open Wychelean
open scoped Wychelean.Notations Wychelean.Utils.Linear

/-- Stepped ranges `[a : b : s]` whose step is a variable, as in the butterfly loops: the
positivity proof is taken from the context (`Bounds.len_pos`) when `decide` cannot supply it. -/
scoped macro_rules
| `([ $start : $stop : $step ]) =>
  `({ start := $start, stop := $stop, step := $step, step_pos := by first | decide | omega :
      Std.Legacy.Range })

namespace Bounds

/-- The loop variable `len` of Algorithms 9 and 10 is positive, so `[0 : 256 : 2 * len]` is a
well-formed range. -/
theorem len_pos {len : ℕ}
    (h0 : len ∈ [128, 64, 32, 16, 8, 4, 2] ∨ len ∈ [2, 4, 8, 16, 32, 64, 128]) : 0 < 2 * len := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h0
  rcases h0 with h0 | h0 <;> rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `j + len < 256` inside the butterfly loops of Algorithms 9 and 10. -/
theorem ntt_idx_lt {len start j : ℕ} {hlen : 0 < 2 * len}
    (h0 : len ∈ [128, 64, 32, 16, 8, 4, 2] ∨ len ∈ [2, 4, 8, 16, 32, 64, 128])
    (h1 : start ∈ ({ start := 0, stop := 256, step := 2 * len, step_pos := hlen } : Std.Legacy.Range))
    (hj : j ∈ [start : start + len]) : j + len < 256 := by
  have hs : start < 256 := h1.2.1
  have hm : (start - 0) % (2 * len) = 0 := h1.2.2
  have hj' : j < start + len := hj.2.1
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h0
  rcases h0 with h0 | h0 <;> rcases h0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end Bounds

open Bounds

/-! ## §4.3 Algorithm 9 — NTT(f) -/
def Polynomial.NTT (f : Polynomial) : Tq := Id.run do
  let mut «f̂» := f.coeffs                                                     -- Alg. 9, step 1
  let mut i := 1                                                              -- Alg. 9, step 2
  for h0 : len in [128, 64, 32, 16, 8, 4, 2] do                              -- Alg. 9, step 3
    have := len_pos (.inl h0)
    for h1 : start in [0:256:2*len] do                                        -- Alg. 9, step 4
      let zeta := ζ ^ bitRev 7 i                                              -- Alg. 9, step 5
      i := i + 1                                                              -- Alg. 9, step 6
      for h : j in [start:start+len] do                                       -- Alg. 9, step 7
        have := ntt_idx_lt (.inl h0) h1 h
        let t := zeta * «f̂»[j + len]                                         -- Alg. 9, step 8
        «f̂» := «f̂».set (j + len) («f̂»[j] - t)                               -- Alg. 9, step 9
        «f̂» := «f̂».set j («f̂»[j] + t)                                       -- Alg. 9, step 10
  return ⟨«f̂»⟩                                                               -- Alg. 9, step 14

/-! ## §4.3 Algorithm 10 — NTT⁻¹(f̂) -/
def Tq.NTTInv («f̂» : Tq) : Polynomial := Id.run do
  let mut f := «f̂».coeffs                                                     -- Alg. 10, step 1
  let mut i := 127                                                            -- Alg. 10, step 2
  for h0 : len in [2, 4, 8, 16, 32, 64, 128] do                              -- Alg. 10, step 3
    have := len_pos (.inr h0)
    for h1 : start in [0:256:2*len] do                                        -- Alg. 10, step 4
      let zeta := ζ ^ bitRev 7 i                                              -- Alg. 10, step 5
      i := i - 1                                                              -- Alg. 10, step 6
      for h : j in [start:start+len] do                                       -- Alg. 10, step 7
        have := ntt_idx_lt (.inr h0) h1 h
        let t := f[j]                                                         -- Alg. 10, step 8
        f := f.set j (t + f[j + len])                                         -- Alg. 10, step 9
        f := f.set (j + len) (zeta * (f[j + len] - t))                        -- Alg. 10, step 10
  f := (3303 : Zq) • f                                                        -- Alg. 10, step 14
  return ⟨f⟩                                                                  -- Alg. 10, step 15

/-! ## §4.3.1 Algorithm 12 — BaseCaseMultiply(a₀, a₁, b₀, b₁, γ) -/
def BaseCaseMultiply (a₀ a₁ b₀ b₁ γ : Zq) : Zq × Zq :=
  let c₀ := a₀ * b₀ + a₁ * b₁ * γ                                             -- Alg. 12, step 1
  let c₁ := a₀ * b₁ + a₁ * b₀                                                 -- Alg. 12, step 2
  (c₀, c₁)                                                                    -- Alg. 12, step 3

/-! ## §4.3.1 Algorithm 11 — MultiplyNTTs(f̂, ĝ) -/
def MultiplyNTTs («f̂» «ĝ» : Tq) : Tq := Id.run do
  let mut «ĥ» : Vector Zq 256 := Vector.replicate 256 0
  for h : i in [0:128] do                                                     -- Alg. 11, step 1
    have : i < 128 := h.2.1
    let (c₀, c₁) := BaseCaseMultiply «f̂»[2 * i] «f̂»[2 * i + 1] «ĝ»[2 * i] «ĝ»[2 * i + 1]
      (ζ ^ (2 * bitRev 7 i + 1))                                              -- Alg. 11, step 2
    «ĥ» := «ĥ».set (2 * i) c₀
    «ĥ» := «ĥ».set (2 * i + 1) c₁
  return ⟨«ĥ»⟩                                                               -- Alg. 11, step 4

/-- `f̂ ×_{T_q} ĝ` is `MultiplyNTTs(f̂, ĝ)` (§2.4.5, Eq. 2.8). -/
instance : Mul Tq := ⟨MultiplyNTTs⟩

/-! ### NTT and NTT⁻¹ of vectors (§2.4.6, Eq. 2.9; §2.4.8, Eq. 2.16) -/

/-- `NTT(v)`: run NTT once for each coordinate of `v`. -/
def PolyVector.NTT {n : ℕ} (v : Vector Polynomial n) : Vector Tq n := v.map Polynomial.NTT

/-- `NTT⁻¹(v̂)`: run NTT⁻¹ once for each coordinate of `v̂`. -/
def NTTVector.NTTInv {n : ℕ} (v : Vector Tq n) : Vector Polynomial n := v.map Tq.NTTInv

end Wychelean.KEM.MLKEM
