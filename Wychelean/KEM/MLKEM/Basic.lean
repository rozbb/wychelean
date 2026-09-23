import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod
import Wychelean.Utils.Round
import Wychelean.KEM.MLKEM.NTT
import Wychelean.Hashes.SHA3.XOF

/-!
# ML-KEM
FIPS 203: https://doi.org/10.6028/NIST.FIPS.203
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.Utils.Linear
open scoped Wychelean.Notations

/-! ## Index bounds (`open Bounds`) -/

namespace Bounds

/-! ### Range membership lemmas -/

/-- Forward-chaining: extract `i < stop` from `i ∈ [start : stop]`. -/
@[scoped grind →]
theorem srrange_upper {i n0 n1 : Nat}
    (hm : i ∈ [n0:n1]) : i < n1 := hm.2.1

/-- Forward-chaining: extract `start ≤ i` from `i ∈ [start : stop]`. -/
@[scoped grind →]
theorem srrange_lower {i n0 n1 : Nat}
    (hm : i ∈ [n0:n1]) : n0 ≤ i := hm.1

/-! ### Sampling index bounds (§4.2.2) -/

/-- `2 * i * η ≤ 510 * η` from `i < 256` (SamplePolyCBD, Algorithm 8). -/
@[scoped grind ←]
theorem sample_cbd_idx_le (i : Nat) (η : Nat) (hi : i < 256) :
    2 * i * η ≤ 510 * η := by
  have : i ≤ 255 := by omega
  calc 2 * i * η ≤ 2 * 255 * η := Nat.mul_le_mul_right η (Nat.mul_le_mul_left 2 this)
    _ = 510 * η := by ring

end Bounds

open Bounds

/-! ## §4.1 Cryptographic Functions (Eq. 4.1–4.5) -/

/-- H(s) := SHA3-256(s) — Eq. (4.4). -/
def H {n} (s : ByteVec n) : ByteVec hashLen := SHA3.sha3_256 s

/-- J(s) := SHAKE256(s, 32) — Eq. (4.4). -/
def J {n} (s : ByteVec n) : ByteVec hashLen := SHA3.shake256 s hashLen

/-- G(c) := SHA3-512(c), split into two 32-byte outputs — Eq. (4.5). -/
def G {n} (s : ByteVec n) : ByteVec hashLen × ByteVec hashLen :=
  split (SHA3.sha3_512 s) hashLen hashLen

/-- PRF_η(s,b) := SHAKE256(s‖b, 8·64·η) — Eq. (4.3). -/
def PRF (η : Η) (s : Seed) (b : Byte) : ByteVec (64 * η) :=
  SHA3.shake256 (s ‖ #v[b]) (64 * η)

/-! ### SHAKE128 XOF — §4.1, Eq. (4.1)–(4.2) -/

def XOF.Init := SHA3.SHAKE128.init

def XOF.Absorb s (B : ByteVec ℓ) := SHA3.SHAKE128.absorb s B

def XOF.Squeeze s ℓ := SHA3.SHAKE128.squeeze s ℓ

/-! ## §4.2.1 Compress / Decompress — Eq. (4.7), (4.8)

Lossy compression from ℤ_q to ℤ_{2^d} and decompression back. -/

def Compress (d : ℕ) (x : Zq) (_ : 1 ≤ d ∧ d < 12 := by grind) : ZMod (m d) :=
  ⌈ ((2^d : ℚ) / (q : ℚ)) * x.val ⌋

def Decompress (d : ℕ) (y : ZMod (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Zq :=
  ⌈ ((q : ℚ) / (2^d : ℚ)) * y.val ⌋

def Polynomial.Compress (d : ℕ) (f : Polynomial) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial (m d) :=
  Polynomial.ofFn fun i => MLKEM.Compress d f[i]

def Polynomial.Decompress (d : ℕ) (f : Polynomial (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial :=
  Polynomial.ofFn fun i => MLKEM.Decompress d f[i]

def PolyVector.Compress {k : K} (d : ℕ) (v : PolyVector q k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector (m d) k :=
  v.map (Polynomial.Compress d)

def PolyVector.Decompress {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector q k :=
  v.map (Polynomial.Decompress d)

/-! ## §4.2.2 Algorithm 7 — SampleNTT(B) -/
def SampleNTT (B : ByteVec (seedLen + 2)) : Tq := Id.run do
  let mut ctx := XOF.Init                                                     -- Alg. 7, step 1
  ctx := XOF.Absorb ctx B                                                     -- Alg. 7, step 2
  let mut «â» : Vector Zq 256 := Vector.replicate 256 0
  let mut j := 0                                                              -- Alg. 7, step 3
  while hj : j < 256 do                                                       -- Alg. 7, step 4
    let (ctx', C) := XOF.Squeeze ctx 3                                        -- Alg. 7, step 5
    ctx := ctx'
    let d₁ := C[0].toNat + 256 * (C[1].toNat % 16)                            -- Alg. 7, step 6
    let d₂ := C[1].toNat / 16 + 16 * C[2].toNat                              -- Alg. 7, step 7
    if d₁ < q then                                                            -- Alg. 7, step 8
      «â» := «â».set j d₁                                                     -- Alg. 7, step 9
      j := j + 1                                                              -- Alg. 7, step 10
    if h : d₂ < q ∧ j < 256 then                                              -- Alg. 7, step 12
      «â» := «â».set j d₂                                                     -- Alg. 7, step 13
      j := j + 1                                                              -- Alg. 7, step 14
  return ⟨«â»⟩                                                               -- Alg. 7, step 17

/-! ## §4.2.2 Algorithm 8 — SamplePolyCBD_η(B) -/

theorem Η.val_le (η : Η) : η.val ≤ 3 := by
  have h := η.property; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; omega

def SamplePolyCBD {η : Η} (B : ByteVec (64 * η)) : Polynomial := Id.run do
  let b := bytesToBits B                                                      -- Alg. 8, step 1
  let mut f : Vector Zq 256 := Vector.replicate 256 0
  for hi: i in [0:256] do                                                     -- Alg. 8, step 2
    have := sample_cbd_idx_le i η (by grind)
    let x := ∑ j : Fin η, b[2 * i * η + j].toNat                              -- Alg. 8, step 3
    let y := ∑ j : Fin η, b[2 * i * η + η + j].toNat                          -- Alg. 8, step 4
    f := f.set i (x - y)                                                      -- Alg. 8, step 5
  return ⟨f⟩                                                                  -- Alg. 8, step 7

end Wychelean.KEM.MLKEM
