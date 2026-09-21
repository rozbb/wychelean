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
open scoped Wychelean.Utils.PolyRing
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

/-! ### Nonlinear index bounds -/

/-- `i * d + j < n * d` from `i < n, j < d`. -/
@[scoped grind ←]
theorem idx_mul_add_lt (i d j n : Nat) (hi : i < n) (hj : j < d) :
    i * d + j < n * d := by
  calc i * d + j < i * d + d := by omega
    _ = (i + 1) * d := by ring
    _ ≤ n * d := Nat.mul_le_mul_right d hi

/-! ### Encoding/sampling index bounds (§4.2.1, §4.2.2) -/

/-- `i * d ≤ 255 * d` from `i < 256` (ByteEncode/ByteDecode, Algorithms 5–6). -/
@[scoped grind ←]
theorem byte_encode_idx_le (i d : Nat) (hi : i < 256) : i * d ≤ 255 * d :=
  Nat.mul_le_mul_right d (by omega)

/-- `32 * d * (i + 1) ≤ 32 * d * k` from `i < k` (PolyVector.ByteDecode). -/
@[scoped grind ←]
theorem poly_vec_decode_idx_le (d i : Nat) {k : Nat} (hi : i < k) :
    32 * d * (i + 1) ≤ 32 * d * k :=
  Nat.mul_le_mul_left _ hi

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
  Utils.PolyRing.PolyMod.ofFn fun i => MLKEM.Compress d f[i]

def Polynomial.Decompress (d : ℕ) (f : Polynomial (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial :=
  Utils.PolyRing.PolyMod.ofFn fun i => MLKEM.Decompress d f[i]

def PolyVector.Compress {k : K} (d : ℕ) (v : PolyVector q k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector (m d) k :=
  v.map (Polynomial.Compress d)

def PolyVector.Decompress {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector q k :=
  v.map (Polynomial.Decompress d)

/-! ## §4.2.1 Algorithm 5 — ByteEncode_d(F) -/
def ByteEncode (d : ℕ) (F : Vector (ZMod (m d)) 256) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (32 * d) := Id.run do
  let mut b := Vector.replicate (256 * d) 0
  for hi: i in [0:256] do
    have := byte_encode_idx_le i d
    let mut a := F[i].val
    for hj: j in [0:d] do
      b := b.set (i * d + j) (Bool.ofNat (a % 2))
      a := (a - b[i * d + j].toNat) / 2
  let B := bitsToBytes (b.cast (by grind))
  pure B

/-! ## §4.2.1 Algorithm 6 — ByteDecode_d(B) -/
def ByteDecode {d : ℕ} (B : ByteVec (32 * d)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : Vector (ZMod (m d)) 256 :=
  let b := bytesToBits B
  Vector.ofFn fun i =>
    have := byte_encode_idx_le i d
    ∑ (j : Fin d), b[i * d + j].toNat * 2^j.val

/-- `ByteEncode_d` of each entry, concatenated (§2.4.8). -/
def PolyVector.ByteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (32 * d * k) :=
  (v.map fun f => MLKEM.ByteEncode d f.coeffs).flatten.cast (Nat.mul_comm _ _)

def PolyVector.ByteDecode {k : K} (d : ℕ) (bytes : ByteVec (32 * d * k)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : PolyVector (m d) k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le d i i.isLt
    Utils.PolyRing.PolyMod.ofCoeffs (MLKEM.ByteDecode (slice bytes (32 * d * i) (32 * d) (by grind)))

/-- `ByteEncode₁₂` of a vector over `T_q`, each entry by its residues in the order of §2.4.6. -/
def ByteEncode₁₂ {k : K} (v : NTTVector k) : ByteVec (vecLen' k) :=
  (v.map fun «f̂» => MLKEM.ByteEncode 12 «f̂».coeffs).flatten.cast (Nat.mul_comm _ _)

def ByteDecode₁₂ {k : K} (bytes : ByteVec (vecLen' k)) : NTTVector k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le 12 i i.isLt
    Tq.mk (MLKEM.ByteDecode (slice bytes (32 * 12 * i) (32 * 12) (by grind)))

/-! ## §4.2.2 Algorithm 7 — SampleNTT(B) -/
def SampleNTT (B : ByteVec (seedLen + 2)) : Tq := Tq.mk <| Id.run do
  let mut ctx := XOF.Init
  ctx := XOF.Absorb ctx B
  let mut «â» : Vector Zq 256 := Vector.replicate 256 0
  let mut j := 0
  while hj : j < 256 do
    let (ctx', C) := XOF.Squeeze ctx 3
    ctx := ctx'
    let d₁ := C[0].toNat + 256 * (C[1].toNat % 16)
    let d₂ := C[1].toNat / 16 + 16 * C[2].toNat
    if d₁ < q then
      «â» := «â».set j d₁
      j := j + 1
    if h : d₂ < q ∧ j < 256 then
      «â» := «â».set j d₂
      j := j + 1
  pure «â»

/-! ## §4.2.2 Algorithm 8 — SamplePolyCBD_η(B) -/

theorem Η.val_le (η : Η) : η.val ≤ 3 := by
  have h := η.property; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; omega

def SamplePolyCBD {η : Η} (B : ByteVec (64 * η)) : Polynomial :=
  let b := bytesToBits B
  Utils.PolyRing.PolyMod.ofFn fun i =>
    have := sample_cbd_idx_le i η (by grind)
    let x := ∑ (j : Fin η), b[2 * i.val * η + j].toNat
    let y := ∑ (j : Fin η), b[2 * i.val * η + η + j].toNat
    x - y

/-- `Â[i][j] = SampleNTT(ρ ‖ j ‖ i)` (Algorithm 13, steps 3–7; Algorithm 14, steps 4–8). -/
def SampleMatrix {k : K} (ρ : Seed) : NTTMatrix k :=
  Vector.ofFn fun i => Vector.ofFn fun j => SampleNTT (ρ ‖ #v[(j : Byte), (i : Byte)])

/-- `k` polynomials `SamplePolyCBD_η(PRF_η(s, N))` for `N = N₀, N₀ + 1, …`
(the loops over `N` of Algorithms 13–14). -/
def SampleCBDVector {k : K} (η : Η) (s : Seed) (N₀ : ℕ) : PolyVector q k :=
  Vector.ofFn fun i => SamplePolyCBD (PRF η s ((N₀ + i : ℕ) : Byte))

end Wychelean.KEM.MLKEM
