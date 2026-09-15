import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Wychelean.Utils.Round
import Wychelean.PolyRing
import Wychelean.Hashes.SHA3.XOF

/-!
# ML-KEM
FIPS 203: https://doi.org/10.6028/NIST.FIPS.203
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.PolyRing
open scoped Wychelean.Notations

/-! ## Bounds infrastructure for `get_elem_tactic`

These scoped lemmas let `grind` discharge array-index bounds arising from `for`
loops over ranges. They are activated by `open Bounds`. -/

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

/-! ## §2.4 / §8 Constants and Parameters (Table 2) -/

/- `ByteVec n` (from Defs) is the standard interface type in FIPS 203. -/

/-- q = 3329, the modulus for ML-KEM (§2). -/
abbrev q : Nat := 3329

/-- ℤ_q = ℤ/3329ℤ, the coefficient ring. -/
abbrev Zq := ZMod q

/-- `ℤ_m[X] / (X^256 + 1)`: `R_q` for `m = q`, and the compressed coefficients for `m = 2^d`
(§4.2.1). -/
abbrev Polynomial (m : ℕ := q) := PolyRing.Poly (ZMod m) 256 (-1)

/-- ζ = 17 ∈ ℤ_q is a primitive 256-th root of unity modulo q (§4.3). -/
def ζ : Zq := 17

/-- `T_q`, the NTT representation of `R_q` (§2.4.6). -/
abbrev Tq := PolyRing.NTTDomain ζ 7

instance : Fact (7 ≤ 8) := ⟨by decide⟩

/-- m(d) = 2^d if d < 12, q if d = 12 (§4.2.1). -/
abbrev m (d : ℕ) := if d < 12 then 2^d else q

/-- ML-KEM parameter sets (§8, Table 2).
    ML-KEM-512, ML-KEM-768, and ML-KEM-1024 correspond to
    NIST security categories 1, 3, and 5 respectively. -/
inductive ParameterSet where
  | ML_KEM_512
  | ML_KEM_768
  | ML_KEM_1024

/-- Module rank `k` (Table 2): dimension of the polynomial module lattice. -/
abbrev K := {k : ℕ // k ∈ ({2, 3, 4} : Set ℕ)}
/-- CBD noise parameter type: η ∈ {2, 3} (Table 2). -/
abbrev Η := {η : ℕ // η ∈ ({2, 3} : Set ℕ)}

/-- Module rank k: 2 for ML-KEM-512, 3 for 768, 4 for 1024 (Table 2). -/

@[reducible, scoped grind] def k (p : ParameterSet) : K :=
  match p with
  | .ML_KEM_512  => ⟨2, by grind⟩
  | .ML_KEM_768  => ⟨3, by grind⟩
  | .ML_KEM_1024 => ⟨4, by grind⟩

/-- CBD noise parameter η₁ (Table 2): 3 for ML-KEM-512, 2 for 768/1024. -/
@[reducible] def η₁ (p : ParameterSet) : Η :=
  match p with
  | .ML_KEM_512  => ⟨3, by grind⟩
  | .ML_KEM_768  => ⟨2, by grind⟩
  | .ML_KEM_1024 => ⟨2, by grind⟩

/-- CBD noise parameter η₂ = 2 for all parameter sets (Table 2). -/
def η₂ : Η := ⟨2, by grind⟩

/-- Ciphertext compression parameter dᵤ (Table 2): 10 for 512/768, 11 for 1024. -/
@[reducible] def dᵤ (p : ParameterSet) : ℕ :=
  match p with
  | .ML_KEM_512  => 10
  | .ML_KEM_768  => 10
  | .ML_KEM_1024 => 11

/-- Ciphertext compression parameter dᵥ (Table 2): 4 for 512/768, 5 for 1024. -/
@[reducible] def dᵥ (p : ParameterSet) : ℕ :=
  match p with
  | .ML_KEM_512  => 4
  | .ML_KEM_768  => 4
  | .ML_KEM_1024 => 5

/-! ### Sizes in bytes (Table 3) -/

/-- Seeds, messages and shared secret keys are 32 bytes (§3.3, §7). -/
abbrev seedLen : ℕ := 32
abbrev Seed := ByteVec seedLen
abbrev SharedKey := ByteVec seedLen
/-- The outputs of `H`, `J` and each half of `G` are 32 bytes (§4.1). -/
abbrev hashLen : ℕ := 32
/-- `ByteEncode₁₂` of a vector of `k` polynomials: `384k`. -/
abbrev vecLen' (k : K) : ℕ := 384 * k
abbrev vecLen (p : ParameterSet) : ℕ := vecLen' (k p)
/-- K-PKE encryption key: the encoded `t̂` and the seed `ρ`. -/
abbrev ekPKELen (p : ParameterSet) : ℕ := vecLen p + seedLen
/-- K-PKE decryption key: the encoded `ŝ`. -/
abbrev dkPKELen (p : ParameterSet) : ℕ := vecLen p
/-- ML-KEM encapsulation key: the K-PKE encryption key. -/
abbrev ekLen (p : ParameterSet) : ℕ := ekPKELen p
/-- ML-KEM decapsulation key: `dkPKE ‖ ek ‖ H(ek) ‖ z`, i.e. `768k + 96`. -/
abbrev dkLen (p : ParameterSet) : ℕ := dkPKELen p + ekLen p + hashLen + seedLen
/-- First ciphertext component, `ByteEncode_dᵤ` of a compressed vector. -/
abbrev c₁Len (p : ParameterSet) : ℕ := 32 * dᵤ p * k p
/-- Second ciphertext component, `ByteEncode_dᵥ` of a compressed polynomial. -/
abbrev c₂Len (p : ParameterSet) : ℕ := 32 * dᵥ p
/-- Ciphertext: `32(dᵤk + dᵥ)`. -/
abbrev ctLen (p : ParameterSet) : ℕ := c₁Len p + c₂Len p

/-! ## Vectors and Matrices of Polynomials (§2.4.4–§2.4.8) -/

abbrev PolyVector (m : ℕ) (k : K) := PolyRing.PolyVec (ZMod m) 256 (-1) k

/-- Vectors and matrices over `T_q` (§2.4.7–§2.4.8). -/
abbrev NTTVector (k : K) := PolyRing.NTTVec ζ 7 k
abbrev NTTMatrix (k : K) := PolyRing.Mat Tq k

/-! ## §4.1 Cryptographic Functions (Eq. 4.1–4.5)

Defined in terms of the SHA-3 specification from `Wychelean.Hashes.SHA3` (byte-level
wrappers) and its incremental sponge API (`XOF`). -/

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

/-! ### eXtendable-Output Function (XOF) — §4.1, Eq. (4.1)–(4.2)

XOF is SHAKE128 (§4.1). The state-passing API (Init/Absorb/Squeeze) allows
incremental squeezing as required by SampleNTT (Algorithm 7). -/

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
  PolyRing.Poly.ofFn fun i => MLKEM.Compress d f[i]

def Polynomial.Decompress (d : ℕ) (f : Polynomial (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial :=
  PolyRing.Poly.ofFn fun i => MLKEM.Decompress d f[i]

def PolyVector.Compress {k : K} (d : ℕ) (v : PolyVector q k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector (m d) k :=
  v.map (Polynomial.Compress d)

def PolyVector.Decompress {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector q k :=
  v.map (Polynomial.Decompress d)

/-! ## §4.2.1 Algorithm 5 — ByteEncode_d(F)

Encodes an array of 256 `d`-bit integers into a byte array, for `1 ≤ d ≤ 12`. -/
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

/-! ## §4.2.1 Algorithm 6 — ByteDecode_d(B)

Decodes a byte array into an array of 256 `d`-bit integers, for `1 ≤ d ≤ 12`. -/
def ByteDecode {d : ℕ} (B : ByteVec (32 * d)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : Vector (ZMod (m d)) 256 :=
  let b := bytesToBits B
  Vector.ofFn fun i =>
    have := byte_encode_idx_le i d
    ∑ (j : Fin d), b[i * d + j].toNat * 2^j.val

/-- `ByteEncode_d` of each entry, concatenated (§2.4.8). -/
def PolyVector.ByteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (k * (32 * d)) :=
  (v.map fun f => MLKEM.ByteEncode d f.coeffs).flatten

def PolyVector.ByteDecode {k : K} (d : ℕ) (bytes : ByteVec (32 * d * k)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : PolyVector (m d) k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le d i i.isLt
    ⟨MLKEM.ByteDecode (slice bytes (32 * d * i) (32 * d) (by grind))⟩

/-- `ByteEncode₁₂` of a vector over `T_q`, each entry by its residues in the order of §2.4.6. -/
def ByteEncode₁₂ {k : K} (v : NTTVector k) : ByteVec (vecLen' k) :=
  ((v.map fun «f̂» => MLKEM.ByteEncode 12 «f̂».flat).flatten).cast (by simp only [vecLen']; omega)

def ByteDecode₁₂ {k : K} (bytes : ByteVec (vecLen' k)) : NTTVector k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le 12 i i.isLt
    ⟨MLKEM.ByteDecode (slice bytes (32 * 12 * i) (32 * 12) (by grind))⟩

/-! ## §4.2.2 Algorithm 7 — SampleNTT(B)

Uses rejection sampling to deterministically generate an element of `T_q`
from the XOF output stream of `B = ρ ‖ j ‖ i`, a seed and two index bytes. -/
def SampleNTT (B : ByteVec (seedLen + 2)) : Tq := ⟨Id.run do
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
  pure «â»⟩

/-! ## §4.2.2 Algorithm 8 — SamplePolyCBD_η(B)

Uses the centered binomial distribution to deterministically generate
a polynomial in `R_q` from a `64·η`-byte array. -/

theorem Η.val_le (η : Η) : η.val ≤ 3 := by
  have h := η.property; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; omega

def SamplePolyCBD {η : Η} (B : ByteVec (64 * η)) : Polynomial :=
  let b := bytesToBits B
  PolyRing.Poly.ofFn fun i =>
    have := sample_cbd_idx_le i η (by grind)
    let x := ∑ (j : Fin η), b[2 * i.val * η + j].toNat
    let y := ∑ (j : Fin η), b[2 * i.val * η + η + j].toNat
    x - y

/-- `Â[i][j] = SampleNTT(ρ ‖ j ‖ i)` (Algorithm 13, steps 3–7; Algorithm 14, steps 4–8). -/
def SampleMatrix {k : K} (ρ : Seed) : NTTMatrix k :=
  Vector.ofFn fun i => Vector.ofFn fun j => SampleNTT (ρ ‖ #v[(j : Byte), (i : Byte)])

/-- `k` polynomials `SamplePolyCBD_η(PRF_η(s, N))` for `N = N₀, N₀ + 1, …`
(the loops over `N` of Algorithms 13–14). -/
def SampleVector {k : K} (η : Η) (s : Seed) (N₀ : ℕ) : PolyVector q k :=
  Vector.ofFn fun i => SamplePolyCBD (PRF η s ((N₀ + i : ℕ) : Byte))

/-! ## §4.3 Algorithms 9–10 — NTT(f), NTT⁻¹(f̂)

The transforms are `f.ntt` and `«f̂».nttInv` of `PolyRing.NTT`, with the seven layers of `ζ = 17`;
NTT⁻¹ ends with the scaling by `128⁻¹ = 3303`, written `(2^7)⁻¹` there. -/

/-! ### Linear algebra over T_q (§2.4.7–§2.4.8)

The transform of a vector is `v.ntt` and its inverse `«v̂».nttInv`; `«Â» * «v̂»` and `⟪«v̂», «ŵ»⟫`
are the matrix-vector and inner products of `PolyRing` over the product of `T_q`
(Algorithms 11–12 are its residue-wise description, `Properties.mul_residue`). -/

/-! ## §5.1 Algorithm 13 — K-PKE.KeyGen(d)

Uses a 32-byte seed `d` to deterministically generate an encryption key
and a corresponding decryption key for the K-PKE scheme. -/
def K_PKE.KeyGen (p : ParameterSet) (d : Seed) : ByteVec (ekPKELen p) × ByteVec (dkPKELen p) :=
  let (ρ, σ) := G (d ‖ #v[(k p : Byte)])                                       -- Alg. 13, step 1
  let «Â» : NTTMatrix (k p) := SampleMatrix ρ                                  -- Alg. 13, steps 3–7
  let s : PolyVector q (k p) := SampleVector (η₁ p) σ 0                        -- Alg. 13, steps 8–11
  let e : PolyVector q (k p) := SampleVector (η₁ p) σ (k p)                    -- Alg. 13, steps 12–15
  let «ŝ» := s.ntt                                                             -- Alg. 13, step 16
  let «ê» := e.ntt                                                             -- Alg. 13, step 17
  let «t̂» := «Â» * «ŝ» + «ê»                                                  -- Alg. 13, step 18
  let ekPKE := ByteEncode₁₂ «t̂» ‖ ρ                                           -- Alg. 13, step 19
  let dkPKE := ByteEncode₁₂ «ŝ»                                                -- Alg. 13, step 20
  (ekPKE, dkPKE)

/-! ## §5.2 Algorithm 14 — K-PKE.Encrypt(ekPKE, m, r)

Uses the encryption key to encrypt a plaintext message using the randomness `r`.

The noise vector is `y` (its NTT `ŷ`), as in FIPS 203 Algorithm 14; the randomness parameter
is `r : Seed`. -/
def K_PKE.Encrypt (p : ParameterSet) (ekPKE : ByteVec (ekPKELen p)) (m : Seed) (r : Seed) :
    ByteVec (ctLen p) :=
  let (t, ρ) := split ekPKE (vecLen p) seedLen                                 -- Alg. 14, steps 2–3
  let «t̂» := ByteDecode₁₂ t
  let «Â» : NTTMatrix (k p) := SampleMatrix ρ                                  -- Alg. 14, steps 4–8
  let y : PolyVector q (k p) := SampleVector (η₁ p) r 0                        -- Alg. 14, steps 9–12
  let e₁ : PolyVector q (k p) := SampleVector η₂ r (k p)                       -- Alg. 14, steps 13–16
  let e₂ := SamplePolyCBD (PRF η₂ r ((2 * k p : ℕ) : Byte))                    -- Alg. 14, step 17
  let «ŷ» := y.ntt                                                             -- Alg. 14, step 18
  let u := («Â».transpose * «ŷ» : NTTVector (k p)).nttInv + e₁                 -- Alg. 14, step 19
  let μ := Polynomial.Decompress 1 ⟨ByteDecode (m.cast (by grind))⟩            -- Alg. 14, step 20
  let v := ⟪«t̂», «ŷ»⟫.nttInv + e₂ + μ                                         -- Alg. 14, step 21
  let c₁ := PolyVector.ByteEncode (dᵤ p) (PolyVector.Compress (dᵤ p) u)        -- Alg. 14, step 22
  let c₂ := ByteEncode (dᵥ p) (Polynomial.Compress (dᵥ p) v).coeffs            -- Alg. 14, step 23
  (c₁ ‖ c₂).cast (by simp only [ctLen, c₁Len, c₂Len]; ring)                   -- Alg. 14, step 24

/-! ## §5.3 Algorithm 15 — K-PKE.Decrypt(dkPKE, c)

Uses the decryption key to decrypt a ciphertext. -/
def K_PKE.Decrypt (p : ParameterSet) (dkPKE : ByteVec (dkPKELen p)) (c : ByteVec (ctLen p)) :
    Seed :=
  let (c₁, c₂) := split c (c₁Len p) (c₂Len p)                                  -- Alg. 15, steps 1–2
  let u' := PolyVector.Decompress (dᵤ p) (PolyVector.ByteDecode (k := k p) (dᵤ p) c₁) -- Alg. 15, step 3
  let v' := Polynomial.Decompress (dᵥ p) ⟨ByteDecode c₂⟩                       -- Alg. 15, step 4
  let «ŝ» := ByteDecode₁₂ dkPKE                                                -- Alg. 15, step 5
  let w := v' - ⟪«ŝ», u'.ntt⟫.nttInv                                           -- Alg. 15, step 6
  let m := ByteEncode 1 (Polynomial.Compress 1 w).coeffs                       -- Alg. 15, step 7
  m.cast (by grind)

/-! ## §6.1 Algorithm 16 — ML-KEM.KeyGen_internal(d,z)

Uses seeds `d` and `z` to deterministically generate an encapsulation key
and a corresponding decapsulation key. -/
def KeyGen_internal (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  let (ekPKE, dkPKE) := K_PKE.KeyGen p d                                       -- Alg. 16, step 1
  let ek := ekPKE                                                              -- Alg. 16, step 2
  let dk := dkPKE ‖ ek ‖ H ek ‖ z                                              -- Alg. 16, step 3
  (ek, dk)

/-- The layout of a decapsulation key, `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` (Algorithm 16, step 3), read
back as in Algorithm 18, steps 1–4 and Eq. (7.2). -/
def dkParts (p : ParameterSet) (dk : ByteVec (dkLen p)) :
    ByteVec (dkPKELen p) × ByteVec (ekLen p) × ByteVec hashLen × Seed :=
  let (dk, z) := split dk (dkPKELen p + ekLen p + hashLen) seedLen
  let (dk, h) := split dk (dkPKELen p + ekLen p) hashLen
  let (dkPKE, ek) := split dk (dkPKELen p) (ekLen p)
  (dkPKE, ek, h, z)

/-! ## §6.2 Algorithm 17 — ML-KEM.Encaps_internal(ek, m)

Uses the encapsulation key and a 32-byte message to deterministically
generate a shared key and an associated ciphertext. -/
def Encaps_internal (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    SharedKey × ByteVec (ctLen p) :=
  let (K, r) := G (m ‖ H ek)                                                -- Alg. 17, step 1
  let c := K_PKE.Encrypt p ek m r                                            -- Alg. 17, step 2
  (K, c)

/-! ## §6.3 Algorithm 18 — ML-KEM.Decaps_internal(dk, c)

Uses the decapsulation key to produce a shared key from a ciphertext.
Uses implicit rejection via the seed `z` embedded in `dk`. -/
def Decaps_internal (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    SharedKey :=
  let (dkPKE, ekPKE, h, z) := dkParts p dk                                    -- Alg. 18, steps 1–4
  let m' := K_PKE.Decrypt p dkPKE c                                           -- Alg. 18, step 5
  let (K', r') := G (m' ‖ h)                                                 -- Alg. 18, step 6
  let «K̄» := J (z ‖ c)                                                       -- Alg. 18, step 7
  let c' := K_PKE.Encrypt p ekPKE m' r'                                       -- Alg. 18, step 8
  if c ≠ c' then «K̄» else K'                                                  -- Alg. 18, steps 9–12

/-! ## §7 The ML-KEM Key-Encapsulation Mechanism

The bytes that Algorithms 19–20 draw from the random bit generator (§3.3), `d` and `z` for
KeyGen and `m` for Encaps, are arguments here. -/

/-! ## §7.1 Algorithm 19 — ML-KEM.KeyGen()

Generates an encapsulation key and a corresponding decapsulation key. -/
def KeyGen (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  KeyGen_internal p d z                                                        -- Alg. 19, step 6

/-- Modulus check (§7.2, Eq. 7.1): every encoded coefficient is reduced modulo `q`. -/
def Encaps.KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) : Bool :=
  let (ekPKE, _) := split ek (vecLen p) seedLen
  ByteEncode₁₂ (ByteDecode₁₂ ekPKE) = ekPKE

/-! ## §7.2 Algorithm 20 — ML-KEM.Encaps(ek)

Uses the encapsulation key to generate a shared key and an associated ciphertext.
Returns `none` if the encapsulation key fails validation. -/
def Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    Option (SharedKey × ByteVec (ctLen p)) :=
  if Encaps.KeyCheck p ek then some (Encaps_internal p ek m)                     -- Alg. 20, steps 5–7
  else none

/-- Hash check (§7.3, Eq. 7.2): the stored `H(ek)` matches the embedded `ek`. -/
def Decaps.KeyCheck (p : ParameterSet) (dk : ByteVec (dkLen p)) : Bool :=
  let (_, ek, h, _) := dkParts p dk
  H ek = h                                                      -- Eq. (7.2)


/-! ## §7.3 Algorithm 21 — ML-KEM.Decaps(dk, c)

Uses the decapsulation key to produce a shared key from a ciphertext.
Returns `none` if the decapsulation key fails validation. -/
def Decaps (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    Option SharedKey :=
  if Decaps.KeyCheck p dk then some (Decaps_internal p dk c)                      -- Alg. 21, steps 1–2
  else none

end Wychelean.KEM.MLKEM
