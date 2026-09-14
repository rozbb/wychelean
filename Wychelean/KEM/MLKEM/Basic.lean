import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Wychelean.Utils.Round
import Wychelean.Lattice
import Wychelean.Hashes.SHA3.XOF

/-!
# ML-KEM
FIPS 203: https://doi.org/10.6028/NIST.FIPS.203
Adapted from Microsoft SymCrypt (MIT; see Wychelean/Hashes/SHA3/LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/MLKEM/Spec.lean
-/

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
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

/-- Polynomial ring element: `ℤ_m[X] / (X^256 + 1)`, represented as `Vector (ZMod m) 256`
(`Lattice.Poly`). When `d = 12`, `m = q`; when `d < 12`, `m = 2^d` (§4.2.1). -/
abbrev Polynomial (m : ℕ := q) := Lattice.Poly m 256

abbrev Polynomial.zero (m : ℕ := q) : Polynomial m := Lattice.Poly.zero

/-- ζ = 17 ∈ ℤ_q is a primitive 256-th root of unity modulo q (§4.3). -/
def ζ : Zq := 17

/-- The NTT domain `T_q` (§2.4.6): a type of its own, with `*` the blockwise product of
Algorithms 11–12 (`Lattice.Tq`), so ring and NTT-domain elements cannot be confused. -/
abbrev NTTPolynomial := Lattice.Tq q ζ 7

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

/-- `ByteEncode₁₂` of a vector of `k` polynomials: `384k`. -/
abbrev vecLen' (k : K) : ℕ := 384 * k
abbrev vecLen (p : ParameterSet) : ℕ := vecLen' (k p)
/-- K-PKE encryption key: the encoded `t̂` and the seed `ρ`. -/
abbrev ekPKELen (p : ParameterSet) : ℕ := vecLen p + 32
/-- K-PKE decryption key: the encoded `ŝ`. -/
abbrev dkPKELen (p : ParameterSet) : ℕ := vecLen p
/-- ML-KEM encapsulation key: the K-PKE encryption key. -/
abbrev ekLen (p : ParameterSet) : ℕ := ekPKELen p
/-- ML-KEM decapsulation key: `dkPKE ‖ ek ‖ H(ek) ‖ z`, i.e. `768k + 96`. -/
abbrev dkLen (p : ParameterSet) : ℕ := dkPKELen p + ekLen p + 32 + 32
/-- First ciphertext component, `ByteEncode_dᵤ` of a compressed vector. -/
abbrev c₁Len (p : ParameterSet) : ℕ := 32 * dᵤ p * k p
/-- Second ciphertext component, `ByteEncode_dᵥ` of a compressed polynomial. -/
abbrev c₂Len (p : ParameterSet) : ℕ := 32 * dᵥ p
/-- Ciphertext: `32(dᵤk + dᵥ)`. -/
abbrev ctLen (p : ParameterSet) : ℕ := c₁Len p + c₂Len p

/-! ## Vectors and Matrices of Polynomials (§2.4.4–§2.4.8) -/

abbrev PolyVector (m : ℕ) (k : K) := Lattice.PolyVec m 256 k
abbrev PolyVector.zero (m : ℕ) (k : K) : PolyVector m k := Lattice.PolyVec.zero

/-- A `k × k` matrix of polynomials as a vector of rows (see the provenance notes). -/
abbrev PolyMatrix (m : ℕ) (k : K) := Lattice.PolyMat m 256 k
abbrev PolyMatrix.zero (m : ℕ) (k : K) : PolyMatrix m k := Lattice.Mat.zero

/-- Vectors and matrices over `T_q` (§2.4.7–§2.4.8). -/
abbrev NTTVector (k : K) := Vector NTTPolynomial k
abbrev NTTVector.zero (k : K) : NTTVector k := Vector.replicate k 0
abbrev NTTMatrix (k : K) := Lattice.Mat NTTPolynomial k
abbrev NTTMatrix.zero (k : K) : NTTMatrix k := Lattice.Mat.zero
/-- `Âᵀ`, the transpose used by K-PKE.Encrypt (Algorithm 14, step 19). -/
abbrev NTTMatrix.transpose {k : K} (M : NTTMatrix k) : NTTMatrix k := Lattice.Mat.transpose M

instance {k : K} : Add (NTTVector k) where
  add v w := Vector.ofFn fun i => v[i] + w[i]

/-! ## §4.1 Cryptographic Functions (Eq. 4.1–4.5)

Defined in terms of the SHA-3 specification from `Wychelean.Hashes.SHA3` (byte-level
wrappers) and its incremental sponge API (`XOF`). -/

/-- H(s) := SHA3-256(s) — Eq. (4.4). -/
def H {n} (s : ByteVec n) : ByteVec 32 := SHA3.sha3_256 s

/-- J(s) := SHAKE256(s, 32) — Eq. (4.4). -/
def J {n} (s : ByteVec n) : ByteVec 32 := SHA3.shake256 s 32

/-- G(c) := SHA3-512(c), split into two 32-byte outputs — Eq. (4.5). -/
def G {n} (s : ByteVec n) : ByteVec 32 × ByteVec 32 :=
  let hash := SHA3.sha3_512 s
  (slice hash 0 32, slice hash 32 32)

/-- PRF_η(s,b) := SHAKE256(s‖b, 8·64·η) — Eq. (4.3). -/
def PRF (η : Η) (s : ByteVec 32) (b : Byte) : ByteVec (64 * η) :=
  SHA3.shake256 (s ‖ #v[b]) (64 * η)

/-! ### eXtendable-Output Function (XOF) — §4.1, Eq. (4.1)–(4.2)

XOF is SHAKE128 (§4.1). The state-passing API (Init/Absorb/Squeeze) allows
incremental squeezing as required by SampleNTT (Algorithm 7). -/

def XOF.Init := SHA3.SHAKE128.init

def XOF.Absorb s (B : ByteVec ℓ) := SHA3.SHAKE128.absorb s B

def XOF.Squeeze s ℓ := SHA3.SHAKE128.squeeze s ℓ

/-! ## §4.2.1 Algorithm 3 — BitsToBytes(b)

Converts a bit array (of a length that is a multiple of eight) into an array of bytes. -/
abbrev BitsToBytes := @Wychelean.bitsToBytes

/-! ## §4.2.1 Algorithm 4 — BytesToBits(B)

Converts a byte array into a bit array. -/
abbrev BytesToBits := @Wychelean.bytesToBits

/-! ## §4.2.1 Compress / Decompress — Eq. (4.7), (4.8)

Lossy compression from ℤ_q to ℤ_{2^d} and decompression back. -/

def Compress (d : ℕ) (x : Zq) (_ : 1 ≤ d ∧ d < 12 := by grind) : ZMod (m d) :=
  ⌈ ((2^d : ℚ) / (q : ℚ)) * x.val ⌋

def Decompress (d : ℕ) (y : ZMod (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Zq :=
  ⌈ ((q : ℚ) / (2^d : ℚ)) * y.val ⌋

def Polynomial.Compress (d : ℕ) (f : Polynomial) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial (m d) :=
  f.map (MLKEM.Compress d)

def Polynomial.Decompress (d : ℕ) (f : Polynomial (m d)) (_ : 1 ≤ d ∧ d < 12 := by grind) : Polynomial :=
  f.map (MLKEM.Decompress d)

def PolyVector.Compress {k : K} (d : ℕ) (v : PolyVector q k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector (m d) k :=
  v.map (Polynomial.Compress d)

def PolyVector.Decompress {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d < 12 := by grind) : PolyVector q k :=
  v.map (Polynomial.Decompress d)

/-! ## §4.2.1 Algorithm 5 — ByteEncode_d(F)

Encodes an array of `d`-bit integers into a byte array, for `1 ≤ d ≤ 12`. -/
def ByteEncode (d : ℕ) (F : Polynomial (m d)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (32 * d) := Id.run do
  let mut b := Vector.replicate (256 * d) 0
  for hi: i in [0:256] do
    have := byte_encode_idx_le i d
    let mut a := F[i].val
    for hj: j in [0:d] do
      b := b.set (i * d + j) (Bool.ofNat (a % 2))
      a := (a - b[i * d + j].toNat) / 2
  let B := BitsToBytes (b.cast (by grind))
  pure B

/-! ## §4.2.1 Algorithm 6 — ByteDecode_d(B)

Decodes a byte array into an array of `d`-bit integers, for `1 ≤ d ≤ 12`. -/
def ByteDecode {d : ℕ} (B : ByteVec (32 * d)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : Polynomial (m d) := Id.run do
  let b := BytesToBits B
  let mut F := Polynomial.zero (m d)
  for hi: i in [0:256] do
    have := byte_encode_idx_le i d
    F := F.set i (∑ (j : Fin d), b[i * d + j].toNat * 2^j.val)
  pure F

def PolyVector.ByteEncode {k : K} (d : ℕ) (v : PolyVector (m d) k) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : ByteVec (k * (32 * d)) :=
  (v.map (MLKEM.ByteEncode d)).flatten

def PolyVector.ByteDecode {k : K} (d : ℕ) (bytes : ByteVec (32 * d * k)) (_ : 1 ≤ d ∧ d ≤ 12 := by grind) : PolyVector (m d) k :=
  Vector.ofFn fun i =>
    have := poly_vec_decode_idx_le d i i.isLt
    MLKEM.ByteDecode (slice bytes (32 * d * i) (32 * d) (by grind))

/-! ### `ByteEncode₁₂`/`ByteDecode₁₂` on the NTT domain (§4.2.1), encoding the residues -/

def NTTPolynomial.ByteEncode («f̂» : NTTPolynomial) : ByteVec (32 * 12) :=
  MLKEM.ByteEncode 12 «f̂».residues
def NTTPolynomial.ByteDecode (B : ByteVec (32 * 12)) : NTTPolynomial := ⟨MLKEM.ByteDecode B⟩
def NTTVector.ByteEncode {k : K} (v : NTTVector k) : ByteVec (vecLen' k) :=
  ((v.map NTTPolynomial.ByteEncode).flatten).cast (by simp only [vecLen']; omega)
def NTTVector.ByteDecode {k : K} (bytes : ByteVec (vecLen' k)) : NTTVector k :=
  (PolyVector.ByteDecode (k := k) 12 (bytes.cast (by simp only [vecLen']))).map (⟨·⟩)

/-! ## §4.2.2 Algorithm 7 — SampleNTT(B)

Uses rejection sampling to deterministically generate an element of `T_q`
from the XOF output stream of the 34-byte seed `B`. -/
def SampleNTT (B : ByteVec 34) : NTTPolynomial := ⟨Id.run do
  let mut ctx := XOF.Init
  ctx := XOF.Absorb ctx B
  let mut «â» := Polynomial.zero
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

def SamplePolyCBD {η : Η} (B : ByteVec (64 * η)) : Polynomial := Id.run do
  let b := BytesToBits B
  let mut f := Polynomial.zero
  for hi: i in [0:256] do
    have := sample_cbd_idx_le i η (by grind)
    let x := ∑ (j : Fin η), b[2 * i * η + j].toNat
    let y := ∑ (j : Fin η), b[2 * i * η + η + j].toNat
    f := f.set i (x - y)
  pure f

/-! ## §4.3 Algorithm 9 — NTT(f)

Computes the NTT representation `f̂ ∈ T_q` of a polynomial `f ∈ R_q`
using Cooley–Tukey butterflies with the seven layers of `ζ = 17`. -/
def NTT (f : Polynomial) : NTTPolynomial := Lattice.NTT.ntt ζ 7 f

/-! ## §4.3 Algorithm 10 — NTT⁻¹(f̂)

Computes the polynomial `f ∈ R_q` corresponding to an NTT representation `f̂ ∈ T_q`
using Gentleman–Sande butterflies; the final scaling by `128⁻¹ = 3303` is `(2^7)⁻¹` in the
library. -/
def NTTInv («f̂» : NTTPolynomial) : Polynomial := Lattice.NTT.nttInv ζ 7 «f̂»

/-! ## §4.3.1 Algorithm 12 — BaseCaseMultiply(a₀,a₁,b₀,b₁,γ)

Computes the product of two degree-one polynomials with respect to a
quadratic modulus `X² − γ`. -/
def BaseCaseMultiply (a₀ a₁ b₀ b₁ γ : Zq) : Zq × Zq :=
  let c₀ := a₀ * b₀ + a₁ * b₁ * γ                                              -- Alg. 12, step 1
  let c₁ := a₀ * b₁ + a₁ * b₀                                                  -- Alg. 12, step 2
  (c₀, c₁)                                                                      -- Alg. 12, step 3

/-! ## §4.3.1 Algorithm 11 — MultiplyNTTs(f̂, ĝ)

Computes the product (in the NTT domain) of two NTT representations,
via 128 base-case multiplications in the factor rings of `T_q`. -/
def MultiplyNTTs («f̂» «ĝ» : NTTPolynomial) : NTTPolynomial := ⟨Id.run do
  let mut «ĥ» := Polynomial.zero
  for h: i in [0:128] do
    let (c₀, c₁) := BaseCaseMultiply «f̂»[2*i] «f̂»[2*i+1] «ĝ»[2*i] «ĝ»[2*i+1] (ζ^(2 * bitRev 7 i + 1))
    «ĥ» := «ĥ».set (2*i) c₀
    «ĥ» := «ĥ».set (2*i+1) c₁
  pure «ĥ»⟩

/-! ### Linear algebra over T_q (§2.4.7–§2.4.8) -/

def PolyVector.NTT {k : K} (v : PolyVector q k) : NTTVector k := v.map MLKEM.NTT
def NTTVector.NTTInv {k : K} (v : NTTVector k) : PolyVector q k := v.map MLKEM.NTTInv

def NTTMatrix.MulVectorNTT {k : K} (A : NTTMatrix k) (v : NTTVector k) : NTTVector k := Id.run do
  let mut w := NTTVector.zero k
  for hi: i in [0:k] do
    for hj: j in [0:k] do
      w := w.set i (w[i] + MultiplyNTTs A[i][j] v[j])
  pure w

instance {k} : HMul (NTTMatrix k) (NTTVector k) (NTTVector k) where
  hMul := NTTMatrix.MulVectorNTT

def NTTVector.innerProductNTT {k : K} (v w : NTTVector k) : NTTPolynomial := Id.run do
  let mut a : NTTPolynomial := 0
  for hi: i in [0:k] do
    a := a + MultiplyNTTs v[i] w[i]
  pure a

/-! ## §5.1 Algorithm 13 — K-PKE.KeyGen(d)

Uses a 32-byte seed `d` to deterministically generate an encryption key
and a corresponding decryption key for the K-PKE scheme. -/
def K_PKE.KeyGen (p : ParameterSet) (d : ByteVec 32) : ByteVec (ekPKELen p) × ByteVec (dkPKELen p) := Id.run do
  let (ρ, σ) := G (d ‖ #v[(k p : Byte)])                                 -- Alg. 13, step 1
  let mut N := 0                                                        -- Alg. 13, step 2
  let mut «Â» := NTTMatrix.zero (k p)                                          -- Alg. 13, steps 3–7
  for hi: i in [0:k p] do
    for hj: j in [0:k p] do
      «Â» := «Â».update i j (SampleNTT (ρ ‖ #v[(j : Byte)] ‖ #v[(i : Byte)]))
  let mut s := PolyVector.zero q (k p)                                         -- Alg. 13, steps 8–11
  for hi: i in [0:k p] do
    s := s.set i (SamplePolyCBD (PRF (η₁ p) σ N))
    N := N + 1
  let mut e := PolyVector.zero q (k p)                                         -- Alg. 13, steps 12–15
  for hi: i in [0:k p] do
    e := e.set i (SamplePolyCBD (PRF (η₁ p) σ N))
    N := N + 1
  let «ŝ» := PolyVector.NTT s                                                  -- Alg. 13, step 16
  let «ê» := PolyVector.NTT e                                                  -- Alg. 13, step 17
  let «t̂» := «Â» * «ŝ» + «ê»                             -- Alg. 13, step 18
  let ekPKE := NTTVector.ByteEncode «t̂» ‖ ρ                                    -- Alg. 13, step 19
  let dkPKE := NTTVector.ByteEncode «ŝ»                                        -- Alg. 13, step 20
  pure (ekPKE, dkPKE)

/-! ## §5.2 Algorithm 14 — K-PKE.Encrypt(ekPKE, m, r)

Uses the encryption key to encrypt a plaintext message using the randomness `r`.

The noise vector is `y` (its NTT `ŷ`), as in FIPS 203 Algorithm 14; the randomness parameter
is `r : ByteVec 32`. -/
def K_PKE.Encrypt (p : ParameterSet) (ekPKE : ByteVec (ekPKELen p)) (m : ByteVec 32) (r : ByteVec 32) :
    ByteVec (ctLen p) := Id.run do
  let mut N := 0                                                               -- Alg. 14, step 1
  let «t̂» := NTTVector.ByteDecode (slice ekPKE 0 (vecLen p))                   -- Alg. 14, step 2
  let ρ := slice ekPKE (vecLen p) 32                                           -- Alg. 14, step 3
  let mut «Â» := NTTMatrix.zero (k p)                                          -- Alg. 14, steps 4–8
  for hi: i in [0:k p] do
    for hj: j in [0:k p] do
      «Â» := «Â».update i j (SampleNTT (ρ ‖ #v[(j : Byte)] ‖ #v[(i : Byte)]))
  let mut y := PolyVector.zero q (k p)                                         -- Alg. 14, steps 9–12
  for hi: i in [0:k p] do
    y := y.set i (SamplePolyCBD (PRF (η₁ p) r N))
    N := N + 1
  let mut e₁ := PolyVector.zero q (k p)                                        -- Alg. 14, steps 13–16
  for hi: i in [0:k p] do
    e₁ := e₁.set i (SamplePolyCBD (PRF η₂ r N))
    N := N + 1
  let e₂ := SamplePolyCBD (PRF η₂ r N)                                         -- Alg. 14, step 17
  let «ŷ» := PolyVector.NTT y                                                  -- Alg. 14, step 18
  let u := NTTVector.NTTInv (NTTMatrix.transpose «Â» * «ŷ») + e₁               -- Alg. 14, step 19
  let μ := Polynomial.Decompress 1 (ByteDecode (m.cast (by grind)))          -- Alg. 14, step 20
  let v := NTTInv (NTTVector.innerProductNTT «t̂» «ŷ») + e₂ + μ                 -- Alg. 14, step 21
  let c₁ := PolyVector.ByteEncode (dᵤ p) (PolyVector.Compress (dᵤ p) u)        -- Alg. 14, step 22
  let c₂ := ByteEncode (dᵥ p) (Polynomial.Compress (dᵥ p) v)                   -- Alg. 14, step 23
  (c₁ ‖ c₂).cast (by simp only [ctLen, c₁Len, c₂Len]; ring)                   -- Alg. 14, step 24

/-! ## §5.3 Algorithm 15 — K-PKE.Decrypt(dkPKE, c)

Uses the decryption key to decrypt a ciphertext. -/
def K_PKE.Decrypt (p : ParameterSet) (dkPKE : ByteVec (dkPKELen p)) (c : ByteVec (ctLen p)) :
    ByteVec 32 :=
  let c₁ := slice c 0 (c₁Len p)                                               -- Alg. 15, step 1
  let c₂ := slice c (c₁Len p) (c₂Len p)                                       -- Alg. 15, step 2
  let u' := PolyVector.Decompress (dᵤ p) (PolyVector.ByteDecode (k := k p) (dᵤ p) c₁) -- Alg. 15, step 3
  let v' := Polynomial.Decompress (dᵥ p) (ByteDecode c₂)                             -- Alg. 15, step 4
  let «ŝ» := NTTVector.ByteDecode dkPKE                                        -- Alg. 15, step 5
  let w := v' - NTTInv (NTTVector.innerProductNTT «ŝ» (PolyVector.NTT u'))       -- Alg. 15, step 6
  let m := ByteEncode 1 (Polynomial.Compress 1 w)                              -- Alg. 15, step 7
  m.cast (by grind)

/-! ## §6.1 Algorithm 16 — ML-KEM.KeyGen_internal(d,z)

Uses seeds `d` and `z` to deterministically generate an encapsulation key
and a corresponding decapsulation key. -/
def KeyGen_internal (p : ParameterSet) (d z : ByteVec 32) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  let (ekPKE, dkPKE) := K_PKE.KeyGen p d                                       -- Alg. 16, step 1
  let ek := ekPKE                                                              -- Alg. 16, step 2
  let dk := dkPKE ‖ ek ‖ H ek ‖ z                                              -- Alg. 16, step 3
  (ek, dk)

/-- The layout of a decapsulation key, `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` (Algorithm 16, step 3), read
back as in Algorithm 18, steps 1–4 and Eq. (7.2). -/
def dkParts (p : ParameterSet) (dk : ByteVec (dkLen p)) :
    ByteVec (dkPKELen p) × ByteVec (ekLen p) × ByteVec 32 × ByteVec 32 :=
  (slice dk 0 (dkPKELen p),
   slice dk (dkPKELen p) (ekLen p),
   slice dk (dkPKELen p + ekLen p) 32,
   slice dk (dkPKELen p + ekLen p + 32) 32)

/-! ## §6.2 Algorithm 17 — ML-KEM.Encaps_internal(ek, m)

Uses the encapsulation key and a 32-byte message to deterministically
generate a shared key and an associated ciphertext. -/
def Encaps_internal (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : ByteVec 32) :
    ByteVec 32 × ByteVec (ctLen p) :=
  let (K, r) := G (m ‖ H ek)                                                -- Alg. 17, step 1
  let c := K_PKE.Encrypt p ek m r                                            -- Alg. 17, step 2
  (K, c)

/-! ## §6.3 Algorithm 18 — ML-KEM.Decaps_internal(dk, c)

Uses the decapsulation key to produce a shared key from a ciphertext.
Uses implicit rejection via the seed `z` embedded in `dk`. -/
def Decaps_internal (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    ByteVec 32 :=
  let (dkPKE, ekPKE, h, z) := dkParts p dk                                    -- Alg. 18, steps 1–4
  let m' := K_PKE.Decrypt p dkPKE c                                           -- Alg. 18, step 5
  let (K', r') := G (m' ‖ h)                                                 -- Alg. 18, step 6
  let «K̄» := J (z ‖ c)                                                       -- Alg. 18, step 7
  let c' := K_PKE.Encrypt p ekPKE m' r'                                       -- Alg. 18, step 8
  if c ≠ c' then «K̄» else K'                                                  -- Alg. 18, steps 9–12

/-! ## §7 The ML-KEM Key-Encapsulation Mechanism

The top-level API wraps the `_internal` functions with a `RandomTape` for randomness. -/

/-- A random tape is an infinite stream of bytes.
    This models the RBG (Random Bit Generator) of §3.3. -/
def RandomTape := ℕ → Byte

def RandomTape.readBytes (tape : RandomTape) (n : ℕ) : ByteVec n × RandomTape :=
  (Vector.ofFn (fun i => tape i), fun i => tape (n + i))

/-! ### Input validation checks (§7.2–§7.3)

These checks were added late in the FIPS 203 standardization process (they are not
present in the earlier CRYSTALS-Kyber specification). They guard against malformed
keys and corrupted decapsulation key material, and are security-relevant: the modulus
check prevents a class of chosen-ciphertext attacks on malformed encapsulation keys,
and the hash check detects decapsulation key corruption before use. -/

/-! ## §7.1 Algorithm 19 — ML-KEM.KeyGen()

Generates an encapsulation key and a corresponding decapsulation key. -/
def KeyGen (p : ParameterSet) (tape : RandomTape) :
    ByteVec (ekLen p) × ByteVec (dkLen p) × RandomTape :=
  -- Steps 3–5: RBG failure check.
  -- Trivially succeeds with `RandomTape` (no RBG failure mode).
  let (d, tape) := tape.readBytes 32
  let (z, tape) := tape.readBytes 32
  let (ek, dk) := KeyGen_internal p d z
  (ek, dk, tape)

/-- Encapsulation Key Modulus Check (§7.2, Eq. 7.1).
    Verifies `ByteEncode₁₂(ByteDecode₁₂(ekPKE)) = ekPKE`, i.e., all encoded
    coefficients are reduced modulo q. Returns `true` if valid. -/
def Encaps.KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) : Bool :=
  let ekPKE := slice ek 0 (vecLen p)
  let decoded := NTTVector.ByteDecode ekPKE
  let recoded := NTTVector.ByteEncode decoded
  recoded = ekPKE

/-! ## §7.2 Algorithm 20 — ML-KEM.Encaps(ek)

Uses the encapsulation key to generate a shared key and an associated ciphertext.
Returns `none` if the encapsulation key fails validation. -/
def Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (tape : RandomTape) :
    Option (ByteVec 32 × ByteVec (ctLen p) × RandomTape) :=
  -- Steps 1–2: Encapsulation Key type check (length).
  -- Trivially enforced by `ek : ByteVec (ekLen p)`.
  -- Steps 3–4: RBG failure check.
  -- Trivially succeeds with `RandomTape` (no RBG failure mode).
  let (m, tape) := tape.readBytes 32
  if Encaps.KeyCheck p ek then                                                   -- Alg. 20, steps 5–6
    let (K, c) := Encaps_internal p ek m                                       -- Alg. 20, step 7
    some (K, c, tape)
  else none

/-- Decapsulation Key Hash Check (§7.3, Eq. 7.2).
    Computes `H(dk[384k : 768k+32])` and compares to `dk[768k+32 : 768k+64]`.
    Verifies integrity of the embedded ekPKE against the stored hash.
    Returns `true` if valid. -/
def Decaps.KeyCheck (p : ParameterSet) (dk : ByteVec (dkLen p)) : Bool :=
  let (_, ek, h, _) := dkParts p dk
  H ek = h                                                      -- Eq. (7.2)


/-! ## §7.3 Algorithm 21 — ML-KEM.Decaps(dk, c)

Uses the decapsulation key to produce a shared key from a ciphertext.
Returns `none` if the decapsulation key fails validation. -/
def Decaps (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    Option (ByteVec 32) :=
  -- Step 1: Decapsulation Key type check (length).
  -- Trivially enforced by `dk : ByteVec (dkLen p)`.
  -- Step 2: Ciphertext type check (length).
  -- Trivially enforced by `c : ByteVec (ctLen p)`.
  if Decaps.KeyCheck p dk then some (Decaps_internal p dk c)                      -- Alg. 21, steps 1–2
  else none

end Wychelean.KEM.MLKEM
