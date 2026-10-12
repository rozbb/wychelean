import Wychelean.KEM.MLKEM.Layout

/-! FIPS 203 §5–§7: K-PKE, the internal algorithms, and ML-KEM. -/

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.Utils.Linear
open scoped Wychelean.Notations
open Bounds
open Polynomial (NTT)
open PolyVector (NTT)
open Tq (NTTInv)
open NTTVector (NTTInv)

/-! ## §5.1 Algorithm 13 — K-PKE.KeyGen(d) -/
def K_PKE.KeyGen (p : ParameterSet) (d : Seed) : ByteVec (ekPKELen p) × ByteVec (dkPKELen p) := Id.run do
  let (ρ, σ) := G (d ‖ #v[(k p : Byte)])                                       -- Alg. 13, step 1
  let mut N : ℕ := 0                                                           -- Alg. 13, step 2
  let mut «Â» : NTTMatrix (k p) := Vector.replicate _ (Vector.replicate _ 0)
  for i in [0:k p] do                                                          -- Alg. 13, step 3
    for j in [0:k p] do                                                        -- Alg. 13, step 4
      «Â» := «Â».set i j (SampleNTT (ρ ‖ #v[(j : Byte), (i : Byte)]))          -- Alg. 13, step 5
  let mut s : PolyVector q (k p) := Vector.replicate _ 0
  for hi : i in [0:k p] do                                                     -- Alg. 13, step 8
    s := s.set i (SamplePolyCBD (PRF (η₁ p) σ N))                              -- Alg. 13, step 9
    N := N + 1                                                                 -- Alg. 13, step 10
  let mut e : PolyVector q (k p) := Vector.replicate _ 0
  for hi : i in [0:k p] do                                                     -- Alg. 13, step 12
    e := e.set i (SamplePolyCBD (PRF (η₁ p) σ N))                              -- Alg. 13, step 13
    N := N + 1                                                                 -- Alg. 13, step 14
  let «ŝ» := NTT s                                                             -- Alg. 13, step 16
  let «ê» := NTT e                                                             -- Alg. 13, step 17
  let «t̂» := «Â» * «ŝ» + «ê»                                                  -- Alg. 13, step 18
  let ekPKE := ByteEncode₁₂ «t̂» ‖ ρ                                           -- Alg. 13, step 19
  let dkPKE := ByteEncode₁₂ «ŝ»                                                -- Alg. 13, step 20
  return (ekPKE, dkPKE)                                                        -- Alg. 13, step 21

/-! ## §5.2 Algorithm 14 — K-PKE.Encrypt(ekPKE, m, r) -/
def K_PKE.Encrypt (p : ParameterSet) (ekPKE : ByteVec (ekPKELen p)) (m : Seed) (r : Seed) :
    ByteVec (ctLen p) := Id.run do
  let mut N : ℕ := 0                                                           -- Alg. 14, step 1
  let «t̂» := ByteDecode₁₂ (slice ekPKE 0 (vecLen p))                          -- Alg. 14, step 2
  let ρ := slice ekPKE (vecLen p) seedLen                                      -- Alg. 14, step 3
  let mut «Â» : NTTMatrix (k p) := Vector.replicate _ (Vector.replicate _ 0)
  for i in [0:k p] do                                                          -- Alg. 14, step 4
    for j in [0:k p] do                                                        -- Alg. 14, step 5
      «Â» := «Â».set i j (SampleNTT (ρ ‖ #v[(j : Byte), (i : Byte)]))          -- Alg. 14, step 6
  let mut y : PolyVector q (k p) := Vector.replicate _ 0
  for hi : i in [0:k p] do                                                     -- Alg. 14, step 9
    y := y.set i (SamplePolyCBD (PRF (η₁ p) r N))                              -- Alg. 14, step 10
    N := N + 1                                                                 -- Alg. 14, step 11
  let mut e₁ : PolyVector q (k p) := Vector.replicate _ 0
  for hi : i in [0:k p] do                                                     -- Alg. 14, step 13
    e₁ := e₁.set i (SamplePolyCBD (PRF η₂ r N))                                -- Alg. 14, step 14
    N := N + 1                                                                 -- Alg. 14, step 15
  let e₂ := SamplePolyCBD (PRF η₂ r N)                                         -- Alg. 14, step 17
  let «ŷ» := NTT y                                                             -- Alg. 14, step 18
  let u := NTTInv («Â»ᵀ * «ŷ») + e₁                                            -- Alg. 14, step 19
  let μ := Polynomial.Decompress 1 ⟨ByteDecode (m.cast (by grind))⟩            -- Alg. 14, step 20
  let v := NTTInv ⟪«t̂», «ŷ»⟫ + e₂ + μ                                         -- Alg. 14, step 21
  let c₁ := PolyVector.ByteEncode (dᵤ p) (PolyVector.Compress (dᵤ p) u)        -- Alg. 14, step 22
  let c₂ := ByteEncode (dᵥ p) (Polynomial.Compress (dᵥ p) v).coeffs            -- Alg. 14, step 23
  return c₁ ‖ c₂                                                               -- Alg. 14, step 24

/-! ## §5.3 Algorithm 15 — K-PKE.Decrypt(dkPKE, c) -/
def K_PKE.Decrypt (p : ParameterSet) (dkPKE : ByteVec (dkPKELen p)) (c : ByteVec (ctLen p)) : Seed :=
  let c₁ := slice c 0 (c₁Len p)                                                -- Alg. 15, step 1
  let c₂ := slice c (c₁Len p) (c₂Len p)                                        -- Alg. 15, step 2
  let u' := PolyVector.Decompress (dᵤ p) (PolyVector.ByteDecode (dᵤ p) c₁)     -- Alg. 15, step 3
  let v' := Polynomial.Decompress (dᵥ p) ⟨ByteDecode c₂⟩                       -- Alg. 15, step 4
  let «ŝ» := ByteDecode₁₂ dkPKE                                                -- Alg. 15, step 5
  let w := v' - NTTInv ⟪«ŝ», NTT u'⟫                                           -- Alg. 15, step 6
  let m := ByteEncode 1 (Polynomial.Compress 1 w).coeffs                       -- Alg. 15, step 7
  m.cast (by grind)                                                            -- Alg. 15, step 8

/-! ## §6.1 Algorithm 16 — ML-KEM.KeyGen_internal(d,z) -/
def Internal.KeyGen (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  let (ekPKE, dkPKE) := K_PKE.KeyGen p d                                       -- Alg. 16, step 1
  let ek := ekPKE                                                              -- Alg. 16, step 2
  let dk := pack (⟨dkPKE, ek, H ek, z⟩ : Dk p)                            -- Alg. 16, step 3
  (ek, dk)

/-! ## §6.2 Algorithm 17 — ML-KEM.Encaps_internal(ek, m) -/
def Internal.Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    SharedKey × ByteVec (ctLen p) :=
  let (K, r) := G (m ‖ H ek)                                                   -- Alg. 17, step 1
  let c := K_PKE.Encrypt p ek m r                                              -- Alg. 17, step 2
  (K, c)

/-! ## §6.3 Algorithm 18 — ML-KEM.Decaps_internal(dk, c) -/
def Internal.Decaps (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    SharedKey :=
  let ⟨dkPKE, ekPKE, h, z⟩ := (unpack dk : Dk p)                               -- Alg. 18, steps 1–4
  let m' := K_PKE.Decrypt p dkPKE c                                            -- Alg. 18, step 5
  let (K', r') := G (m' ‖ h)                                                   -- Alg. 18, step 6
  let «K̄» := J (z ‖ c)                                                        -- Alg. 18, step 7
  let c' := K_PKE.Encrypt p ekPKE m' r'                                        -- Alg. 18, step 8
  if c ≠ c' then «K̄» else K'                                                  -- Alg. 18, steps 9–12

/-! ## §7 ML-KEM (random bytes are explicit arguments) -/

/-! ## §7.1 Algorithm 19 — ML-KEM.KeyGen() -/
def KeyGen (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  Internal.KeyGen p d z                                                        -- Alg. 19, step 6

/-- Modulus check (§7.2, Eq. 7.1): every encoded coefficient is reduced modulo `q`. -/
def Encaps.KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) : Bool :=
  let test := ByteEncode₁₂ (ByteDecode₁₂ (slice ek 0 (vecLen p)) : NTTVector (k p))
  test = slice ek 0 (vecLen p)                                                 -- Eq. (7.1)

/-! ## §7.2 Algorithm 20 — ML-KEM.Encaps(ek) -/
def Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    Option (SharedKey × ByteVec (ctLen p)) :=
  if Encaps.KeyCheck p ek then some (Internal.Encaps p ek m)                     -- Alg. 20, step 5
  else none

/-- Hash check (§7.3, Eq. 7.2): the stored `H(ek)` matches the embedded `ek`. -/
def Decaps.KeyCheck (p : ParameterSet) (dk : ByteVec (dkLen p)) : Bool :=
  let ⟨_, ek, h, _⟩ := (unpack dk : Dk p)
  H ek = h                                                      -- Eq. (7.2)


/-! ## §7.3 Algorithm 21 — ML-KEM.Decaps(dk, c) -/
def Decaps (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    Option SharedKey :=
  if Decaps.KeyCheck p dk then some (Internal.Decaps p dk c)                      -- Alg. 21, steps 1–2
  else none

end Wychelean.KEM.MLKEM
