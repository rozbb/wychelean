import Wychelean.KEM.MLKEM.Layout

/-! FIPS 203 §5–§7: K-PKE, the internal algorithms, and ML-KEM. -/

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.PolyRing
open scoped Wychelean.Notations
open Bounds

/-! ## §5.1 Algorithm 13 — K-PKE.KeyGen(d) -/
def K_PKE.KeyGen (p : ParameterSet) (d : Seed) : ByteVec (ekPKELen p) × ByteVec (dkPKELen p) :=
  let (ρ, σ) := G (d ‖ #v[(k p : Byte)])                                       -- Alg. 13, step 1
  let «Â» : NTTMatrix (k p) := SampleMatrix ρ                                  -- Alg. 13, steps 3–7
  let s : PolyVector q (k p) := SampleVector (η₁ p) σ 0                        -- Alg. 13, steps 8–11
  let e : PolyVector q (k p) := SampleVector (η₁ p) σ (k p)                    -- Alg. 13, steps 12–15
  let «ŝ» := s.ntt                                                             -- Alg. 13, step 16
  let «ê» := e.ntt                                                             -- Alg. 13, step 17
  let «t̂» := «Â» * «ŝ» + «ê»                                                  -- Alg. 13, step 18
  let ekPKE := pack (⟨«t̂», ρ⟩ : EkPKE p)                                      -- Alg. 13, step 19
  let dkPKE := ByteEncode₁₂ «ŝ»                                                -- Alg. 13, step 20
  (ekPKE, dkPKE)

/-! ## §5.2 Algorithm 14 — K-PKE.Encrypt(ekPKE, m, r) -/
def K_PKE.Encrypt (p : ParameterSet) (ekPKE : ByteVec (ekPKELen p)) (m : Seed) (r : Seed) :
    ByteVec (ctLen p) :=
  let ⟨«t̂», ρ⟩ := (unpack ekPKE : EkPKE p)                                    -- Alg. 14, steps 2–3
  let «Â» : NTTMatrix (k p) := SampleMatrix ρ                                  -- Alg. 14, steps 4–8
  let y : PolyVector q (k p) := SampleVector (η₁ p) r 0                        -- Alg. 14, steps 9–12
  let e₁ : PolyVector q (k p) := SampleVector η₂ r (k p)                       -- Alg. 14, steps 13–16
  let e₂ := SamplePolyCBD (PRF η₂ r ((2 * k p : ℕ) : Byte))                    -- Alg. 14, step 17
  let «ŷ» := y.ntt                                                             -- Alg. 14, step 18
  let u := («Â»ᵀ * «ŷ»).map (·.nttInv) + e₁                                    -- Alg. 14, step 19
  let μ := Polynomial.Decompress 1 ⟨ByteDecode (m.cast (by grind))⟩            -- Alg. 14, step 20
  let v := ⟪«t̂», «ŷ»⟫.nttInv + e₂ + μ                                         -- Alg. 14, step 21
  let c₁ := PolyVector.ByteEncode (dᵤ p) (PolyVector.Compress (dᵤ p) u)        -- Alg. 14, step 22
  let c₂ := ByteEncode (dᵥ p) (Polynomial.Compress (dᵥ p) v).coeffs            -- Alg. 14, step 23
  pack (⟨c₁, c₂⟩ : Ciphertext p)                                               -- Alg. 14, step 24

/-! ## §5.3 Algorithm 15 — K-PKE.Decrypt(dkPKE, c) -/
def K_PKE.Decrypt (p : ParameterSet) (dkPKE : ByteVec (dkPKELen p)) (c : ByteVec (ctLen p)) :
    Seed :=
  let ⟨c₁, c₂⟩ := (unpack c : Ciphertext p)                                    -- Alg. 15, steps 1–2
  let u' := PolyVector.Decompress (dᵤ p) (PolyVector.ByteDecode (k := k p) (dᵤ p) c₁) -- Alg. 15, step 3
  let v' := Polynomial.Decompress (dᵥ p) ⟨ByteDecode c₂⟩                       -- Alg. 15, step 4
  let «ŝ» := ByteDecode₁₂ dkPKE                                                -- Alg. 15, step 5
  let w := v' - ⟪«ŝ», u'.ntt⟫.nttInv                                           -- Alg. 15, step 6
  let m := ByteEncode 1 (Polynomial.Compress 1 w).coeffs                       -- Alg. 15, step 7
  m.cast (by grind)

/-! ## §6.1 Algorithm 16 — ML-KEM.KeyGen_internal(d,z) -/
def Internal.KeyGen (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  let (ekPKE, dkPKE) := K_PKE.KeyGen p d                                       -- Alg. 16, step 1
  let ek := ekPKE                                                              -- Alg. 16, step 2
  let dk := pack (⟨dkPKE, ek, H ek, z⟩ : Dk p)                                 -- Alg. 16, step 3
  (ek, dk)

/-! ## §6.2 Algorithm 17 — ML-KEM.Encaps_internal(ek, m) -/
def Internal.Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    SharedKey × ByteVec (ctLen p) :=
  let (K, r) := G (m ‖ H ek)                                                -- Alg. 17, step 1
  let c := K_PKE.Encrypt p ek m r                                            -- Alg. 17, step 2
  (K, c)

/-! ## §6.3 Algorithm 18 — ML-KEM.Decaps_internal(dk, c) -/
def Internal.Decaps (p : ParameterSet) (dk : ByteVec (dkLen p)) (c : ByteVec (ctLen p)) :
    SharedKey :=
  let ⟨dkPKE, ekPKE, h, z⟩ := (unpack dk : Dk p)                               -- Alg. 18, steps 1–4
  let m' := K_PKE.Decrypt p dkPKE c                                           -- Alg. 18, step 5
  let (K', r') := G (m' ‖ h)                                                 -- Alg. 18, step 6
  let «K̄» := J (z ‖ c)                                                       -- Alg. 18, step 7
  let c' := K_PKE.Encrypt p ekPKE m' r'                                       -- Alg. 18, step 8
  if c ≠ c' then «K̄» else K'                                                  -- Alg. 18, steps 9–12

/-! ## §7 The ML-KEM Key-Encapsulation Mechanism

The bytes that Algorithms 19–20 draw from the random bit generator (§3.3), `d` and `z` for
KeyGen and `m` for Encaps, are arguments here. -/

/-! ## §7.1 Algorithm 19 — ML-KEM.KeyGen() -/
def KeyGen (p : ParameterSet) (d z : Seed) : ByteVec (ekLen p) × ByteVec (dkLen p) :=
  Internal.KeyGen p d z                                                        -- Alg. 19, step 6

/-- Modulus check (§7.2, Eq. 7.1): every encoded coefficient is reduced modulo `q`. -/
def Encaps.KeyCheck (p : ParameterSet) (ek : ByteVec (ekLen p)) : Bool :=
  pack (unpack ek : EkPKE p) = ek

/-! ## §7.2 Algorithm 20 — ML-KEM.Encaps(ek) -/
def Encaps (p : ParameterSet) (ek : ByteVec (ekLen p)) (m : Seed) :
    Option (SharedKey × ByteVec (ctLen p)) :=
  if Encaps.KeyCheck p ek then some (Internal.Encaps p ek m)                     -- Alg. 20, steps 5–7
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
