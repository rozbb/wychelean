import Wychelean.KEM.MLKEM.Basic

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.PolyRing
open scoped Wychelean.Notations
open Bounds

/-! ## Key and ciphertext layouts -/

/-- `ekPKE = ByteEncode₁₂(t̂) ‖ ρ` (Algorithm 13, step 19). -/
structure EkPKE (p : ParameterSet) where
  «t̂» : NTTVector (k p)
  ρ : Seed

instance : ByteLayout (EkPKE p) (ekPKELen p) where
  pack e := ByteEncode₁₂ e.«t̂» ‖ e.ρ
  unpack b :=
    let (t, ρ) := split b (vecLen p) seedLen
    ⟨ByteDecode₁₂ t, ρ⟩

/-- `dkPKE = ByteEncode₁₂(ŝ)` (Algorithm 13, step 20). -/
structure DkPKE (p : ParameterSet) where
  «ŝ» : NTTVector (k p)

instance : ByteLayout (DkPKE p) (dkPKELen p) where
  pack d := ByteEncode₁₂ d.«ŝ»
  unpack b := ⟨ByteDecode₁₂ b⟩

/-- `c = ByteEncode_dᵤ(u) ‖ ByteEncode_dᵥ(v)` of the compressed `u` and `v`
(Algorithm 14, steps 22–24). -/
structure Ciphertext (p : ParameterSet) where
  u : PolyVector (m (dᵤ p)) (k p)
  v : Polynomial (m (dᵥ p))

instance : ByteLayout (Ciphertext p) (ctLen p) where
  pack c := PolyVector.ByteEncode (dᵤ p) c.u ‖ ByteEncode (dᵥ p) c.v.coeffs
  unpack b :=
    let (c₁, c₂) := split b (c₁Len p) (c₂Len p)
    ⟨PolyVector.ByteDecode (dᵤ p) c₁, ⟨ByteDecode c₂⟩⟩

/-- `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` (Algorithm 16, step 3). -/
structure Dk (p : ParameterSet) where
  pke : DkPKE p
  ek : ByteVec (ekLen p)
  h : ByteVec hashLen
  z : Seed

instance : ByteLayout (Dk p) (dkLen p) where
  pack d := pack d.pke ‖ d.ek ‖ d.h ‖ d.z
  unpack b :=
    let (b, z) := split b (dkPKELen p + ekLen p + hashLen) seedLen
    let (b, h) := split b (dkPKELen p + ekLen p) hashLen
    let (pke, ek) := split b (dkPKELen p) (ekLen p)
    ⟨unpack pke, ek, h, z⟩

end Wychelean.KEM.MLKEM
