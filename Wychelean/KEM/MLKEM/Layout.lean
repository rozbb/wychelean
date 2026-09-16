import Wychelean.KEM.MLKEM.Basic

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.PolyRing
open scoped Wychelean.Notations
open Bounds

/-! ## Key and ciphertext layouts (Algorithm 13 step 19, Algorithm 16 step 3, Algorithm 14 step 24) -/

/-- `ekPKE = ByteEncode₁₂(t̂) ‖ ρ`. -/
structure EkPKE (p : ParameterSet) where
  «t̂» : NTTVector (k p)
  ρ : Seed

instance : ByteLayout (EkPKE p) (ekPKELen p) where
  pack e := ByteEncode₁₂ e.«t̂» ‖ e.ρ
  unpack b :=
    let (t, ρ) := split b (vecLen p) seedLen
    ⟨ByteDecode₁₂ t, ρ⟩

/-- `dk = dkPKE ‖ ek ‖ H(ek) ‖ z`. -/
structure Dk (p : ParameterSet) where
  pke : ByteVec (dkPKELen p)
  ek : ByteVec (ekLen p)
  h : ByteVec hashLen
  z : Seed

instance : ByteLayout (Dk p) (dkLen p) where
  pack d := d.pke ‖ d.ek ‖ d.h ‖ d.z
  unpack b :=
    let (b, z) := split b (dkPKELen p + ekLen p + hashLen) seedLen
    let (b, h) := split b (dkPKELen p + ekLen p) hashLen
    let (pke, ek) := split b (dkPKELen p) (ekLen p)
    ⟨pke, ek, h, z⟩

/-- `c = c₁ ‖ c₂`. -/
structure Ciphertext (p : ParameterSet) where
  c₁ : ByteVec (c₁Len p)
  c₂ : ByteVec (c₂Len p)

instance : ByteLayout (Ciphertext p) (ctLen p) where
  pack c := c.c₁ ‖ c.c₂
  unpack b :=
    let (c₁, c₂) := split b (c₁Len p) (c₂Len p)
    ⟨c₁, c₂⟩

end Wychelean.KEM.MLKEM
