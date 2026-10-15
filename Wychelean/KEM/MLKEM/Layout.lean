module

public import Wychelean.KEM.MLKEM.Encode

@[expose] public section

namespace Wychelean.KEM.MLKEM

open Wychelean Wychelean.Hashes
open scoped Wychelean.Utils.Linear
open scoped Wychelean.Notations
open Bounds

/-- `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` (Algorithm 16, step 3). -/
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

end Wychelean.KEM.MLKEM
