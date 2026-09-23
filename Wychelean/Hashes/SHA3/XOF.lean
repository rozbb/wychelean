import Wychelean.Hashes.SHA3.Basic

/-!
# Incremental sponge API

One absorb followed by repeated squeezes; equivalence to one-shot SHAKE is tested, not proved.

Adapted from Microsoft SymCrypt (MIT; see LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/XOF.lean
-/

namespace Wychelean.Hashes.SHA3
open Wychelean Internal

section Sponge -- generic sponge construction

namespace Incremental

variable
  -- algorithm
  (f : BitVec b → BitVec b)
  (r : Nat)  -- rate: number of bits added/squeezed at a time
  (hr : 0 < r ∧ r < b := by decide)

/-- The state of a sponge; the rate is a phantom parameter, fixed by the functions below. -/
structure sponge.state (_rate : Nat) where
  S : BitVec b        -- permutation internal state
  Z : Array Bit       -- output stream squeezed so far, including the rate block of `S`
  x : Nat             -- number of bits already returned
  hx : x ≤ Z.size

def sponge.init : sponge.state r := {
  S := 0,
  Z := #[],
  x := 0,
  hx := by omega }

/-- Pad and absorb a bit vector into the initial context (FIPS 202 Algorithm 8, steps 1–6); the
first output block is then available. The argument is the context of `init`, kept for the
`XOF.Absorb(ctx, str)` shape of FIPS 203 §4.1. -/
def sponge.absorb1 {n} (_s : sponge.state r) (N : BitVec n) : sponge.state r :=
  let S := absorb f r N
  { S, Z := (S.extractLsb' 0 r).toBitsLE.toArray, x := 0, hx := by omega }

/-- Permute and append the next rate block to the output stream. -/
def sponge.squeeze_r (s : sponge.state r) : sponge.state r :=
  let (_, S) := squeezeStep f r s.S
  let Z := s.Z ++ (S.extractLsb' 0 r).toBitsLE.toArray
  have hx : s.x ≤ Z.size := Nat.le_trans s.hx (by simp [Z])
  { s with Z, S, hx }

@[simp] theorem sponge.squeeze_r_x (s : sponge.state r) : (squeeze_r f r s).x = s.x := rfl

@[simp] theorem sponge.squeeze_r_size (s : sponge.state r) :
    (squeeze_r f r s).Z.size = s.Z.size + r := by
  simp [squeeze_r]

/-- Squeeze `d` bits on demand, permuting only when the stream is exhausted. -/
def sponge.squeeze1 (hr : 0 < r ∧ r < b := by decide) (s : sponge.state r) (d : Nat) :
    sponge.state r × Vector Bit d :=
  if hd : s.Z.size < s.x + d then
    squeeze1 hr (squeeze_r f r s) d
  else
    let D : Vector Bit d := (s.Z.extract s.x (s.x + d)).toVector.cast (by simp; omega)
    have hx : s.x + d ≤ s.Z.size := by omega
    ({ s with x := s.x + d, hx }, D)
termination_by s.x + d - s.Z.size
decreasing_by
  have := hr.1
  simp only [sponge.squeeze_r_x, sponge.squeeze_r_size]
  omega

end Incremental

end Sponge

/-! ## Incremental API for SHAKE128 and SHAKE256

Top-level functions operate on byte vectors; the internal state uses bits. -/

def SHAKE128.init := Incremental.sponge.init (r := b - 256)
def SHAKE256.init := Incremental.sponge.init (r := b - 512)

def SHAKE128.absorb {n} (s : Incremental.sponge.state (b - 256)) (msg : ByteVec n) :=
  Incremental.sponge.absorb1 (Permutations.Keccak.keccak_f .w1600) (r := b - 256) s
    (xofSuffix ++ BitVec.ofBytesLE msg)

def SHAKE256.absorb {n} (s : Incremental.sponge.state (b - 512)) (msg : ByteVec n) :=
  Incremental.sponge.absorb1 (Permutations.Keccak.keccak_f .w1600) (r := b - 512) s
    (xofSuffix ++ BitVec.ofBytesLE msg)

def SHAKE128.squeeze (s : Incremental.sponge.state (b - 256)) (outBytes : Nat) :
    Incremental.sponge.state (b - 256) × ByteVec outBytes :=
  let (s, bits) := Incremental.sponge.squeeze1 (Permutations.Keccak.keccak_f .w1600) (r := b - 256) (hr := by decide)
    s (8 * outBytes)
  (s, bitsToBytes bits)

def SHAKE256.squeeze (s : Incremental.sponge.state (b - 512)) (outBytes : Nat) :
    Incremental.sponge.state (b - 512) × ByteVec outBytes :=
  let (s, bits) := Incremental.sponge.squeeze1 (Permutations.Keccak.keccak_f .w1600) (r := b - 512) (hr := by decide)
    s (8 * outBytes)
  (s, bitsToBytes bits)

end Wychelean.Hashes.SHA3
