import Wychelean.Hashes.SHA3.Basic

/-!
# Incremental sponge API

An incremental (streaming) sponge: `init → absorb → squeeze*`. FIPS 202 only defines the
functional sponge (Algorithm 8); this models the software pattern of squeezing on demand, as
ML-KEM's `SampleNTT` (FIPS 203 Algorithm 7) requires from its XOF. Each `squeeze` returns the
next bits of the same output stream that `shake128`/`shake256` produce in one call.

Adapted from Microsoft SymCrypt (MIT; see LICENSE.SymCrypt):
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/Spec/SHA3/XOF.lean
The state is expressed over the `BitVec` sponge of `Wychelean.Hashes.SHA3.Basic`.
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

structure sponge.state where
  S : BitVec b        -- permutation internal state
  Z : Array Bit       -- bits already squeezed, excluding the rate block still in `S`
  x : Nat             -- number of bits already returned
  hx : x ≤ Z.size + r

def sponge.init : sponge.state r := {
  S := 0,
  Z := #[],
  x := 0,
  hx := by omega }

/-- Pad and absorb a bit vector (FIPS 202 Algorithm 8, steps 1–6). -/
def sponge.absorb1 {n} (s : sponge.state r) (N : BitVec n) : sponge.state r :=
  { s with S := absorb f r N }

/-- Squeeze `r` extra bits into the buffer. -/
def sponge.squeeze_r (s : sponge.state r) : sponge.state r :=
  let (block, S) := squeezeStep f r s.S
  let Z := s.Z ++ block.toBitsLE.toArray
  have hx : s.x ≤ Z.size + r := Nat.le_trans s.hx (by simp [Z])
  { s with Z, S, hx }

/-- Squeeze `d` bits on demand, permuting only when the buffer is exhausted. -/
def sponge.squeeze1 (s : sponge.state r) (d : Nat) : sponge.state r × Vector Bit d :=
  if hd : s.Z.size + r < s.x + d then
    squeeze1 (squeeze_r f r s) d
  else
    let A := s.Z ++ (s.S.extractLsb' 0 r).toBitsLE.toArray
    let D : Vector Bit d := (A.extract s.x (s.x + d)).toVector.cast (by simp [A]; omega)
    have hx : s.x + d ≤ s.Z.size + r := by omega
    ({ s with x := s.x + d, hx }, D)
termination_by s.x + d - (s.Z.size + r)
decreasing_by
  simp only [squeeze_r, squeezeStep, Array.size_append, BitVec.toBitsLE, Vector.size_toArray]
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
