import Wychelean.Hashes.SHA3.XOF.Basic
import Wychelean.Hashes.TurboSHAKE.Basic

/-!
# Incremental API for TurboSHAKE128 and TurboSHAKE256

RFC 9861 §2.1's incremental output interface, over the generic sponge of
`Wychelean.Hashes.SHA3.XOF`: `init`, any number of `absorb`s, `finalize` with the domain
separation byte, then repeated `squeeze`s. Agreement with one-shot TurboSHAKE is proved in
`Wychelean.Hashes.TurboSHAKE.XOF.Properties`.

Top-level functions operate on byte vectors; the internal state uses bits.
-/

namespace Wychelean.Hashes.TurboSHAKE
open Wychelean Hashes.SHA3 Hashes.SHA3.Internal Internal

/-- RFC 9861 §2.2: initialize TurboSHAKE128 at rate 1344 bits (Table 1: capacity 32 bytes). -/
def TurboSHAKE128.init := Incremental.sponge.init (r := b - 256) (hr := by decide)

/-- RFC 9861 §2.2: initialize TurboSHAKE256 at rate 1088 bits (Table 1: capacity 64 bytes). -/
def TurboSHAKE256.init := Incremental.sponge.init (r := b - 512) (hr := by decide)

/-- Absorb more of the message `M` into a TurboSHAKE128 state. -/
def TurboSHAKE128.absorb {n} (s : Incremental.sponge.absorbingState (b - 256)) (M : ByteVec n) :=
  Incremental.sponge.absorb KP (b - 256) (by decide) s (bytesToBits M).toList

/-- Absorb more of the message `M` into a TurboSHAKE256 state. -/
def TurboSHAKE256.absorb {n} (s : Incremental.sponge.absorbingState (b - 512)) (M : ByteVec n) :=
  Incremental.sponge.absorb KP (b - 512) (by decide) s (bytesToBits M).toList

/-- RFC 9861 §2.2: append `D` to the message and pad. As in the one-shot API, pad10*1 contributes
the top bit of `D`. -/
def TurboSHAKE128.finalize (s : Incremental.sponge.absorbingState (b - 256)) (D : Byte)
    (_ : 0 < D ∧ D < 0x80 := by decide) :=
  Incremental.sponge.finalize KP (b - 256) (by decide) s (domainSuffix D).toBitsLE.toList

/-- RFC 9861 §2.2: append `D` to the message and pad. As in the one-shot API, pad10*1 contributes
the top bit of `D`. -/
def TurboSHAKE256.finalize (s : Incremental.sponge.absorbingState (b - 512)) (D : Byte)
    (_ : 0 < D ∧ D < 0x80 := by decide) :=
  Incremental.sponge.finalize KP (b - 512) (by decide) s (domainSuffix D).toBitsLE.toList

/-- Squeeze `L` bytes out of a TurboSHAKE128 state. Returns the new state and the bytes. -/
def TurboSHAKE128.squeeze (s : Incremental.sponge.squeezingState (b - 256)) (L : Nat) :
    Incremental.sponge.squeezingState (b - 256) × ByteVec L :=
  let (s, bits) := Incremental.sponge.squeeze KP (b - 256) (by decide) s (8 * L)
  (s, bitsToBytes bits)

/-- Squeeze `L` bytes out of a TurboSHAKE256 state. Returns the new state and the bytes. -/
def TurboSHAKE256.squeeze (s : Incremental.sponge.squeezingState (b - 512)) (L : Nat) :
    Incremental.sponge.squeezingState (b - 512) × ByteVec L :=
  let (s, bits) := Incremental.sponge.squeeze KP (b - 512) (by decide) s (8 * L)
  (s, bitsToBytes bits)

end Wychelean.Hashes.TurboSHAKE
