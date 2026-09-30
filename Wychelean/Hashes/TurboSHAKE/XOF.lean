import Wychelean.Hashes.SHA3.XOF
import Wychelean.Hashes.TurboSHAKE.Basic

/-!
# Incremental API for TurboSHAKE128 and TurboSHAKE256

RFC 9861 §2.1's incremental output interface: the whole input is absorbed at once by
`initAndAbsorb`, followed by repeated squeezes, over the generic sponge of
`Wychelean.Hashes.SHA3.XOF`. Equivalence to one-shot TurboSHAKE is tested, not proved.

Top-level functions operate on byte vectors; the internal state uses bits.
-/

namespace Wychelean.Hashes.TurboSHAKE
open Wychelean Hashes.SHA3 Hashes.SHA3.Internal Internal

/-- Start a TurboSHAKE128 sponge and absorb all of `M || D`, ready to squeeze. Rate is b value minus
capacity. §2.2 Table 1: Capacity of TurboSHAKE128 is 32 bytes. -/
def TurboSHAKE128.initAndAbsorb {n} (M : ByteVec n) (D : Byte)
    (_ : 0 < D ∧ D < 0x80 := by decide) : Incremental.sponge.state (b - 256) :=
  -- Like the one-shot API, absorb1 does pad10*1 for us
  Incremental.sponge.absorb1 KP (r := b - 256) (Incremental.sponge.init (b - 256))
    (domainSuffix D ++ BitVec.ofBytesLE M)

/-- Start a TurboSHAKE256 sponge and absorb all of `M || D`, ready to squeeze. Rate is b value minus
capacity. §2.2 Table 1: Capacity of TurboSHAKE256 is 64 bytes. -/
def TurboSHAKE256.initAndAbsorb {n} (M : ByteVec n) (D : Byte)
    (_ : 0 < D ∧ D < 0x80 := by decide) : Incremental.sponge.state (b - 512) :=
  -- Like the one-shot API, absorb1 does pad10*1 for us
  Incremental.sponge.absorb1 KP (r := b - 512) (Incremental.sponge.init (b - 512))
    (domainSuffix D ++ BitVec.ofBytesLE M)

/-- Squeeze bytes out of a TurboSHAKE128 state. Returns the bytes and the new state. -/
def TurboSHAKE128.squeeze (s : Incremental.sponge.state (b - 256)) (L : Nat) :
    Incremental.sponge.state (b - 256) × ByteVec L :=
  let (s, bits) := Incremental.sponge.squeeze1 KP (r := b - 256) (hr := by decide) s (8 * L)
  (s, bitsToBytes bits)

/-- Squeeze bytes out of a TurboSHAKE256 state. Returns the bytes and the new state. -/
def TurboSHAKE256.squeeze (s : Incremental.sponge.state (b - 512)) (L : Nat) :
    Incremental.sponge.state (b - 512) × ByteVec L :=
  let (s, bits) := Incremental.sponge.squeeze1 KP (r := b - 512) (hr := by decide) s (8 * L)
  (s, bitsToBytes bits)

end Wychelean.Hashes.TurboSHAKE
