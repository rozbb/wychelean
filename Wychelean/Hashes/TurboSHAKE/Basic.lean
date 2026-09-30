import Wychelean.Hashes.SHA3.Basic

/-!
# TurboSHAKE
RFC 9861 §2: https://www.rfc-editor.org/rfc/rfc9861.html#section-2

The FIPS 202 sponge of `Wychelean.Hashes.SHA3`, with the permutation reduced to 12 rounds.
-/
namespace Wychelean.Hashes.TurboSHAKE
open Wychelean Hashes.SHA3.Internal

namespace Internal

/-- RFC 9861 §2.2: KP, Keccak-p[1600, n_r=12]. -/
abbrev KP := Permutations.Keccak.keccak_p .w1600 12

/-- The bits of `D` up to and excluding the most significant `1`. Per §2.2: we let the topmost bit
of `D` (which necessarily exists because `D ≠ 0`) be contributed by pad10*1. So all we add to M is
lower bits of `D`. -/
def domainSuffix (D : Byte) : BitVec D.toNat.log2 := D.toBitVec.setWidth _

/-- RFC 9861 §2.2: the sponge over KP with capacity `c`, absorbing `M || D`; `L`-byte output. -/
def turboShake (c : Nat) {n} (M : ByteVec n) (D : Byte) (L : Nat)
    (hc : 0 < c ∧ c < 1600 := by grind) : ByteVec L :=
  -- Sponge does the pad10*1 for us, including the top one of D. So we feed in M || domainSuffix D
  (sponge KP (1600 - c) (domainSuffix D ++ BitVec.ofBytesLE M) (8 * L)).toBytesLE

end Internal

/-- TurboSHAKE128, RFC 9861 §2. Any finite byte string; `L`-byte output. The domain separation
byte `D` lies in [0x01, 0x7F]. Technically `D` is optional in the spec, but we require it. -/
def turboShake128 {n} (M : ByteVec n) (D : Byte) (L : Nat)
    (_ : 0 < D ∧ D < 0x80 := by decide) : ByteVec L :=
  -- §2.2 Table 1: Capacity of TurboSHAKE128 is 32 bytes
  Internal.turboShake 256 M D L

/-- TurboSHAKE128, RFC 9861 §2. Any finite byte string; `L`-byte output. The domain separation
byte `D` lies in [0x01, 0x7F]. Technically `D` is optional in the spec, but we require it. -/
def turboShake256 {n} (M : ByteVec n) (D : Byte) (L : Nat)
    (_ : 0 < D ∧ D < 0x80 := by decide) : ByteVec L :=
  -- §2.2 Table 1: Capacity of TurboSHAKE256 is 64 bytes
  Internal.turboShake 512 M D L

end Wychelean.Hashes.TurboSHAKE
