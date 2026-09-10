import Wychelean.Hashes.Keccak
import Mathlib.Data.Nat.Log

/-!
# TurboSHAKE
RFC 9861 §2: https://www.rfc-editor.org/rfc/rfc9861.html#section-2
Keccak-p[1600,12], capacities 256 and 512 bits, with a delimited domain byte D in 1..127.
-/
namespace Wychelean.Hashes.TurboSHAKE
open Wychelean

/-- RFC 9861 §2: the delimiter byte ranges from 0x01 through 0x7f. -/
abbrev Domain := {D : UInt8 // 0 < D.toNat ∧ D.toNat < 128}

/-- The highest set bit of D supplies the first padding one. Its lower bits are the domain.
Passing only those lower bits to pad10*1 avoids applying that first one twice. -/
def domainLength (D : Domain) : Nat := Nat.log2 D.val.toNat

/-- Indexed message followed by the domain bits, in FIPS 202 Appendix B.1 bit order. -/
def inputBit (M : Vector UInt8 n) (D : Domain) (i : Fin (8 * n + domainLength D)) : Bool :=
  if h : i.val < 8 * n then
    (M[i.val / 8]'(by omega)).toBitVec.getLsbD (i.val % 8)
  else D.val.toBitVec.getLsbD (i.val - 8 * n)

/-- RFC 9861 Table 1: the two capacities and corresponding rates. -/
def capacity (strength256 : Bool) : Nat := if strength256 then 512 else 256

def bits (strength256 : Bool) (M : Vector UInt8 n) (D : Domain) (d : Nat) : Vector Bool d :=
  Keccak.SPONGE_fn (Permutations.Keccak.KECCAK_p 6 12) (1600 - capacity strength256)
    (8 * n + domainLength D) (inputBit M D) d (by cases strength256 <;> decide)

/-- TurboSHAKE128, RFC 9861 §2. Output length d is in bytes; the default domain is 0x1f.
The empty output is also defined, as the zero-length prefix of the XOF. -/
def TurboSHAKE128 (M : Vector UInt8 n) (d : Nat) (D : Domain := ⟨31, by decide⟩) : Vector UInt8 d :=
  bitsToBytes (bits false M D (8 * d))

/-- TurboSHAKE256, RFC 9861 §2; byte-oriented interface. -/
def TurboSHAKE256 (M : Vector UInt8 n) (d : Nat) (D : Domain := ⟨31, by decide⟩) : Vector UInt8 d :=
  bitsToBytes (bits true M D (8 * d))

abbrev turboshake128 := @TurboSHAKE128
abbrev turboshake256 := @TurboSHAKE256

theorem bits_prefix (strength256 : Bool) (M : Vector UInt8 n) (D : Domain)
    (d e : Nat) (h : d ≤ e) :
    slice (bits strength256 M D e) 0 d (by omega) = bits strength256 M D d :=
  Keccak.SPONGE_fn_prefix _ _ _ _ _ _ (by cases strength256 <;> decide) h

theorem TurboSHAKE128_prefix (M : Vector UInt8 n) (D : Domain) (d e : Nat) (h : d ≤ e) :
    slice (TurboSHAKE128 M e D) 0 d (by omega) = TurboSHAKE128 M d D := by
  unfold TurboSHAKE128
  rw [← bitsToBytes_slice _ d h, bits_prefix _ _ _ _ _ (by omega)]

theorem TurboSHAKE256_prefix (M : Vector UInt8 n) (D : Domain) (d e : Nat) (h : d ≤ e) :
    slice (TurboSHAKE256 M e D) 0 d (by omega) = TurboSHAKE256 M d D := by
  unfold TurboSHAKE256
  rw [← bitsToBytes_slice _ d h, bits_prefix _ _ _ _ _ (by omega)]

end Wychelean.Hashes.TurboSHAKE
