import Wychelean.Hashes.SHA3.Basic

namespace Wychelean.Hashes.SHA3
open Wychelean

/-- The SHA3 and RawSHAKE domains differ (FIPS 202 §§6.1, 6.3). -/
theorem hash_raw_suffixes_distinct : hashSuffix ≠ rawSuffix := by decide

/-- FIPS 202 §6.2 XOF outputs share every shorter prefix. -/
theorem SHAKE128_prefix (M : Vector Bool n) (d e : Nat) (h : d ≤ e) :
    slice (SHAKE128 M e) 0 d (by omega) = SHAKE128 M d :=
  Keccak.SPONGE_prefix _ _ _ _ _ (by decide) h

theorem SHAKE256_prefix (M : Vector Bool n) (d e : Nat) (h : d ≤ e) :
    slice (SHAKE256 M e) 0 d (by omega) = SHAKE256 M d :=
  Keccak.SPONGE_prefix _ _ _ _ _ (by decide) h

theorem shake128_prefix (M : Vector UInt8 n) (d e : Nat) (h : d ≤ e) :
    slice (shake128 M e) 0 d (by omega) = shake128 M d := by
  unfold shake128
  rw [← bitsToBytes_slice _ d h, SHAKE128_prefix _ _ _ (by omega)]

theorem shake256_prefix (M : Vector UInt8 n) (d e : Nat) (h : d ≤ e) :
    slice (shake256 M e) 0 d (by omega) = shake256 M d := by
  unfold shake256
  rw [← bitsToBytes_slice _ d h, SHAKE256_prefix _ _ _ (by omega)]

end Wychelean.Hashes.SHA3
