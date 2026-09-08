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

end Wychelean.Hashes.SHA3
