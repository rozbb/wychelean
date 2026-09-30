import Wychelean.Hashes.TurboSHAKE
import RunTests.Parser.Basic

/-!
# TurboSHAKE elaboration-time checks

Evaluated when this module is built.
-/

namespace Wychelean.Hashes.TurboSHAKE.Tests
open RunTests.Parser Permutations.Keccak

-- RFC 9861 Appendix A.1: the round constants of KP, as the little-endian lanes printed there.
#guard (List.range 12).map (fun i =>
    BitVec.toBytesLE (n := 8) (ι.RC .w1600 (roundIndex .w1600 12 i))) = [
  hex! "8b80008000000000", hex! "8b00000000000080", hex! "8980000000000080",
  hex! "0380000000000080", hex! "0280000000000080", hex! "8000000000000080",
  hex! "0a80000000000000", hex! "0a00008000000080", hex! "8180008000000080",
  hex! "8080000000000080", hex! "0100008000000000", hex! "0880008000000080"]

-- The default domain separation byte matches SHAKE's suffix (FIPS 202 §6.2).
#guard (Internal.domainSuffix 0x1F).cast (by decide) = Hashes.SHA3.Internal.xofSuffix

end Wychelean.Hashes.TurboSHAKE.Tests
