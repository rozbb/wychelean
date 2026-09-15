import Wychelean.KEM.MLKEM
import RunTests.Basic
import RunTests.Parser.Rsp

/-!
# ML-KEM known-answer tests from the SymCrypt specification

The three NIST ACVP vectors (one per parameter set) and the Appendix A table of
`ζ^BitRev₇(i)` values that ship with the SymCrypt Lean specification, plus its round-trip
checks. The vectors are in `TestVectors/symcrypt_acvp.rsp`, copied from
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/SpecTests/MLKEM/TestVectors.lean
which attributes them to SymCrypt's `unittest/kat_kem.dat`, derived from NIST ACVP
ML-KEM-keyGen-FIPS203 and ML-KEM-encapDecap-FIPS203. Each parameter set runs
`KeyGen_internal` against the expected keys, `Encaps_internal` against the expected shared key
and ciphertext, and a `KeyGen_internal → Encaps_internal → Decaps_internal`/`Decaps` round trip.
-/

namespace Wychelean.KEM.MLKEM.Tests
open RunTests RunTests.Parser RunTests.Parser.Rsp
open Std.Internal.Parsec.String

/-- FIPS 203 Appendix A: `ζ^BitRev₇(i) mod q` for `i = 0, …, 127`. -/
private def appendixA : Array Nat := #[
  1, 1729, 2580, 3289, 2642, 630, 1897, 848,
  1062, 1919, 193, 797, 2786, 3260, 569, 1746,
  296, 2447, 1339, 1476, 3046, 56, 2240, 1333,
  1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
  289, 331, 3253, 1756, 1197, 2304, 2277, 2055,
  650, 1977, 2513, 632, 2865, 33, 1320, 1915,
  2319, 1435, 807, 452, 1438, 2868, 1534, 2402,
  2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
  17, 2761, 583, 2649, 1637, 723, 2288, 1100,
  1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
  1703, 1651, 2789, 1789, 1847, 952, 1461, 2687,
  939, 2308, 2437, 2388, 733, 2337, 268, 641,
  1584, 2298, 2037, 3220, 375, 2549, 2090, 1645,
  1063, 319, 2773, 757, 2099, 561, 2466, 2594,
  2804, 1092, 403, 1026, 1143, 2150, 2775, 886,
  1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]

/-- Every value of the Appendix A table, and the NTT round-trip identities. -/
def appendixAAndRoundTrips : Suite where
  name := "ML-KEM Appendix A and NTT round trips"
  tests := pure <| (List.range 128).map (fun i =>
      check s!"zeta^BitRev7({i})" appendixA[i]! (ζ ^ (bitRev 7 i) : Zq).val) ++ [
    let F : Vector (ZMod (m 12)) 256 := Vector.ofFn fun i => (i.val : ZMod (m 12))
    check "ByteDecode (ByteEncode 12 F) = F" true (ByteDecode (ByteEncode 12 F) == F),
    let f : Polynomial := PolyRing.Poly.ofFn fun i => ((i.val + 1 : ℕ) : Zq)
    check "nttInv (ntt f) = f" true ((f.ntt : Tq).nttInv == f),
    let one : Polynomial := 1
    let f : Polynomial := PolyRing.Poly.ofFn fun i => ((i.val * 7 + 3 : ℕ) : Zq)
    check "nttInv (ntt f * ntt one) = f" true ((f.ntt * one.ntt : Tq).nttInv == f) ]

private def vectorFile : System.FilePath := "Wychelean/KEM/MLKEM/TestVectors/symcrypt_acvp.rsp"

/-- One parameter set's section of the response file. -/
private structure Kat where
  d : Array UInt8
  z : Array UInt8
  ek : Array UInt8
  dk : Array UInt8
  encEk : Array UInt8
  m : Array UInt8
  K : Array UInt8
  c : Array UInt8

private def parameterSet (name : String) : Parser Kat := do
  header name
  let d ← field "keygen_d" readHex
  let z ← field "keygen_z" readHex
  let ek ← field "keygen_ek" readHex
  let dk ← field "keygen_dk" readHex
  let encEk ← field "encaps_ek" readHex
  let m ← field "encaps_m" readHex
  let K ← field "encaps_K" readHex
  let c ← field "encaps_c" readHex
  return { d, z, ek, dk, encEk, m, K, c }

private def parseAll : Parser (Kat × Kat × Kat) := responseFile do
  let a ← parameterSet "ML-KEM-512"
  let b ← parameterSet "ML-KEM-768"
  let c ← parameterSet "ML-KEM-1024"
  return (a, b, c)

private def run (p : ParameterSet) (kat : Kat) : IO (List Test) := do
  let d ← IO.ofExcept (toFixed 32 kat.d)
  let z ← IO.ofExcept (toFixed 32 kat.z)
  let kgEk ← IO.ofExcept (toFixed (ekLen p) kat.ek)
  let kgDk ← IO.ofExcept (toFixed (dkLen p) kat.dk)
  let encEk ← IO.ofExcept (toFixed (ekLen p) kat.encEk)
  let m ← IO.ofExcept (toFixed 32 kat.m)
  let encK ← IO.ofExcept (toFixed 32 kat.K)
  let encC ← IO.ofExcept (toFixed (ctLen p) kat.c)
  let (ek, dk) := KeyGen_internal p d z
  let (K, c) := Encaps_internal p encEk m
  let (K2, c2) := Encaps_internal p ek m
  return [ check "KeyGen ek" kgEk ek,
           check "KeyGen dk" kgDk dk,
           check "Encaps K" encK K,
           check "Encaps c" encC c,
           check "Decaps_internal round trip" K2 (Decaps_internal p dk c2),
           check "Decaps round trip" (some K2) (Decaps p dk c2) ]

private def cavp (name : String) (p : ParameterSet) (pick : Kat × Kat × Kat → Kat) : Suite where
  name := s!"{name} (SymCrypt ACVP vectors)"
  tests := do
    let kats ← RunTests.Parser.parseFile parseAll vectorFile
    run p (pick kats)

def cavpSuites : List Suite :=
  [ appendixAAndRoundTrips,
    cavp "ML-KEM-512" .ML_KEM_512 (·.1),
    cavp "ML-KEM-768" .ML_KEM_768 (·.2.1),
    cavp "ML-KEM-1024" .ML_KEM_1024 (·.2.2) ]

end Wychelean.KEM.MLKEM.Tests
