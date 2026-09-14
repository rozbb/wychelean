import Wychelean.KEM.MLKEM

/-!
# ML-KEM elaboration-time checks

The `#guard` micro tests of the SymCrypt specification, evaluated when this module is built:
https://github.com/microsoft/SymCrypt/blob/c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be/SymCRust/lean/SpecTests/MLKEM/TestVectors.lean
-/

namespace Wychelean.KEM.MLKEM.Tests

#guard
  let b : Vector Bool (8 * 2) :=
    ⟨⟨[false, true, false, true, false, false, false, false,
      true, false, false, false, false, false, false, false]⟩, by simp⟩
  BytesToBits (BitsToBytes b) = b

#guard Compress 1 (0 : Zq) = (0 : ZMod (m 1))
#guard Decompress 1 (0 : ZMod (m 1)) = (0 : Zq)
#guard Compress 4 (Decompress 4 (7 : ZMod (m 4))) = (7 : ZMod (m 4))

#guard ByteDecode (ByteEncode 1 (Vector.replicate 256 (0 : ZMod (m 1)))) = Vector.replicate 256 0

#guard (Polynomial.zero.ntt : NTTPolynomial) = 0
#guard (0 : NTTPolynomial).nttInv = Polynomial.zero
#guard (Polynomial.zero.ntt : NTTPolynomial).nttInv = Polynomial.zero

-- Appendix A spot checks: ζ^{BitRev7(i)} mod q
#guard (ζ ^ (bitRev 7 0) : Zq).val = 1
#guard (ζ ^ (bitRev 7 1) : Zq).val = 1729
#guard (ζ ^ (bitRev 7 64) : Zq).val = 17
#guard (ζ ^ (bitRev 7 127) : Zq).val = 2154

end Wychelean.KEM.MLKEM.Tests
