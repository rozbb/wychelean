import Wychelean.Hashes.SHA3.Basic

namespace Wychelean.Hashes.SHA3
open Wychelean Internal

namespace Incremental

section

-- FIPS 202 §4: an underlying function on b-bit strings and a rate satisfying 0 < r < b.
variable (f : BitVec b → BitVec b) (r : Nat) (hr : 0 < r ∧ r < b := by decide)

/-- Absorbing state (FIPS 202 Algorithm 8, steps 4–6). -/
structure sponge.absorbingState (rate : Nat) where
  S : BitVec b
  pending : Array Bit
  h_pending : pending.size < rate

/-- Squeezing state (FIPS 202 Algorithm 8, steps 8–10). -/
structure sponge.state (rate : Nat) where
  S : BitVec b
  x : Nat
  hx : x ≤ rate

/-- FIPS 202 Algorithm 8, step 5: initialize the permutation state to zero. -/
def sponge.init : sponge.absorbingState r :=
  { S := 0, pending := #[], h_pending := by simpa using hr.1 }

/-- FIPS 202 Algorithm 8, step 6: encode the rate block followed by zero capacity bits. -/
def sponge.blockMask (P : Array Bit) : BitVec b :=
  (BitVec.ofBitsLE P.toVector).zeroExtend b

/-- FIPS 202 Algorithm 8, step 6: absorb a complete block; otherwise buffer the bit. -/
def sponge.absorbBit (s : sponge.absorbingState r) (bit : Bit) : sponge.absorbingState r :=
  let input := s.pending.push bit
  if h : input.size = r then
    { S := f (s.S ^^^ sponge.blockMask input),
      pending := #[], h_pending := by simpa using hr.1 }
  else
    have h_pending : input.size < r := by
      have := s.h_pending
      simp only [input, Array.size_push] at h ⊢
      omega
    { s with pending := input, h_pending }

/-- Incremental form of FIPS 202 Algorithm 8, steps 4–6; padding is deferred. -/
def sponge.absorb (s : sponge.absorbingState r) (N : List Bit) : sponge.absorbingState r :=
  let k := r - s.pending.size
  let chunk := N.take k
  if h : chunk.length < k then
    { s with
      pending := s.pending ++ N.toArray,
      h_pending := by
        simp only [Array.size_append, List.size_toArray]
        have := s.h_pending
        simp only [chunk, List.length_take] at h
        omega }
  else
    let P := s.pending ++ chunk.toArray
    let S := f (s.S ^^^ sponge.blockMask P)
    sponge.absorb { S, pending := #[], h_pending := by simpa using hr.1 } (N.drop k)
termination_by N.length
decreasing_by
  have := s.h_pending
  simp_wf
  simp only [chunk, List.length_take] at *
  omega

/-- Append the suffix and padding (FIPS 202 Algorithm 8, step 1; §5.1, Algorithm 9). -/
def sponge.finalize (s : sponge.absorbingState r) (suffix : List Bit) : sponge.state r :=
  let s := sponge.absorb f r hr s suffix
  let s := sponge.absorb f r hr s («pad10*1» r s.pending.size).toBitsLE.toList
  { S := s.S, x := 0, hx := Nat.zero_le r }

/-- Bitwise FIPS 202 Algorithm 8, steps 8–10; permute when more output needs a new block. -/
def sponge.squeezeBit (s : sponge.state r) : sponge.state r × Bit :=
  if h : s.x = r then
    ({ S := f s.S, x := 1, hx := hr.1 }, (f s.S).getLsbD 0)
  else
    ({ s with x := s.x + 1, hx := by have := s.hx; omega }, s.S.getLsbD s.x)

/-- FIPS 202 Algorithm 8, steps 8–9: extract a portion of the rate block, low bits first. -/
def sponge.outputBits (S : BitVec b) (x d : Nat) : List Bit :=
  (S.extractLsb' x d).toBitsLE.toList

private theorem sponge.outputBits_length (S : BitVec b) (x d : Nat) :
    (sponge.outputBits S x d).length = d := by
  simp only [sponge.outputBits, Vector.length_toList]

end

/-- FIPS 202 Algorithm 8, steps 8–10; retain unused rate bits and permute only for more output. -/
def sponge.squeezeList (f : BitVec b → BitVec b) (r : Nat) (hr : 0 < r ∧ r < b := by decide)
    (s : sponge.state r) (d : Nat) : sponge.state r × List Bit :=
  if hd : d = 0 then (s, [])
  else if hx : s.x = r then
    sponge.squeezeList f r hr { S := f s.S, x := 0, hx := Nat.zero_le r } d
  else
    let k := r - s.x
    if h : d ≤ k then
      ({ s with x := s.x + d, hx := by have := s.hx; omega },
        sponge.outputBits s.S s.x d)
    else
      let Z := sponge.outputBits s.S s.x k
      let (s', Z') := sponge.squeezeList f r hr { s with x := r, hx := Nat.le_refl r } (d - k)
      (s', Z ++ Z')
termination_by (d, s.x)
decreasing_by
  all_goals have := s.hx; have := hr.1; omega

variable (f : BitVec b → BitVec b) (r : Nat) (hr : 0 < r ∧ r < b := by decide)

/-- FIPS 202 Algorithm 8's output-length requirement: exactly `d` bits. -/
@[simp] theorem sponge.squeezeList_length (s : sponge.state r) (d : Nat) :
    (sponge.squeezeList f r hr s d).2.length = d := by
  fun_induction sponge.squeezeList f r hr s d <;>
    simp_all [List.length_append, sponge.outputBits_length]
  rename_i s d hd hx k Z s' Z' hk heq ih
  simp only [Z, sponge.outputBits_length]
  omega

/-- Stateful form of FIPS 202 Algorithm 8, steps 8–10: output `d` bits and retain the context. -/
def sponge.squeeze (s : sponge.state r) (d : Nat) : sponge.state r × Vector Bit d :=
  let result := sponge.squeezeList f r hr s d
  (result.1, ⟨result.2.toArray, by simp [result]⟩)

end Incremental

/-! ## SHAKE128 and SHAKE256 -/

/-- FIPS 202 §§5.2, 6.2: initialize SHAKE128 at rate 1344 bits. -/
def SHAKE128.init := Incremental.sponge.init (r := b - 256) (hr := by decide)

/-- FIPS 202 §§5.2, 6.2: initialize SHAKE256 at rate 1088 bits. -/
def SHAKE256.init := Incremental.sponge.init (r := b - 512) (hr := by decide)

/-- FIPS 203 §4.1, Algorithm 2, step 3; Keccak-f: FIPS 202 §3.4; byte order: Appendix B.1. -/
def SHAKE128.absorb {n} (s : Incremental.sponge.absorbingState (b - 256)) (msg : ByteVec n) :=
  Incremental.sponge.absorb (Permutations.Keccak.keccak_f .w1600) (b - 256) (by decide)
    s (bytesToBits msg).toList

/-- SHAKE256 incremental analogue (FIPS 202 §§3.4, 6.2); byte order: Appendix B.1. -/
def SHAKE256.absorb {n} (s : Incremental.sponge.absorbingState (b - 512)) (msg : ByteVec n) :=
  Incremental.sponge.absorb (Permutations.Keccak.keccak_f .w1600) (b - 512) (by decide)
    s (bytesToBits msg).toList

/-- FIPS 202 §6.2: append the SHAKE suffix `1111` before padding. -/
def SHAKE128.finalize (s : Incremental.sponge.absorbingState (b - 256)) :=
  Incremental.sponge.finalize (Permutations.Keccak.keccak_f .w1600) (b - 256) (by decide)
    s xofSuffix.toBitsLE.toList

/-- FIPS 202 §6.2: append the SHAKE suffix `1111` before padding. -/
def SHAKE256.finalize (s : Incremental.sponge.absorbingState (b - 512)) :=
  Incremental.sponge.finalize (Permutations.Keccak.keccak_f .w1600) (b - 512) (by decide)
    s xofSuffix.toBitsLE.toList

/-- FIPS 203 §4.1, Algorithm 2, step 6; byte packing: FIPS 202 Appendix B.1. -/
def SHAKE128.squeeze (s : Incremental.sponge.state (b - 256)) (outBytes : Nat) :
    Incremental.sponge.state (b - 256) × ByteVec outBytes :=
  let (s, bits) := Incremental.sponge.squeeze (Permutations.Keccak.keccak_f .w1600)
    (b - 256) (by decide) s (8 * outBytes)
  (s, bitsToBytes bits)

/-- SHAKE256 incremental analogue (FIPS 202 §6.2); byte packing: Appendix B.1. -/
def SHAKE256.squeeze (s : Incremental.sponge.state (b - 512)) (outBytes : Nat) :
    Incremental.sponge.state (b - 512) × ByteVec outBytes :=
  let (s, bits) := Incremental.sponge.squeeze (Permutations.Keccak.keccak_f .w1600)
    (b - 512) (by decide) s (8 * outBytes)
  (s, bitsToBytes bits)

end Wychelean.Hashes.SHA3
